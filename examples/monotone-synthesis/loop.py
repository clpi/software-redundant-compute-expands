"""The monotone synthesis loop: incremental admission over one append-only log, checked
against a from-scratch spec at every prefix.

Spec (MonotoneSynthesis.lean): an add is admitted iff the verifier accepts it, its id is
fresh and every premise is reachable; a retirement iff old and new are live, distinct, and
everything reachable stays reachable (checked as replaceB: same head, new's premises
reachable without old). Reach = least closure of the host primitives under live artifacts.

Incremental engine: a premise counter per pending candidate and a waiter index per missing
capability (the counter worklist of srce proof/Worklist.lean, specialized to admission);
a pending candidate is retried exactly when its last missing premise becomes reachable, so
the loop is saturated after every event. Retirements recheck only the replacement's
premises against a closure without the retired artifact.

Cold baseline at every prefix: (a) the least closure of the log's live rules from scratch;
(b) the closure of every verified candidate offered so far (`target`, saturated_exact).
Both computed with a from-scratch worklist (fair baseline) and with naive rounds.

usage: loop.py stream.jsonl [--strict] [--order history|reverse|shuffle:SEED] [--raw]
                 [--mutant NAME] [--flip-home HOME] [--fake-retire]
Prints one JSON summary line; with --trace, also one line per event.
"""
import argparse, json, random, sys
from collections import defaultdict

ap = argparse.ArgumentParser()
ap.add_argument("stream")
ap.add_argument("--strict", action="store_true", help="verifier: battery PASSED and applied directly from battery code")
ap.add_argument("--order", default="history")
ap.add_argument("--raw", action="store_true", help="no strongly-connected grouping (mutual recursion stays blocked)")
ap.add_argument("--mutant", default="")
ap.add_argument("--flip-home", default="")
ap.add_argument("--fake-retire", action="store_true", help="control: retire an admitted function for a live one with a different head")
ap.add_argument("--trace", action="store_true")
ap.add_argument("--abstractions", action="store_true")
ap.add_argument("--dump-reach", default="")
args = ap.parse_args()

lines = open(args.stream).read().split("\n")
header = json.loads(lines[0])
arts = [json.loads(l) for l in lines[1:] if l]

def verified(a):
    if a["home"] == args.flip_home:
        return False
    if args.mutant == "no-verifier":
        return True
    if a["verdict"] != "PASSED":
        return False
    return a["observed"] == "root" if args.strict else a["observed"] in ("root", "reached")

# ---- encoding: strongly connected groups become one artifact plus one projection per member
def group(arts):
    out, byver = [], defaultdict(list)
    for a in arts:
        byver[a["version"]].append(a)
    nid = max(a["id"] for a in arts) + 1
    for ver, A in byver.items():
        g = {a["head"]: a for a in A}
        idx, low, st, on, comp_of, c = {}, {}, [], set(), {}, [0]
        sys.setrecursionlimit(100000)
        def dfs(v):
            idx[v] = low[v] = c[0]; c[0] += 1; st.append(v); on.add(v)
            for w in g[v]["prem"]:
                if w not in g:
                    continue
                if w not in idx:
                    dfs(w); low[v] = min(low[v], low[w])
                elif w in on:
                    low[v] = min(low[v], idx[w])
            if low[v] == idx[v]:
                comp = []
                while True:
                    w = st.pop(); on.discard(w); comp.append(w)
                    if w == v:
                        break
                for w in comp:
                    comp_of[w] = tuple(sorted(comp))
        for v in g:
            if v not in idx:
                dfs(v)
        done = set()
        for a in A:
            comp = comp_of[a["head"]]
            if len(comp) == 1:
                out.append(a); continue
            if comp in done:
                continue
            done.add(comp)
            members = [g[h] for h in comp]
            ghead = f"{a['home']}:<group {'+'.join(h.split(':', 1)[1] for h in comp)}>"
            ext = sorted({p for m in members for p in m["prem"] if p not in comp})
            first = min(members, key=lambda m: (m["time"], m["line"]))
            gart = dict(first, head=ghead, prem=ext, id=nid, path=ghead, group=list(comp),
                        observed=("root" if any(m["observed"] == "root" for m in members) else
                                  "reached" if any(m["observed"] == "reached" for m in members) else "unreached"))
            nid += 1
            out.append(gart)
            for m in sorted(members, key=lambda m: m["line"]):
                out.append(dict(m, prem=[ghead], projection_of=ghead))
    order = {a["id"]: k for k, a in enumerate(arts)}
    out.sort(key=lambda a: (a["time"], 0 if a["version"] == "0be14af" else 1, a["home"],
                            a["line"], 0 if "group" in a else 1))
    return out

if not args.raw:
    arts = group(arts)

# ---- events: offers, then replacement requests for PR 24's versions
byhead_old = {a["head"]: a for a in arts if a["version"] == "0be14af"}
events = []
for a in arts:
    events.append(("offer", a))
    if a["version"] == "f754884" and a["head"] in byhead_old and "projection_of" not in a:
        events.append(("retire", byhead_old[a["head"]], a))
changed = {a["home"] for a in arts if a["version"] == "f754884"}
newheads = {a["head"] for a in arts if a["version"] == "f754884"}
last_new = max((k for k, e in enumerate(events) if e[0] == "offer" and e[1]["version"] == "f754884"), default=-1)
removed = [a for a in arts if a["version"] == "0be14af" and a["home"] in changed and a["head"] not in newheads]
for a in removed:
    events.insert(last_new + 1, ("retire", a, None))
if args.fake_retire:
    # retire json:parse for json:render (both live by the end, different heads): must be refused
    old = next(a for a in arts if a["head"] == "json:parse")
    new = next(a for a in arts if a["head"] == "json:render")
    events.append(("retire", old, new))

if args.order == "reverse":
    events.reverse()
elif args.order.startswith("shuffle:"):
    random.Random(int(args.order.split(":")[1])).shuffle(events)

# ---- incremental engine
P = set()          # host primitives: builtins are unresolved applications, never premises here
log, live, provides = [], {}, defaultdict(int)
providers = defaultdict(set)
used_ids, pending, waiters = set(), {}, defaultdict(set)
retire_waits = defaultdict(list)
ops = defaultdict(int)
spec_ops = [0]
cone_disagree = []
refusals = defaultdict(int)
admitted_at = {}
deferred = set()
deferred_commit = {}

def reachable(h):
    return h in P or provides[h] > 0

def admit(a):
    got = [a["id"]]
    log.append(("add", a["id"], a["head"], tuple(a["prem"])))
    live[a["id"]] = a
    used_ids.add(a["id"])
    admitted_at[a["id"]] = len(log)
    new = provides[a["head"]] == 0
    provides[a["head"]] += 1
    providers[a["head"]].add(a["id"])
    if new and args.mutant != "no-retry":
        stack = [a["head"]]
        while stack:
            h = stack.pop()
            for w in sorted(waiters.pop(h, ())):
                ops["wake"] += 1
                if w not in pending:
                    continue
                miss, cand = pending[w]
                miss.discard(h)
                if not miss:
                    del pending[w]
                    deferred.add(w)
                    deferred_commit[w] = cur_commit[0]
                    if provides[cand["head"]] == 0:
                        stack.append(cand["head"])
                    log.append(("add", cand["id"], cand["head"], tuple(cand["prem"])))
                    live[cand["id"]] = cand
                    used_ids.add(cand["id"])
                    admitted_at[cand["id"]] = len(log)
                    provides[cand["head"]] += 1
                    providers[cand["head"]].add(cand["id"])
                    got.append(cand["id"])
    try_retires(got)

def offer(a):
    ops["offer"] += 1
    if not verified(a):
        refusals["evidence"] += 1; return "refused:evidence"
    if a["id"] in used_ids:
        refusals["id"] += 1; return "refused:id"
    ops["premise_check"] += len(a["prem"])
    if args.mutant == "no-premise-check":
        admit(a); return "admitted"
    miss = {p for p in a["prem"] if not reachable(p)}
    if not miss:
        admit(a); return "admitted"
    if args.mutant == "no-retry":
        refusals["premise"] += 1; return "refused:premise"
    pending[a["id"]] = (miss, a)
    for p in miss:
        waiters[p].add(a["id"])
    return "pending"

def closure_without(rules, skip):
    """Least closure of `rules` (id -> (head, prem)) without id `skip`, from scratch."""
    have, cnt, wait, q = set(P), {}, defaultdict(list), []
    for i, (h, ps) in rules.items():
        if i == skip:
            continue
        m = [p for p in set(ps) if p not in have]
        spec_ops[0] += len(ps)
        cnt[i] = len(m)
        for p in m:
            wait[p].append(i)
        if not m:
            q.append(i)
    while q:
        i = q.pop()
        h = rules[i][0]
        if h in have:
            continue
        have.add(h)
        for j in wait.pop(h, ()):
            spec_ops[0] += 1
            cnt[j] -= 1
            if cnt[j] == 0:
                q.append(j)
    return have

def retire(old, new):
    ops["retire_req"] += 1
    if args.mutant == "no-cover":
        if old["id"] in live:
            do_retire(old, new); return "retired"
        return "deferred"
    if not verified(old):
        refusals["moot"] += 1; return "moot"
    if new is None:
        refusals["no_replacement"] += 1; return "refused:no-replacement"
    if old["id"] not in live or new["id"] not in live:
        if args.mutant == "eager-retire" and old["id"] in live:
            do_retire(old, new); return "retired"
        wait_id = old["id"] if old["id"] not in live else new["id"]
        retire_waits[wait_id].append((old, new)); return "deferred"
    if new["head"] != old["head"] or new["id"] == old["id"]:
        refusals["not_covering"] += 1; return "refused:not-covering"
    # incremental: closure restricted to the backward cone of new's premises, without old
    cone, stack, seen = {}, list(new["prem"]), set()
    while stack:
        h = stack.pop()
        if h in seen:
            continue
        seen.add(h)
        for i in providers[h]:
            if i == old["id"]:
                continue
            ops["retire_check"] += 1
            cone[i] = (live[i]["head"], live[i]["prem"])
            stack.extend(live[i]["prem"])
    after, c = cold_closure(cone)
    ops["retire_check"] += c
    ok = all(p in after for p in new["prem"])
    # spec cross-check (not counted as incremental work): the full closure without old
    rules = {i: (x["head"], x["prem"]) for i, x in live.items()}
    full = closure_without(rules, old["id"])
    if ok != all(p in full for p in new["prem"]):
        cone_disagree.append(old["head"])
    if not ok:
        refusals["not_covering"] += 1; return "refused:not-covering"
    do_retire(old, new); return "retired"

def do_retire(old, new):
    log.append(("retire", old["id"], new["id"] if new else None))
    del live[old["id"]]
    provides[old["head"]] -= 1
    providers[old["head"]].discard(old["id"])

def try_retires(ids):
    for i in ids:
        for old, new in retire_waits.pop(i, ()):
            retire(old, new)

# ---- cold spec
def cold_closure(rules):
    """From-scratch worklist closure; returns (set, checks)."""
    have, cnt, wait, q, checks = set(P), {}, defaultdict(list), [], 0
    for i, (h, ps) in rules.items():
        ps = set(ps)
        checks += len(ps)
        m = [p for p in ps if p not in have]
        cnt[i] = len(m)
        for p in m:
            wait[p].append(i)
        if not m:
            q.append(i)
    while q:
        i = q.pop()
        h = rules[i][0]
        if h in have:
            continue
        have.add(h)
        for j in wait.pop(h, ()):
            checks += 1
            cnt[j] -= 1
            if cnt[j] == 0:
                q.append(j)
    return have, checks

def naive_closure_checks(rules):
    have, checks, changed = set(P), 0, True
    while changed:
        changed = False
        for i, (h, ps) in rules.items():
            if h in have:
                continue
            checks += len(ps)
            if all(p in have for p in ps):
                have.add(h); changed = True
    return checks

def log_rules():
    retired = {e[1] for e in log if e[0] == "retire"}
    return {e[1]: (e[2], e[3]) for e in log if e[0] == "add" and e[1] not in retired}

pool = {}
mismatch, monotone_breaks, unsat = [], 0, 0
cold_wl = cold_naive = 0
prev_reach = set()
trace = []
cur_commit = [None]
offer_commit = {}
for k, ev in enumerate(events):
    cur_commit[0] = ev[2]["commit"] if ev[0] == "retire" and ev[2] else ev[1]["commit"]
    if ev[0] == "offer":
        a = ev[1]
        offer_commit[a["id"]] = a["commit"]
        r = offer(a)
        if verified(a):
            pool[a["id"]] = (a["head"], a["prem"])
    else:
        r = retire(ev[1], ev[2])
    inc = {h for h, n in provides.items() if n > 0} | P
    cold, _ = cold_closure(log_rules())        # spec check: reach of the log, from scratch
    tgt, c2 = cold_closure(pool)               # cold baseline: what a from-scratch system computes
    cold_wl += c2
    cold_naive += naive_closure_checks(pool)
    if inc != cold:
        mismatch.append((k, "log", len(inc ^ cold)))
    if inc != tgt:
        unsat += 1
        if len(mismatch) < 20:
            mismatch.append((k, "target", len(inc ^ tgt)))
    if not prev_reach <= inc:
        monotone_breaks += 1
    prev_reach = inc
    if args.trace:
        trace.append({"k": k, "event": ev[0], "head": ev[1]["head"], "result": r, "reach": len(inc)})

# ---- measures
final = {h for h, n in provides.items() if n > 0} | P
live_rules = log_rules()
depth = {}
def d(h, seen=()):
    if h in depth:
        return depth[h]
    provs = [ps for (hh, ps) in live_rules.values() if hh == h]
    best = min((1 + max((d(p, seen + (h,)) for p in ps), default=0)) for ps in provs) if provs else 0
    depth[h] = best
    return best
for h in final:
    d(h)

abstr = {}
if args.abstractions:
    # one round of composition: inline one premise of an admitted artifact by the premises of a
    # live provider. Each such rule's head is derivable from its premises (by construction), so
    # by abstract_conservative reach is unchanged; measured: reach unchanged, depth shortened.
    prov = defaultdict(list)
    for i, (h, ps) in live_rules.items():
        prov[h].append(ps)
    new_rules = dict(live_rules)
    nid = 10**6
    for i, (h, ps) in list(live_rules.items()):
        for p in ps:
            for qs in prov.get(p, []):
                comp = tuple(sorted((set(ps) - {p}) | set(qs)))
                if h in comp:
                    continue
                new_rules[nid] = (h, comp); nid += 1
    after, _ = cold_closure(new_rules)
    depth2 = {}
    def d2(h):
        if h in depth2:
            return depth2[h]
        depth2[h] = 0
        provs = [ps for (hh, ps) in new_rules.values() if hh == h]
        best = min((1 + max((d2(p) for p in ps), default=0)) for ps in provs) if provs else 0
        depth2[h] = best
        return best
    for h in after:
        d2(h)
    abstr = {"rules_added": nid - 10**6, "reach_unchanged": after == final,
             "max_depth_before": max(depth.values(), default=0), "max_depth_after": max(depth2.values(), default=0),
             "sum_depth_before": sum(depth.values()), "sum_depth_after": sum(depth2[h] for h in depth)}

dependents = defaultdict(set)
for i, (h, ps) in live_rules.items():
    for p in ps:
        dependents[p].add(h)
def trans(h, memo={}):
    if h in memo:
        return memo[h]
    memo[h] = set()
    acc = set()
    for x in dependents.get(h, ()):
        acc.add(x); acc |= trans(x)
    memo[h] = acc
    return acc
tdeps = [len(trans(h)) for h in final]
compounding = {
    "capabilities_used_by_others": sum(1 for h in final if dependents.get(h)),
    "mean_transitive_dependents": round(sum(tdeps) / max(1, len(tdeps)), 3),
    "max_transitive_dependents": max(tdeps, default=0),
    "deferred_across_commits": sum(1 for w in deferred if deferred_commit.get(w) != offer_commit.get(w)),
}
cross_home = sum(1 for (h, ps) in live_rules.values() for p in ps if p.split(":")[0] != h.split(":")[0])
retire_log = [e for e in log if e[0] == "retire"]
summary = {
    "order": args.order, "strict": args.strict, "raw": args.raw, "mutant": args.mutant,
    "flip_home": args.flip_home, "fake_retire": args.fake_retire,
    "events": len(events), "offered": sum(1 for e in events if e[0] == "offer"),
    "admitted": sum(1 for e in log if e[0] == "add"), "live": len(live), "reach": len(final),
    "pending_at_end": len(pending), "pending_retire_at_end": sum(len(v) for v in retire_waits.values()),
    "retired": len(retire_log),
    "cone_vs_full_disagreements": cone_disagree,
    "pending_retire_heads": sorted({o["head"] for v in retire_waits.values() for o, n in v}), "refusals": dict(refusals), "deferred_admissions": len(deferred),
    "incremental_ops": dict(ops), "incremental_total": sum(ops.values()),
    "cold_worklist_checks": cold_wl, "cold_naive_checks": cold_naive,
    "mismatch_log": sum(1 for m in mismatch if m[1] == "log"), "unsaturated_prefixes": unsat,
    "monotone_breaks": monotone_breaks, "first_mismatches": mismatch[:5],
    "max_depth": max(depth.values(), default=0),
    "depth_hist": {str(k): sum(1 for v in depth.values() if v == k) for k in sorted(set(depth.values()))},
    "cross_home_premises": cross_home, "compounding": compounding, "abstractions": abstr,
    "reach_sha_input": sorted(final),
}
import hashlib
_once, _c = cold_closure(pool)
summary["cold_once_final_checks"] = _c
if args.dump_reach:
    open(args.dump_reach, "w").write("\n".join(sorted(final)) + "\n")
summary["reach_sha256"] = hashlib.sha256("\n".join(summary.pop("reach_sha_input")).encode()).hexdigest()
summary["live_ids_sha256"] = hashlib.sha256(",".join(map(str, sorted(live))).encode()).hexdigest()
if args.trace:
    for t in trace:
        print(json.dumps(t))
print(json.dumps(summary, sort_keys=True))
