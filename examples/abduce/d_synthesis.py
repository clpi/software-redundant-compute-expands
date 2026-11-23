"""Domain D1: why are verified artifacts of the monotone-synthesis stream not admitted?

Observations: live artifacts that pass their verifier but whose admission record is not
derivable (pending). Log: one record per artifact, ok#id <- premises (verified) or
ok#id <- premises + qualify#id (not verified: assuming qualify#id is assuming a direct battery
check is added), and head <- ok#id. Abducibles: qualify#id for live unverified artifacts
(cost 1), assume:head for every head (cost 3: a capability from outside the evidence).

Usage: d_synthesis.py STREAM MODE K OUT.json   (MODE strict|raw)
"""
import json, sys, time
from collections import defaultdict
from engine import Log, ATMS, closure, front, minimal

stream, mode, k, out = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
rows = [json.loads(l) for l in open(stream).read().split("\n")[1:] if l]
changed = {a["home"] for a in rows if a["version"] == "f754884"}
live = {a["id"] for a in rows if a["version"] == "f754884" or a["home"] not in changed}


def ver(a):
    if a["verdict"] != "PASSED":
        return False
    return a["observed"] == "root" if mode == "strict" else a["observed"] in ("root", "reached")


lg = Log()
A, cost = [], {}
for a in rows:
    ok = f"ok#{a['id']}"
    if ver(a):
        lg.add(a["prem"], ok, artifact=a["id"])
    else:
        q = f"qualify#{a['id']}"
        if a["id"] in live:
            A.append(lg.atom(q)); cost[lg.atom(q)] = 1
        lg.add(a["prem"] + [q], ok, artifact=a["id"])
    lg.add([ok], a["head"], artifact=a["id"])
for h in sorted({a["head"] for a in rows}):
    v = f"assume:{h}"
    A.append(lg.atom(v)); cost[lg.atom(v)] = 3
    lg.add([v], h)

S0 = closure(lg.recs, [])
pending_all = [a for a in rows if ver(a) and lg.atom(f"ok#{a['id']}") not in S0]
O = [lg.atom(f"ok#{a['id']}") for a in pending_all if a["id"] in live]

t0 = time.time()
at = ATMS(A, k)
for r in lg.recs:
    at.add(r)
gen_secs = time.time() - t0

# candidates: every per-observation minimal explanation (size <= k)
cands = {}
for o in O:
    for e in at.explanations([o]):
        cands[e] = None

# components (observations sharing qualify abducibles in their backward cone) and their joint
# explanation, computed by the same ATMS with only that component's qualify abducibles.
byhead = defaultdict(list)
for r in lg.recs:
    byhead[r["head"]].append(r)


def cone_abd(o):
    seen, st, ab = set(), [o], set()
    while st:
        x = st.pop()
        if x in seen:
            continue
        seen.add(x)
        if x in at.A and lg.names[x].startswith("qualify#"):
            ab.add(x)
        for r in byhead[x]:
            st.extend(r["premises"])
    return ab


qc = {o: cone_abd(o) for o in O}
par = {o: o for o in O}


def find(x):
    while par[x] != x:
        par[x] = par[par[x]]; x = par[x]
    return x


inv = defaultdict(list)
for o in O:
    for x in qc[o]:
        inv[x].append(o)
for os_ in inv.values():
    for o in os_[1:]:
        par[find(o)] = find(os_[0])
comps = defaultdict(list)
for o in O:
    comps[find(o)].append(o)
joint = []
for os_ in comps.values():
    Aq = set().union(*(qc[o] for o in os_))
    at2 = ATMS(Aq, len(Aq))
    for r in lg.recs:
        at2.add(r)
    ex = at2.explanations(os_)
    joint.append({"obs": sorted(os_), "explanations": [sorted(e) for e in ex]})
    for e in ex:
        cands[e] = None

# components with no qualify-only explanation: union the cheapest per-observation explanations,
# then erase hypotheses while the union still explains (ends minimal: checked below).
def shrink(e, os_):
    e = sorted(e)
    for x in sorted(e, key=lambda x: (-cost[x], x)):
        t = [y for y in e if y != x]
        S = closure(lg.recs, t)
        if 0 not in S and all(o in S for o in os_):
            e = t
    return frozenset(e)


best = []
for j in joint:
    if j["explanations"]:
        e = min((frozenset(x) for x in j["explanations"]), key=lambda e: (sum(cost[x] for x in e), sorted(e)))
    else:
        # every abducible in the backward cone explains (if anything does); erase greedily,
        # dearest first, while it still explains: the result is erase-one minimal, not proven cheapest
        allc = set()
        for o in j["obs"]:
            seen, st_ = set(), [o]
            while st_:
                x = st_.pop()
                if x in seen:
                    continue
                seen.add(x)
                if x in at.A:
                    allc.add(x)
                for r in byhead[x]:
                    st_.extend(r["premises"])
        e = shrink(frozenset(allc), j["obs"])
        j["fallback"] = sorted(e)
    if e:
        best.append((e, j["obs"]))
        cands[e] = None

# plan: components in order of coverage per unit cost; every prefix is a candidate
best.sort(key=lambda b: (-len(b[1]) / sum(cost[x] for x in b[0]), sorted(b[0])))
acc = frozenset()
plan = []
for e, os_ in best:
    acc = acc | e
    cands[acc] = None
    plan.append(acc)

# score every candidate against every observation (closure), then the Pareto front
scored = []
for e in cands:
    S = closure(lg.recs, e)
    if 0 in S:
        continue
    cov = sorted(o for o in O if o in S)
    scored.append((tuple(sorted(e)), len(cov), sum(cost[x] for x in e), cov))
fr = front([(s[0], s[1], s[2]) for s in scored])
frkeys = {f[0] for f in fr}


def kind(e):
    """Type of a hypothesis: missing direct evidence, a cycle, or a missing capability."""
    kinds = set()
    pend_heads = {a["head"] for a in pending_all}
    for x in e:
        n = lg.names[x]
        if n.startswith("qualify#"):
            kinds.add("missing-direct-evidence")
        elif n[len("assume:"):] in pend_heads:
            kinds.add("cycle")
        else:
            kinds.add("missing-capability")
    return sorted(kinds)


res = {
    "mode": mode, "k": k, "records": len(lg.recs), "log_head": lg.head_hash(),
    "pending_all": len(pending_all), "pending_live": len(O), "abducibles": len(A),
    "atms_ops": dict(at.ops), "generation_seconds": round(gen_secs, 3),
    "observations": [lg.names[o] for o in O],
    "obs_without_explanation_at_k": [lg.names[o] for o in O if not at.explanations([o])],
    "components": len(comps), "component_sizes": sorted(len(v) for v in comps.values()),
    "joint": [{"obs": [lg.names[o] for o in j["obs"]], "explanations": [[lg.names[x] for x in e] for e in j["explanations"]], "fallback": [lg.names[x] for x in j.get("fallback", [])]} for j in joint],
    "candidates": len(scored),
    "plan": [{"hyp_count": len(p_), "cost": sum(cost[x] for x in p_),
              "cover": sum(1 for o in O if o in closure(lg.recs, p_))} for p_ in plan],
    "plan_final": [lg.names[x] for x in sorted(plan[-1])] if plan else [],
    "front": [{"hyp": [lg.names[x] for x in s[0]], "cover": s[1], "cost": s[2], "kind": kind(s[0]),
               "covers": [lg.names[o] for o in s[3]]} for s in sorted(scored, key=lambda s: (-s[1], s[2], s[0])) if s[0] in frkeys],
    "names": lg.names, "recs": lg.recs, "A": A, "O": O,
}
json.dump(res, open(out, "w"), indent=0, sort_keys=True)
print(json.dumps({k_: v for k_, v in res.items() if k_ not in ("names", "recs", "A", "O", "joint", "front", "observations", "plan", "plan_final")}, sort_keys=True))
print("plan", [(p_["cover"], p_["cost"]) for p_ in res["plan"]])
for f_ in res["front"][:12]:
    print(f_["cover"], f_["cost"], f_["kind"], f_["hyp"][:6])
