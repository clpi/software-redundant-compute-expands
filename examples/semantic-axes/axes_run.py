# Semantic axes over the candidate space (AXES.json), same contract
# and same hash-chained log discipline as examples/algorithm-search.
#   python3 axes_run.py dev OUT            measure every candidate on every axis (dev)
#   python3 axes_run.py heldout OUT IDOL_LIB
#                                          re-run the frozen survivors on held-out data
import gc, itertools, json, os, random, statistics, sys, time, tracemalloc
HERE = os.path.dirname(os.path.abspath(__file__))
AS = os.path.join(HERE, "..", "algorithm-search")
sys.path.insert(0, HERE); sys.path.insert(0, AS)
import engines as E
import closure, decide, traces
import run_search as R
from space import Space, sha

REPEATS = int(os.environ.get("REPEATS", "5"))
EYES = R.EYES

def timed(fn, repeats=REPEATS):
    ws = []
    out = None
    for _ in range(repeats):
        gc.collect(); t = time.perf_counter(); out = fn(); ws.append((time.perf_counter() - t) * 1000)
    q = statistics.quantiles(ws, n=4) if len(ws) > 1 else [ws[0]] * 3
    return out, {"median": statistics.median(ws), "p25": q[0], "p75": q[2]}

def peak(fn):
    gc.collect(); tracemalloc.start(); fn(); p = tracemalloc.get_traced_memory()[1]; tracemalloc.stop()
    return round(p / 1024, 1)

def meas(S, cand, inp, obj, value, phase, extra=None):
    R.meas(S, cand, inp, obj, value, phase, extra)

# ------------------------------------------------------------------
# candidate generation (components x constraints), as records
# ------------------------------------------------------------------
AXES = {
 "a": {"engine": ["counter", "watch", "rounds"], "undo": ["none", "journal", "snapshot"],
       "witness": ["on", "off"], "merge": ["propagate", "recompute"]},
 "b": {"engine": ["archive", "cold"], "undo": ["none", "residual", "snapshot", "recompute"],
       "witness": ["off", "on", "repoint"]},
 "j": {"compose": ["sequential", "tree"]},
 "s": {"rule": ["ws", "ch", "ach"], "frame": ["fixed", "data"]},
}
CONTROLS = {
 "cand:ax-a/control=null": "do-nothing: derives nothing, merge returns left state, undo does nothing",
 "cand:ax-a/control=lookahead": "gamed: handed the future, reports every derivable term at the first append",
 "cand:ax-a/control=firsthead": "gamed visibility: counter whose witness is the first record with that head",
 "cand:ax-a/control=lastwitness": "gamed visibility: counter whose witness is always the record just appended",
 "cand:ax-b/control=null": "do-nothing: empty front, no witnesses",
 "cand:ax-b/control=allfront": "gamed: reports every point as the front",
}

def generate(S):
    S.append("axes", [], ["declared"], {"sha256": sha(os.path.join(HERE, "AXES.json")),
             "extends": sha(os.path.join(AS, "OBJECTIVES.json"))})
    for fam, ax in AXES.items():
        for a, vals in ax.items():
            for v in vals:
                S.append("comp:ax-%s/%s=%s" % (fam, a, v), [], ["component", "family:ax-" + fam], {})
    S.append("rule:ax-a rounds has no journal", [], ["constraint"], {"why": "a round-based engine has no per-append change set to journal; undo=journal collapses to none"})
    S.append("rule:ax-b cold has no residual", [], ["constraint"], {"why": "cold recomputation keeps no per-insert removals; undo=residual collapses to recompute"})
    made = {}
    for fam, ax in AXES.items():
        names = list(ax)
        for combo in itertools.product(*[ax[n] for n in names]):
            c = dict(zip(names, combo))
            if fam == "a" and c["engine"] == "rounds" and c["undo"] == "journal": c["undo"] = "none"
            if fam == "b" and c["engine"] == "cold" and c["undo"] == "residual": c["undo"] = "recompute"
            key = "cand:ax-%s/" % fam + ",".join("%s=%s" % (n, c[n]) for n in names)
            colors = ["candidate", "family:ax-" + fam, "generated:product"] + (["collapsed"] if key in made else [])
            S.append(key, ["comp:ax-%s/%s=%s" % (fam, n, combo[i]) for i, n in enumerate(names)], colors, {"components": c})
            made[key] = c
    for k, why in CONTROLS.items():
        S.append(k, [], ["candidate", "control", "family:" + k.split(":")[1].split("/")[0]], {"what": why})
        made[k] = {"control": k.split("=")[1]}
    # the current approach (PR 7 survivors) as derivations of the same terms
    for k in ["cand:ax-a/engine=counter,undo=none,witness=on,merge=propagate",
              "cand:ax-a/engine=watch,undo=none,witness=on,merge=propagate",
              "cand:ax-b/engine=archive,undo=none,witness=off", "cand:ax-b/engine=cold,undo=recompute,witness=off"]:
        S.append(k, [], ["candidate", "current-approach", "family:" + k.split(":")[1].split("/")[0]], {"source": "PR 7 survivor"})
    return made

# ------------------------------------------------------------------
# closure family
# ------------------------------------------------------------------
def make_closure(c, trace):
    if "control" in c:
        if c["control"] == "null": return E.Null()
        if c["control"] == "lookahead": return E.Lookahead(future=trace)
        if c["control"] == "firsthead": return E.Counter(firsthead=True)
        if c["control"] == "lastwitness": return E.Counter(lastwitness=True)
    return E.ENGINES[c["engine"]](undo=c["undo"], witness=c["witness"])

def check_witness(trace, emitted):
    """emitted: list of (step, term, witness). Independent checker."""
    pos, ok = {}, 0
    for n, (k, g, w) in enumerate(emitted):
        pos.setdefault(g, n)
    for n, (k, g, w) in enumerate(emitted):
        if w is None or not (0 <= w <= k) or not closure.admits(trace[w]) or trace[w][4] != g:
            continue
        if all(p in pos and pos[p] < pos[g] for p in trace[w][3]):
            ok += 1
    return ok

def closure_main(c, trace, e):
    def once():
        x = make_closure(c, trace)
        emitted, cum = [], []
        for k, rec in enumerate(trace):
            for g in x.append(rec, k):
                emitted.append((k, g, x.wit.get(g)))
            cum.append(x.ops)
        return x, emitted, cum
    (x, emitted, cum), w = timed(once)
    correct = all(e.get(g) == k for k, g, _ in emitted) and set(x.D) == set(e) and len(emitted) == len(e)
    vis = check_witness(trace, emitted) / max(len(e), 1)
    pk = peak(once)
    return x, correct, vis, cum, w, pk

def closure_undo(c, trace, e, cum, every=50):
    """cum: cumulative ops of the plain counter (common baseline)."""
    x = make_closure(c, trace)
    ok = tested = changed = 0
    savings = []
    for k, rec in enumerate(trace):
        x.append(rec, k)
        if k % every == every - 1 and k > 0:
            tested += 1
            before = x.ops
            refk1 = {t for t, s in e.items() if s <= k - 1}
            refk = {t for t, s in e.items() if s <= k}
            if refk != refk1: changed += 1
            done = x.undo_last()
            uops = x.ops - before
            good = done and set(x.D) == refk1
            x.append(rec, k)
            good = good and set(x.D) == refk
            ok += good
            if good:
                savings.append(1 - uops / max(cum[k - 1], 1))
    if tested == 0:
        return 0.0, {}
    rate = ok / tested
    score = rate * (statistics.mean(savings) if savings else 0.0)
    return max(score, 0.0), {"tested": tested, "exact": ok, "appends_that_changed_state": changed}

def closure_merge(c, trace, made_kind, base_ops):
    mid = len(trace) // 2
    LA, LB = trace[:mid], trace[mid:]
    ref = set(closure.earliest(trace))
    if "control" in c:
        if c["control"] == "null":
            return 0.0, {"correct": False}
        kind = "recompute" if c["control"] == "lookahead" else "propagate"
        base = {"engine": "counter", "undo": "none", "witness": "on"}
    else:
        kind, base = made_kind, c
    def build(L, off=0):
        s = E.ENGINES[base["engine"]](witness=base["witness"])
        for k, r in enumerate(L): s.append(r, k + off)
        return s
    whole = build(trace)
    A, B = build(LA), build(LB)
    m, mops = E.merge(kind, A, B, mid, lambda: build(trace))
    good = set(m.D) == ref
    # continuation: re-append the first 200 records; nothing may change
    for k, r in enumerate(trace[:200]):
        m.append(r, len(trace) + k)
    good = good and set(m.D) == ref
    return (good * max(0.0, 1 - mops / max(base_ops, 1))), {"correct": good, "merge_ops": mops, "whole_ops_same_engine": whole.ops, "baseline_ops": base_ops}

def closure_orders(c, trace, base_ops):
    outs = []
    variants = [list(reversed(trace))]
    for seed in (1, 2, 3):
        t = list(trace); random.Random(seed).shuffle(t); variants.append(t)
    ok = True
    for t in variants:
        e = closure.earliest(t)
        x = make_closure(c, t)
        for k, r in enumerate(t): x.append(r, k)
        ok = ok and set(x.D) == set(e)
        outs.append(x.ops)
    spread = (max(outs) - min(outs)) / max(base_ops, 1)
    return (ok * max(0.0, 1 - spread)), {"ops": outs, "all_correct": ok, "baseline_ops": base_ops}

def closure_robust(c, trace, name):
    import heldout as H
    ctl = H.controls(name, trace)
    keep = [k for k in ctl if k.endswith(("+dup-records", "+dup-premises", "+filtered"))]
    good = 0
    for k in keep:
        t = ctl[k]; e = closure.earliest(t)
        x = make_closure(c, t); ok = True
        for i, r in enumerate(t):
            for g in x.append(r, i):
                ok = ok and e.get(g) == i
        good += ok and set(x.D) == set(e)
    return good / len(keep), {"variants": keep}

def run_closure(S, made, inputs, phase, only=None):
    cands = [k for k in made if k.startswith("cand:ax-a/") and (only is None or k in only)]
    for name, tr in inputs.items():
        e = closure.earliest(tr)
        sc = closure.Scratch("on", "short")
        for r in tr: sc.append(r)
        base_ops = sc.ops
        once = E.Rounds(witness="off")
        once.rules = [(E.dprem(r), r[4], k) for k, r in enumerate(tr) if closure.admits(r)]
        once._close(); once_ops = once.ops
        pc = E.Counter(witness="off"); ccum = []
        for k, r in enumerate(tr):
            pc.append(r, k); ccum.append(pc.ops)
        S.append("input:ax/" + name, [], ["input", "trace", "phase:" + phase],
                 {"records": len(tr), "sha256": traces.digest(tr), "scratch_ops": base_ops,
                  "one_fixpoint_ops": once_ops, "plain_counter_ops": pc.ops})
        for k in cands:
            c = made[k]
            x, correct, vis, cum, w, pk = closure_main(c, tr, e)
            inp = "ax/" + name
            meas(S, k, inp, "correct_every_prefix", correct, phase)
            meas(S, k, inp, "premise_ops", x.ops, phase)
            meas(S, k, inp, "wall_ms", round(w["median"], 3), phase, {"p25": w["p25"], "p75": w["p75"]})
            meas(S, k, inp, "peak_kib", pk, phase)
            meas(S, k, inp, "visibility", round(vis, 4), phase)
            meas(S, k, inp, "work_saved", round(correct * max(0.0, 1 - x.ops / base_ops), 6), phase, {"scratch_ops": base_ops})
            u, ux = closure_undo(c, tr, e, ccum)
            meas(S, k, inp, "reversibility", round(u, 6), phase, ux)
            mk = c.get("merge", "propagate")
            m, mx = closure_merge(c, tr, mk, once_ops)
            meas(S, k, inp, "compositionality", round(m, 6), phase, mx)
            o, ox = closure_orders(c, tr, base_ops)
            meas(S, k, inp, "order_invariance", round(o, 6), phase, ox)
            rb, rx = closure_robust(c, tr, name)
            meas(S, k, inp, "robustness", round(rb, 4), phase, rx)
            print(phase, name, k, correct, x.ops, round(w["median"], 2), pk, "vis", round(vis, 3), "ws", round(1 - x.ops / base_ops, 4),
                  "rev", round(u, 3), "comp", round(m, 3), "ord", round(o, 3), "rob", round(rb, 3), flush=True)

# ------------------------------------------------------------------
# front family
# ------------------------------------------------------------------
class Cold:
    """Cold sort-filter recomputation after every arrival (PR 7 survivor)."""
    def __init__(self, undo="recompute", witness="off"):
        self.items, self.m, self.wit, self.ops = [], {}, {}, [0]
        self.witness_on = witness != "off"; self.undo = undo; self.last = None
    def _recompute(self):
        srt = sorted(self.items, key=lambda t: (sum(t[1]), t[1], t[0]))
        kept = []
        self.wit = {}
        for i, a in srt:
            sa, dom = sum(a), None
            for j, b in kept:
                if sum(b) < sa and E.dominates(b, a, self.ops):
                    dom = j; break
            if dom is None: kept.append((i, a))
            elif self.witness_on: self.wit[i] = dom
        self.m = dict(kept)
    def insert(self, i, a):
        if self.undo == "snapshot":
            self.last = (dict(self.m), dict(self.wit)); self.ops[0] += len(self.m) + len(self.wit)
        self.items.append((i, a)); self._recompute()
    def undo_last(self):
        self.items.pop()
        if self.undo == "snapshot":
            self.m, self.wit = self.last; return True
        self._recompute(); return True

class Repoint(E.Archive):
    """Archive whose witnesses follow removals: when a member is removed,
    every point it witnessed is re-pointed to the remover (cost counted)."""
    def __init__(self, undo="none"):
        super().__init__(undo=undo, witness="on")
        self.by = {}
    def insert(self, i, a):
        before = set(self.m)
        super().insert(i, a)
        if i in self.m:
            for j in before - set(self.m):
                for x in self.by.pop(j, []):
                    self.wit[x] = i; self.by.setdefault(i, []).append(x); self.ops[0] += 1
                self.by.setdefault(i, []).append(j)
        elif i in self.wit:
            self.by.setdefault(self.wit[i], []).append(i)

class NullFront:
    def __init__(self, **kw): self.m, self.wit, self.ops = {}, {}, [0]
    def insert(self, i, a): pass
    def undo_last(self): return True

class AllFront(NullFront):
    def insert(self, i, a): self.m[i] = a

def make_front(c):
    if "control" in c:
        return NullFront() if c["control"] == "null" else AllFront()
    if c["engine"] == "cold":
        return Cold(undo=c["undo"], witness=c["witness"])
    if c["witness"] == "repoint":
        return Repoint(undo=c["undo"])
    return E.Archive(undo=c["undo"], witness=c["witness"])

def front_main(c, items):
    def once():
        x = make_front(c); fronts = []
        for i, v in items:
            x.insert(i, v); fronts.append(set(x.m))
        return x, fronts
    (x, fronts), w = timed(once)
    refs = [R.exact_front(items[:j + 1]) for j in range(len(items))]
    correct = fronts == refs
    final = refs[-1]
    vals = dict(items)
    nonfront = [i for i, _ in items if i not in final]
    good = 0
    for i in nonfront:
        j = x.wit.get(i)
        if j is not None and j in x.m and j in final and all(a <= b for a, b in zip(vals[j], vals[i])) and vals[j] != vals[i]:
            good += 1
    vis = good / max(len(nonfront), 1)
    return x, correct, vis, w

def front_undo(c, items, every=10):
    x = make_front(c); ok = tested = 0; sav = []
    def cold(j):
        o = decide.Ops(); decide.front_sortfilter(items[:j], o); return o.n
    if "control" not in c and c["undo"] == "none":
        return 0.0, {"supported": False}
    for k, (i, v) in enumerate(items):
        x.insert(i, v)
        if k % every == every - 1:
            tested += 1
            b = x.ops[0]
            done = x.undo_last()
            u = x.ops[0] - b
            good = done and set(x.m) == R.exact_front(items[:k])
            x.insert(i, v)
            good = good and set(x.m) == R.exact_front(items[:k + 1])
            ok += good
            if good: sav.append(1 - u / max(cold(k), 1))
    return (ok / max(tested, 1)) * (statistics.mean(sav) if sav else 0.0), {"tested": tested, "exact": ok}

def front_merge(c, items, once):
    if "control" in c:
        return 0.0, {"correct": False}
    mid = len(items) // 2
    def build(L):
        x = make_front(c)
        for i, v in L: x.insert(i, v)
        return x
    whole = build(items)
    A, B = build(items[:mid]), build(items[mid:])
    b0 = A.ops[0]
    for i, v in B.m.items():
        A.insert(i, v)
    mops = A.ops[0] - b0
    good = set(A.m) == R.exact_front(items)
    return good * max(0.0, 1 - mops / max(once, 1)), {"correct": good, "merge_tests": mops, "whole_tests_same_engine": whole.ops[0], "baseline_tests": once}

def front_orders(c, items, base):
    ok, outs = True, []
    vs = [list(reversed(items))]
    for s in (1, 2, 3):
        t = list(items); random.Random(s).shuffle(t); vs.append(t)
    for t in vs:
        x = make_front(c)
        for i, v in t: x.insert(i, v)
        ok = ok and set(x.m) == R.exact_front(t)
        outs.append(x.ops[0])
    spread = (max(outs) - min(outs)) / max(base, 1)
    return ok * max(0.0, 1 - spread), {"tests": outs, "all_correct": ok, "baseline_tests": base}

FRONT_ROBUST = {"chris": [(0, (0, 4)), (1, (4, 0)), (2, (3, 3))],
                "all-equal": [(i, (5, 5, 5)) for i in range(6)],
                "duplicates": [(0, (1, 9)), (1, (1, 9)), (2, (9, 1)), (3, (5, 5)), (4, (5, 5)), (5, (6, 6))]}

def front_robust(c):
    good = 0
    for name, it in FRONT_ROBUST.items():
        x = make_front(c); ok = True
        for j, (i, v) in enumerate(it):
            x.insert(i, v); ok = ok and set(x.m) == R.exact_front(it[:j + 1])
        good += ok
    return good / len(FRONT_ROBUST)

def run_front(S, made, camps, phase, only=None):
    cands = [k for k in made if k.startswith("cand:ax-b/") and (only is None or k in only)]
    for n, (rows, h) in camps.items():
        items = R.run_vectors(rows)
        inp = "ax/campaign-%d" % n
        ops = decide.Ops()
        for j in range(1, len(items) + 1):
            decide.front_sortfilter(items[:j], ops)
        base = ops.n
        o1 = decide.Ops(); decide.front_sortfilter(items, o1); once = o1.n
        S.append("input:" + inp, [], ["input", "decision-data", "phase:" + phase], {"sha256": h, "runs": len(items), "cold_tests": base, "one_sortfilter_tests": once})
        for k in cands:
            c = made[k]
            x, correct, vis, w = front_main(c, items)
            meas(S, k, inp, "correct_every_prefix", correct, phase)
            meas(S, k, inp, "dominance_tests", x.ops[0], phase)
            meas(S, k, inp, "wall_ms", round(w["median"], 3), phase, {"p25": w["p25"], "p75": w["p75"]})
            meas(S, k, inp, "visibility", round(vis, 4), phase)
            meas(S, k, inp, "work_saved", round(correct * max(0.0, 1 - x.ops[0] / base), 6), phase, {"cold_tests": base})
            u, ux = front_undo(c, items)
            meas(S, k, inp, "reversibility", round(u, 6), phase, ux)
            m, mx = front_merge(c, items, once)
            meas(S, k, inp, "compositionality", round(m, 6), phase, mx)
            o, ox = front_orders(c, items, base)
            meas(S, k, inp, "order_invariance", round(o, 6), phase, ox)
            meas(S, k, inp, "robustness", round(front_robust(c), 4), phase)
            print(phase, inp, k, correct, x.ops[0], "vis", round(vis, 3), "rev", round(u, 3), "comp", round(m, 3), "ord", round(o, 3), flush=True)

# ------------------------------------------------------------------
# joint plans: compositionality of the fold; selection: frames
# ------------------------------------------------------------------
def fold_tree(fs, ops):
    if len(fs) == 1:
        return decide.plans_fold(fs, ops)
    mid = len(fs) // 2
    P1, P2 = fold_tree(fs[:mid], ops), fold_tree(fs[mid:], ops)
    items = [(n, decide.add(p, q, ops)) for n, (p, q) in enumerate(itertools.product(sorted(P1), sorted(P2)))]
    keep = decide.front_sortfilter(items, ops)
    return {items[k][1] for k in keep}

def joint_reference(fs, brute_ok):
    """Reference front not produced by either candidate: brute force over
    every plan where feasible, else the unpruned fold (it shares the fold's
    merge code but not its per-factor pruning; recorded as such)."""
    o = decide.Ops()
    if brute_ok:
        return decide.plans_brute(fs, o, prune=False), "brute"
    return decide.plans_fold(fs, o, prune=False), "unpruned-fold (shares merge code)"

def run_joint_select(S, made, camps, phase, only=None):
    jc = [k for k in made if k.startswith("cand:ax-j/") and (only is None or k in only)]
    sc = [k for k in made if k.startswith("cand:ax-s/") and (only is None or k in only)]
    for n, (rows, h) in camps.items():
        for iname, fs, size, brute_ok in R.joint_instances(rows):
            inp = "ax/campaign-%d/%s" % (n, iname)
            ref, basis = joint_reference(fs, brute_ok)
            for k in jc:
                ops = decide.Ops()
                f = decide.plans_fold(fs, ops) if made[k]["compose"] == "sequential" else fold_tree(fs, ops)
                meas(S, k, inp, "correct", f == ref, phase, {"front": len(f), "basis": basis})
                meas(S, k, inp, "ops", ops.n, phase)
            if not brute_ok or size > 5000:
                continue
            plans = []
            for combo in itertools.product(*fs):
                plans.append((len(plans), tuple(sum(x) for x in zip(*combo))))
            front = R.exact_front(plans)
            fitems = [(i, v) for i, v in plans if i in front]
            if len(fitems) < 2:
                continue
            A, B = fitems[0::2], fitems[1::2]
            d = len(plans[0][1])
            gframe = decide.normalize([v for _, v in plans])
            for k in sc:
                rule, frame = made[k]["rule"], made[k]["frame"]
                agree = total = 0
                for w in decide.simplex(d, 10):
                    o = decide.Ops()
                    fr = (lambda L: gframe) if frame == "fixed" else (lambda L: decide.normalize([v for _, v in L]))
                    pu = decide.pick(rule, fitems, w, o, fr(fitems))
                    pa = decide.pick(rule, A, w, o, fr(A)); pb = decide.pick(rule, B, w, o, fr(B))
                    two = [(i, v) for i, v in fitems if i in (pa, pb)]
                    pc = decide.pick(rule, two, w, o, fr(two))
                    agree += pu == pc; total += 1
                meas(S, k, inp, "compositionality", round(agree / total, 4), phase, {"weights": total})
        print(phase, "joint/select campaign", n, flush=True)

def main():
    phase, out = sys.argv[1], sys.argv[2]
    os.makedirs(out, exist_ok=True)
    S = Space(os.path.join(out, "space.jsonl"))
    if phase == "dev":
        assert not S.recs
        made = generate(S)
        run_closure(S, made, traces.dev_closure(), "dev")
        camps = R.campaign_inputs([1, 2, 3, 4])
        run_front(S, made, camps, "dev")
        run_joint_select(S, made, camps, "dev")
    print("records", len(S.recs), "head", S.prev)

if __name__ == "__main__":
    main()
