# Rebuild every number in CLAIMS.md from the log alone and check it.
#   python3 verify.py out/space.jsonl            the committed log: every check exact
#   python3 verify.py OTHER/space.jsonl --rerun  a fresh rerun: deterministic checks
#                                                exact, wall-time-dependent ones skipped
# Exits non-zero on any failed check. The log's hash chain is verified on load.
import json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "algorithm-search"))
from space import Space

CTR = "cand:ax-a/engine=counter,undo=%s,witness=on,merge=%s"
WAT = "cand:ax-a/engine=watch,undo=%s,witness=on,merge=%s"
ARC = "cand:ax-b/engine=archive,undo=%s,witness=off"

def latest(S):
    L = {}
    for r in S.recs:
        if r["head"].startswith("meas:"):
            L[r["head"][5:]] = r["receipt"]
    return L

def v(L, cand, inp, obj, phase):
    return L["%s|ax/%s|%s|%s" % (cand, inp, obj, phase)]["value"]

def rec(S, head):
    rs = [r for r in S.recs if r["head"] == head]
    return rs[-1]["receipt"] if rs else None

def checks(S, L):
    C = []
    def add(cid, what, ok, seen, wall=False):
        C.append((cid, what, bool(ok), seen, wall))
    # ---------------- round 1 ----------------
    for eng, T, dev, ho, ops in (("counter", CTR, (0.997, 0.996), (0.992, 0.955), (4299, 6280)),
                                 ("watch", WAT, (0.998, 0.996), (0.995, 0.955), (2652, 4914))):
        cid = "S1" if eng == "counter" else "S2"
        got = tuple(round(v(L, T % ("journal", "propagate"), i, "reversibility", "dev"), 3) for i in ("estate", "v2"))
        add(cid, eng + " journal reversibility dev", got == dev, got)
        got = tuple(round(v(L, T % ("journal", "propagate"), i, "reversibility", "heldout"), 3) for i in ("refs", "v2-rr"))
        add(cid, eng + " journal reversibility held-out", got == ho, got)
        got = tuple(v(L, T % ("journal", "propagate"), i, "premise_ops", "dev") for i in ("estate", "v2"))
        cur = tuple(v(L, T % ("none", "propagate"), i, "premise_ops", "dev") for i in ("estate", "v2"))
        add(cid, eng + " journal ops equal current ops", got == cur == ops, (got, cur))
        cur0 = tuple(v(L, T % ("none", "propagate"), i, "reversibility", ph) for i, ph in (("estate", "dev"), ("v2", "dev"), ("refs", "heldout"), ("v2-rr", "heldout")))
        add(cid, eng + " current reversibility is 0", all(x == 0 for x in cur0), cur0)
    camps = {"dev": ["campaign-%d" % i for i in (1, 2, 3, 4)], "heldout": ["campaign-5", "campaign-6"]}
    for ph, cs in camps.items():
        res = ARC % "residual" if ph == "dev" else "cand:ax-b/engine=archive,undo=residual,witness=on"  # survivors re-run on held-out
        rv = [v(L, res, c, "reversibility", ph) for c in cs]
        add("S3", "residual archive undo >= 0.996 (%s)" % ph, min(rv) >= 0.996, rv)
        t = [v(L, res, c, "dominance_tests", ph) for c in cs]
        t0 = [v(L, ARC % "none", c, "dominance_tests", ph) for c in cs]
        add("S3", "residual archive tests equal current (%s)" % ph, t == t0, (sum(t), sum(t0)))
    tot = sum(v(L, ARC % "none", c, "dominance_tests", "dev") for c in camps["dev"])
    cold = sum(v(L, "cand:ax-b/engine=cold,undo=recompute,witness=off", c, "dominance_tests", "dev") for c in camps["dev"])
    add("S4", "archive 3,291 vs cold 314,184 tests (dev)", (tot, cold) == (3291, 314184), (tot, cold))
    vd = rec(S, "verdict:cand:ax-b/engine=cold,undo=recompute,witness=off|ax-dev")
    add("S4", "cold sort-filter dominated (dev)", vd is not None and vd["dominated_by"], len(vd["dominated_by"]) if vd else None)
    fixed = [x["value"] for k, x in L.items() if k.startswith("cand:ax-s/") and "frame=fixed" in k and "|compositionality|" in k]
    add("S5", "fixed-frame picks compose 100%", fixed and all(x == 1.0 for x in fixed), (len(fixed), min(fixed) if fixed else None))
    prop = [x for k, x in L.items() if k.startswith("cand:ax-a/") and "merge=propagate" in k and "|compositionality|" in k and "control" not in k]
    add("S6", "every propagate merge correct", prop and all(x.get("correct") for x in prop), len(prop))
    for fam, cols, pts, wts in (("ax-a", (3650, 34740), (2000, 34679), (24, 24)), ("ax-b", (2240, 21475), None, (11, 11))):
        c = rec(S, "axisfront-columns:%s|dev" % fam)
        got = (c.get("incremental_scalar_compares"), c["cold_scalar_compares"])
        add("F1", fam + " column appends exact and cheaper (dev)", c["exact_every_step"] and got == cols, got)
        if pts:
            p = rec(S, "axisfront-points:%s|dev" % fam)
            got = (p["incremental_scalar_compares"], p["cold_scalar_compares"])
            add("F2", fam + " candidate appends exact and cheaper (dev)", p["exact_every_step"] and got == pts, got)
        w = rec(S, "axisfront-weights:%s|dev" % fam)
        got = (w["front"], w["reached_by_own_weights"])
        add("F3", fam + " every front point reached by own weights (dev)", got == wts, got, wall=True)
    for ph in ("dev", "heldout"):
        val = [r for r in S.recs if r["head"].startswith("axis-validity:") and r["head"].endswith("|" + ph)]
        last = {}
        for r in val: last[r["head"]] = "valid" in r["colors"]
        add("V", "all 12 axis/family pairs valid (%s)" % ph, len(last) == 12 and all(last.values()), sum(last.values()))
    # ---------------- round 2 ----------------
    if rec(S, "axes-round-2") is None:
        return C
    for ph, ins in (("r2-dev", ("estate", "v2")), ("r2-heldout", ("refs", "v2-rr", "fresh-refs", "fresh-v2"))):
        if not any(k.endswith("|" + ph) for k in L):
            continue
        fh = [v(L, "cand:ax-a/control=firsthead", i + "+alias", "visibility", ph) for i in ins]
        hon = [v(L, CTR % ("none", "propagate"), i + "+alias", "visibility", ph) for i in ins]
        add("R1", "alias traces: firsthead visibility < 1, honest 1.0 (%s)" % ph, max(fh) < 1 and min(hon) == 1.0, (fh, hon))
        last = {}
        for r in S.recs:
            if r["head"].startswith("axis-validity:ax-a/") and r["head"].endswith("|" + ph):
                last[r["head"]] = "valid" in r["colors"]
        add("R1", "all 6 ax-a axes valid with firsthead now rejectable (%s)" % ph, len(last) == 6 and all(last.values()), sum(last.values()))
        for T, eng in ((CTR, "counter"), (WAT, "watch")):
            pa = [L["%s|ax/%s|compositionality|%s" % (T % ("journal", "propagate"), i, ph)] for i in ins]
            ad = [L["%s|ax/%s|compositionality|%s" % (T % ("journal", "adaptive"), i, ph)] for i in ins]
            add("R2", eng + " adaptive merge correct everywhere (%s)" % ph, all(x["correct"] for x in ad), [x["path"] for x in ad])
            add("R2", eng + " adaptive merge never costs more than propagate (%s)" % ph,
                all(a["merge_ops"] <= p["merge_ops"] for a, p in zip(ad, pa)), [(a["merge_ops"], p["merge_ops"]) for a, p in zip(ad, pa)])
            add("R2", eng + " adaptive merge cheaper than the same engine's whole build (%s)" % ph,
                all(a["merge_ops"] < a["whole_ops_same_engine"] for a in ad), [(a["merge_ops"], a["whole_ops_same_engine"]) for a in ad])
    return C

def main():
    path = sys.argv[1]; rerun = "--rerun" in sys.argv
    S = Space(path)  # asserts the hash chain
    L = latest(S)
    bad = 0
    for cid, what, ok, seen, wall in checks(S, L):
        if rerun and wall:
            print("SKIP %-3s %s (depends on wall time)" % (cid, what)); continue
        print("%s %-3s %s  %s" % ("PASS" if ok else "FAIL", cid, what, json.dumps(seen)))
        bad += not ok
    print("chain ok, records %d, head %s, failed %d" % (len(S.recs), S.prev, bad))
    sys.exit(1 if bad else 0)

if __name__ == "__main__":
    main()
