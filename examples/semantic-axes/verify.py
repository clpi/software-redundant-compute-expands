# Rebuild every number in CLAIMS.md from the log alone and check it.
#   python3 verify.py out/space.jsonl            the committed log: every check must pass
#   python3 verify.py OTHER/space.jsonl --rerun  a fresh rerun: deterministic checks must
#                                                pass; checks that depend on wall time, or
#                                                on which candidates a timing-dependent
#                                                down-select sent to held-out, are skipped
# Exits non-zero on any failed check. The log's hash chain is verified on load.
import json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "algorithm-search"))
from space import Space

CTR = "cand:ax-a/engine=counter,undo=%s,witness=on,merge=%s"
WAT = "cand:ax-a/engine=watch,undo=%s,witness=on,merge=%s"
ARC = "cand:ax-b/engine=archive,undo=%s,witness=off"
ARC_ON = "cand:ax-b/engine=archive,undo=%s,witness=on"

class Missing(Exception):
    pass

def main():
    path = sys.argv[1]; rerun = "--rerun" in sys.argv
    S = Space(path)  # asserts the hash chain
    L = {}
    for r in S.recs:
        if r["head"].startswith("meas:"):
            L[r["head"][5:]] = r["receipt"]   # later records supersede (rescore)
    def m(cand, inp, obj, phase):
        k = "%s|ax/%s|%s|%s" % (cand, inp, obj, phase)
        if k not in L: raise Missing(k)
        return L[k]
    def v(*a):
        return m(*a)["value"]
    def rec(head):
        rs = [r for r in S.recs if r["head"] == head]
        if not rs: raise Missing(head)
        return rs[-1]["receipt"]
    out = []
    def chk(cid, what, fn, wall=False, selected=False):
        """fn() -> (ok, seen). wall: depends on timings. selected: depends on
        which candidates a timing-dependent down-select sent on."""
        try:
            ok, seen = fn()
            out.append((cid, what, bool(ok), seen, wall))
        except Missing as e:
            out.append((cid, what, None, "missing " + str(e), wall or selected))

    # ---------------- round 1 ----------------
    for cid, eng, T, dev, ho, ops in (("S1", "counter", CTR, (0.997, 0.996), (0.992, 0.955), (4299, 6280)),
                                      ("S2", "watch", WAT, (0.998, 0.996), (0.995, 0.955), (2652, 4914))):
        J, N = T % ("journal", "propagate"), T % ("none", "propagate")
        chk(cid, eng + " journal reversibility dev",
            lambda: (lambda g: (g == dev, g))(tuple(round(v(J, i, "reversibility", "dev"), 3) for i in ("estate", "v2"))))
        chk(cid, eng + " journal reversibility held-out",
            lambda: (lambda g: (g == ho, g))(tuple(round(v(J, i, "reversibility", "heldout"), 3) for i in ("refs", "v2-rr"))), selected=True)
        chk(cid, eng + " journal ops equal current ops",
            lambda: (lambda g, c: (g == c == ops, (g, c)))(tuple(v(J, i, "premise_ops", "dev") for i in ("estate", "v2")),
                                                            tuple(v(N, i, "premise_ops", "dev") for i in ("estate", "v2"))))
        chk(cid, eng + " current reversibility is 0",
            lambda: (lambda g: (all(x == 0 for x in g), g))(tuple(v(N, i, "reversibility", ph) for i, ph in
                                                                   (("estate", "dev"), ("v2", "dev"), ("refs", "heldout"), ("v2-rr", "heldout")))))
    camps = {"dev": ["campaign-%d" % i for i in (1, 2, 3, 4)], "heldout": ["campaign-5", "campaign-6"]}
    for ph, cs in camps.items():
        res = ARC % "residual" if ph == "dev" else ARC_ON % "residual"
        chk("S3", "residual archive undo >= 0.996 (%s)" % ph,
            lambda: (lambda rv: (min(rv) >= 0.996, rv))([v(res, c, "reversibility", ph) for c in cs]), selected=(ph == "heldout"))
        chk("S3", "residual archive tests equal current (%s)" % ph,
            lambda: (lambda t, t0: (t == t0, (sum(t), sum(t0))))([v(res, c, "dominance_tests", ph) for c in cs],
                                                                 [v(ARC % "none", c, "dominance_tests", ph) for c in cs]), selected=(ph == "heldout"))
    chk("S4", "archive 3,291 vs cold 314,184 tests (dev)",
        lambda: (lambda a, b: ((a, b) == (3291, 314184), (a, b)))(sum(v(ARC % "none", c, "dominance_tests", "dev") for c in camps["dev"]),
                                                                  sum(v("cand:ax-b/engine=cold,undo=recompute,witness=off", c, "dominance_tests", "dev") for c in camps["dev"])))
    chk("S4", "cold sort-filter dominated (dev)",
        lambda: (lambda d: (len(d) > 0, len(d)))(rec("verdict:cand:ax-b/engine=cold,undo=recompute,witness=off|ax-dev")["dominated_by"]), wall=True)
    def s5():
        fixed = [x["value"] for k, x in L.items() if k.startswith("cand:ax-s/") and "frame=fixed" in k and "|compositionality|" in k]
        return fixed and all(x == 1.0 for x in fixed), (len(fixed), min(fixed) if fixed else None)
    chk("S5", "fixed-frame picks compose 100%", s5)
    def s6():
        prop = [x for k, x in L.items() if k.startswith("cand:ax-a/") and "merge=propagate" in k and "|compositionality|" in k and "control" not in k]
        return prop and all(x.get("correct") for x in prop), len(prop)
    chk("S6", "every propagate merge correct", s6)
    for fam, cols, pts, wts in (("ax-a", (3650, 34740), (2000, 34679), (24, 24)), ("ax-b", (2240, 21475), None, (11, 11))):
        chk("F1", fam + " column appends exact (dev)", lambda fam=fam: (lambda c: (c["exact_every_step"], (c.get("incremental_scalar_compares"), c["cold_scalar_compares"])))(rec("axisfront-columns:%s|dev" % fam)))
        chk("F1", fam + " column-append compare counts (dev)", lambda fam=fam, cols=cols: (lambda c: ((c.get("incremental_scalar_compares"), c["cold_scalar_compares"]) == cols, cols))(rec("axisfront-columns:%s|dev" % fam)), wall=True)
        if pts:
            chk("F2", fam + " candidate appends exact (dev)", lambda fam=fam: (lambda p: (p["exact_every_step"], (p["incremental_scalar_compares"], p["cold_scalar_compares"])))(rec("axisfront-points:%s|dev" % fam)))
        chk("F3", fam + " every front point reached by own weights (dev)",
            lambda fam=fam: (lambda w: (w["front"] == w["reached_by_own_weights"], (w["front"], w["reached_by_own_weights"])))(rec("axisfront-weights:%s|dev" % fam)))
        chk("F3", fam + " front size (dev)", lambda fam=fam, wts=wts: (lambda w: ((w["front"], w["reached_by_own_weights"]) == wts, wts))(rec("axisfront-weights:%s|dev" % fam)), wall=True)
    for ph in ("dev", "heldout"):
        def val(ph=ph):
            last = {}
            for r in S.recs:
                if r["head"].startswith("axis-validity:") and r["head"].endswith("|" + ph):
                    last[r["head"]] = "valid" in r["colors"]
            return len(last) == 12 and all(last.values()), sum(last.values())
        chk("V", "all 12 axis/family pairs valid (%s)" % ph, val)

    # ---------------- round 2 ----------------
    if any(r["head"] == "axes-round-2" for r in S.recs):
        for ph, ins in (("r2-dev", ("estate", "v2")), ("r2-heldout", ("refs", "v2-rr", "fresh-refs", "fresh-v2"))):
            al = ins + tuple(i + "+alias" for i in ins)
            chk("R1", "alias traces: firsthead visibility < 1, honest 1.0 (%s)" % ph,
                lambda ph=ph, ins=ins: (lambda fh, hon: (max(fh) < 1 and min(hon) == 1.0, (fh, hon)))(
                    [v("cand:ax-a/control=firsthead", i + "+alias", "visibility", ph) for i in ins],
                    [v(CTR % ("none", "propagate"), i + "+alias", "visibility", ph) for i in ins]))
            def val2(ph=ph):
                last = {}
                for r in S.recs:
                    if r["head"].startswith("axis-validity:ax-a/") and r["head"].endswith("|" + ph):
                        last[r["head"]] = "valid" in r["colors"]
                return len(last) == 6 and all(last.values()), sum(last.values())
            chk("R1", "all 6 closure axes valid (%s)" % ph, val2)
            def r2(ph=ph, al=al):
                pairs = better = 0
                for eng in ("counter", "watch"):
                    for i in al:
                        p = m("cand:ax-a/engine=%s,undo=none,witness=on,merge=propagate" % eng, i, "compositionality", ph)
                        a = m("cand:ax-a/engine=%s,undo=none,witness=on,merge=adaptive" % eng, i, "compositionality", ph)
                        if not (a["correct"] and p["correct"]):
                            return False, ("incorrect merge", eng, i)
                        pairs += 1; better += a["merge_ops"] < p["merge_ops"]
                return (better, pairs) == {"r2-dev": (8, 8), "r2-heldout": (4, 16)}[ph], (better, pairs)
            chk("R2", "adaptive merge correct everywhere; cheaper than propagate on %s pairs (%s)" % ({"r2-dev": "8 of 8", "r2-heldout": "4 of 16"}[ph], ph), r2,
                selected=(ph == "r2-heldout"))
            chk("F1", "ax-a column appends exact (%s)" % ph, lambda ph=ph: (lambda c: (c["exact_every_step"], (c.get("incremental_scalar_compares"), c["cold_scalar_compares"])))(rec("axisfront-columns:ax-a|" + ph)))
            chk("F2", "ax-a candidate appends exact (%s)" % ph, lambda ph=ph: (lambda c: (c["exact_every_step"], (c["incremental_scalar_compares"], c["cold_scalar_compares"])))(rec("axisfront-points:ax-a|" + ph)))
            chk("F3", "ax-a every front point reached by own weights (%s)" % ph, lambda ph=ph: (lambda w: (w["front"] == w["reached_by_own_weights"], (w["front"], w["reached_by_own_weights"])))(rec("axisfront-weights:ax-a|" + ph)))

    bad = 0
    for cid, what, ok, seen, skip in out:
        if rerun and skip:
            print("SKIP %-3s %s (depends on timing)" % (cid, what)); continue
        print("%s %-3s %s  %s" % ("PASS" if ok else "FAIL", cid, what, json.dumps(seen)))
        bad += not ok
    print("chain ok, records %d, head %s, failed %d" % (len(S.recs), S.prev, bad))
    sys.exit(1 if bad else 0)

if __name__ == "__main__":
    main()
