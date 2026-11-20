# Axis validity, Pareto down-selection on every axis, and "what dominates
# the current approach" on every axis subset, all read from the log and
# appended back to it.
#   python3 axes_select.py out/space.jsonl dev
import itertools, json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "algorithm-search"))
import downselect as DS
from space import Space

SEM = {"visibility": "max", "work_saved": "max", "reversibility": "max", "compositionality": "max",
       "order_invariance": "max", "robustness": "max"}
OBJ = {
 "ax-a": dict({"correct_every_prefix": "constraint", "premise_ops": "min", "wall_ms": "min", "peak_kib": "min"}, **SEM),
 "ax-b": dict({"correct_every_prefix": "constraint", "dominance_tests": "min", "wall_ms": "min"}, **SEM),
 "ax-j": {"correct": "constraint", "ops": "min"},
 "ax-s": {"compositionality": "max"},
}
GAMED = {"ax-a": ["cand:ax-a/control=lookahead", "cand:ax-a/control=firsthead", "cand:ax-a/control=lastwitness"],
         "ax-b": ["cand:ax-b/control=allfront"]}
NULL = {"ax-a": "cand:ax-a/control=null", "ax-b": "cand:ax-b/control=null"}
CURRENT = {"ax-a": ["cand:ax-a/engine=counter,undo=none,witness=on,merge=propagate",
                    "cand:ax-a/engine=watch,undo=none,witness=on,merge=propagate"],
           "ax-b": ["cand:ax-b/engine=archive,undo=none,witness=off",
                    "cand:ax-b/engine=cold,undo=recompute,witness=off"]}

def table(S, phase):
    T = {}
    for r in S.with_color("measurement"):
        if "phase:" + phase not in r["colors"]:
            continue
        cand, inp, obj, _ = r["head"][5:].split("|")
        fam = cand.split(":")[1].split("/")[0]
        if fam in OBJ and obj in OBJ[fam]:
            T.setdefault(fam, {}).setdefault(cand, {})[(inp, obj)] = r["receipt"]
    return T

def dominates(fam, B, A, axes):
    strict = False
    for (inp, obj), ra in A.items():
        if obj not in axes:
            continue
        d = OBJ[fam][obj]
        if d == "constraint":
            continue
        if (inp, obj) not in B:
            return False
        c = DS.cmp(obj, d, B[(inp, obj)], ra)
        if c == 1:
            return False
        if c == -1:
            strict = True
    return strict

def correct(fam, m):
    return all(v["value"] is True for (i, o), v in m.items() if OBJ[fam][o] == "constraint")

def main():
    S = Space(sys.argv[1]); phase = sys.argv[2]
    T = table(S, phase)
    summary = {"validity": {}, "survivors": {}, "dominates_current": {}}
    # 1. axis validity
    valid = {}
    for fam in ("ax-a", "ax-b"):
        C = T[fam]
        honest = [c for c in C if "/control=" not in c and correct(fam, C[c])]
        for ax in SEM:
            inputs = sorted({i for c in C for (i, o) in C[c] if o == ax})
            nulls = [C[NULL[fam]][(i, ax)]["value"] for i in inputs if (i, ax) in C.get(NULL[fam], {})]
            gamed = {g: max(C[g][(i, ax)]["value"] - max(C[h][(i, ax)]["value"] for h in honest) for i in inputs)
                     for g in GAMED[fam] if g in C}
            ok = all(v == 0 for v in nulls) and all(v <= 1e-9 for v in gamed.values())
            if ax == "compositionality":
                # a merge that rebuilds from empty is a gamed merge and must score exactly 0 (amendment 2)
                reb = {c: max(C[c][(i, ax)]["value"] for i in inputs if (i, ax) in C[c]) for c in C if "merge=recompute" in c or "undo=recompute" in c and fam == "ax-b" and "engine=cold" in c}
                gamed.update({c + " (rebuild merge)": v for c, v in reb.items()})
                ok = ok and all(v == 0 for v in reb.values())
            valid[(fam, ax)] = ok
            S.append("axis-validity:%s/%s|%s" % (fam, ax, phase), ["obj:" + ax], ["axis-validity", "valid" if ok else "invalid"],
                     {"null_scores": nulls, "gamed_minus_best_honest": gamed})
            summary["validity"]["%s/%s" % (fam, ax)] = {"valid": ok, "null": nulls, "gamed_excess": gamed}
    # 2. Pareto down-selection on classic + valid semantic axes
    for fam, C in T.items():
        axes = {o for o in OBJ[fam] if OBJ[fam][o] != "constraint" and (o not in SEM or valid.get((fam, o), True))}
        alive = [c for c in C if correct(fam, C[c])]
        surv = []
        for c in sorted(C):
            if not correct(fam, C[c]):
                S.append("verdict:%s|ax-%s" % (c, phase), [c], ["verdict", "incorrect"], {}); continue
            doms = [b for b in alive if b != c and dominates(fam, C[b], C[c], axes)]
            S.append("verdict:%s|ax-%s" % (c, phase), [c] + doms, ["verdict", "dominated" if doms else "survivor"], {"axes": sorted(axes), "dominated_by": doms})
            if not doms: surv.append(c)
        summary["survivors"][fam] = surv
    allsurv = sorted(c for f in summary["survivors"].values() for c in f)
    S.append("downselect:ax-%s" % phase, allsurv, ["frozen", "downselect"], {"survivors": allsurv})
    # 3. what dominates the current approach, per axis subset
    for fam in ("ax-a", "ax-b"):
        C = T[fam]
        alive = [c for c in C if correct(fam, C[c])]
        names = [o for o in OBJ[fam] if OBJ[fam][o] != "constraint" and (o not in SEM or valid[(fam, o)])]
        for cur in CURRENT[fam]:
            res = {}
            for r in range(1, len(names) + 1):
                for sub in itertools.combinations(names, r):
                    doms = [b for b in alive if b != cur and dominates(fam, C[b], C[cur], set(sub))]
                    if doms:
                        res[",".join(sub)] = doms
            # report singletons, the full semantic set and the full set
            keep = {k: v for k, v in res.items() if k.count(",") == 0 or set(k.split(",")) in (set(names), set(names) & set(SEM))}
            S.append("dominates-current:%s|%s" % (cur, phase), [cur], ["dominance-analysis"],
                     {"axes": names, "subsets_with_a_dominator": len(res), "of_subsets": 2 ** len(names) - 1, "shown": keep})
            summary["dominates_current"][cur] = {"subsets_with_dominator": len(res), "of": 2 ** len(names) - 1, "shown": keep}
    print(json.dumps(summary, indent=1))

if __name__ == "__main__":
    main()
