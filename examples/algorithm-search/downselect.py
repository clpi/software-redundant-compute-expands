# Pareto down-selection read from the space log only, by the rule in
# OBJECTIVES.json. Appends one verdict record per candidate and one
# `downselect:<phase>` record that freezes the survivor set.
import json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from space import Space

OBJ = {
 "a": {"correct_every_prefix": "constraint", "premise_ops": "min", "wall_ms": "min", "peak_kib": "min"},
 "b1": {"correct": "constraint", "dominance_tests": "min", "wall_ms": "min"},
 "b2": {"correct": "constraint", "ops": "min", "wall_ms": "min", "peak_kib": "min"},
 "b3": {"pick_on_front_rate": "max", "front_coverage_on_grid": "max", "evaluations": "min"},
 "c": {"regret": "min", "examined_ops": "min", "certified": "max"},
 "d": {"correct_every_prefix": "constraint", "dominance_tests": "min", "wall_ms": "min"},
 "e": {"coverage": "max", "unsupported_reached": "max", "evaluations": "min"},
 "f": {"lexically_unsound_edges": "min", "ambiguous_refs": "min", "unresolved_refs": "min"},
}

def table(S, phase):
    T = {}
    for r in S.with_color("measurement"):
        if "phase:" + phase not in r["colors"]:
            continue
        cand, inp, obj, _ = r["head"][5:].split("|")
        fam = cand.split(":")[1].split("/")[0]
        if obj not in OBJ.get(fam, {}):
            continue
        T.setdefault(fam, {}).setdefault(cand, {})[(inp, obj)] = r["receipt"]
    return T

def wall_cmp(a, b):
    """-1 if a clearly lower, 1 if clearly higher, 0 tie (10% or IQR overlap)."""
    ma, mb = a["value"], b["value"]
    lo, hi = min(ma, mb), max(ma, mb)
    if hi <= lo * 1.10:
        return 0
    if "p25" in a and "p25" in b and not (a["p75"] < b["p25"] or b["p75"] < a["p25"]):
        return 0
    return -1 if ma < mb else 1

def cmp(obj, d, a, b):
    """-1 if a better, 1 if b better, 0 equal or tie."""
    if obj == "wall_ms":
        return wall_cmp(a, b)
    x, y = a["value"], b["value"]
    if x == y:
        return 0
    better = (x < y) if d == "min" else (x > y)
    return -1 if better else 1

def dominates(fam, B, A):
    strict = False
    for key, ra in A.items():
        inp, obj = key
        d = OBJ[fam][obj]
        if d == "constraint":
            continue
        if key not in B:
            return False
        c = cmp(obj, d, B[key], ra)
        if c == 1:
            return False
        if c == -1:
            strict = True
    return strict

def downselect(S, phase):
    T = table(S, phase)
    out = {}
    for fam, C in sorted(T.items()):
        bad = {c for c, m in C.items() if any(OBJ[fam][o] == "constraint" and v["value"] is not True for (i, o), v in m.items())}
        alive = [c for c in C if c not in bad]
        for c in sorted(C):
            if c in bad:
                S.append("verdict:%s|%s" % (c, phase), [c], ["verdict", "incorrect"], {"family": fam})
                out[c] = "incorrect"; continue
            doms = [b for b in alive if b != c and dominates(fam, C[b], C[c])]
            if doms:
                S.append("verdict:%s|%s" % (c, phase), [c] + doms, ["verdict", "dominated"], {"family": fam, "dominated_by": doms})
                out[c] = "dominated"
            else:
                S.append("verdict:%s|%s" % (c, phase), [c], ["verdict", "survivor"], {"family": fam})
                out[c] = "survivor"
    surv = sorted(c for c, v in out.items() if v == "survivor")
    S.append("downselect:%s" % phase, surv, ["frozen", "downselect"], {"survivors": surv, "log_head_before": S.prev, "candidates": len(out)})
    return out

if __name__ == "__main__":
    S = Space(sys.argv[1])
    res = downselect(S, sys.argv[2] if len(sys.argv) > 2 else "dev")
    for c, v in sorted(res.items()):
        print(v, c)
