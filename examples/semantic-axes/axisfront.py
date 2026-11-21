# The candidate space as one weighted, incrementally searchable front.
# Points: candidates of a family. Coordinates: (input, axis) columns, in
# the order their measurements were appended to the log (max axes are
# negated so every coordinate is minimized). Two exact-update tests,
# each checked against a cold recompute at every step:
#   column append  (a new axis or a new trace):  keep each point's weak
#                  dominators; a new column only filters them (Axes.dom_ext_le,
#                  Axes.front_ext)
#   point append   (a new candidate): compare it with every point once,
#                  in both directions (AlgoSearch.mem_arch)
# Then every front point gets solved Chebyshev weights (AlgoSearch.cheb_target),
# appended as a weight-coloring record, and the pick under those weights
# is checked to be that point.
#   python3 axisfront.py out/space.jsonl dev
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "algorithm-search"))
import decide
from space import Space
from axes_select import OBJ

def columns(S, fam, phase):
    vals, order = {}, []
    for r in S.with_color("measurement"):
        if "phase:" + phase not in r["colors"]:
            continue
        cand, inp, obj, _ = r["head"][5:].split("|")
        if not cand.startswith("cand:%s/" % fam) or obj not in OBJ[fam]:
            continue
        d = OBJ[fam][obj]
        v = r["receipt"]["value"]
        if d == "constraint":
            vals.setdefault(cand, {})["ok"] = vals.get(cand, {}).get("ok", True) and v is True
            continue
        col = (inp, obj)
        if col not in order:
            order.append(col)
        vals.setdefault(cand, {})[col] = -v if d == "max" else v
    cands = sorted(c for c in vals if vals[c].get("ok", False) and all(col in vals[c] for col in order))
    return cands, order, vals

def cold_front(pts, ncol, cnt):
    out = set()
    for x in pts:
        dom = False
        for y in pts:
            if y == x: continue
            le = True
            for k in range(ncol):
                cnt[0] += 1
                if pts[y][k] > pts[x][k]:
                    le = False; break
            if le and pts[y][:ncol] != pts[x][:ncol]:
                dom = True; break
        if not dom: out.add(x)
    return out

def run(S, fam, phase):
    cands, order, vals = columns(S, fam, phase)
    pts = {c: [vals[c][col] for col in order] for c in cands}
    # --- column appends ---
    W = {x: {y for y in cands if y != x} for x in cands}
    inc, cold, exact = [0], [0], True
    for k, col in enumerate(order):
        for x in cands:
            keep = set()
            for y in W[x]:
                inc[0] += 1
                if pts[y][k] <= pts[x][k]:
                    keep.add(y)
            W[x] = keep
        front = {x for x in cands if not any(pts[y][:k + 1] != pts[x][:k + 1] for y in W[x])}
        exact = exact and front == cold_front(pts, k + 1, cold)
    S.append("axisfront-columns:%s|%s" % (fam, phase), [], ["axisfront"],
             {"points": len(cands), "columns": len(order), "exact_every_step": exact,
              "incremental_scalar_compares": inc[0], "cold_scalar_compares": cold[0], "front": sorted(front)})
    # --- point appends (candidates in log order) ---
    ncol = len(order)
    seen, F, incp, coldp, exactp = {}, set(), [0], [0], True
    def le(a, b, cnt):
        for k in range(ncol):
            cnt[0] += 1
            if pts[a][k] > pts[b][k]: return False
        return True
    for z in cands:
        zdom = False
        for m in list(F):
            if le(m, z, incp) and pts[m] != pts[z]:
                zdom = True; break
        if not zdom:
            for m in list(F):
                if le(z, m, incp) and pts[z] != pts[m]:
                    F.discard(m)
            F.add(z)
        seen[z] = pts[z]
        exactp = exactp and F == cold_front({c: pts[c] for c in seen}, ncol, coldp)
    S.append("axisfront-points:%s|%s" % (fam, phase), [], ["axisfront"],
             {"points": len(cands), "exact_every_step": exactp, "incremental_scalar_compares": incp[0], "cold_scalar_compares": coldp[0]})
    # --- weight colorings from the solved front ---
    items = [(i, tuple(pts[c])) for i, c in enumerate(cands)]
    frame = decide.normalize([v for _, v in items])
    fitems = [(i, v) for i, v in items if cands[i] in front]
    hit = 0
    for i, v in fitems:
        w = decide.solved_weights(v, frame)
        p = decide.pick("ch", fitems, w, decide.Ops(), frame)
        hit += p == i
        S.append("weight-coloring:%s|%s" % (cands[i], phase), [cands[i]] + ["obj:%s@%s" % (o, inp) for inp, o in order],
                 ["weight-coloring"], {"weights": dict(zip(["%s@%s" % (o, inp) for inp, o in order], [round(x, 6) for x in w])),
                                       "picks_itself": p == i})
    S.append("axisfront-weights:%s|%s" % (fam, phase), [], ["axisfront"], {"front": len(fitems), "reached_by_own_weights": hit})
    print(fam, "points", len(cands), "columns", len(order), "column-append exact", exact, inc[0], "vs cold", cold[0],
          "| point-append exact", exactp, incp[0], "vs cold", coldp[0], "| front", len(fitems), "reached", hit)

if __name__ == "__main__":
    S = Space(sys.argv[1]); phase = sys.argv[2]
    for fam in ("ax-a", "ax-b"):
        if any("phase:" + phase in r["colors"] and r["head"].startswith("meas:cand:" + fam + "/") for r in S.recs):
            run(S, fam, phase)
