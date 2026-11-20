# Phase 2: re-validate the frozen dev survivors.
#   python3 heldout.py OUT_DIR IDOL_LIB
# Refuses to run unless the log holds a `downselect:dev` record. The
# held-out traces are built here, after that record, and their hashes
# are appended before any survivor runs on them.
import os, random, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import closure, decide, traces, run_search as R, downselect as select
from space import Space

def controls(name, tr):
    """Adversarial variants of one trace (CLAIMS-style controls)."""
    out = {}
    out[name + "+dup-records"] = [(2 * i + j, lv, cs, ps, h) for i, (_, lv, cs, ps, h) in enumerate(tr) for j in (0, 1)]
    out[name + "+dup-premises"] = [(i, lv, cs, [p for p in ps for _ in (0, 1)], h) for i, lv, cs, ps, h in tr]
    filt, top = [], 1 + max(max([h] + ps) for _, _, _, ps, h in tr)
    for i, rec in enumerate(tr):
        filt.append(rec)
        if i % 10 == 0:
            # would derive a new term and its consequences if admitted
            filt.append((len(filt), 0, [4], [], top + i))           # disqualified color
            filt.append((len(filt), 1, [2], [], top + i + 1))       # level 1 > r
            filt.append((len(filt), 0, [2], [top + i], rec[4]))    # depends on the filtered root
    out[name + "+filtered"] = filt
    out[name + "+reversed"] = list(reversed(tr))
    for seed in (1, 2, 3):
        t = list(tr); random.Random(seed).shuffle(t)
        out[name + "+shuffle%d" % seed] = t
    return out

def decision_controls(S, surv):
    """Chris's counterexample and degenerate sets, through every
    surviving front, selection and weight candidate."""
    sets = {"chris-(0,4)(4,0)(3,3)": [(0, (0, 4)), (1, (4, 0)), (2, (3, 3))],
            "all-equal": [(i, (5, 5, 5)) for i in range(6)],
            "duplicates": [(0, (1, 9)), (1, (1, 9)), (2, (9, 1)), (3, (5, 5)), (4, (5, 5)), (5, (6, 6))]}
    for name, items in sets.items():
        ref = R.exact_front(items)
        S.append("input:control/" + name, [], ["input", "phase:control"], {"items": items})
        for k in surv:
            fam = k.split(":")[1].split("/")[0]
            ops = decide.Ops()
            if fam == "b1":
                how = k.split("front=")[1]
                if how == "pairwise": f = decide.front_pairwise(items, ops)
                elif how == "sortfilter": f = decide.front_sortfilter(items, ops)
                else:
                    a = decide.Archive()
                    for i, v in items: a.insert(i, v, ops)
                    f = set(a.m)
                R.meas(S, k, "control/" + name, "correct", f == ref, "control")
            if fam == "d":
                for order in ("forward", "reversed"):
                    seq = items if order == "forward" else list(reversed(items))
                    a = decide.Archive(); ok = True
                    for j, (i, v) in enumerate(seq):
                        a.insert(i, v, ops)
                        if "archive" in k:
                            ok = ok and set(a.m) == R.exact_front(seq[:j + 1])
                    if "archive" in k:
                        R.meas(S, k, "control/%s/%s" % (name, order), "correct_every_prefix", ok, "control")
            if fam in ("e", "b3"):
                frame = decide.normalize([v for _, v in items])
                fitems = [(i, v) for i, v in items if i in ref]
                d = len(items[0][1])
                if fam == "e":
                    rule, par = k[len("cand:e/"):].split(",params=")
                    reached = set()
                    if par == "solved":
                        for i, v in fitems: reached.add(decide.pick(rule, fitems, decide.solved_weights(v, frame), ops, frame))
                    elif rule == "eps":
                        for w in decide.eps_grid(d, int(par)):
                            p = decide.pick("eps", fitems, w, ops, frame)
                            if p is not None: reached.add(p)
                    elif rule == "lex":
                        import itertools
                        for w in itertools.permutations(range(d)): reached.add(decide.pick("lex", fitems, w, ops, frame))
                    else:
                        for w in decide.simplex(d, int(par)): reached.add(decide.pick(rule, fitems, w, ops, frame))
                    R.meas(S, k, "control/" + name, "coverage", round(len(reached) / len(fitems), 4), "control", {"reached": sorted(reached), "front": sorted(ref)})

def main():
    out, idol_lib = sys.argv[1], sys.argv[2]
    S = Space(os.path.join(out, "space.jsonl"))
    frozen = S.with_color("downselect")
    assert frozen and frozen[-1]["head"] == "downselect:dev", "run the dev phase and select.py first"
    surv = frozen[-1]["receipt"]["survivors"]
    made = {}
    for r in S.with_color("candidate"):
        if "components" in r["receipt"]:
            made[r["head"]] = r["receipt"]["components"]
    R._COMP.update(made)
    # held-out closure traces, built now
    ho = traces.heldout_closure(idol_lib)
    for name, tr in ho.items():
        S.append("heldout-built:" + name, [], ["heldout", "phase:heldout"],
                 {"records": len(tr), "sha256": traces.digest(tr), "idol_lib": R.git_head(idol_lib)})
    csurv = [k for k in surv if k.startswith("cand:a/")]
    R.run_closure(S, csurv, ho, "heldout")
    # adversarial controls on dev and held-out traces
    base = dict(traces.dev_closure()); base.update(ho)
    ctr = {}
    for name, tr in base.items():
        ctr.update(controls(name, tr))
    R.run_closure(S, csurv, ctr, "control", repeats=1)
    # held-out decision data
    R.run_decisions(S, made, R.campaign_inputs([5, 6]), "heldout", only=set(surv))
    decision_controls(S, surv)
    # held-out verdicts: correct everywhere, and Pareto standing among survivors on held-out data
    res = select.downselect(S, "heldout")
    bad = set()
    for r in S.with_color("measurement"):
        if "phase:control" in r["colors"] or "phase:heldout" in r["colors"]:
            cand, inp, obj, ph = r["head"][5:].split("|")
            if obj.startswith("correct") and r["receipt"]["value"] is not True:
                bad.add(cand)
    for k in surv:
        st = "failed-correctness" if k in bad else ("held" if res.get(k) == "survivor" else ("lost-on-heldout" if k in res else "not-applicable-on-heldout"))
        S.append("validation:%s" % k, [k], ["validation", st], {"heldout_verdict": res.get(k), "correctness_failures": k in bad})
        print(st, k)
    print("records", len(S.recs), "head", S.prev)

if __name__ == "__main__":
    main()
