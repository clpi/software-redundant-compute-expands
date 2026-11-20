# Re-run the frozen semantic-axes survivors (plus every control, so axis
# validity is re-checked) on held-out data built only now.
#   python3 axes_heldout.py out IDOL_LIB
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, "..", "algorithm-search"))
import axes_run as A
import traces, run_search as R
from space import Space

def main():
    out, idol_lib = sys.argv[1], sys.argv[2]
    S = Space(os.path.join(out, "space.jsonl"))
    fr = [r for r in S.with_color("downselect") if r["head"] == "downselect:ax-dev"]
    assert fr, "run axes_select.py on the dev phase first"
    surv = set(fr[-1]["receipt"]["survivors"])
    made = {}
    for r in S.with_color("candidate"):
        if "components" in r["receipt"]:
            made[r["head"]] = r["receipt"]["components"]
        elif "control" in r["colors"]:
            made[r["head"]] = {"control": r["head"].split("=")[1]}
    keep = surv | {k for k in made if "/control=" in k}
    # current approach always re-run, so its standing can be compared on held-out data
    from axes_select import CURRENT
    for v in CURRENT.values(): keep |= set(v)
    ho = traces.heldout_closure(idol_lib)
    for name, tr in ho.items():
        S.append("heldout-built:ax/" + name, [], ["heldout", "phase:heldout"], {"records": len(tr), "sha256": traces.digest(tr)})
    A.run_closure(S, made, ho, "heldout", only=keep)
    camps = R.campaign_inputs([5, 6])
    A.run_front(S, made, camps, "heldout", only=keep)
    A.run_joint_select(S, made, camps, "heldout", only=keep)
    print("records", len(S.recs), "head", S.prev)

if __name__ == "__main__":
    main()
