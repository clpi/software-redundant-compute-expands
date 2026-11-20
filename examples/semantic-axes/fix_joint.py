# Correction (appended, never edited): the first dev run checked the
# sequential fold against itself (the same review finding as PR 7's
# cross-agreement). Re-measure the ax-j correctness against a reference
# that neither candidate produced, and append the records; later records
# supersede earlier ones key by key.
#   python3 fix_joint.py out/space.jsonl dev 1,2,3,4
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, "..", "algorithm-search"))
import axes_run as A, decide, run_search as R
from space import Space

S = Space(sys.argv[1]); phase = sys.argv[2]
camps = R.campaign_inputs([int(x) for x in sys.argv[3].split(",")])
S.append("correction:ax-j-reference|" + phase, [], ["correction"],
         {"why": "the sequential fold was its own reference; re-checked against brute force or the unpruned fold",
          "source": "Codex review on srce PR 7 (same flaw in run_search.py) and this thread's own check"})
for n, (rows, h) in camps.items():
    for iname, fs, size, brute_ok in R.joint_instances(rows):
        inp = "ax/campaign-%d/%s" % (n, iname)
        ref, basis = A.joint_reference(fs, brute_ok)
        for comp in ("sequential", "tree"):
            k = "cand:ax-j/compose=" + comp
            f = decide.plans_fold(fs, decide.Ops()) if comp == "sequential" else A.fold_tree(fs, decide.Ops())
            A.meas(S, k, inp, "correct", f == ref, phase, {"front": len(f), "basis": basis, "correction": True})
            print(inp, comp, f == ref, basis)
