# Amendment 2 (after the held-out run, disclosed): compositionality was
# defined against a common baseline to stop slow engines from scoring
# high, but then a "merge" that just rebuilds with a cheaper engine
# scored above 0 (watch with merge=recompute: 0.21). The score is now
#   correct * (1 - merge cost / min(same engine's whole build, common baseline))
# so neither padding nor rebuilding can score above 0. Re-scored from the
# raw counts already in each receipt; no candidate is re-run. Appended,
# superseding key by key.
#   python3 rescore.py out/space.jsonl
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "algorithm-search"))
from space import Space

S = Space(sys.argv[1])
S.append("correction:compositionality-min-baseline", ["obj:compositionality"], ["correction", "axis-amendment"],
         {"when": "after the held-out run", "why": "rebuild-with-a-cheaper-engine scored above 0 under the common baseline; the min of the two baselines rules out both padding and rebuilding",
          "rescored_from": "merge_ops/merge_tests, whole_*_same_engine and baseline_* already in each receipt"})
latest = {}
for r in S.with_color("measurement"):
    if "|compositionality|" in r["head"] and r["head"].startswith(("meas:cand:ax-a/", "meas:cand:ax-b/")):
        latest[r["head"]] = r
n = 0
for h, r in latest.items():
    x = r["receipt"]
    if "baseline_ops" in x:
        m, w, b = x["merge_ops"], x["whole_ops_same_engine"], x["baseline_ops"]
    elif "baseline_tests" in x:
        m, w, b = x["merge_tests"], x["whole_tests_same_engine"], x["baseline_tests"]
    else:
        continue  # controls without a merge: already 0
    v = round(x["correct"] * max(0.0, 1 - m / max(min(w, b), 1)), 6)
    rec = dict(x); rec["value"] = v; rec["amendment"] = 2
    S.append(h, r["premises"], r["colors"], rec)
    n += 1
print("rescored", n)
