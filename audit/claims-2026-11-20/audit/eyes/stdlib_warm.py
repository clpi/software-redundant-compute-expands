#!/usr/bin/env python3
"""In-process repetitions of the same-work stdlib driver (audit). argv: BASE OUT.
21 reps per static task, first dropped; prints per-task p50 ms and correctness."""
import json, os, sys, time, statistics
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from stdlib_driver import run
base = sys.argv[1]
T = {t["id"]: t for t in json.load(open(os.environ["EYES"] + "/bench/browser/tasks.json"))["tasks"]}
res = {}
for tid in ["login", "chain", "prefs", "table", "search"]:
    plan = "".join(("open\t" + base + s[1] if s[0] == "open" else "\t".join(s)) + "\n" for s in T[tid]["steps"])
    ts, ok = [], True
    for _ in range(21):
        s = time.perf_counter(); a = run(plan); ts.append((time.perf_counter() - s) * 1000); ok &= a == T[tid]["answer"]
    res[tid] = {"warm_p50_ms": statistics.median(ts[1:]), "warm_min_ms": min(ts[1:]), "correct_all": ok, "task_ms": ts[1:]}
json.dump(res, open(sys.argv[2], "w"), indent=1)
print(json.dumps({k: (round(v["warm_p50_ms"], 2), v["correct_all"]) for k, v in res.items()}))
