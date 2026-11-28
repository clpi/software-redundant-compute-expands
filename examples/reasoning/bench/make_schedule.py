#!/usr/bin/env python3
"""Greedy strategy schedule from per-setting sweep runs (bench.py output, one file per setting).

Each step picks the (setting, time slice) that solves the most not-yet-solved problems per second
of slice, where a problem counts as solved by (s, t) if setting s solved it in at most t seconds in
its sweep. Every attempt restarts from scratch, so slices add up. Use it on a training half only
and report on the other half: the schedule is fitted to the problems it sees.

Usage: make_schedule.py BUDGET_SECONDS SWEEP.jsonl [SWEEP.jsonl ...]
"""
import json
import sys

budget = float(sys.argv[1])
times = {}
for f in sys.argv[2:]:
    t = {}
    for line in open(f):
        r = json.loads(line)
        if r["status"] == "Unsatisfiable" and r.get("checked") is not False:
            t[r["problem"]] = r["wall"]
    times[f] = t
slices = [0.05, 0.1, 0.2, 0.5, 1, 2, 5]
done, used, plan = set(), 0.0, []
while used < budget:
    best = None
    for f, t in times.items():
        for s in slices:
            if used + s > budget:
                continue
            gain = sum(1 for p, w in t.items() if w <= s and p not in done)
            if gain and (best is None or gain / s > best[0]):
                best = (gain / s, f, s, gain)
    if best is None:
        break
    _, f, s, gain = best
    done |= {p for p, w in times[f].items() if w <= s}
    used += s
    plan.append((f, s, gain))
for f, s, g in plan:
    print(f"{f}\t{s}\t+{g}")
print(f"# {len(done)} solved in {used:.2f} s of schedule")
