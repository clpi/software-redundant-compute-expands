#!/usr/bin/env python3
"""Recompute each campaign summary from its raw samples and the comparator/Idol
p50 ratios. argv: IDOL_EYES_RESULTS_DIR (the project-folder idol-eyes/)."""
import json, sys, os
d = sys.argv[1] if len(sys.argv) > 1 else "/mnt/project-files/idol-eyes"
def pct(xs, q):
    s = sorted(xs); return s[min(len(s) - 1, int(round(q * (len(s) - 1))))] if s else None
for c in ["campaign-1", "campaign-2", "campaign-3", "campaign-4", "campaign-5"]:
    raw = [json.loads(l) for l in open(os.path.join(d, c, "raw.jsonl"))]
    summ = json.load(open(os.path.join(d, c, "summary.json")))
    bad = 0
    for cell in summ["cells"]:
        cold = [r for r in raw if r.get("mode") == "cold" and r["driver"] == cell["driver"] and r["task"] == cell["task"]]
        vt = [r["wall_ms"] for r in cold if r["verified"]]
        if (sum(r["verified"] for r in cold), pct(vt, .5), pct(vt, .95)) != (cell["verified"], cell["cold_p50_ms"], cell["cold_p95_ms"]): bad += 1
    def ratios(key):
        out = []
        for cell in summ["cells"]:
            if cell["driver"] in ("playwright", "selenium", "agent-browser") and cell.get(key):
                i = [x for x in summ["cells"] if x["driver"] == "idol" and x["task"] == cell["task"] and x.get(key)]
                if i: out.append(cell[key] / i[0][key])
        return out
    cr, wr = ratios("cold_p50_ms"), ratios("warm_p50_ms")
    print(c, "cells=%d summary-mismatches-vs-raw=%d" % (len(summ["cells"]), bad),
          "cold ratio min %.0fx max %.0fx" % (min(cr), max(cr)), "warm ratio min %.0fx max %.0fx" % (min(wr), max(wr)))
