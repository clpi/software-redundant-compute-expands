#!/usr/bin/env python3
"""Summarize a bench.py run: per solver, problems solved (answer matching the TPTP status),
and, on the problems every compared solver solved, median and total wall time, median peak
memory, and median inference steps in the printed proof. Inference steps exclude input
clauses and pure clausification steps; ours are hyperresolution steps, also given as binary
resolution steps (one hyperresolution step with k premises = k binary resolutions).

Usage: table.py RUN.jsonl LOGS_DIR [SOLVER ...]"""
import json
import os
import re
import statistics
import sys
from collections import defaultdict

PRE = ("cnf_transformation", "flattening", "rectify", "ennf_transformation", "nnf_transformation", "fof_simplification",
       "negated_conjecture", "sat_conversion", "choice_axiom", "pure_predicate_removal", "avatar_definition")


def steps(solver, log):
    m = re.search(r"SZS output start[^\n]*\n(.*?)SZS output end", log, re.S)
    if not m:
        return None
    body = m.group(1)
    if solver == "vampire":
        inf = re.findall(r"inference\((\w+)", body)
        return sum(1 for k in inf if k not in PRE)
    if solver == "eprover":
        n = 0
        for line in body.splitlines():
            mm = re.match(r"\s*\d+ : [^:]*: .* : (.*)$", line)
            if not mm:
                continue
            src = mm.group(1).strip()
            if src.startswith("initial") or src.startswith("fof_simplification") or re.fullmatch(r"\d+", src):
                continue
            n += 1
        return n
    return None


def main():
    run, logs = sys.argv[1], sys.argv[2]
    R = [json.loads(l) for l in open(run)]
    want = sys.argv[3:] or sorted({r["solver"] for r in R})
    status = {}
    for p in {r["problem"] for r in R}:
        status[p] = "Unsatisfiable"  # every problem in the CNF_UNS lists is Unsatisfiable by TPTP status
    by = defaultdict(dict)
    for r in R:
        if r["solver"] not in want:
            continue
        ok = r["status"] == status[r["problem"]] and r.get("checked", True) is not False
        st = None
        if ok and r["solver"] in ("vampire", "eprover") and r.get("log_sha256"):
            st = steps(r["solver"], open(os.path.join(logs, r["log_sha256"] + ".log")).read())
        if ok and r["solver"] in ("native", "ours"):
            st = r.get("proof_steps", 1) - 1 if r.get("proof_steps") else None
        by[r["solver"]][r["problem"]] = (ok, r["wall"], r["rss_kib"], st, r)
    probs = sorted(status)
    print(f"{len(probs)} problems")
    common = [p for p in probs if all(by[s].get(p, (False,))[0] for s in want)]
    print(f"solved by every solver: {len(common)}")
    for s in want:
        solved = [p for p in probs if by[s].get(p, (False,))[0]]
        w = [by[s][p][1] for p in common]; m = [by[s][p][2] for p in common if by[s][p][2]]
        stp = [by[s][p][3] for p in common if by[s][p][3] is not None]
        print(f"{s:8} solved {len(solved):4}  common: median wall {statistics.median(w)*1000:8.1f} ms  total {sum(w):8.2f} s"
              f"  median rss {statistics.median(m) if m else 0:8.0f} KiB  median proof steps {statistics.median(stp) if stp else '-'}")
    # head to head against native on every problem
    if "native" in want:
        for s in want:
            if s == "native":
                continue
            only_n = [p for p in probs if by["native"].get(p, (False,))[0] and not by[s].get(p, (False,))[0]]
            only_s = [p for p in probs if by[s].get(p, (False,))[0] and not by["native"].get(p, (False,))[0]]
            both = [p for p in probs if by["native"].get(p, (False,))[0] and by[s].get(p, (False,))[0]]
            faster = sum(1 for p in both if by["native"][p][1] < by[s][p][1])
            less_mem = sum(1 for p in both if by["native"][p][2] < by[s][p][2])
            print(f"native vs {s:8}: only native {len(only_n):3}, only {s} {len(only_s):3}; on {len(both)} both: native faster on {faster}, less memory on {less_mem}")
            if only_s:
                print("   ", s, "solves, native does not:", ", ".join(os.path.basename(p) for p in only_s))


if __name__ == "__main__":
    main()
