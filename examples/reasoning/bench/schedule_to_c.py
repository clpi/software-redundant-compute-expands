#!/usr/bin/env python3
"""Turn make_schedule.py output into the SCHED table of native/hyper.c.

Usage: schedule_to_c.py SCHEDULE.txt   (sweep file names map to settings through the wrapper
scripts named in SETTINGS below: each wrapper is `exec hyper "$@" OPTIONS`)
"""
import re
import sys

rows = []
for line in open(sys.argv[1]):
    if line.startswith("#") or not line.strip():
        continue
    f, secs, _ = line.split("\t")
    m = re.search(r"train-s(\w+)\.jsonl", f)
    script = open(f"/tmp/claude-0/bench/cfg/s{m.group(1)}.sh").read()
    opts = script.split('"$@"', 1)[1].strip()
    rows.append((opts, float(secs)))
for o, s in rows:
    print(f'    {{ "{o}", {s} }},')
