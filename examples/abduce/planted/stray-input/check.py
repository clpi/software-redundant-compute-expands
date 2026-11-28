#!/usr/bin/env python3
"""Checks every run of one battery (planted: it reads each .json in results/NAME as a run)."""
import json
import os
import sys


def check(bdir):
    n = 0
    for f in sorted(os.listdir(bdir)):
        if not f.endswith(".json"):
            continue
        summ = json.load(open(os.path.join(bdir, f)))
        lines = open(os.path.join(bdir, summ["log_file"])).read().splitlines()
        assert lines and all(l == "ok" for l in lines), f
        n += 1
    assert n == 3, f"{n} runs"
    print(f"checked {n} runs")


if __name__ == "__main__":
    base = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results")
    check(os.path.join(base, sys.argv[1]))
