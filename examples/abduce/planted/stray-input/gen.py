#!/usr/bin/env python3
"""Writes the runs of one battery into results/NAME (planted: the producer of what check.py reads)."""
import json
import os
import sys

if __name__ == "__main__":
    base = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results")
    which = sys.argv[1]
    out = os.path.join(base, which)
    os.makedirs(out, exist_ok=True)
    for i in range(3):
        log = f"run-{i}.log"
        open(os.path.join(out, log), "w").write("ok\n" * (i + 1))
        with open(os.path.join(out, f"run-{i}.json"), "w") as fh:
            json.dump({"run": i, "log_file": log}, fh)
