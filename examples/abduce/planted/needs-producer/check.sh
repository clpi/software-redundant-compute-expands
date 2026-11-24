#!/bin/sh
# planted control: the gate reads a file that only tools/gen.py writes, and gen.py needs a
# module that lives in lib/ (not on its path)
python3 -c 'import json,sys; d=json.load(open("data/out.json")); sys.exit(0 if d["total"]==2080 else 1)' && echo ok
