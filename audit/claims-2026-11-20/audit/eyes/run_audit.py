#!/usr/bin/env python3
"""Audit runner: cold cells spawn-to-exit (as the campaign measures),
CPU from wait4, largest-process maxrss. Writes raw.jsonl and summary.json."""
import json, os, random, subprocess, sys, time, statistics
HERE = os.path.dirname(os.path.abspath(__file__))
EYES = os.environ["EYES"]; OUT = sys.argv[1]; N = int(sys.argv[2]) if len(sys.argv) > 2 else 10
TASKS = {t["id"]: t for t in json.load(open(EYES + "/bench/browser/tasks.json"))["tasks"]}
STATIC = ["login", "chain", "prefs", "table", "search"]
port = 18600; base = "http://127.0.0.1:%d" % port
os.makedirs(OUT, exist_ok=True); ev = os.path.join(OUT, "events.jsonl"); open(ev, "w").close()
srv = subprocess.Popen([sys.executable, EYES + "/bench/browser/fixture.py", str(port), ev]); time.sleep(0.6)
def plan(t):
    return "".join(("open\t" + base + s[1] if s[0] == "open" else "\t".join(s)) + "\n" for s in TASKS[t]["steps"]).encode()
def measured(argv, stdin=b""):
    t0 = time.perf_counter()
    p = subprocess.Popen(argv, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    out, _ = p.communicate(stdin)
    _, _, ru = os.wait4(p.pid, 0) if p.returncode is None else (0, 0, None)
    wall = (time.perf_counter() - t0) * 1000
    return out, wall
def measured4(argv, stdin=b""):
    t0 = time.perf_counter()
    p = subprocess.Popen(argv, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    p.stdin.write(stdin); p.stdin.close(); out = p.stdout.read()
    _, _, ru = os.wait4(p.pid, 0)
    return out, (time.perf_counter() - t0) * 1000, (ru.ru_utime + ru.ru_stime) * 1000, ru.ru_maxrss
PY = sys.executable
cells = []
for t in STATIC:
    for i in range(N):
        cells += [("python-floor", t, i), ("stdlib", t, i), ("pw-import", t, i), ("pw-launch", t, i), ("pw-task", t, i)]
random.Random(20261120).shuffle(cells)
raw = []
for d, t, i in cells:
    if d == "python-floor": argv, stdin = [PY, "-c", "pass"], b""
    elif d == "stdlib": argv, stdin = [PY, HERE + "/stdlib_driver.py"], plan(t)
    else: argv, stdin = [PY, HERE + "/pw_decompose.py", base, t, d.split("-")[1]], b""
    out, wall, cpu, rss = measured4(argv, stdin)
    last = out.decode(errors="replace").strip().split("\n")[-1] if out else ""
    if d == "stdlib": ans = last.partition("\t")[2]
    elif d == "pw-task":
        try: j = json.loads(last); ans = j.get("answer")
        except Exception: ans = None
    else: ans = None
    rec = {"driver": d, "task": t, "rep": i, "wall_ms": wall, "cpu_ms": cpu, "maxrss_kib": rss, "answer": ans,
           "correct": (ans == TASKS[t]["answer"]) if d in ("stdlib", "pw-task") else None}
    if d in ("pw-launch", "pw-task"):
        try: rec["launch_ms"] = json.loads(last).get("launch_ms"); rec["task_ms"] = json.loads(last).get("task_ms")
        except Exception: pass
    raw.append(rec); print(json.dumps(rec), flush=True)
# warm: DOM-dispatch in a resident browser, every task (first rep dropped inside the script)
for t in TASKS:
    out, wall, cpu, rss = measured4([PY, HERE + "/pw_decompose.py", base, t, "dom"])
    try: j = json.loads(out.decode().strip().split("\n")[-1])
    except Exception: j = {}
    rec = {"driver": "pw-dom-warm", "task": t, "task_ms": j.get("task_ms"), "answer": j.get("answer"), "correct": j.get("answer") == TASKS[t]["answer"]}
    raw.append(rec); print(json.dumps(rec), flush=True)
srv.terminate()
with open(os.path.join(OUT, "raw.jsonl"), "w") as f:
    for r in raw: f.write(json.dumps(r) + "\n")
def p(xs, q):
    s = sorted(xs); return s[min(len(s) - 1, int(round(q * (len(s) - 1))))] if s else None
summ = {"machine": {"cpus": os.cpu_count(), "uname": " ".join(os.uname()), "chromium": os.environ.get("CHROMIUM")}, "cells": []}
for d in ["python-floor", "stdlib", "pw-import", "pw-launch", "pw-task"]:
    for t in STATIC:
        rs = [r for r in raw if r["driver"] == d and r["task"] == t]
        summ["cells"].append({"driver": d, "task": t, "n": len(rs), "correct": sum(1 for r in rs if r["correct"]),
            "wall_p50": p([r["wall_ms"] for r in rs], .5), "wall_p95": p([r["wall_ms"] for r in rs], .95),
            "cpu_p50": p([r["cpu_ms"] for r in rs], .5), "maxrss_kib_max": max(r["maxrss_kib"] for r in rs),
            "task_ms_p50": p([r["task_ms"] for r in rs if r.get("task_ms") is not None], .5)})
for r in raw:
    if r["driver"] == "pw-dom-warm":
        summ["cells"].append({"driver": "pw-dom-warm", "task": r["task"], "correct": r["correct"], "warm_p50": p(r["task_ms"] or [], .5), "warm_min": min(r["task_ms"] or [0])})
json.dump(summ, open(os.path.join(OUT, "summary.json"), "w"), indent=1)
