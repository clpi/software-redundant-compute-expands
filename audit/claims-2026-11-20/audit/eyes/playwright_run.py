#!/usr/bin/env python3
"""Playwright comparator driver (test-only). Runs one task of tasks.json.

argv: BASE TASKID [warm-iterations]
Prints one JSON line: {"answer": ..., "commands": n, "launch_ms": ..., "task_ms": [...]}.
The browser is the shared Chromium build; launch is timed separately
so cold and warm can be reported apart."""
import json, os, sys, time
from playwright.sync_api import sync_playwright, expect
HERE = os.path.dirname(os.path.abspath(__file__))
TASKS = {t["id"]: t for t in json.load(open(os.environ["EYES"]+"/bench/browser/tasks.json"))["tasks"]}
EXE = os.environ.get("CHROMIUM", "/tmp/chromium")
ARGS = ["--no-sandbox", "--disable-gpu", "--disable-dev-shm-usage"]

def run(page, base, task):
    answer, n = None, 0
    for st in task["steps"]:
        op = st[0]; n += 1
        if op == "open": page.goto(base + st[1])
        elif op == "fill": page.get_by_label(st[1], exact=True).fill(st[2])
        elif op == "check": page.get_by_label(st[1], exact=True).check()
        elif op == "select": page.get_by_label(st[1], exact=True).select_option(label=st[2])
        elif op == "click": page.get_by_role(st[1], name=st[2], exact=True).click()
        elif op == "read":
            loc = page.locator("#" + st[1])
            if task.get("js"):
                # Script pages settle after the click returns. The driver is
                # given the expected answer as a wait condition (bounded
                # 2 s), the most favourable wait it could have; Idol gets
                # no such oracle.
                try: expect(loc).to_have_text(task["answer"], timeout=2000)
                except AssertionError: pass
            answer = loc.inner_text(timeout=2000)
        elif op == "cell": answer = page.locator("tr", has=page.get_by_role("cell", name=st[1], exact=True)).locator("td").nth(int(st[2]) - 1).inner_text()
    return answer, n

def main():
    base, tid = sys.argv[1], sys.argv[2]
    reps = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    t0 = time.perf_counter()
    with sync_playwright() as p:
        b = p.chromium.launch(executable_path=EXE, args=ARGS, headless=True)
        ctx = b.new_context()
        launch = (time.perf_counter() - t0) * 1000
        times, answer, n = [], None, 0
        for _ in range(reps):
            page = ctx.new_page()
            s = time.perf_counter()
            try:
                answer, n = run(page, base, TASKS[tid])
            except Exception as e:
                answer = "ERROR " + type(e).__name__
            times.append((time.perf_counter() - s) * 1000)
            page.close()
        b.close()
    print(json.dumps({"answer": answer, "commands": n, "launch_ms": launch, "task_ms": times}))

