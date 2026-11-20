#!/usr/bin/env python3
"""Playwright cost decomposition (audit). argv: BASE TASKID MODE
MODE=import   : start python, import playwright, exit
MODE=launch   : + start driver, launch Chromium, open context, close
MODE=task     : + run the task once (the campaign's cold cell)
MODE=dom      : launch once, then run the task 11 times by dispatching
                the same DOM actions with page.evaluate (no actionability
                waits); prints per-repetition ms. Still a real browser:
                parsing, style, layout and script all run.
Prints one JSON line."""
import json, os, sys, time
t0 = time.perf_counter()
base, tid, mode = sys.argv[1], sys.argv[2], sys.argv[3]
from playwright.sync_api import sync_playwright
if mode == "import":
    print(json.dumps({"mode": mode})); sys.exit()
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
TASKS = {t["id"]: t for t in json.load(open(os.environ["EYES"] + "/bench/browser/tasks.json"))["tasks"]}
EXE = os.environ["CHROMIUM"]; ARGS = ["--no-sandbox", "--disable-gpu", "--disable-dev-shm-usage"]
JS = """([op, a, b]) => {
 const norm = s => s.replace(/\\s+/g,' ').trim();
 const lab = t => { for (const l of document.querySelectorAll('label')) if (norm(l.textContent)===t) return l.control; };
 if (op==='fill') { lab(a).value = b; return null; }
 if (op==='check') { lab(a).checked = true; return null; }
 if (op==='select') { const s = lab(a); for (const o of s.options) if (norm(o.text)===b) s.value=o.value; return null; }
 if (op==='click') { const sel = a==='button' ? 'button' : 'a';
   for (const e of document.querySelectorAll(sel)) if (norm(e.textContent)===b && e.checkVisibility({visibilityProperty:true})) { e.click(); return null; } return 'missing'; }
 if (op==='read') { const e = document.getElementById(a); return e ? norm(e.textContent) : null; }
 if (op==='cell') { for (const tr of document.querySelectorAll('tr')) { const td = tr.querySelectorAll('td'); if (td.length && norm(td[0].textContent)===a) return norm(td[+b-1].textContent);} }
}"""
def dom_run(page, base, task):
    ans = None
    for st in task["steps"]:
        if st[0] == "open":
            page.goto(base + st[1]); continue
        if st[0] == "click":
            with page.expect_navigation(wait_until="commit") if not task.get("js") else _null():
                page.evaluate(JS, [st[0], st[1], st[2]])
            continue
        if st[0] == "read" and task.get("js"):
            page.wait_for_function("([i,v]) => { const e=document.getElementById(i); return e && e.textContent.trim()===v; }", arg=[st[1], task["answer"]], timeout=2000, polling="raf")
        r = page.evaluate(JS, [st[0], st[1], st[2] if len(st) > 2 else None])
        if st[0] in ("read", "cell"): ans = r
    return ans
class _null:
    def __enter__(s): return s
    def __exit__(s, *a): return False
with sync_playwright() as p:
    b = p.chromium.launch(executable_path=EXE, args=ARGS, headless=True)
    ctx = b.new_context()
    launch_ms = (time.perf_counter() - t0) * 1000
    out = {"mode": mode, "launch_ms": launch_ms}
    if mode == "task":
        from playwright_run import run  # noqa: the campaign's own step code
    if mode == "task":
        page = ctx.new_page(); s = time.perf_counter()
        out["answer"], _ = run(page, base, TASKS[tid]); out["task_ms"] = (time.perf_counter() - s) * 1000
    if mode == "dom":
        ts = []
        for _ in range(11):
            page = ctx.new_page(); s = time.perf_counter()
            out["answer"] = dom_run(page, base, TASKS[tid]); ts.append((time.perf_counter() - s) * 1000); page.close()
        out["task_ms"] = ts[1:]
    b.close()
print(json.dumps(out))
