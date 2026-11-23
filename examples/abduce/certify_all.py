"""Pick the hypotheses to certify and run certify.py on each (JOBS in parallel).
D1 raw: the front's full explanation. D1 strict: each component's cheapest joint explanation.
D0: the planted core of the first 6 used instances, and 3 planted false hypotheses (expected
refused by the kernel). Writes OUTDIR/certs.jsonl."""
import json, os, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
rec, outdir, jobs = sys.argv[1], sys.argv[2], int(os.environ.get("JOBS", "2"))
here = os.path.dirname(os.path.abspath(__file__))
tasks = []
raw = json.load(open(os.path.join(rec, "d1-raw.json")))
tasks.append(("d1-raw.json", "d1-raw-front", raw["front"][0]["hyp"], raw["front"][0]["covers"], False))
strict = json.load(open(os.path.join(rec, "d1-strict.json")))
for i, j in enumerate(strict["joint"]):
    hyp = min(j["explanations"], key=len) if j["explanations"] else j["fallback"]
    if hyp:
        tasks.append(("d1-strict.json", f"d1-strict-comp{i:02d}", hyp, j["obs"], False))
d0 = json.load(open(os.path.join(rec, "d0-planted.json")))
used = [r for r in d0["rows"] if "skipped" not in r]
for r in used[:6]:
    json.dump(r, open(os.path.join(outdir, f"d0-{r['seed']}.json"), "w"))
    tasks.append((f"d0-{r['seed']}.json", f"d0-seed{r['seed']}-core", r["core"], [r["names"][o] for o in r["O"]], False))
for r in used[:3]:
    for f in r["false"]:
        tasks.append((f"d0-{r['seed']}.json", f"d0-seed{r['seed']}-false-{f['kind']}", f["hyp"], [r["names"][o] for o in r["O"]], True))


def go(t):
    src, name, hyp, obs, neg = t
    path = os.path.join(outdir, src) if src.startswith("d0-") else os.path.join(rec, src)
    cmd = [sys.executable, os.path.join(here, "certify.py"), path, outdir, name, ",".join(hyp), ",".join(obs)] + (["--expect-fail"] if neg else [])
    p = subprocess.run(cmd, capture_output=True, text=True)
    line = p.stdout.strip().splitlines()[-1] if p.stdout.strip() else json.dumps({"name": name, "ok": False, "error": p.stderr[-400:]})
    d = json.loads(line); d["domain"] = src
    print(name, d["ok"], d.get("seconds"), flush=True)
    return d


with ThreadPoolExecutor(jobs) as ex:
    res = list(ex.map(go, tasks))
with open(os.path.join(outdir, "certs.jsonl"), "w") as f:
    for d in res:
        f.write(json.dumps(d, sort_keys=True) + "\n")
print("certified", sum(d["ok"] for d in res if not d.get("expect_fail")), "of", sum(1 for d in res if not d.get("expect_fail")),
      "| false refused", sum(d["ok"] for d in res if d.get("expect_fail")), "of", sum(1 for d in res if d.get("expect_fail")))
