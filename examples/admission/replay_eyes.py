# elimination order: rung 1 has the harness append its own runs; this script reshapes recorded
# idol-eyes campaign rows into kernel records and decides nothing. The kernel reads every number
# back from the trace files written here.
# usage: python3 -I replay_eyes.py <campaign dir> <run.py of the harness> <out dir> <with-audit-dims 0|1>
#
# Encoding (stated, so it can be checked):
#  - one domain per campaign; comparators playwright, selenium, agent-browser are configs;
#    every idol driver in the campaign is a built subject.
#  - dimensions the campaign itself registered: cold (wall us, cold rows), warm (one run per task_ms
#    sample of the warm rows; run.py checks no answer in warm mode, so these traces say "unverified",
#    which is not ok), tree (peak tree KiB, cold rows), cpu (cpu us, cold rows), and work (instructions) where the
#    campaign has work rows. verified becomes the trace's ok line. Determinism is folded into
#    verified (answers are checked per run); it is not a separate dimension here.
#  - with-audit-dims=1 also registers generality, conformance, rendering, tls, network: the
#    dimensions the claims audit (2026-11-20, E4) found missing. Nobody has runs on them.
#  - the contract binds the harness bytes given (run.py; the campaigns did not hash inputs at run
#    time, per the claims audit C3), floor 0 (generous: the campaigns used none), repeats = the
#    fewest repeats the campaign recorded per cell. No held-out set was sealed: the seal is the
#    hash of a fixed sentence, which no reveal can match. No do-nothing subject was run.
#  - idol-map is built from the record-map pass (run.py record_maps): one run of idol per task whose
#    output becomes idol-map's input. That pass's trace was not kept; it is written here as one
#    sample of 0, which cannot raise idol's worst sample. Only its existence matters to the check.
import collections, hashlib, json, os, sys

camp, harness, out, audit = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4] == "1"
os.makedirs(out + "/b", exist_ok=True)
rows = [json.loads(l) for l in open(camp + "/raw.jsonl")]
recs = []
nblob = [0]


def blob(text, name=None):
    nblob[0] += 1
    p = "b/" + (name or "%05d.txt" % nblob[0])
    with open(out + "/" + p, "w") as f:
        f.write(text)
    return p


def add(*r):
    recs.append([str(x) for x in r])
    return len(recs)


def sha_bytes(b):
    return hashlib.sha256(b).hexdigest()


comparators = ["playwright", "selenium", "agent-browser"]
drivers = sorted({r["driver"] for r in rows})
subjects = [d for d in drivers if d not in comparators]
tasks = sorted({r["task"] for r in rows})
haswork = any(r.get("mode") == "work" for r in rows)
dims = ["cold", "warm", "tree", "cpu"] + (["work"] if haswork else [])
if audit:
    dims += ["generality", "conformance", "rendering", "tls", "network"]
reps = min(collections.Counter((r["driver"], r["task"]) for r in rows if r.get("mode") == "cold" and "wall_ms" in r).values())

D = "0"
did = {d: str(i + 1) for i, d in enumerate(dims)}
sid = {d: str(100 + i) for i, d in enumerate(drivers)}
wid = {t: str(10 + i) for i, t in enumerate(tasks)}
for d in dims:
    add("dim", D, did[d])
wline = {}
for t in tasks:
    wline[t] = add("work", D, wid[t], blob("task " + t + "\n"))
for c in comparators:
    if c in drivers:
        add("config", D, sid[c])
hpath = blob(open(harness).read(), "harness-run.py")
sealed = sha_bytes(b"no held-out set was sealed for this campaign\n")
k = add("contract", D, sha_bytes(open(harness, "rb").read()), sealed, 0, reps)
ins = ",".join(str(wline[t]) for t in tasks)
built = {}
for s in subjects:
    if s != "idol-map":
        built[s] = add("build", D, sid[s], ins)
if "idol-map" in subjects:
    rec = [add("run", k, sid["idol"], wid[t], did["cold"], hpath, blob("ok\n0\n")) for t in tasks]
    built["idol-map"] = add("build", D, sid["idol-map"], ",".join(map(str, rec)))


def trace(ok, v):
    return blob(("ok" if ok else "fail") + "\n%d\n" % v)


for r in rows:
    if "wall_ms" in r:
        ok = bool(r["verified"])
        if r["mode"] == "cold":
            add("run", k, sid[r["driver"]], wid[r["task"]], did["cold"], hpath, trace(ok, round(r["wall_ms"] * 1000)))
            add("run", k, sid[r["driver"]], wid[r["task"]], did["tree"], hpath, trace(ok, r["peak_tree_kib"]))
            add("run", k, sid[r["driver"]], wid[r["task"]], did["cpu"], hpath, trace(ok, round(r["cpu_ms"] * 1000)))
        elif r["mode"] == "warm":
            add("run", k, sid[r["driver"]], wid[r["task"]], did["warm"], hpath, trace(ok, round(r["wall_ms"] * 1000)))
    elif r.get("mode") == "warm" and "task_ms" in r:
        for x in r["task_ms"]:
            add("run", k, sid[r["driver"]], wid[r["task"]], did["warm"], hpath, blob("unverified\n%d\n" % round(x * 1000)))
    elif r.get("mode") == "work" and "instructions" in r:
        add("run", k, sid[r["driver"]], wid[r["task"]], did["work"], hpath, trace(bool(r["verified"]), r["instructions"]))
claims = {}
for s in subjects:
    claims[add("beats", D, sid[s])] = s
with open(out + "/log.tsv", "w") as f:
    f.write("".join("\t".join(r) + "\n" for r in recs))
json.dump({"claims": {str(a): b for a, b in claims.items()}, "subjects": sid, "dims": did, "tasks": wid,
           "reps": reps, "audit_dims": audit}, open(out + "/map.json", "w"), indent=1, sort_keys=True)
print(camp, len(recs), "records", "subjects", subjects, "dims", dims, "reps", reps)
