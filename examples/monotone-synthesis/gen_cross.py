"""Extend the candidate stream with homes whose unit is built on another home's library.

For each idol-lib home whose run.sh builds its unit from another home's file
(`cat ../other/other.id own.id`), run `idol graph` on exactly that unit with the named
compiler and emit one artifact per function of the home's own file. Premises are the
compiler's resolved applications; a callee defined in the other home's file is the
capability of that home ("sha256:hexof"), so these are cross-home premises. The other
home's file must be byte-identical to the bytes its own artifacts were offered at (checked).

Verdict: the home's own run.sh, run with the same compiler (exit 0 = PASSED), recorded with
its output's sha256. Observed: reachable from the unit's top-level code through resolved
applications (root if applied from top level, reached otherwise, unreached if neither).

usage: gen_cross.py stream.jsonl <idol-lib checkout> <idol binary> <work dir> > stream-cross.jsonl
"""
import hashlib, json, os, re, subprocess, sys
from pathlib import Path

stream, IL, IDOL, WORK = Path(sys.argv[1]), Path(sys.argv[2]), sys.argv[3], Path(sys.argv[4])
WORK.mkdir(parents=True, exist_ok=True)
lines = open(stream).read().split("\n")
header = json.loads(lines[0])
arts = [json.loads(l) for l in lines[1:] if l]
nid = max(a["id"] for a in arts) + 1
offered_sha = {}
for a in arts:
    offered_sha.setdefault(a["home"], set()).add(a["lib_sha256"])

def git(*a):
    return subprocess.run(["git", "-C", str(IL), *a], capture_output=True, text=True, check=True).stdout

head_commit = git("rev-parse", "HEAD").strip()
idol_sha = hashlib.sha256(open(IDOL, "rb").read()).hexdigest()
CROSS = re.compile(r"^\s*cat\s+\.\./([A-Za-z0-9_]+)/([A-Za-z0-9_.]+)\s+([A-Za-z0-9_.]+)\s+>")
new, inputs = [], {"idol_lib_commit": head_commit, "idol_sha256": idol_sha}
for run in sorted(IL.glob("*/run.sh")):
    home = run.parent.name
    m = next((CROSS.match(l) for l in run.read_text().splitlines() if CROSS.match(l)), None)
    if not m:
        continue
    other, ofile, own = m.groups()
    otext = (IL / other / ofile).read_bytes()
    osha = hashlib.sha256(otext).hexdigest()
    assert osha in offered_sha.get(other, set()), f"{other}/{ofile} bytes differ from the offered ones"
    ownb = (IL / home / own).read_bytes()
    unit = WORK / f"{home}.unit.id"
    unit.write_bytes(otext + ownb)
    g = json.loads(subprocess.run([IDOL, "graph", str(unit)], capture_output=True, text=True, check=True).stdout)
    r = subprocess.run(["sh", str(run)], capture_output=True, text=True, env=dict(os.environ, IDOL=IDOL))
    verdict = "PASSED" if r.returncode == 0 else "FAILED"
    inputs[f"{home}:run_exit"] = r.returncode
    inputs[f"{home}:run_output_sha256"] = hashlib.sha256(r.stdout.encode()).hexdigest()
    inputs[f"{home}:unit_sha256"] = hashlib.sha256(unit.read_bytes()).hexdigest()
    nother = otext.decode().count("\n")
    nodes = {n["id"]: n for n in g["nodes"]}
    funcs = {i: n for i, n in nodes.items() if n["kind"] == "func"}
    def owner(i):
        return other if funcs[i]["line"] <= nother else home
    def path(i):
        names, j = [], i
        while j in funcs:
            names.append(funcs[j]["name"]); j = funcs[j].get("scope")
        return "/".join(reversed(names))
    callees, top = {}, set()
    for a in g["applications"]:
        c, t = a["caller"], a["relation"]
        if t not in funcs:
            continue
        if c in funcs:
            if c != t:
                callees.setdefault(c, set()).add(t)
        else:
            top.add(t)
    reached, stack = set(top), list(top)
    while stack:
        for nx in callees.get(stack.pop(), ()):
            if nx not in reached:
                reached.add(nx); stack.append(nx)
    t, c = git("log", "-1", "--format=%ct %H", "--", f"{home}/{own}").split()
    for i, n in sorted(funcs.items(), key=lambda kv: kv[1]["line"]):
        if owner(i) != home:
            continue
        new.append({
            "id": nid, "version": head_commit[:7], "home": home, "line": n["line"] - nother,
            "path": path(i), "head": f"{home}:{path(i)}",
            "prem": sorted({f"{owner(j)}:{path(j)}" for j in callees.get(i, ())}),
            "verdict": verdict, "receipt_transcript": inputs[f"{home}:run_output_sha256"],
            "lib_file": f"{home}/{own}", "lib_sha256": hashlib.sha256(ownb).hexdigest(),
            "observed": "root" if i in top else "reached" if i in reached else "unreached",
            "time": int(t), "commit": c, "built_on": f"{other}/{ofile}@{osha[:16]}",
        })
        nid += 1

header = dict(header, artifacts=len(arts) + len(new), cross=inputs)
print(json.dumps(header, sort_keys=True))
for a in arts + new:
    print(json.dumps(a, sort_keys=True))
