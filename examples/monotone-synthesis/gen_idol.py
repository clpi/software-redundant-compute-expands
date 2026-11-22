"""Build the candidate stream for the monotone synthesis loop from real idol-lib data.

Inputs (read only, never executed):
  graphs/receipts  the Idol compiler's `idol graph` export of each home's battery unit and
                   the battery receipt for the same bytes, as recorded by the idol-qualification
                   thread (compiler clpi/idol e5ade0aa; idol-lib 0be14af, and f754884 for the
                   three homes PR 24 changed or added).
  idol-lib         a checkout, for library line counts at each commit and for history: the
                   commit time at which each top-level definition first appears in its file.

One artifact per compiler function defined in a home's library file.
  head     capability "home:path", path = enclosing function names then the function's name
  prem     heads of the library functions it applies, as the compiler resolved them (never by
           name); host builtins the compiler leaves unresolved are host primitives, not premises
  verdict  the home's battery verdict for exactly these bytes, judged by the home's verify.py
  observed root (applied from battery code), reached (only through library code) or unreached

Capability identity across versions is (home, path): a premise of this encoding, stated.
Order: by the commit time a definition (or its top-level ancestor) first appears in the
library file; ties by version then line. The 0be14af bytes are offered at their history
times; receipts exist only for the 0be14af and f754884 bytes, so the stream is "the 0be14af
library offered in the order its definitions arrived", then PR 24's versions.

usage: gen_idol.py <idol-qualification dir> <idol-lib checkout> > stream.jsonl
"""
import hashlib, json, re, subprocess, sys
from pathlib import Path

IQ, IL = Path(sys.argv[1]), Path(sys.argv[2])
VERSIONS = [("0be14af", "0be14af8d63a749c5121dbf790665cf38593b077",
             "resolve-e5ade0aa-0be14af", "resolve-e5ade0aa-0be14af.jsonl", "run-e5ade0aa-0be14af/receipts.jsonl"),
            ("f754884", "f754884", "resolve-e5ade0aa-f754884", "resolve-e5ade0aa-f754884.jsonl", "run-e5ade0aa-f754884/receipts.jsonl")]
DEF = re.compile(r"^([A-Za-z_][A-Za-z0-9_]*)\s*(?::[^=\n]*)?=\s*\(")

def git(*a):
    return subprocess.run(["git", "-C", str(IL), *a], capture_output=True, text=True, check=True).stdout

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

first_seen = {}
def history(libfile, upto):
    """(name -> (commit time, commit)) of the first commit whose file defines a top-level name."""
    key = (libfile, upto)
    if key in first_seen:
        return first_seen[key]
    out = {}
    for line in git("log", "--reverse", "--format=%H %ct", upto, "--", libfile).split("\n"):
        if not line:
            continue
        c, t = line.split()
        try:
            text = git("show", f"{c}:{libfile}")
        except subprocess.CalledProcessError:
            continue
        for ln in text.split("\n"):
            m = DEF.match(ln)
            if m and m.group(1) not in out:
                out[m.group(1)] = (int(t), c)
    first_seen[key] = out
    return out

inputs, arts = {}, []
for ver, commit, gdir, rfile, recfile in VERSIONS:
    res = {json.loads(l)["home"]: json.loads(l) for l in open(IQ / rfile)}
    rec = {json.loads(l)["home"]: json.loads(l) for l in open(IQ / recfile)}
    inputs[f"{ver}:resolve"] = sha(IQ / rfile)
    inputs[f"{ver}:receipts"] = sha(IQ / recfile)
    for home, r in sorted(res.items()):
        gp = IQ / gdir / f"{home}.graph.json"
        inputs[f"{ver}:{home}:graph"] = sha(gp)
        g = json.loads(gp.read_text())
        libfile = f"{home}/{r['files'][0]}"
        libtext = git("show", f"{commit}:{libfile}")
        nlib = libtext.count("\n") + (0 if libtext.endswith("\n") else 1)
        libsha = hashlib.sha256(libtext.encode()).hexdigest()
        nodes = {n["id"]: n for n in g["nodes"]}
        funcs = {i: n for i, n in nodes.items() if n["kind"] == "func" and 1 <= n.get("line", 0) <= nlib}
        def path(i):
            names, j = [], i
            while j in funcs:
                names.append(funcs[j]["name"])
                j = funcs[j].get("scope")
            return "/".join(reversed(names))
        top = lambda i: path(i).split("/")[0]
        roots = {x["line"] for x in r["roots"]}
        reached = {x["line"] for x in r["reached_not_roots"]}
        callees = {}
        for a in g["applications"]:
            if a["caller"] in funcs and a["relation"] in funcs and a["relation"] != a["caller"]:
                callees.setdefault(a["caller"], set()).add(a["relation"])
        hist = history(libfile, commit)
        for i, n in sorted(funcs.items(), key=lambda kv: kv[1]["line"]):
            t, c = hist.get(top(i), (None, None))
            obs = "root" if n["line"] in roots else "reached" if n["line"] in reached else "unreached"
            arts.append({
                "version": ver, "home": home, "line": n["line"], "path": path(i),
                "head": f"{home}:{path(i)}",
                "prem": sorted({f"{home}:{path(j)}" for j in callees.get(i, ())}),
                "verdict": rec[home]["verdict"], "receipt_transcript": rec[home]["transcript_sha256"],
                "lib_file": libfile, "lib_sha256": libsha, "observed": obs,
                "time": t, "commit": c,
            })

assert all(a["time"] is not None for a in arts), [a["head"] for a in arts if a["time"] is None]
arts.sort(key=lambda a: (a["time"], 0 if a["version"] == "0be14af" else 1, a["home"], a["line"]))
for k, a in enumerate(arts):
    a["id"] = k
print(json.dumps({"inputs": inputs, "artifacts": len(arts)}, sort_keys=True))
for a in arts:
    print(json.dumps(a, sort_keys=True))
