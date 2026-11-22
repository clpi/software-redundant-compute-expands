"""Generate new implementations of admitted capabilities and verify each with its home's battery.

Generator (deterministic): for every single-expression function f in a library file whose
offered bytes equal the checkout's, and every call g(args) in f's body where g is a
single-expression function of the same unit, inline g: replace the call by g's body with its
parameters substituted by the arguments (parenthesized). An argument that is not a plain
name or number may be substituted only where its parameter occurs once, so no expression is
evaluated a different number of times. The result is new code for f's capability with
different premises.

Control variant (must not pass by construction of a good battery): the same inlining with
the first two arguments swapped, emitted only where g takes two or more distinct arguments.

Verifier: the home's own run.sh on a scratch clone in which only that function's body line is
replaced, with the named compiler (exit 0 = PASSED). Premises: `idol graph` of the rewritten
unit, the compiler's resolved applications. Each candidate is emitted as an artifact plus a
retire request of the artifact it would replace (same head); the loop admits the replacement
only if it passes and covers.

usage: gen_rewrite.py stream.jsonl <idol-lib checkout> <idol binary> <work dir> > stream-gen.jsonl
"""
import hashlib, json, os, re, shutil, subprocess, sys
from pathlib import Path

stream, IL, IDOL, WORK = Path(sys.argv[1]), Path(sys.argv[2]), sys.argv[3], Path(sys.argv[4])
lines = open(stream).read().split("\n")
header = json.loads(lines[0])
arts = [json.loads(l) for l in lines[1:] if l]
nid = max(a["id"] for a in arts) + 1
latest = {}
for a in arts:
    if "projection_of" in a or "group" in a:
        continue
    latest[a["head"]] = a          # stream order: later versions replace earlier ones

DEF = re.compile(r"^([A-Za-z_][A-Za-z0-9_]*)(\s*(?::[^=\n]*)?=\s*)\((.*)\)\s*$")
IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$|^-?[0-9]+$")

def singles(text):
    out, L = {}, text.split("\n")
    for i, l in enumerate(L):
        m = DEF.match(l)
        if not m:
            continue
        body, j = [], i + 1
        while j < len(L) and (L[j].startswith(" ") or not L[j].strip()):
            if L[j].strip():
                body.append(j)
            j += 1
        if len(body) == 1:
            params = [p.split(":")[0].strip() for p in m.group(3).split(",") if p.strip()]
            out[m.group(1)] = {"def": i, "line": body[0], "params": params, "body": L[body[0]].strip()}
    return out

def calls(expr, name):
    """(start, end, args) of each call name(...) not preceded by a name char, '.' or ':'."""
    res = []
    for m in re.finditer(r"(?<![A-Za-z0-9_.:])" + re.escape(name) + r"\(", expr):
        depth, i, start = 1, m.end(), m.end()
        args, cur = [], start
        while i < len(expr) and depth:
            c = expr[i]
            if c in "([{":
                depth += 1
            elif c in ")]}":
                depth -= 1
            elif c == "," and depth == 1:
                args.append(expr[cur:i].strip()); cur = i + 1
            i += 1
        if depth == 0:
            last = expr[cur:i - 1].strip()
            if last or args:
                args.append(last)
            res.append((m.start(), i, args))
    return res

def substitute(body, params, args):
    toks = re.split(r"([A-Za-z_][A-Za-z0-9_]*)", body)
    sub = dict(zip(params, args))
    out = []
    for k, t in enumerate(toks):
        prev = toks[k - 1][-1:] if k else ""
        if k % 2 == 1 and t in sub and prev not in (".", ":"):
            a = sub[t]
            out.append(a if IDENT.match(a) else "(" + a + ")")
        else:
            out.append(t)
    return "".join(out)

def occurrences(body, p):
    return len(re.findall(r"(?<![A-Za-z0-9_.:])" + re.escape(p) + r"(?![A-Za-z0-9_])", body))

def git(*a, cwd=IL):
    return subprocess.run(["git", "-C", str(cwd), *a], capture_output=True, text=True, check=True).stdout

if WORK.exists():
    shutil.rmtree(WORK)
WORK.mkdir(parents=True)
scratch = WORK / "il"
subprocess.run(["git", "clone", "-q", "--local", str(IL), str(scratch)], check=True)
subprocess.run(["git", "-C", str(scratch), "checkout", "-q", git("rev-parse", "HEAD").strip()], check=True)

UNIT = re.compile(r"^\s*cat\s+(.+?)\s*>\s*\"?\$work/unit\.id\"?")
def unit_files(home):
    for l in (scratch / home / "run.sh").read_text().splitlines():
        m = UNIT.match(l)
        if m:
            return m.group(1).split()
    return None

NET = re.compile(r"\bgh api\b|\bcurl\b|\bwget\b")
def battery(home):
    """The home's run.sh, or None if it cannot run here. A battery that ends by fetching an
    incumbent from the network only to print its line count may run without that tail
    (allowed only if every line from the first fetch on is the fetch or an echo); a battery
    whose network step feeds a check cannot run here."""
    L = (scratch / home / "run.sh").read_text().split("\n")
    k = next((i for i, l in enumerate(L) if NET.search(l)), None)
    if k is None:
        return "run.sh", "run.sh"
    tail = [l.strip() for l in L[k:] if l.strip()]
    if not all(NET.search(l) or l.startswith("echo ") for l in tail):
        return None, "network step feeds a check"
    (scratch / home / "run.local.sh").write_text("\n".join(L[:k]) + "\n")
    return "run.local.sh", "run.sh without its trailing incumbent fetch (echo only)"

def run_battery(home, script):
    r = subprocess.run(["sh", str(scratch / home / script)], capture_output=True, text=True,
                       env=dict(os.environ, IDOL=IDOL))
    return ("PASSED" if r.returncode == 0 else "FAILED"), hashlib.sha256(r.stdout.encode()).hexdigest()

def graph_prem(home, files, fname):
    text = b"".join((scratch / home / f).read_bytes() for f in files)
    up = WORK / "unit.id"; up.write_bytes(text)
    g = json.loads(subprocess.run([IDOL, "graph", str(up)], capture_output=True, text=True, check=True).stdout)
    starts, pos = [], 1
    for f in files:
        n = (scratch / home / f).read_text().count("\n")
        starts.append((f, pos, pos + n - 1)); pos += n
    def owner(line):
        for f, a, b in starts:
            if a <= line <= b:
                return f
    funcs = {n["id"]: n for n in g["nodes"] if n["kind"] == "func"}
    lib = files[0] if not files[0].startswith("../") else files[1]
    capof = {}
    for i, n in funcs.items():
        f = owner(n["line"])
        if f and not f.endswith(("vectors.id", "battery.id", "streams.id")):
            h = f.split("/")[1] if f.startswith("../") else home
            capof[i] = f"{h}:{n['name']}"
    me = [i for i, n in funcs.items() if n["name"] == fname and owner(n["line"]) == lib and n.get("scope") == 0]
    prem = set()
    for a in g["applications"]:
        if me and a["caller"] == me[0] and a["relation"] in capof and a["relation"] != me[0]:
            prem.add(capof[a["relation"]])
    return sorted(prem)

new, tried, homes = [], {"candidates": 0, "controls": 0}, {}
dependents = {}
for r in sorted(scratch.glob("*/run.sh")):
    for o in sorted(set(re.findall(r"\.\./([A-Za-z0-9_]+)/", r.read_text()))):
        if o != "tools":
            dependents.setdefault(o, []).append(r.parent.name)
for home in sorted(p.parent.name for p in scratch.glob("*/run.sh")):
    files = unit_files(home)
    if not files:
        continue
    libf = [f for f in files if not f.startswith("../")][0]
    path = scratch / home / libf
    orig = path.read_text()
    libsha = hashlib.sha256(orig.encode()).hexdigest()
    S = singles(orig)
    script, how = battery(home)
    if script is None:
        homes[home] = "skipped: " + how
        continue
    base, _ = run_battery(home, script)
    homes[home] = how + ("" if base == "PASSED" else "; skipped: unmodified library fails it here")
    if base != "PASSED":
        continue
    for fname, f in sorted(S.items()):
        head = f"{home}:{fname}"
        old = latest.get(head)
        if not old or old["lib_sha256"] != libsha:
            continue                      # only rewrite bytes the stream offered
        for gname, g in sorted(S.items()):
            if gname == fname:
                continue
            for (s, e, args) in calls(f["body"], gname):
                if len(args) != len(g["params"]):
                    continue
                if any(not IDENT.match(a) and occurrences(g["body"], p) > 1 for p, a in zip(g["params"], args)):
                    continue
                variants = [("inline", args)]
                if len(args) >= 2 and args[0] != args[1]:
                    variants.append(("control-swap", [args[1], args[0]] + args[2:]))
                for kind, use in variants:
                    expr = f["body"][:s] + "(" + substitute(g["body"], g["params"], use) + ")" + f["body"][e:]
                    L = orig.split("\n")
                    indent = L[f["line"]][:len(L[f["line"]]) - len(L[f["line"]].lstrip())]
                    L[f["line"]] = indent + expr
                    path.write_text("\n".join(L))
                    verdict, tsha = run_battery(home, script)
                    # every home built on this one must still pass on the rewritten bytes
                    for d in dependents.get(home, []):
                        if verdict == "PASSED":
                            dscript, _ = battery(d)
                            dv, dsha = run_battery(d, dscript) if dscript else ("FAILED", "")
                            verdict = dv
                            tsha = hashlib.sha256((tsha + dsha).encode()).hexdigest()
                    prem = graph_prem(home, files, fname) if verdict == "PASSED" else sorted(set(old["prem"]))
                    newsha = hashlib.sha256(path.read_bytes()).hexdigest()
                    path.write_text(orig)
                    tried["candidates" if kind == "inline" else "controls"] += 1
                    new.append({
                        "id": nid, "version": f"gen:{newsha[:12]}", "home": home, "line": old["line"],
                        "path": fname, "head": head, "prem": prem, "verdict": verdict,
                        "receipt_transcript": tsha, "lib_file": f"{home}/{libf}", "lib_sha256": newsha,
                        "observed": old["observed"], "time": 2**40, "commit": "generated",
                        "generated": {"kind": kind, "inlined": gname, "replaces": old["id"],
                                      "from": f["body"], "to": expr, "verifier": how,
                                      "dependents_checked": dependents.get(home, [])},
                    })
                    nid += 1

header = dict(header, artifacts=len(arts) + len(new), generated=dict(tried, homes=homes, idol_sha256=hashlib.sha256(open(IDOL, "rb").read()).hexdigest(),
              idol_lib_commit=git("rev-parse", "HEAD").strip()))
print(json.dumps(header, sort_keys=True))
for a in arts + new:
    print(json.dumps(a, sort_keys=True))
