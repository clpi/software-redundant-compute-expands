"""Domain D2: why does a gate fail? Observations come from running it; causes are abduced on
the canonical log; each surviving cause is tested by a controlled rerun.

A gate run is an observation: exit status plus symptom terms extracted from its output.
Candidate causes come from the gate script (static reads: required variables, positional
arguments, argv indices, tools it calls, the step after its last progress line) and from the
symptoms themselves (paths that were missing, URLs that failed to fetch). Each cause enters the
log as records `cause -> predicted symptom`; every predicted symptom that the run did NOT show
enters as `symptom -> bot`, so a cause that predicts something absent is inconsistent.

Experiments: for a cause, an intervention removes it (set the variable, pass the argument, put
the file in place, rewrite the URL, run the hidden step visibly). The cause is VERIFIED when
the symptom it predicts is present in every control run, absent in every intervention run, and
present in every placebo run (an unread variable set instead). REPAIRED when the intervention
runs exit 0. REFUTED when the symptom survives the intervention. After a verified cause the
next symptom (if the gate still fails) is abduced again with the intervention kept, up to
ROUNDS rounds, so a joint repair is assembled one tested cause at a time.

Usage: gates.py GATES.json OUT.jsonl [--only NAME]
Each gate: {"name", "cwd", "cmd": [...], "script", "env": {}, "inject": optional, "planted": optional,
            "false": [optional planted false causes]}.
Environment: MONO (root that cwd is relative to), CACHE (clones), LEAN_BIN (dir with lean, lake).
"""
import json, os, re, shutil, subprocess, sys, time
from engine import Log, ATMS, closure, front, sha

MONO = os.environ.get("MONO", ".")
CACHE = os.environ.get("CACHE", "/tmp/abduction-cache")
SEARCH = [p for p in os.environ.get("SEARCH", "/mnt/project-files:/home/user").split(":") if p]
REPEATS = int(os.environ.get("REPEATS", "2"))
ROUNDS = int(os.environ.get("ROUNDS", "4"))
PREREQ = os.environ.get("PREREQ", "1") == "1"
FLAKY_N = int(os.environ.get("FLAKY_N", "12"))  # runs per arm when the controls disagree
ALPHA = 0.05


def fisher_greater(a, n1, b, n2):
    """One-sided Fisher exact p: P(at least a of the n1+n2 runs' a+b failures fall in arm 1)."""
    from math import comb
    k, n = a + b, n1 + n2
    return sum(comb(n1, i) * comb(n2, k - i) for i in range(a, min(n1, k) + 1) if 0 <= k - i <= n2) / comb(n, k)


def decide(target, ctrl, ivr, pl):
    """Verdict from run records. Deterministic gates: target in every control and placebo run, in no
    intervention run. When the controls disagree (a flaky gate): the intervention must show the
    target in no run, and the control and placebo failure counts must each exceed the intervention's
    by a one-sided Fisher exact test at ALPHA."""
    hit = lambda r: all(t in r["symptoms"] for t in target)
    gone = all(not any(t in r["symptoms"] for t in target) for r in ivr) and len(ivr) >= 2
    if all(hit(r) for r in ctrl) and len(ctrl) >= 2:
        if gone and all(hit(r) for r in pl) and len(pl) >= 2:
            return ("REPAIRED" if all(r["rc"] == 0 for r in ivr) else "VERIFIED"), None
        return ("REFUTED" if not gone else "INCONCLUSIVE"), None
    c, i_, q = sum(map(hit, ctrl)), sum(map(hit, ivr)), sum(map(hit, pl))
    stat = {"control": [c, len(ctrl)], "intervention": [i_, len(ivr)], "placebo": [q, len(pl)],
            "p_control": fisher_greater(c, len(ctrl), i_, len(ivr)), "p_placebo": fisher_greater(q, len(pl), i_, len(ivr))}
    if c == 0:
        return "INCONCLUSIVE", stat
    if i_ == 0 and stat["p_control"] < ALPHA and stat["p_placebo"] < ALPHA:
        return ("REPAIRED" if all(r["rc"] == 0 for r in ivr) else "VERIFIED"), stat
    return ("REFUTED" if i_ >= c * len(ivr) / len(ctrl) else "INCONCLUSIVE"), stat
TIMEOUT = int(os.environ.get("GATE_TIMEOUT", "1800"))
LOGS = {}  # log sha -> full text, for this process

# ------------------------------------------------------------------ running

def git_reset(cwd):
    top = subprocess.run(["git", "-C", cwd, "rev-parse", "--show-toplevel"], capture_output=True, text=True).stdout.strip()
    if top:
        subprocess.run(["git", "-C", top, "checkout", "-q", "--", os.path.relpath(cwd, top)], capture_output=True)
        subprocess.run(["git", "-C", top, "clean", "-qffdx", "--", os.path.relpath(cwd, top)], capture_output=True)


def run(g, iv=None, tag=""):
    """One gate run under intervention iv: {"env": {}, "args": [], "files": [(src, dst)], "git": [(url, to)], "unset_path": [tool]}."""
    iv = iv or {}
    cwd = os.path.join(MONO, g["cwd"])
    env = dict(os.environ)
    env.update({k_: (os.environ[v[1:]] if isinstance(v, str) and v.startswith("@") else v) for k_, v in g.get("env", {}).items()})
    for k_ in g.get("inject", {}).get("unset_env", []):
        env.pop(k_, None)
    if g.get("inject", {}).get("path_without"):
        bad = g["inject"]["path_without"]
        env["PATH"] = ":".join(d for d in env["PATH"].split(":") if not os.path.exists(os.path.join(d, bad)))
    env.update(iv.get("env", {}))
    if iv.get("git"):
        env["GIT_CONFIG_COUNT"] = str(len(iv["git"]))
        for i, (url, to) in enumerate(iv["git"]):
            env[f"GIT_CONFIG_KEY_{i}"] = f"url.{to}.insteadOf"; env[f"GIT_CONFIG_VALUE_{i}"] = url
    if g.get("inject", {}).get("git"):
        n = int(env.get("GIT_CONFIG_COUNT", "0"))
        for j, (url, to) in enumerate(g["inject"]["git"]):
            env[f"GIT_CONFIG_KEY_{n + j}"] = f"url.{to}.insteadOf"; env[f"GIT_CONFIG_VALUE_{n + j}"] = url
        env["GIT_CONFIG_COUNT"] = str(n + len(g["inject"]["git"]))
    placed = []
    for f in g.get("inject", {}).get("remove", []):
        p = os.path.join(cwd, f)
        if os.path.exists(p):
            os.remove(p)
    made = []
    for src, dst in iv.get("files", []):
        dst = dst.replace("$MONO", MONO)
        d = dst if os.path.isabs(dst) else os.path.join(cwd, dst)
        p_ = os.path.dirname(d)
        while not os.path.exists(p_):
            made.append(p_); p_ = os.path.dirname(p_)
        os.makedirs(os.path.dirname(d), exist_ok=True)
        if not os.path.exists(d):
            if src is None:
                open(d, "w").close()
            elif isinstance(src, tuple):  # (git commit, path in repo): restore from history
                blob = subprocess.run(["git", "-C", MONO, "show", f"{src[0]}:{src[1]}"], capture_output=True).stdout
                open(d, "wb").write(blob)
            elif os.path.isdir(src):
                shutil.copytree(src, d)
            else:
                shutil.copy(src, d)
            placed.append(d)
    pre_out = []
    for a in iv.get("pre", []):  # prerequisite actions, run before the gate on the same fresh tree
        try:
            pp = subprocess.run(a["cmd"], cwd=os.path.join(MONO, a["cwd"]), env=env, capture_output=True, text=True, timeout=TIMEOUT)
            prc, pout = pp.returncode, pp.stdout + pp.stderr
        except subprocess.TimeoutExpired:
            prc, pout = 124, "TIMEOUT"
        pout = f"$ (cd {a['cwd']} && {' '.join(a['cmd'])})\n" + pout.replace(MONO, "$MONO")
        if os.environ.get("RUNLOGS"):
            os.makedirs(os.environ["RUNLOGS"], exist_ok=True)
            open(os.path.join(os.environ["RUNLOGS"], sha(pout) + ".log"), "w").write(pout)
        pre_out.append({"rc": prc, "log_sha256": sha(pout)})
    cmd = list(iv.get("cmd") or g["cmd"]) + list(iv.get("args", []))
    t = time.time()
    try:
        p = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True, timeout=TIMEOUT)
        rc, out = p.returncode, p.stdout + p.stderr
    except subprocess.TimeoutExpired as e:
        rc, out = 124, ((e.stdout or b"").decode(errors="replace") if isinstance(e.stdout, bytes) else (e.stdout or "")) + "\nTIMEOUT"
    secs = round(time.time() - t, 2)
    # what the gate wrote to files it tracks or creates is part of the observation
    st_ = subprocess.run(["git", "-C", cwd, "status", "--porcelain", "--untracked-files=all", "--", "."], capture_output=True, text=True).stdout
    top = subprocess.run(["git", "-C", cwd, "rev-parse", "--show-toplevel"], capture_output=True, text=True).stdout.strip()
    for line in sorted(st_.splitlines()):
        f = os.path.join(top, line[3:].strip())
        if os.path.isfile(f) and os.path.getsize(f) < 200000 and f not in placed and not f.endswith((".olean", ".ilean", ".c")):
            try:
                out += f"\n==> {os.path.relpath(f, cwd)} <==\n" + open(f).read()
            except UnicodeDecodeError:
                pass
    for d in placed:
        if os.path.isdir(d):
            shutil.rmtree(d, ignore_errors=True)
        elif os.path.exists(d):
            os.remove(d)
    for p_ in made:
        try:
            os.removedirs(p_)
        except OSError:
            pass
    if not g.get("keep_tree"):
        git_reset(os.path.join(MONO, *g["cwd"].split("/")[:2]))  # the whole thesis, not just the gate's folder
    out = out.replace(MONO, "$MONO")
    if os.environ.get("RUNLOGS"):
        os.makedirs(os.environ["RUNLOGS"], exist_ok=True)
        open(os.path.join(os.environ["RUNLOGS"], sha(out) + ".log"), "w").write(out)
    LOGS[sha(out)] = out
    r = {"rc": rc, "secs": secs, "log_sha256": sha(out), "tail": out[-1500:], "symptoms": symptoms(out, rc, g), "tag": tag}
    if pre_out:
        r["pre"] = pre_out
    return r

# ------------------------------------------------------------------ symptoms

RX = [
    ("unset", re.compile(r"^\S+: (?:line )?\d+: ([A-Za-z_]\w*): (.+)$", re.M)),
    ("nofile", re.compile(r"No such file or directory: '([^']+)'")),
    ("nofile", re.compile(r"^[\w.-]+: (/?[^:\s]+): No such file or directory", re.M)),
    ("nofile", re.compile(r"required fixture is missing: (\S+)")),
    ("nofile", re.compile(r"cannot open ([^:\s]+): No such file")),
    ("nofile", re.compile(r"can't open file '([^']+)': \[Errno 2\]")),
    ("notfound", re.compile(r"^\S+: (?:line )?\d+: ([\w./+-]+): (?:command )?not found", re.M)),
    ("notfound", re.compile(r"^\S+: ([\w./+-]+): not found$", re.M)),
    ("fetch", re.compile(r"cloning (https://\S+)")),
    ("emptycmd", re.compile(r"^\S+: (?:line )?(\d+): : (?:Permission denied|not found|command not found)", re.M)),
]


def symptoms(out, rc, g):
    S = set()
    if rc != 0:
        S.add("fails")
    for kind, rx in RX:
        for m in rx.finditer(out):
            if kind == "fetch":
                rest = out[m.end():]
                nxt = re.search(r"checking out revision '([0-9a-f]+)'|exited with code 128", rest)
                if nxt and nxt.group(0).startswith("exited"):
                    S.add(f"fetch:{m.group(1).removesuffix('.git').rstrip('/')}")
                elif nxt and re.search(r"exited with code 128", rest[nxt.end():]):
                    S.add(f"revision_missing:{nxt.group(1)}")
            elif kind == "emptycmd":
                S.add("emptycmd")
            elif kind == "unset":
                if m.group(1) not in ("error", "warning", "info") and not re.match(r"(command )?not found|Permission denied", m.group(2)):
                    S.add(f"unset:{m.group(1)}")
            else:
                S.add(f"{kind}:{m.group(1)}")
    m = re.search(r"IndexError: list index out of range", out)
    if m:
        a = re.findall(r"sys\.argv\[(\d+)\]", out)
        S.add(f"argv:{a[-1] if a else '?'}")
    if rc != 0 and len(S) == 1:
        lines = [l for l in out.strip().splitlines() if l.strip()]
        if lines:
            S.add(f"silent:{lines[-1].strip()[:80]}")
    return sorted(S)

# ------------------------------------------------------------------ static reads

def static(g):
    path = os.path.join(MONO, g["cwd"], g["script"])
    src = open(path, errors="replace").read()
    st = {"required": {}, "positional": {}, "argv": [], "tools": [], "steps": {}, "usage": "", "argv_base": None, "as_command": []}
    for m in re.finditer(r"\$\{([A-Za-z_]\w*):\?([^}]*)\}", src):
        st["required"][m.group(1)] = m.group(2)
    # var=$N and later "$var/suffix"
    for m in re.finditer(r"(?:^|[\s;])(\w+)=\$\{?(\d)\}?", src):
        var, n = m.group(1), m.group(2)
        for m2 in re.finditer(r'\$\{?' + var + r'\}?(/[\w./-]+)', src):
            st["positional"].setdefault(n, []).append(m2.group(1))
        st["positional"].setdefault(n, [])
        if re.search(r'^\s*"\$\{?' + var + r'\}?"\s', src, re.M):
            st["as_command"].append(n)
    u = re.search(r"#\s*usage:\s*(.*)", src, re.I)
    if u:
        st["usage"] = u.group(1)
    for m in re.finditer(r"sys\.argv\[(\d+)\]", src):
        st["argv"].append(m.group(1))
    b = re.search(r"os\.path\.join\((\w+),\s*sys\.argv\[1\]\)", src)
    if b:
        mb = re.search(b.group(1) + r'\s*=\s*os\.path\.join\(os\.path\.dirname\(os\.path\.abspath\(__file__\)\),\s*"([^"]+)"\)', src)
        if mb:
            st["argv_base"] = os.path.join(os.path.dirname(path), mb.group(1))
    tools = set()
    for line in src.splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        w = re.match(r'(?:"\$[\w{}]+"|\$\{?\w+\}?|[\w.+-]+)', line)
        if w and w.group(0) in ("lean", "lake", "git", "python3", "cc", "gcc", "sha256sum", "curl", "zig", "idol"):
            tools.add(w.group(0))
    st["tools"] = sorted(tools)
    lines = src.splitlines()
    for i, line in enumerate(lines):
        m = re.match(r'\s*echo\s+"([^"$]+)"\s*$', line)
        if m:
            for nxt in lines[i + 1:]:
                if nxt.strip() and not nxt.strip().startswith("#"):
                    st["steps"][m.group(1)] = re.sub(r'\s*>.*$', '', nxt.strip())
                    break
    return st

# ------------------------------------------------------------------ theory

def theory(g, obs, st, pre=()):
    """Canonical log for this gate: causes -> predicted symptoms; absent predictions -> bot."""
    lg = Log()
    causes = {}  # name -> (cost, predicted symptoms, intervention spec)

    def cause(name, cost, preds, spec):
        causes[name] = (cost, sorted(set(preds)), spec)

    for a, pr, hit in pre:  # prerequisite actions read from the tree; they predict what they create
        cause(f"pre:{a['name']}", a["cost"], ["fails"] + [f"mentions:{h}" for h in hit], {"kind": "pre", "act": a})

    for v, msg in st["required"].items():
        cause(f"env_unset:{v}", 1, [f"unset:{v}"], {"kind": "env", "var": v, "msg": msg})
    for n, sufs in st["positional"].items():
        preds = [f"nofile:{s}" for s in sufs] + (["emptycmd"] if n in st["as_command"] else [])
        cause(f"arg_missing:{n}", 1, preds or [f"argmissing:{n}"], {"kind": "posarg", "n": int(n)})
    for n in set(st["argv"]):
        cause(f"argv_missing:{n}", 1, [f"argv:{n}"], {"kind": "argv", "n": int(n)})
    for t in st["tools"]:
        cause(f"tool_missing:{t}", 1, [f"notfound:{t}"], {"kind": "tool", "tool": t})
    for s in obs:
        k, _, v = s.partition(":")
        if k == "nofile":
            cause(f"file_absent:{v}", 1, [s], {"kind": "file", "path": v})
        elif k == "fetch":
            cause(f"fetch_denied:{v}", 1, [s], {"kind": "fetch", "url": v})
        elif k == "notfound":
            cause(f"tool_missing:{v}", 1, [s], {"kind": "tool", "tool": v})
        elif k == "silent":
            if v in st["steps"]:
                cause(f"step_fails:{v}", 2, [s], {"kind": "step", "marker": v, "cmd": st["steps"][v]})
    for f in g.get("false", []):  # planted false causes (controls), each with its prediction
        cause(f["name"], 1, f["predicts"], f["spec"])
    A = []
    for name, (cost, preds, spec) in sorted(causes.items()):
        A.append(lg.atom(name))
        for p in preds:
            lg.add([name], p, kind="predicts")
        lg.add([name], "fails", kind="predicts")
    observed = set(obs)
    for name, (cost, preds, spec) in sorted(causes.items()):
        for p in preds:
            if p not in observed:
                lg.add([p], "⊥", kind="absent")
    O = [lg.atom(s) for s in obs if s != "fails"]
    return lg, A, O, causes

# ------------------------------------------------------------------ resolvers (where would the missing thing come from)

def clone_at(repo, rev=None):
    os.makedirs(CACHE, exist_ok=True)
    d = os.path.join(CACHE, repo.replace("/", "_") + ("@" + rev if rev else ""))
    if not os.path.exists(d):
        local = f"/home/user/{repo.split('/')[1]}"
        src = local if os.path.isdir(os.path.join(local, ".git")) else f"https://github.com/{repo}"
        subprocess.run(["git", "clone", "-q", src, d], check=True, capture_output=True)
        if rev:
            subprocess.run(["git", "-C", d, "checkout", "-q", rev], check=True, capture_output=True)
    return d


_found = {}


def find_named(name, want_dir=None):
    key = (name, want_dir)
    if key not in _found:
        _found[key] = _find_named(name, want_dir)
    return _found[key]


def history(path, cwd=MONO):
    """A commit (on any ref of the MONO repo) whose tree holds this path."""
    full = path.replace("$MONO", MONO)
    rel = os.path.relpath(full if os.path.isabs(full) else os.path.join(cwd, full), MONO)
    if rel.startswith(".."):
        return None
    h = subprocess.run(["git", "-C", MONO, "log", "--all", "-1", "--format=%H", "--", rel], capture_output=True, text=True).stdout.strip()
    if h and subprocess.run(["git", "-C", MONO, "cat-file", "-e", f"{h}:{rel}"], capture_output=True).returncode == 0:
        return (h, rel)
    if h:  # the commit that deleted it: take its parent
        h2 = subprocess.run(["git", "-C", MONO, "rev-parse", f"{h}^"], capture_output=True, text=True).stdout.strip()
        if h2 and subprocess.run(["git", "-C", MONO, "cat-file", "-e", f"{h2}:{rel}"], capture_output=True).returncode == 0:
            return (h2, rel)
    return None


def _find_named(name, want_dir=None):
    hits = []
    for root in SEARCH:
        for dp, dns, fns in os.walk(root):
            dns[:] = [x for x in dns if not x.startswith(".") and x not in ("node_modules", "__pycache__")]
            for x in (dns if want_dir else fns) if want_dir is not None else dns + fns:
                if x == name:
                    hits.append(os.path.join(dp, x))
            if len(hits) > 5:
                return hits
    return hits


def resolve_text(msg):
    """Value candidates for something described in words."""
    out = []
    for m in re.finditer(r"(\w[\w.-]*) binary", msg):  # an executable named by the word before "binary"
        for h in find_named(m.group(1), want_dir=False):
            if open(h, "rb").read(4) == b"\x7fELF":
                os.makedirs(CACHE, exist_ok=True)
                d = os.path.join(CACHE, "bin-" + m.group(1))
                if not os.path.exists(d):
                    shutil.copy(h, d); os.chmod(d, 0o755)
                out.append(d)
                break
    for m in re.finditer(r"clpi/([\w.-]+)(?:\s+at\s+([0-9a-f]{7,40}))?", msg):
        try:
            out.append(clone_at("clpi/" + m.group(1), m.group(2)))
        except subprocess.CalledProcessError:
            pass
    for tok in re.findall(r"[\w][\w.-]{4,}", msg):
        if tok.startswith("clpi") or tok in ("checkout", "directory", "receipts", "binary"):
            continue
        for h in find_named(tok, want_dir=True)[:1]:
            out.append(h)
    return out


def interventions(spec, g, st):
    """Candidate interventions removing a cause (most specific first)."""
    k = spec["kind"]
    if k == "env":
        return [{"env": {spec["var"]: v}, "why": f"{spec['var']}={v}"} for v in resolve_text(spec["msg"])[:2]]
    if k == "posarg":
        parts = re.findall(r"<([^>]+)>", st.get("usage", ""))
        args = []
        for i, ph in enumerate(parts, start=1):
            vals = resolve_text(ph) if i == spec["n"] or True else []
            args.append(vals[0] if vals else "")
        if not parts:
            args = [""] * (spec["n"] - 1) + ["."]
        return [{"args": args, "why": f"positional {args}"}]
    if k == "argv":
        base = st.get("argv_base")
        if base and os.path.isdir(base):
            return [{"args": [x], "why": f"argv[{spec['n']}]={x}"} for x in sorted(os.listdir(base))[:4]]
        return [{"args": ["."], "why": "argv placeholder"}]
    if k == "file":
        p = spec["path"]
        ivs = []
        hz = history(p, os.path.join(MONO, g["cwd"]))
        if hz:
            ivs.append({"files": [(hz, p)], "why": f"restore from history {hz[0][:12]}:{hz[1]}"})
        hits = [h for h in find_named(os.path.basename(p)) if os.path.realpath(h) != os.path.realpath(p.replace("$MONO", MONO))]
        ivs += [{"files": [(h, p)], "why": f"copy {h}"} for h in hits[:2]]
        ivs.append({"files": [(None, p)], "why": "empty placeholder (tests the fail point only)"})
        return ivs
    if k == "fetch":
        name = spec["url"].rstrip("/").split("/")[-1].replace("software-", "")
        mirror = os.path.join(MONO, "theses", name)
        if os.path.isdir(mirror):
            bare = os.path.join(CACHE, f"mirror-{name}")
            if not os.path.exists(bare):
                subprocess.run(["git", "init", "-q", bare], check=True)
                shutil.copytree(mirror, bare, dirs_exist_ok=True, symlinks=True)
                subprocess.run(["git", "-C", bare, "add", "-A"], check=True)
                subprocess.run(["git", "-C", bare, "-c", "user.email=a@b", "-c", "user.name=abduction", "commit", "-qm", "mirror"], check=True)
            return [{"git": [(spec["url"], "file://" + bare), (spec["url"] + ".git", "file://" + bare)],
                     "why": "rewrite URL to a local mirror of the same content (pinned commit absent)"}]
        return []
    if k == "tool":
        w = shutil.which(spec["tool"])
        return [{"env": {"PATH": os.path.dirname(w) + ":" + os.environ["PATH"]}, "why": f"put {spec['tool']} on PATH"}] if w else []
    if k == "step":
        return [{"cmd": ["sh", "-c", spec["cmd"]], "why": f"run the hidden step visibly: {spec['cmd']}", "acquire": True}]
    if k == "placebo":
        return [{"env": spec.get("env", {}), "why": "planted false cause"}]
    if k == "pre":
        a = spec["act"]
        return [{"pre": [{"cwd": a["cwd"], "cmd": a["cmd"]}], "why": f"run {a['name']} first (from {a['src']})"}]
    if k == "restore":
        return [{"files": spec["files"], "why": f"restore only {', '.join(spec['units'])} from the {spec['act']} snapshot"}]
    return []

# ------------------------------------------------------------------ prerequisite abduction (no symptom vocabulary)
#
# A gate that fails on a fresh tree may need state that some other action produces: a build of
# its package, a dependency checkout, or its own earlier run (then the gate is not idempotent
# from a clean checkout). Candidate actions are read from the tree, never from the failure text:
#   self       the gate itself (cost 1)
#   build:DIR  the build system of each package that builds the gate's folder: markers in the
#              gate's folder (depth <= 3) and in its ancestors up to the thesis root (cost 2)
#   doc:CMD    shell lines in fenced sh/bash blocks of the gate folder's README (cost 3)
# Each action is probed once on a fresh tree: what it creates (untracked or ignored paths) is
# snapshotted. The names it creates that the failing log mentions become observations
# `mentions:NAME`, and `pre:ACTION -> mentions:NAME` records, so an action whose products the
# failure talks about covers more and ranks first. The test is symptom free: target "fails",
# intervention = run ACTION first, placebo = run `true` first. A verified action is narrowed by
# delta debugging over the snapshot to a 1-minimal set of created paths that, restored alone,
# makes the gate pass; that set is verified again the same way.

BUILD = [("lakefile.lean", ["lake", "build"]), ("lakefile.toml", ["lake", "build"]), ("Makefile", ["make"]),
         ("build.zig", ["zig", "build"]), ("Cargo.toml", ["cargo", "build", "--offline"])]
SKIPDIR = {".git", ".lake", "node_modules", "__pycache__", "target", "zig-out", ".zig-cache", "zig-cache"}
GENERIC = {"build", "packages", "lib", "lean", "ir", "lake", "cache", "target", "debug", "release", "olean",
           "ilean", "trace", "hash", "c", "o", "json", "README", "LICENSE", "manifest", "config", "objects"}
PROBES = {}


def thesis_root(g):
    return os.path.join(MONO, *g["cwd"].split("/")[:2])


def harvest(g):
    root, cwd = thesis_root(g), os.path.join(MONO, g["cwd"])
    acts = [{"name": "self", "cwd": g["cwd"], "cmd": list(g["cmd"]), "cost": 1, "src": "the gate itself"}]
    dirs = []
    d = cwd
    while True:  # ancestors up to the thesis root
        dirs.append(d)
        if os.path.realpath(d) == os.path.realpath(root) or len(d) <= len(root):
            break
        d = os.path.dirname(d)
    for dp, dns, fns in os.walk(cwd):  # the gate's own subtree
        dns[:] = sorted(x for x in dns if x not in SKIPDIR and not x.startswith("."))
        if dp.count(os.sep) - cwd.count(os.sep) >= 3:
            dns[:] = []
        if dp != cwd:
            dirs.append(dp)
    seen = set()
    for d in dirs:
        for marker, cmd in BUILD:
            if os.path.isfile(os.path.join(d, marker)) and shutil.which(cmd[0]) and d not in seen:
                seen.add(d)
                rel = os.path.relpath(d, MONO)
                acts.append({"name": f"build:{os.path.relpath(d, cwd)}", "cwd": rel, "cmd": cmd, "cost": 2, "src": marker})
    rd = os.path.join(cwd, "README.md")
    if os.path.isfile(rd):
        fence = False
        for line in open(rd, errors="replace"):
            t = line.strip()
            if t.startswith("```"):
                fence = t[3:].strip() in ("sh", "bash", "shell", "console")
                continue
            t = t.removeprefix("$ ").strip()
            if fence and t and not t.startswith("#") and t != " ".join(g["cmd"]) and "${{" not in t:
                acts.append({"name": f"doc:{t}", "cwd": g["cwd"], "cmd": ["sh", "-c", t], "cost": 3, "src": "README.md"})
    return acts


def created(root):
    """Untracked and ignored paths under root (git collapses whole new directories)."""
    out = subprocess.run(["git", "-C", root, "status", "--porcelain", "--ignored", "--untracked-files=normal", "--", "."],
                         capture_output=True, text=True).stdout
    top = subprocess.run(["git", "-C", root, "rev-parse", "--show-toplevel"], capture_output=True, text=True).stdout.strip()
    paths = []
    for line in out.splitlines():
        if line[:2] in ("??", "!!"):
            paths.append(os.path.relpath(os.path.join(top, line[3:].strip().rstrip("/")), root))
    return sorted(paths)


def units_of(snap, paths, limit=24):
    """Split created paths into at most `limit` units, expanding directories breadth first."""
    units = list(paths)
    changed = True
    while changed:
        changed = False
        for u in sorted(units, key=lambda x: x.count("/")):
            full = os.path.join(snap, u)
            if os.path.isdir(full) and not os.path.islink(full):
                kids = sorted(os.listdir(full))
                if kids and len(units) - 1 + len(kids) <= limit:
                    units.remove(u)
                    units += [os.path.join(u, k) for k in kids]
                    changed = True
                    break
    return sorted(units)


def names_in(snap, paths, cap=20000):
    out, n = set(), 0
    for p in paths:
        for dp, dns, fns in os.walk(os.path.join(snap, p)):
            for x in dns + fns:
                n += 1
                for v in {x, x.split(".")[0]}:
                    if len(v) >= 5 and v not in GENERIC and not v.startswith("."):
                        out.add(v)
            if n > cap:
                break
        for c in p.split("/"):
            for v in {c, c.split(".")[0]}:
                if len(v) >= 5 and v not in GENERIC and not v.startswith("."):
                    out.add(v)
    return out


def probe(g, a, keep):
    """Run action a once on a fresh tree; snapshot what it creates."""
    root = thesis_root(g)
    key = (root, a["cwd"], tuple(a["cmd"]), json.dumps(keep.get("env", {}), sort_keys=True))
    if key in PROBES:
        return PROBES[key]
    git_reset(root)
    env = dict(os.environ); env.update(keep.get("env", {}))
    try:
        p = subprocess.run(a["cmd"], cwd=os.path.join(MONO, a["cwd"]), env=env, capture_output=True, text=True, timeout=TIMEOUT)
        rc = p.returncode
    except subprocess.TimeoutExpired:
        rc = 124
    paths = created(root)
    snap = os.path.join(CACHE, "snap-" + sha(json.dumps(key))[:16])
    shutil.rmtree(snap, ignore_errors=True)
    for q in paths:
        src, dst = os.path.join(root, q), os.path.join(snap, q)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        if os.path.isdir(src) and not os.path.islink(src):
            shutil.copytree(src, dst, symlinks=True)
        elif os.path.lexists(src):
            shutil.copy2(src, dst, follow_symlinks=False)
    git_reset(root)
    PROBES[key] = {"rc": rc, "snap": snap, "paths": paths, "names": names_in(snap, paths)}
    return PROBES[key]


def mentions(g, ctrl, keep):
    """For each candidate action: the names it creates that the failing log mentions."""
    text = LOGS.get(ctrl[0]["log_sha256"], ctrl[0]["tail"])
    res = []
    for a in harvest(g):
        pr = probe(g, a, keep)
        hit = sorted(n for n in pr["names"] if re.search(r"(?<![\w-])" + re.escape(n) + r"(?![\w-])", text))[:8]
        res.append((a, pr, hit))
    return res


def ddmin(units, test, cap=40):
    """Zeller's ddmin: a 1-minimal subset of units for which test passes (test(units) must pass)."""
    calls = [0]

    def t(s):
        calls[0] += 1
        return test(s)

    n = 2
    while len(units) >= 2 and calls[0] < cap:
        chunk = max(1, len(units) // n)
        parts = [units[i:i + chunk] for i in range(0, len(units), chunk)]
        done = False
        for p in parts:
            if calls[0] >= cap:
                break
            if t(p):
                units, n, done = p, 2, True
                break
        if not done:
            for p in parts:
                if calls[0] >= cap:
                    break
                rest = [u for u in units if u not in p]
                if rest and t(rest):
                    units, n, done = rest, max(n - 1, 2), True
                    break
        if not done:
            if n >= len(units):
                break
            n = min(len(units), 2 * n)
    if len(units) == 1 and calls[0] < cap and t([]):
        units = []
    return units, calls[0], calls[0] < cap


def narrow(g, a, keep, flaky=False, cap=80):
    """Smallest set of paths created by a that, restored alone on a fresh tree, makes the gate pass.
    Hierarchical: after ddmin over the top units, each chosen directory is opened and narrowed
    again with the rest held fixed, while the run budget lasts. On a flaky gate a set passes only
    if every one of 3 runs passes."""
    pr = probe(g, a, keep)
    root = thesis_root(g)
    units = units_of(pr["snap"], pr["paths"])
    log = []

    def test(s):
        for _ in range(3 if flaky else 1):
            iv = merge(keep, {"files": [(os.path.join(pr["snap"], u), os.path.join(root, u)) for u in s]})
            r = run(g, iv, "narrow")
            log.append({"units": sorted(s), "rc": r["rc"], "log_sha256": r["log_sha256"]})
            if r["rc"] != 0:
                return False
        return True

    if not units or not test(units):
        return {"units": units, "minimal": None, "tests": log, "note": "restoring every created path does not repair"}
    m, calls, complete = ddmin(units, test, cap)
    opened = True
    while opened and complete and len(log) < cap:
        opened = False
        for u in sorted(m):
            full = os.path.join(pr["snap"], u)
            kids = sorted(os.listdir(full)) if os.path.isdir(full) and not os.path.islink(full) else []
            if 1 < len(kids) <= 24:
                rest = [v for v in m if v != u]
                sub, c2, complete = ddmin([os.path.join(u, k) for k in kids], lambda s_: test(rest + s_), cap - len(log))
                if complete and sub:
                    m, opened = sorted(rest + sub), True
                    break
    return {"units": units, "minimal": sorted(m), "tests": log, "complete": complete}

# ------------------------------------------------------------------ the loop

def runs(g, iv, n, tag):
    return [run(g, iv, tag) for _ in range(n)]


def abduce_round(g, ctrl, st, keep=None):
    pre = mentions(g, ctrl, keep or {}) if PREREQ else []
    obs = sorted(set(ctrl[0]["symptoms"]) | {f"mentions:{h}" for _, _, hit in pre for h in hit})
    lg, A, O, causes = theory(g, obs, st, pre)
    at = ATMS(A, 2)
    for r in lg.recs:
        at.add(r)
    ex = at.explanations(O) if O else []
    cands = []
    for e in ex:
        S = closure(lg.recs, e)
        cov = sum(1 for o in O if o in S)
        cands.append((tuple(sorted(lg.names[x] for x in e)), cov, sum(causes[lg.names[x]][0] for x in e)))
    # also every single consistent cause that explains at least one observation (partial hypotheses)
    for a in A:
        S = closure(lg.recs, [a])
        if 0 in S:
            continue
        cov = sum(1 for o in O if o in S)
        if cov:
            cands.append(((lg.names[a],), cov, causes[lg.names[a]][0]))
    cands = sorted(set(cands), key=lambda c: (-c[1], c[2], c[0]))
    fr = front(cands)
    inconsistent = sorted(lg.names[a] for a in A if 0 in closure(lg.recs, [a]))
    return {"observed": obs, "abducibles": [lg.names[a] for a in A], "inconsistent": inconsistent,
            "probes": [{"action": a["name"], "cwd": a["cwd"], "cmd": a["cmd"], "rc": pr["rc"], "created": pr["paths"], "mentioned": hit} for a, pr, hit in pre],
            "explanations": [list(c[0]) for c in cands if c[1] == len(O)], "front": [list(c[0]) for c in fr],
            "ranked": [{"hyp": list(c[0]), "cover": c[1], "cost": c[2]} for c in cands],
            "log_head": lg.head_hash(), "records": len(lg.recs)}, causes


def experiment(g, cname, spec, st, ctrl, keep):
    if spec["kind"] in ("pre", "restore"):  # symptom free: the gate's own exit status
        target = ["fails"]
    else:
        target = [p for p in theory(g, ctrl[0]["symptoms"], st)[3][cname][1] if p in ctrl[0]["symptoms"] and p != "fails"]
    if not target:  # the cause predicts nothing observed: test it against what was observed
        target = [p for p in ctrl[0]["symptoms"] if p != "fails"] or ["fails"]
    trials = []
    n = max(REPEATS, len(ctrl))
    for iv in interventions(spec, g, st):
        merged = merge(keep, iv)
        ivr = runs(g, merged, n, "intervention")
        placebo = {"env": {"ABDUCTION_PLACEBO": "1"}}
        if spec["kind"] == "pre":  # same slot, no effect
            placebo["pre"] = [{"cwd": spec["act"]["cwd"], "cmd": ["true"]}]
        pl = runs(g, merge(keep, placebo), n, "placebo")
        verdict, stat = ("ACQUIRED", None) if iv.get("acquire") else decide(target, ctrl, ivr, pl)
        extra = []
        hit = lambda r: all(t in r["symptoms"] for t in target)
        if verdict == "INCONCLUSIVE" and stat is None and 0 < sum(map(hit, pl)) < len(pl):
            # the placebo arm shows the gate is flaky after all: measure every arm at FLAKY_N
            extra = runs(g, keep, FLAKY_N - len(ctrl), "control")
            ivr += runs(g, merged, FLAKY_N - len(ivr), "intervention")
            pl += runs(g, merge(keep, placebo), FLAKY_N - len(pl), "placebo")
            verdict, stat = decide(target, ctrl + extra, ivr, pl)
        trials.append({"why": iv["why"], "verdict": verdict, "target": target, "intervention": ivr, "placebo": pl, "iv": iv, "stat": stat,
                       **({"control_extra": extra} if extra else {})})
        if verdict in ("REPAIRED", "VERIFIED", "ACQUIRED") and not iv.get("why", "").startswith("empty placeholder"):
            break
    return trials


def merge(a, b):
    out = {k: (dict(v) if isinstance(v, dict) else list(v)) for k, v in (a or {}).items() if k not in ("why", "acquire")}
    for k, v in (b or {}).items():
        if k in ("why", "acquire"):
            out[k] = v
        elif isinstance(v, dict):
            out.setdefault(k, {}).update(v)
        elif k == "args":
            out[k] = list(v)
        elif isinstance(v, list):
            out.setdefault(k, []).extend(v)
        else:
            out[k] = v
    return out


def gate(g):
    st = static(g)
    keep, rounds, status = {}, [], "FAILING"
    for rnd in range(ROUNDS):
        ctrl = runs(g, keep, REPEATS, "control")
        if len({r["rc"] == 0 for r in ctrl}) > 1:  # the gate is flaky from a fresh tree: measure its rate
            ctrl += runs(g, keep, FLAKY_N - len(ctrl), "control")
        if all(r["rc"] == 0 for r in ctrl):
            status = "PASSING" if rnd == 0 else "REPAIRED"
            rounds.append({"round": rnd, "control": ctrl})
            break
        reproducible = len({tuple(r["symptoms"]) for r in ctrl}) == 1 and len({r["rc"] for r in ctrl}) == 1
        ab, causes = abduce_round(g, ctrl, st, keep)
        tested, verified = [], None
        order = [h[0] for h in ab["front"] if len(h) == 1 and not h[0].startswith("pre:")] + [c for c in ab["abducibles"] if c in {f["name"] for f in g.get("false", [])}]
        prs = sorted((c for c in causes if c.startswith("pre:")), key=lambda c: (-len(causes[c][1]), causes[c][0], c))
        exhaustive = bool(g.get("planted") or g.get("false") or g.get("exhaustive"))
        for cname in dict.fromkeys(order + prs):
            if verified is not None and cname.startswith("pre:") and not exhaustive:
                break
            trials = experiment(g, cname, causes[cname][2], st, ctrl, keep)
            tested.append({"cause": cname, "trials": trials})
            good = [t for t in trials if t["verdict"] in ("REPAIRED", "VERIFIED", "ACQUIRED") and not t["why"].startswith("empty placeholder")]
            if good and verified is None:
                verified = (cname, good[0])
        rd = {"round": rnd, "control": ctrl, "reproducible": reproducible, "abduction": ab, "tested": tested}
        rounds.append(rd)
        if verified is None:
            break
        cname, t = verified
        if cname.startswith("pre:"):
            a = causes[cname][2]["act"]
            nar = narrow(g, a, keep, flaky=not reproducible)
            rd["narrowed"] = nar
            if nar.get("minimal"):
                pr = probe(g, a, keep)
                root = thesis_root(g)
                spec = {"kind": "restore", "act": a["name"], "units": nar["minimal"],
                        "files": [(os.path.join(pr["snap"], u), os.path.join(root, u)) for u in nar["minimal"]]}
                rd["artifact"] = {"cause": f"artifact_absent:{','.join(nar['minimal'])}", "produced_by": cname,
                                  "trials": experiment(g, "restore", spec, st, ctrl, keep)}
            if a["name"] == "self":  # not idempotent from a clean tree: where the first run's output diverges
                warm = set(LOGS.get(t["intervention"][0]["log_sha256"], "").splitlines())
                cold = LOGS.get(ctrl[0]["log_sha256"], "").splitlines()
                rd["first_run_only"] = [l for l in cold if l not in warm and l.strip()][:12]
        if t["verdict"] == "ACQUIRED":
            # the hidden step's own output becomes the observation for the next round
            g = dict(g, cmd=t["iv"]["cmd"], script=g["script"])
            continue
        keep = merge(keep, t["iv"])
        if t["verdict"] == "REPAIRED":
            status = "REPAIRED"
            break
    return {"gate": g["name"], "status": status, "static": st, "rounds": rounds,
            "repair": {k: v for k, v in keep.items() if k not in ("why", "acquire")} if status == "REPAIRED" else None}


if __name__ == "__main__":
    gates = json.load(open(sys.argv[1]))
    only = sys.argv[sys.argv.index("--only") + 1] if "--only" in sys.argv else None
    with open(sys.argv[2], "a") as f:
        for g in gates:
            if only and g["name"] != only:
                continue
            t = time.time()
            r = gate(g)
            r["seconds"] = round(time.time() - t, 1)
            f.write(json.dumps(r, sort_keys=True) + "\n"); f.flush()
            last = r["rounds"][-1]
            print(g["name"], r["status"], r["seconds"], [(x["cause"], [t["verdict"] for t in x["trials"]]) for rd in r["rounds"] for x in rd.get("tested", [])], flush=True)
