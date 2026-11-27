#!/usr/bin/env python3
"""Same-contract benchmark: each solver gets the same problem, the same wall-clock limit, one
core, and is run as its own process. Recorded per run: status, wall seconds, peak resident
memory (KiB, from wait4), proof steps where the solver prints a proof, and whether our proofs
pass check.py. A solver's answer counts only if it matches the TPTP status of the problem.

Usage: bench.py LIST ROOT OUT.jsonl LIMIT_SECONDS SOLVER[,SOLVER...] [--jobs N]
Solvers: ours (horn.py), native (native/horn), hyper (native/hyper), vampire, eprover, z3, cvc5. Paths: VAMPIRE, EPROVER env vars (or PATH).
"""
import json
import os
import re
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
REASON = os.path.dirname(HERE)
VAMPIRE = os.environ.get("VAMPIRE", "vampire")
MEMRUN = os.environ.get("MEMRUN", os.path.join(HERE, "memrun"))  # gcc -O2 -o memrun memrun.c
EPROVER = os.environ.get("EPROVER", "eprover")
HORNC = os.environ.get("HORNC", os.path.join(REASON, "native", "horn"))  # gcc -O2 -o horn horn.c
HYPER = os.environ.get("HYPER", os.path.join(REASON, "native", "hyper"))  # gcc -O2 -o hyper hyper.c


def run(cmd, limit, env=None):
    """Wall time and peak resident memory (KiB) of one child process tree, reaped by wait4."""
    import threading
    t0 = time.perf_counter()
    p = subprocess.Popen([MEMRUN] + list(cmd), stdout=subprocess.PIPE, stderr=subprocess.STDOUT, env=env, text=True, start_new_session=True)
    killed = []

    def kill():
        killed.append(1)
        try:
            os.killpg(p.pid, 9)
        except ProcessLookupError:
            pass
    timer = threading.Timer(limit + 2, kill); timer.start()
    out = p.stdout.read()
    _, status, ru = os.wait4(p.pid, 0)
    timer.cancel()
    p.returncode = os.waitstatus_to_exitcode(status)
    wall = time.perf_counter() - t0
    m = re.search(r"@@memrun maxrss_kib=(\d+)", out)
    out = re.sub(r"\n?@@memrun [^\n]*\n?", "\n", out)
    return out, wall, bool(killed), int(m.group(1)) if m else None


def szs(out):
    m = re.search(r"SZS status (\w+)", out)
    return m.group(1) if m else None


def proof_lines(out):
    m = re.search(r"SZS output start[^\n]*\n(.*?)SZS output end", out, re.S)
    if not m:
        return None
    body = m.group(1)
    return (len(re.findall(r"^\s*(?:cnf|fof|tff)\(", body, re.M))
            or len(re.findall(r"^\s*\d+ : ", body, re.M))  # E's default proof object listing
            or len([l for l in body.splitlines() if "<-" in l]))


LOGS = None  # directory: every solver output is kept under its sha256, cited by the record


def keep(rec, out):
    import hashlib
    if LOGS:
        h = hashlib.sha256(out.encode()).hexdigest()
        p = os.path.join(LOGS, h + ".log")
        if not os.path.exists(p):
            open(p, "w").write(out)
        rec["log_sha256"] = h
    return rec


def solve(solver, prob, root, limit):
    path = os.path.join(root, prob)
    env = dict(os.environ, TPTP=root)
    rec = {"solver": solver, "problem": prob, "limit": limit}
    if solver in ("ours", "native", "hyper"):
        pf = tempfile.mktemp(suffix=".json")
        cmd = (["timeout", str(limit), sys.executable, os.path.join(REASON, "horn.py"), path, "--root", root, "--proof-json", pf] if solver == "ours"
               else ["timeout", str(limit), HYPER, path, "--root", root, "--limit", str(limit), "--proof-json", pf] if solver == "hyper"
               else ["timeout", str(limit), HORNC, path, "--root", root, "--proof-json", pf])
        out, wall, to, rss = run(cmd, limit, env)
        st = szs(out)
        m = re.search(r"proof_steps (\d+)", out)
        rec.update(status=st or "Timeout", wall=wall, rss_kib=rss, proof_steps=int(m.group(1)) if m and st == "Unsatisfiable" else None)
        keep(rec, out)
        if st == "Unsatisfiable":
            eng = re.search(r"^% engine (\S+)", out, re.M)
            if eng:
                rec["engine"] = eng.group(1)
            checker = ("check_res.py" if eng and eng.group(1).startswith("ord") else
                       "check_hyp.py" if eng and eng.group(1) == "hyper" else "check.py")
            c = subprocess.run([sys.executable, os.path.join(REASON, checker), path, pf, "--root", root], capture_output=True, text=True)
            # exit 0 = every step checks, 1 = a step is rejected; anything else is the checker failing
            # (for example out of memory on a proof with millions of steps), which is not a verdict
            rec["checked"] = True if c.returncode == 0 else (False if c.returncode == 1 else None)
            if c.returncode not in (0, 1):
                rec["checker_exit"] = c.returncode
        if os.path.exists(pf):
            os.remove(pf)
    elif solver == "vampire":
        out, wall, to, rss = run([VAMPIRE, "--mode", "casc", "-t", str(limit), "--include", root, path], limit, env)
        st = szs(out)
        rec.update(status=st or ("Timeout" if to else "Unknown"), wall=wall, rss_kib=rss, proof_steps=proof_lines(out) if st == "Unsatisfiable" else None)
        keep(rec, out)
    elif solver == "eprover":
        out, wall, to, rss = run([EPROVER, "--auto", "-s", "--proof-object", f"--cpu-limit={limit}", "--tptp3-in", path], limit, env)
        st = szs(out)
        rec.update(status=st or ("Timeout" if to else "Unknown"), wall=wall, rss_kib=rss, proof_steps=proof_lines(out) if st == "Unsatisfiable" else None)
        keep(rec, out)
    elif solver in ("z3", "cvc5"):
        smt = tempfile.mktemp(suffix=".smt2")
        open(smt, "w").write(subprocess.run([sys.executable, os.path.join(HERE, "tosmt.py"), path, root], capture_output=True, text=True, check=True).stdout)
        cmd = ["z3", f"-T:{limit}", smt] if solver == "z3" else ["timeout", str(limit), sys.executable, os.path.join(HERE, "cvc5run.py"), smt, str(limit)]
        out, wall, to, rss = run(cmd, limit, env)
        w = out.strip().splitlines()
        st = {"unsat": "Unsatisfiable", "sat": "Satisfiable"}.get(w[0].strip() if w else "", None)
        rec.update(status=st or ("Timeout" if to or "timeout" in out else "Unknown"), wall=wall, rss_kib=rss, proof_steps=None)
        keep(rec, out)
        os.remove(smt)
    return rec


if __name__ == "__main__":
    lst, root, outp, limit, solvers = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), sys.argv[5].split(",")
    jobs = int(sys.argv[sys.argv.index("--jobs") + 1]) if "--jobs" in sys.argv else 2
    if "--logs" in sys.argv:
        LOGS = sys.argv[sys.argv.index("--logs") + 1]
        os.makedirs(LOGS, exist_ok=True)
    probs = open(lst).read().split()
    done = set()
    if os.path.exists(outp):  # resume: (solver, problem) pairs already recorded are not rerun
        for line in open(outp):
            r = json.loads(line); done.add((r["solver"], r["problem"]))
    tasks = [(s, p) for p in probs for s in solvers if (s, p) not in done]
    with open(outp, "a") as f, ThreadPoolExecutor(jobs) as ex:
        for rec in ex.map(lambda sp: solve(sp[0], sp[1], root, limit), tasks):
            f.write(json.dumps(rec) + "\n"); f.flush()
