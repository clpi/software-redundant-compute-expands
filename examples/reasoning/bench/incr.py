#!/usr/bin/env python3
"""Incremental benchmark: clauses arrive one at a time, and after each one the solver must say
whether the clauses so far are satisfiable. Same contract for every solver: the same clause
order (the problem file's, includes expanded in place), an answer after every append, and the
same per-answer limit.

  native   one process; horn --each answers after every appended clause
  z3       one process; one SMT-LIB script with (check-sat) after every assert (Z3's incremental mode)
  cvc5     one process; the same script, with incremental solving on
  vampire, eprover   no incremental mode: one run per prefix, from scratch

Records per (solver, problem): answers (one per prefix), how many are right (the answer for a
prefix is Unsatisfiable iff the native engine's refutation index has been reached, which is
checked against the problem's TPTP status for the full set), total wall seconds, peak memory.

Usage: incr.py LIST ROOT OUT.jsonl PER_ANSWER_LIMIT SOLVERS [--logs DIR]
"""
import json
import os
import re
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.dirname(HERE))
import bench  # noqa: E402
from horn import parse_file, is_var  # noqa: E402


def clauses(path, root):
    out = []
    for name, role, lits in parse_file(path, root, []):
        body = " | ".join(("~ " if neg else "") + p + ("(" + ",".join(a) + ")" if a else "") for neg, p, a in lits) or "$false"
        out.append((name, role, lits, f"cnf({name},{role if role != 'negated_conjecture' else 'negated_conjecture'},( {body} )).\n"))
    return out


def smt_script(cl, incremental_option=None):
    consts, preds = set(), {}
    for _, _, lits, _ in cl:
        for _, p, a in lits:
            preds[p] = len(a)
            consts |= {x for x in a if not is_var(x)}
    q = lambda s: "|" + s.replace("|", "_") + "|"
    out = ["(set-logic UF)"] + ([f"(set-option :{incremental_option} true)"] if incremental_option else []) + ["(declare-sort U 0)"]
    out += [f"(declare-const {q(c)} U)" for c in sorted(consts)]
    out += [f"(declare-fun {q(p)} ({' '.join(['U'] * n)}) Bool)" for p, n in sorted(preds.items())]
    for _, _, lits, _ in cl:
        vs = sorted({x for _, _, a in lits for x in a if is_var(x)})
        ls = [(f"(not {x})" if neg else x) for neg, x in ((neg, f"({q(p)} {' '.join(q(t) for t in a)})" if a else q(p)) for neg, p, a in lits)]
        body = ls[0] if len(ls) == 1 else ("(or " + " ".join(ls) + ")" if ls else "false")
        if vs:
            body = "(forall (" + " ".join(f"({q(v)} U)" for v in vs) + ") " + body + ")"
        out += [f"(assert {body})", "(check-sat)"]
    return "\n".join(out) + "\n"


def run_problem(solver, prob, root, limit):
    path = os.path.join(root, prob)
    cl = clauses(path, root)
    n = len(cl)
    rec = {"solver": solver, "problem": prob, "clauses": n, "limit_per_answer": limit}
    if solver == "native":
        out, wall, to, rss = bench.run(["timeout", str(limit * n), bench.HORNC, path, "--root", root, "--each"], limit * n)
        ans = re.findall(r"% after \d+ (\w+)", out)
        bench.keep(rec, out)
    elif solver in ("z3", "cvc5"):
        smt = tempfile.mktemp(suffix=".smt2")
        open(smt, "w").write(smt_script(cl, None if solver == "z3" else "incremental"))
        cmd = ["z3", f"-t:{limit * 1000}", smt] if solver == "z3" else ["timeout", str(limit * n), sys.executable, os.path.join(HERE, "cvc5run.py"), smt, str(limit)]
        out, wall, to, rss = bench.run(cmd, limit * n)
        ans = [{"unsat": "Unsatisfiable", "sat": "Satisfiable"}.get(w.strip(), "Unknown") for w in out.strip().splitlines() if w.strip() in ("sat", "unsat", "unknown") or w.startswith("unknown")]
        os.remove(smt)
        bench.keep(rec, out)
    else:
        ans, wall, rss, logs = [], 0.0, 0, []
        d = tempfile.mkdtemp()
        unsat_from = None
        for k in range(1, n + 1):
            pf = os.path.join(d, f"prefix{k}.p")
            open(pf, "w").write("".join(c[3] for c in cl[:k]))
            if solver == "vampire":
                cmd = [bench.VAMPIRE, "--mode", "casc", "-t", str(limit), pf]
            else:
                cmd = [bench.EPROVER, "--auto", "-s", f"--cpu-limit={limit}", "--tptp3-in", pf]
            out, w, to, r = bench.run(cmd, limit)
            wall += w; rss = max(rss, r or 0)
            st = bench.szs(out)
            st = {"Theorem": "Unsatisfiable", "CounterSatisfiable": "Satisfiable"}.get(st, st)
            ans.append(st or ("Timeout" if to else "Unknown"))
            logs.append(bench.keep({}, out).get("log_sha256"))
            os.remove(pf)
        os.rmdir(d)
        rec["logs"] = logs
    rec.update(answers=ans, wall=wall, rss_kib=rss)
    return rec


if __name__ == "__main__":
    lst, root, outp, limit, solvers = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), sys.argv[5].split(",")
    if "--logs" in sys.argv:
        bench.LOGS = sys.argv[sys.argv.index("--logs") + 1]
        os.makedirs(bench.LOGS, exist_ok=True)
    with open(outp, "a") as f:
        for prob in open(lst).read().split():
            for s in solvers:
                f.write(json.dumps(run_problem(s, prob, root, limit)) + "\n"); f.flush()
