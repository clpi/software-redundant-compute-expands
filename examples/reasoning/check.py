#!/usr/bin/env python3
"""Independent checker for horn.py refutations.

Re-reads the problem's clauses and checks every proof step on its own: the derived fact is an
instance of the named clause's head, its premises are exactly instances of that clause's body
under one substitution, every premise was derived at an earlier step, a head variable that does
not occur in the body is bound to a constant of the problem, and the last step derives $false
from an all-negative clause. The matcher is written here, not imported from horn.py; only the
TPTP tokenizer and parser are shared.

Usage: check.py PROBLEM.p PROOF.json [--root TPTP_ROOT]   (exit 0 iff the proof checks)
"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from horn import parse_file  # noqa: E402


def var(s):
    return s[:1].isupper() or s[:1] == "_"


def unify_atom(pat, fact, sub):
    (p, args), (q, vals) = pat, fact
    if p != q or len(args) != len(vals):
        return None
    s = dict(sub)
    for a, v in zip(args, vals):
        if var(a):
            if s.get(a, v) != v:
                return None
            s[a] = v
        elif a != v:
            return None
    return s


def check(problem, proof, root):
    clauses = {}
    consts = set()
    for name, role, lits in parse_file(problem, root, []):
        pos = [(p, a) for neg, p, a in lits if not neg]
        neg = [(p, a) for neg, p, a in lits if neg]
        if len(pos) > 1:
            return False, f"{name} is not Horn"
        clauses.setdefault(name, []).append((pos[0] if pos else None, neg))
        for _, _, a in lits:
            consts |= {x for x in a if not var(x)}
    if not consts:
        consts = {"c0"}
    known = set()
    for k, (fact, rule, prem) in enumerate(proof):
        fact = (fact[0], tuple(fact[1]))
        prem = [(q[0], tuple(q[1])) for q in prem]
        last = k == len(proof) - 1
        if last != (fact[0] == "$false"):
            return False, f"step {k}: $false must be the last step and only there"
        for q in prem:
            if q not in known:
                return False, f"step {k}: premise {q} not derived earlier"
        ok = False
        for head, body in clauses.get(rule, []):
            if (head is None) != last or len(body) != len(prem):
                continue
            starts = [{}] if last else ([unify_atom(head, fact, {})] if unify_atom(head, fact, {}) is not None else [])

            def assign(i, used, s):
                if i == len(body):
                    if head is not None:
                        free = {a for a in head[1] if var(a)} - {a for _, args in body for a in args if var(a)}
                        if any(s.get(a) not in consts for a in free):
                            return False
                    return True
                for j, q in enumerate(prem):
                    if j in used:
                        continue
                    s2 = unify_atom(body[i], q, s)
                    if s2 is not None and assign(i + 1, used | {j}, s2):
                        return True
                return False
            if any(assign(0, frozenset(), s0) for s0 in starts):
                ok = True
                break
        if not ok:
            return False, f"step {k}: {fact} does not follow from {rule} and its premises"
        known.add(fact)
    return bool(proof) and proof[-1][0][0] == "$false", "ok"


if __name__ == "__main__":
    prob, pf = sys.argv[1], sys.argv[2]
    root = sys.argv[sys.argv.index("--root") + 1] if "--root" in sys.argv else os.environ.get("TPTP", ".")
    ok, why = check(prob, json.load(open(pf)), root)
    print("CHECKED" if ok else f"REJECTED: {why}")
    sys.exit(0 if ok else 1)
