#!/usr/bin/env python3
"""Independent checker for the native engine's resolution refutations (engine ord- or ord+).

The proof is a JSON list of clauses, premises first. A clause marked "input" must be a variant of
the problem clause of that name. A clause marked "from": [i, j] must be a variant of a binary
resolvent of clauses i and j, which appear earlier: the head of one is unified with some body
literal of the other (renamed apart) and the resolvent is recomputed here and compared up to a
renaming of variables and the order of body literals. The last clause must be empty. Binary
resolution is sound, so a proof that checks is a refutation whatever ordering found it. Only the
TPTP parser is shared with horn.py; unification and the variant test are written here.

Usage: check_res.py PROBLEM.p PROOF.json [--root TPTP_ROOT]   (exit 0 iff the proof checks)
"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from horn import parse_file  # noqa: E402


def var(s):
    return isinstance(s, str) and (s[:1].isupper() or s[:1] == "_")


def walk(t, s):
    while var(t) and t in s:
        t = s[t]
    return t


def unify(a, b, s):
    if a[0] != b[0] or len(a) != len(b):
        return None
    s = dict(s)
    for x, y in zip(a[1:], b[1:]):
        x, y = walk(x, s), walk(y, s)
        if x == y:
            continue
        if var(x):
            s[x] = y
        elif var(y):
            s[y] = x
        else:
            return None
    return s


def apply(a, s):
    return (a[0],) + tuple(walk(t, s) for t in a[1:])


def rename(c, tag):
    h, b = c
    r = lambda a: (a[0],) + tuple(t + tag if var(t) else t for t in a[1:])
    return (r(h) if h else None, [r(a) for a in b])


def variant(c, d):
    """c and d are equal under a bijective renaming of variables, body as a multiset"""
    (ch, cb), (dh, db) = c, d
    if (ch is None) != (dh is None) or len(cb) != len(db):
        return False

    def m(a, b, f, g):
        if a[0] != b[0] or len(a) != len(b):
            return None
        f, g = dict(f), dict(g)
        for x, y in zip(a[1:], b[1:]):
            if var(x) != var(y):
                return None
            if var(x):
                if f.get(x, y) != y or g.get(y, x) != x:
                    return None
                f[x] = y
                g[y] = x
            elif x != y:
                return None
        return f, g

    start = [({}, {})] if ch is None else ([m(ch, dh, {}, {})] if m(ch, dh, {}, {}) else [])

    def go(i, used, f, g):
        if i == len(cb):
            return True
        for j, y in enumerate(db):
            if j in used:
                continue
            r = m(cb[i], y, f, g)
            if r and go(i + 1, used | {j}, *r):
                return True
        return False
    return any(go(0, frozenset(), f, g) for f, g in start)


def resolvents(p, q):
    """every binary resolvent with p's head against a body literal of q"""
    if p[0] is None:
        return
    p, q = rename(p, "_1"), rename(q, "_2")
    for i, lit in enumerate(q[1]):
        s = unify(p[0], lit, {})
        if s is None:
            continue
        yield (apply(q[0], s) if q[0] else None, [apply(a, s) for a in p[1] + q[1][:i] + q[1][i + 1:]])


def check(problem, proof, root):
    inputs = {}
    for name, role, lits in parse_file(problem, root, []):
        pos = [(p,) + tuple(a) for neg, p, a in lits if not neg]
        neg = [(p,) + tuple(a) for neg, p, a in lits if neg]
        if len(pos) > 1:
            return False, f"{name} is not Horn"
        inputs.setdefault(name, []).append((pos[0] if pos else None, neg))
    have = {}
    for k, st in enumerate(proof):
        c = (tuple(st["head"]) if st["head"] else None, [tuple(a) for a in st["body"]])
        if "input" in st:
            if not any(variant(c, d) for d in inputs.get(st["input"], [])):
                return False, f"step {k}: not a variant of input clause {st['input']}"
        else:
            i, j = st["from"]
            if i not in have or j not in have:
                return False, f"step {k}: premise not derived earlier"
            if not any(variant(c, r) for a, b in ((have[i], have[j]), (have[j], have[i])) for r in resolvents(a, b)):
                return False, f"step {k}: not a resolvent of {i} and {j}"
        have[st["id"]] = c
    if not proof:
        return False, "empty proof"
    last = proof[-1]
    return (last["head"] is None and not last["body"]), "ok"


if __name__ == "__main__":
    prob, pf = sys.argv[1], sys.argv[2]
    root = sys.argv[sys.argv.index("--root") + 1] if "--root" in sys.argv else os.environ.get("TPTP", ".")
    ok, why = check(prob, json.load(open(pf)), root)
    print("CHECKED" if ok else f"REJECTED: {why}")
    sys.exit(0 if ok else 1)
