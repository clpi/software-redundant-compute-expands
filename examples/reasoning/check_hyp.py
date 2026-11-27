#!/usr/bin/env python3
"""Independent checker for hyperresolution refutations of Horn CNF with function symbols (engine hyper).

The proof is a JSON list of steps. A step {"id", "atom", "rule", "parents"} claims that atom is a
positive unit derived from problem clause `rule`: with no parents, the atom must be a variant of
that clause (a positive unit clause); otherwise the clause's body literals, in file order, are
unified simultaneously with the parents' atoms (each renamed apart), and the atom must be a variant
of the clause head under that most general unifier, or an instance of it (a derived unit holds for
every instance, so instantiating one is sound). The last step has atom null: the rule must be
a clause without a positive literal whose body unifies with its parents. Unification has an occurs
check. Hyperresolution is sound, so a proof that checks is a refutation.

This file has its own TPTP reader and unification; nothing is shared with the engine.

Usage: check_hyp.py PROBLEM.p PROOF.json [--root TPTP_ROOT]   (exit 0 iff the proof checks)
"""
import json
import os
import re
import sys

sys.setrecursionlimit(100000)
TOK = re.compile(r"\s+|%[^\n]*|/\*.*?\*/|'(?:[^'\\]|\\.)*'|\"(?:[^\"\\]|\\.)*\"|[A-Za-z0-9_$]+|!=|.", re.S)


def lex(text):
    return [t for t in TOK.findall(text) if t.strip() and not t.startswith("%") and not t.startswith("/*")]


class Reader:
    def __init__(self, toks):
        self.t, self.i = toks, 0

    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else None

    def take(self, want=None):
        x = self.t[self.i]
        if want is not None and x != want:
            raise SyntaxError(f"expected {want}, got {x}")
        self.i += 1
        return x

    def term(self, vs):
        x = self.take()
        if x[0].isupper() or x[0] == "_":
            return ("?", vs.setdefault(x, len(vs)))
        args = []
        if self.peek() == "(":
            self.take("(")
            args.append(self.term(vs))
            while self.peek() == ",":
                self.take(",")
                args.append(self.term(vs))
            self.take(")")
        return (x,) + tuple(args)


def read_problem(path, root, sel=None, out=None):
    out = {} if out is None else out
    r = Reader(lex(open(path).read()))
    while r.peek() is not None:
        kw = r.take()
        if kw == "include":
            r.take("(")
            fn = r.take()[1:-1]
            names = None
            if r.peek() == ",":
                r.take(",")
                r.take("[")
                names = []
                while r.peek() != "]":
                    x = r.take()
                    if x != ",":
                        names.append(x)
                r.take("]")
            r.take(")")
            r.take(".")
            read_problem(os.path.join(root, fn), root, names, out)
            continue
        if kw != "cnf":
            raise SyntaxError("not CNF")
        r.take("(")
        name = r.take()
        r.take(",")
        r.take()
        r.take(",")
        vs, lits, depth = {}, [], 0
        while True:
            p = r.peek()
            if p == "(":
                depth += 1
                r.take()
                continue
            if p == ")":
                if depth == 0:
                    break
                depth -= 1
                r.take()
                continue
            if p == "|":
                r.take()
                continue
            if p == ",":
                break
            neg = False
            if p == "~":
                neg = True
                r.take()
            a = r.term(vs)
            if r.peek() in ("=", "!="):
                raise SyntaxError("equality")
            lits.append((neg, a))
        d = 0
        while not (r.peek() == "." and d <= 0):
            x = r.take()
            d += x == "("
            d -= x == ")"
        r.take(".")
        if sel is not None and name not in sel:
            continue
        taut = any((a[0] == "$true" and not n) or (a[0] == "$false" and n) for n, a in lits)
        if taut:
            continue
        lits = [(n, a) for n, a in lits if a[0] not in ("$true", "$false")]
        heads = [a for n, a in lits if not n]
        if len(heads) > 1:
            raise SyntaxError("non-Horn")
        out[name] = (heads[0] if heads else None, [a for n, a in lits if n])
    return out


def walk(t, s):
    while t[0] == "?" and t in s:
        t = s[t]
    return t


def occurs(v, t, s):
    t = walk(t, s)
    if t == v:
        return True
    return t[0] != "?" and any(occurs(v, a, s) for a in t[1:])


def unify(a, b, s):
    stack = [(a, b)]
    while stack:
        x, y = stack.pop()
        x, y = walk(x, s), walk(y, s)
        if x == y:
            continue
        if x[0] == "?":
            if occurs(x, y, s):
                return None
            s[x] = y
        elif y[0] == "?":
            if occurs(y, x, s):
                return None
            s[y] = x
        elif x[0] != y[0] or len(x) != len(y):
            return None
        else:
            stack.extend(zip(x[1:], y[1:]))
    return s


def subst(t, s):
    t = walk(t, s)
    return t if t[0] == "?" else (t[0],) + tuple(subst(a, s) for a in t[1:])


def rename(t, tag):
    return ("?", (tag, t[1])) if t[0] == "?" else (t[0],) + tuple(rename(a, tag) for a in t[1:])


def variant(a, b):
    m, inv = {}, {}

    def go(x, y):
        if x[0] == "?" or y[0] == "?":
            if x[0] != "?" or y[0] != "?":
                return False
            if m.setdefault(x, y) != y or inv.setdefault(y, x) != x:
                return False
            return True
        return x[0] == y[0] and len(x) == len(y) and all(go(p, q) for p, q in zip(x[1:], y[1:]))
    return go(a, b)


def instance(a, g):
    """a is g with its variables replaced by terms (one-way match of g onto a)"""
    m = {}

    def go(x, y):
        if y[0] == "?":
            if y in m:
                return m[y] == x
            m[y] = x
            return True
        return x[0] == y[0] and len(x) == len(y) and all(go(p, q) for p, q in zip(x[1:], y[1:]))
    return go(a, g)


def from_json(j):
    if isinstance(j, str):
        assert j.startswith("?")
        return ("?", int(j[1:]))
    return (j[0],) + tuple(from_json(a) for a in j[1:])


def main():
    prob, pf = sys.argv[1], sys.argv[2]
    root = sys.argv[sys.argv.index("--root") + 1] if "--root" in sys.argv else os.path.dirname(os.path.dirname(os.path.dirname(prob)))
    cls = read_problem(prob, root)
    steps = json.load(open(pf))
    have = {}
    for n, st in enumerate(steps):
        rule = cls.get(st["rule"])
        if rule is None:
            print(f"REJECTED: step {n}: no clause {st['rule']}")
            return 1
        head, body = rule
        par = st["parents"]
        if any(p not in have for p in par):
            print(f"REJECTED: step {n}: a parent is not established earlier")
            return 1
        if len(par) != len(body):
            print(f"REJECTED: step {n}: {len(par)} parents for {len(body)} body literals of {st['rule']}")
            return 1
        s = {}
        for k, (lit, p) in enumerate(zip(body, par)):
            s = unify(rename(lit, "r"), rename(have[p], k), s)
            if s is None:
                print(f"REJECTED: step {n}: body literal {k} of {st['rule']} does not unify with its parent")
                return 1
        last = n == len(steps) - 1
        if st["atom"] is None:
            if head is not None or not last:
                print(f"REJECTED: step {n}: an empty conclusion needs a clause without a head, as the last step")
                return 1
            print("CHECKED")
            return 0
        if head is None:
            print(f"REJECTED: step {n}: {st['rule']} has no head")
            return 1
        atom = from_json(st["atom"])
        if not instance(atom, subst(rename(head, "r"), s)):
            print(f"REJECTED: step {n}: atom is not an instance of the head of {st['rule']} under the unifier")
            return 1
        have[st["id"]] = atom
    print("REJECTED: no empty conclusion")
    return 1


if __name__ == "__main__":
    sys.exit(main())
