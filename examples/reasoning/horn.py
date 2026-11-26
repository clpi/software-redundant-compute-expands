#!/usr/bin/env python3
"""Incremental Horn reasoning over a single append-only clause log.

Decides function-free Horn clause sets (TPTP CNF, class EPR + HRN, no equality) by
semi-naive forward chaining: each new fact is joined against the facts already derived,
and only through the rule body positions it can occupy. A clause appended later costs only
the derivations it enables; nothing already derived is recomputed. A refutation is a
derivation of an all-negative clause's body; its proof is the derivation DAG, printed in
TPTP-like steps and re-checked by `check.py`.

Usage: horn.py PROBLEM.p [--root TPTP_ROOT] [--proof]
Prints `% SZS status Unsatisfiable|Satisfiable|GaveUp` and, with --proof, the derivation.
"""
import os
import re
import sys
import time
from collections import defaultdict

TOK = re.compile(r"\s*(?:(%[^\n]*)|(/\*.*?\*/)|('(?:[^'\\]|\\.)*')|(\"(?:[^\"\\]|\\.)*\")|([A-Za-z0-9_$]+)|(!=|=>|<=>|<=|<~>|~\||~&|[(),.\[\]|&~=:!?*+<>-]))", re.S)


def tokens(text):
    pos, out = 0, []
    while pos < len(text):
        m = TOK.match(text, pos)
        if not m:
            if text[pos:].strip() == "":
                break
            raise ValueError(f"bad token at {pos}: {text[pos:pos + 30]!r}")
        pos = m.end()
        if m.group(1) or m.group(2):
            continue
        out.append(next(g for g in m.groups()[2:] if g is not None))
    return out


class OutOfClass(Exception):
    pass


def parse_file(path, root, out):
    toks = tokens(open(path, errors="replace").read())
    i = 0

    def expect(t):
        nonlocal i
        if toks[i] != t:
            raise ValueError(f"{path}: expected {t!r}, got {toks[i]!r}")
        i += 1

    def term():
        # a ground compound term is a constant of the Herbrand universe; one with a variable is
        # outside the function-free class
        nonlocal i
        name = toks[i]; i += 1
        if i < len(toks) and toks[i] == "(":
            i += 1
            args = []
            while True:
                args.append(term())
                if toks[i] == ",":
                    i += 1; continue
                expect(")"); break
            if any(is_var(a) for a in args):
                raise OutOfClass("function symbol over a variable")
            return name + "(" + ",".join(args) + ")"
        return name

    def atom():
        nonlocal i
        neg = False
        if toks[i] == "~":
            neg = True; i += 1
        if toks[i] == "(":
            raise OutOfClass("nested literal")
        p = toks[i]; i += 1
        args = []
        if i < len(toks) and toks[i] == "(":
            i += 1
            while True:
                args.append(term())
                if toks[i] == ",":
                    i += 1; continue
                expect(")"); break
        if i < len(toks) and toks[i] in ("=", "!="):
            raise OutOfClass("equality")
        return neg, p, tuple(args)

    while i < len(toks):
        kw = toks[i]; i += 1
        if kw == "include":
            expect("(")
            f = toks[i].strip("'"); i += 1
            sel = None
            if toks[i] == ",":
                i += 1; expect("["); sel = []
                while toks[i] != "]":
                    if toks[i] != ",":
                        sel.append(toks[i])
                    i += 1
                expect("]")
            expect(")"); expect(".")
            sub = []
            parse_file(os.path.join(root, f), root, sub)
            out.extend(c for c in sub if sel is None or c[0] in sel)
            continue
        if kw != "cnf":
            raise OutOfClass(f"{kw} formula")
        expect("(")
        name = toks[i]; i += 1; expect(",")
        role = toks[i]; i += 1; expect(",")
        depth = 0
        lits = []
        while True:
            t = toks[i]
            if t == "(":
                depth += 1; i += 1; continue
            if t == ")" and depth > 0:
                depth -= 1; i += 1; continue
            if t == "|":
                i += 1; continue
            if t == ")" or t == ",":
                break
            lits.append(atom())
        while toks[i] != ".":  # annotations
            i += 1
        i += 1
        out.append((name, role, lits))
    return out


def is_var(s):
    return s[0].isupper() or s[0] == "_"


class Horn:
    """Append-only Horn clause log with incremental forward chaining."""

    def __init__(self):
        self.consts = set()
        self.rules = []                 # (name, head|None, body)
        self.by_pred = defaultdict(list)  # pred -> [(rule index, body position)]
        self.facts = defaultdict(set)   # pred -> set of tuples
        self.index = defaultdict(set)   # (pred, pos, value) -> tuples
        self.why = {}                   # (pred, tuple) -> (rule name, [premise facts])
        self.queue = []
        self.refuted = None             # (rule name, premises)
        self.ops = 0                    # join steps, the incremental cost measure
        self.pending_open = []          # rules whose unsafe head variables wait for constants

    # ---- appending
    def add_clause(self, name, lits):
        pos = [l for l in lits if not l[0]]
        neg = [l for l in lits if l[0]]
        if len(pos) > 1:
            raise OutOfClass("non-Horn clause")
        for _, _, args in lits:
            for a in args:
                if not is_var(a):
                    self.consts.add(a)
        head = (pos[0][1], pos[0][2]) if pos else None
        body = [(p, a) for _, p, a in neg]
        r = len(self.rules)
        self.rules.append((name, head, body))
        for j, (p, _) in enumerate(body):
            self.by_pred[p].append((r, j))
        new_consts = self._fresh_consts()
        if not body:
            self._fire(r, {}, [])
        else:
            # join the new rule against everything already derived (only this rule)
            self._join_rule(r, None, None)
        if new_consts:
            # a new constant widens every unsafe head variable already seen
            for r2, b in list(self.pending_open):
                if r2 != r:
                    self._fire_unsafe(r2, b[0], b[1], only=new_consts)
        self._run()

    def _fresh_consts(self):
        old = getattr(self, "_known", set())
        new = self.consts - old
        self._known = set(self.consts)
        return new

    # ---- core
    def _insert(self, p, t, rule, prem):
        if t in self.facts[p]:
            return
        self.facts[p].add(t)
        for k, v in enumerate(t):
            self.index[(p, k, v)].add(t)
        self.why[(p, t)] = (rule, prem)
        self.queue.append((p, t))

    def _fire(self, r, b, prem):
        name, head, body = self.rules[r]
        if head is None:
            if self.refuted is None:
                self.refuted = (name, list(prem))
            return
        p, args = head
        free = [a for a in args if is_var(a) and a not in b]
        if free:
            self.pending_open.append((r, (dict(b), list(prem))))
            self._fire_unsafe(r, b, prem, only=None)
            return
        self._insert(p, tuple(b.get(a, a) for a in args), name, prem)

    def _fire_unsafe(self, r, b, prem, only):
        name, (p, args), _ = self.rules[r]
        free = sorted({a for a in args if is_var(a) and a not in b})
        consts = sorted(self.consts) or ["c0"]
        if not self.consts:
            self.consts.add("c0"); self._known.add("c0")

        def rec(k, bb, used_new):
            if k == len(free):
                if only is None or used_new:
                    self._insert(p, tuple(bb.get(a, a) for a in args), name, prem)
                return
            for c in consts:
                bb[free[k]] = c
                rec(k + 1, bb, used_new or (only is not None and c in only))
            del bb[free[k]]
        rec(0, dict(b), False)

    def _match(self, args, t, b):
        b = dict(b)
        for a, v in zip(args, t):
            if is_var(a):
                if b.setdefault(a, v) != v:
                    return None
            elif a != v:
                return None
        return b

    def _candidates(self, p, args, b):
        best = None
        for k, a in enumerate(args):
            v = b.get(a, a) if is_var(a) else a
            if not is_var(v):
                s = self.index.get((p, k, v), ())
                if best is None or len(s) < len(best):
                    best = s
        return self.facts[p] if best is None else best

    def _join(self, r, rest, b, prem):
        if self.refuted is not None:
            return
        if not rest:
            self._fire(r, b, prem)
            return
        # most constrained atom first
        k = min(range(len(rest)), key=lambda j: len(self._candidates(rest[j][0], rest[j][1], b)))
        p, args = rest[k]
        others = rest[:k] + rest[k + 1:]
        for t in list(self._candidates(p, args, b)):
            self.ops += 1
            b2 = self._match(args, t, b)
            if b2 is not None:
                self._join(r, others, b2, prem + [(p, t)])

    def _join_rule(self, r, j, fact):
        _, _, body = self.rules[r]
        if fact is None:
            self._join(r, list(body), {}, [])
            return
        p, t = fact
        b = self._match(body[j][1], t, {})
        if b is not None:
            self._join(r, body[:j] + body[j + 1:], b, [fact])

    def _run(self):
        while self.queue and self.refuted is None:
            p, t = self.queue.pop()
            for r, j in self.by_pred.get(p, ()):
                self._join_rule(r, j, (p, t))
                if self.refuted is not None:
                    return

    # ---- proof
    def proof(self):
        if self.refuted is None:
            return []
        steps, seen = [], set()
        for root in self.refuted[1]:  # iterative post-order: derivation chains can be thousands deep
            stack = [(root, False)]
            while stack:
                f, done = stack.pop()
                if done:
                    steps.append((f, *self.why[f]))
                    continue
                if f in seen:
                    continue
                seen.add(f)
                stack.append((f, True))
                for q in reversed(self.why[f][1]):
                    if q not in seen:
                        stack.append((q, False))
        steps.append((("$false", ()), self.refuted[0], self.refuted[1]))
        return steps


def fmt(f):
    p, t = f
    return p + ("(" + ",".join(t) + ")" if t else "")


def solve(path, root, want_proof=False):
    t0 = time.perf_counter()
    try:
        cl = parse_file(path, root, [])
        h = Horn()
        for name, role, lits in cl:
            h.add_clause(name, lits)
            if h.refuted is not None:
                break
    except OutOfClass as e:
        return {"status": "GaveUp", "reason": str(e), "secs": time.perf_counter() - t0}
    st = "Unsatisfiable" if h.refuted is not None else "Satisfiable"
    out = {"status": st, "secs": time.perf_counter() - t0, "ops": h.ops,
           "facts": sum(len(v) for v in h.facts.values())}
    if h.refuted is not None:
        pr = h.proof()
        out["proof_steps"] = len(pr)
        if want_proof:
            out["proof"] = pr
    return out


if __name__ == "__main__":
    path = sys.argv[1]
    root = sys.argv[sys.argv.index("--root") + 1] if "--root" in sys.argv else os.environ.get("TPTP", os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(path)))))
    res = solve(path, root, "--proof" in sys.argv or "--proof-json" in sys.argv)
    print(f"% SZS status {res['status']} for {os.path.basename(path)}")
    if "proof" in res:
        print("% SZS output start Refutation")
        for f, rule, prem in res["proof"]:
            print(f"{fmt(f)} <- {rule}({', '.join(fmt(q) for q in prem)})")
        print("% SZS output end Refutation")
    if "--proof-json" in sys.argv and "proof" in res:
        import json
        json.dump([[list(f[0:1]) + [list(f[1])], rule, [[q[0], list(q[1])] for q in prem]] for f, rule, prem in res["proof"]],
                  open(sys.argv[sys.argv.index("--proof-json") + 1], "w"))
    print(f"% secs {res['secs']:.4f} ops {res.get('ops', 0)} facts {res.get('facts', 0)} proof_steps {res.get('proof_steps', 0)}")
