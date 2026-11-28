#!/usr/bin/env python3
"""TPTP CNF (function-free, no equality) to SMT-LIB 2 over one uninterpreted sort, for Z3 and cvc5.

Same contract as the TPTP file: no unique-names assumption, every clause universally closed."""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
from horn import parse_file, is_var  # noqa: E402


def q(s):
    return "|" + s.replace("|", "_").replace("\\", "_") + "|"


def convert(path, root):
    cl = parse_file(path, root, [])
    consts, preds = set(), {}
    for _, _, lits in cl:
        for _, p, a in lits:
            preds[p] = len(a)
            consts |= {x for x in a if not is_var(x)}
    out = ["(set-logic UF)", "(declare-sort U 0)"]
    out += [f"(declare-const {q(c)} U)" for c in sorted(consts)]
    out += [f"(declare-fun {q(p)} ({' '.join(['U'] * n)}) Bool)" for p, n in sorted(preds.items())]
    for name, _, lits in cl:
        vs = sorted({x for _, _, a in lits for x in a if is_var(x)})
        ls = []
        for neg, p, a in lits:
            at = f"({q(p)} {' '.join(q(x) for x in a)})" if a else q(p)
            ls.append(f"(not {at})" if neg else at)
        body = ls[0] if len(ls) == 1 else "(or " + " ".join(ls) + ")" if ls else "false"
        if vs:
            body = "(forall (" + " ".join(f"({q(v)} U)" for v in vs) + ") " + body + ")"
        out.append(f"(assert (! {body} :named {q('c_' + name)}))" if False else f"(assert {body})")
    out.append("(check-sat)")
    return "\n".join(out) + "\n"


if __name__ == "__main__":
    sys.stdout.write(convert(sys.argv[1], sys.argv[2]))
