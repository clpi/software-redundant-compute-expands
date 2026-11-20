#!/usr/bin/env python3
"""Heuristic scan of Lean theorems (audit). For each theorem: hypothesis
binders, proof size, and flags:
  DEFN   proof is rfl / Iff.rfl / trivial / id / a one-token term: the
         statement holds by unfolding definitions (a restatement)
  DATA   proof is decide/by decide/simp over a concrete literal: checks a
         data file or a hand-built example, not a general property
  HYP    has a hypothesis whose name says premise/fidelity/assume/faithful
         or the conclusion text appears verbatim among the hypotheses
argv: files... ; prints TSV and a summary."""
import re, sys, collections
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(theorem|lemma)\s+([^\s(:{\[]+)')
TOP = re.compile(r'^(?:@\[|/--|/-!|theorem|lemma|def|abbrev|structure|inductive|instance|class|namespace|end|section|open|#|example|noncomputable|private|protected|variable|set_option|macro|syntax|notation)')
rows = []
for path in sys.argv[1:]:
    lines = open(path, errors="replace").read().split("\n")
    i = 0
    while i < len(lines):
        m = DECL.match(lines[i])
        if not m:
            i += 1; continue
        j = i + 1
        while j < len(lines) and not (lines[j] and not lines[j][0].isspace() and TOP.match(lines[j])):
            j += 1
        text = "\n".join(lines[i:j]).rstrip()
        head, sep, proof = text.partition(":=")
        proof = proof.strip()
        # binders before the final colon of the statement
        depth, cut = 0, None
        for k, ch in enumerate(head):
            if ch in "([{⦃": depth += 1
            elif ch in ")]}⦄": depth -= 1
            elif ch == ":" and depth == 0: cut = k
        binders = head[:cut] if cut else head
        concl = " ".join(head[cut + 1:].split()) if cut else ""
        hyps = re.findall(r'\(([^():]+):([^()]*(?:\([^()]*\)[^()]*)*)\)', binders)
        hypnames = [h[0].strip() for h in hyps]
        hyptypes = [" ".join(h[1].split()) for h in hyps]
        p1 = " ".join(proof.split())
        flags = []
        if re.fullmatch(r'(by\s+)?(rfl|Iff\.rfl|trivial|id|fun\s+\w+\s*=>\s*\w+|⟨\w*⟩|by\s+exact\s+\w+|by\s+simp)', p1) or p1 in ("rfl", "Iff.rfl"):
            flags.append("DEFN")
        if re.search(r'\b(decide|native_decide)\b', p1) and len(p1) < 60:
            flags.append("DATA")
        if any(re.search(r'premise|fidel|assum|faith|hyp', n, re.I) for n in hypnames) or (concl and any(concl == t for t in hyptypes)):
            flags.append("HYP")
        rows.append((path, i + 1, m.group(2), len(hyps), len(p1), ",".join(flags), concl[:110]))
        i = j
c = collections.Counter()
for r in rows:
    for f in (r[5].split(",") if r[5] else []): c[f] += 1
    print("\t".join(map(str, r)))
print("SUMMARY\ttheorems=%d\t%s" % (len(rows), dict(c)), file=sys.stderr)
