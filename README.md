# Software redundant compute expands

The claim: under expansion-only growth of a behavioral
hypergraph — nodes and hyperedges appended, nothing
removed — redundant compute, once witnessed, never
disappears; the redundancy measure never decreases along
an expansion chain; and redundancy compounds into joined
structures, at least additively and strictly wherever the
parts overlap. This repository carries the proved model:
a Lean development in which the measure, its exact append
split, its superadditivity, its strict overlap gain, the
appearance of redundancy at a join of irredundant parts,
and the witness reconstruction kernel are all theorems,
with standing controls exhibiting exactly where each
load-bearing condition bites — including the control that
refutes the universal form of the claim.

## Contents

- `defs.md` — every term of the model defined at
  implementer resolution, each tied to its Lean counterpart.
- `spec.md` — the claim in its author's terms, the
  executable method, the theorem inventory at its honest
  strength, the premise labels, and a falsification
  protocol for every claim not proven outright.
- `proof/Core.lean` — the measure and its append algebra,
  the duplicate witness characterization, derivability
  under expansion, and the graph-level monotonicity
  theorems.
- `proof/Join.lean` — compounding into joined structures
  and the touch kernel of witness reconstruction.
- `proof/Controls.lean` — six standing controls, each a
  proved statement over concrete data.
- `proof/Synthesis.lean` — the joined theorem assembling
  the parts, with the campaign's empirical yield rate
  carried as a named premise.
- `proof/check.sh` — the family gate.

## The gate

`proof/check.sh` compiles every Lean file under `proof/`
with warnings as errors, rejects every proof escape token,
and enforces that every printed axiom lies in the allowed
set {propext, Classical.choice, Quot.sound}. At the landed
pin it passes cold; the printed axioms actually used are
exactly {propext, Quot.sound}, and several theorems depend
on no axioms at all. The gate log is `proof/CHECK.log`.
Toolchain: Lean 4.19.0 (`proof/lean-toolchain`).
