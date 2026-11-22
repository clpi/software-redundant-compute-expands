# Incremental recomputation: spec

Directive: Chris, 2026-11-21 18:20 PST: make the algorithm search, deterministic
synthesis and finite bounded search incremental recomputation. Witnesses join,
derivations re-derive over their premise cones, verdicts carry, and a
from-scratch sweep exists only as the independent checker's route.

The record Chris pasted (2026-11-22 02:33Z) describes engines in
`~/workspace/incremental-scratch/` on another machine. None of that code is on
GitHub or in the project files. Everything here was rebuilt from the record's
spec text against the home repos at the pins below.

## Pins (inputs, read only)

| Home | Repo | Pin | File, sha256 prefix |
| --- | --- | --- | --- |
| candidate space (s1) | software-redundant-compute-expands | main 84eb1cd | fixture from semantic-axes/out/space.jsonl, see fixtures/ |
| meta-search (s1) | software-is-reversible | 0ac60e7 (meta.py identical at 12047b2) | meta.py df109f3bd30015d0 |
| synthesis (s2) | software-is-a-parametric-language-model | ca4ca2b | harness/run.py 0ebaaa3b345ecd26 |
| bounded search (s3) | software-has-a-highest-minimal-axis | b12fdb2 | solver/solver.py 582955f6254c23fa, model.py c28e029d59764a02 |

## System 1: frontier (frontier.py)

- Carried state: per item, its score vector, a hash of it (the premise), its
  dominator set and the set it dominates.
- Cone: dominance of a pair reads only that pair's two vectors.
- Join of item y: 2(n-1) ordered evaluations, (y, x) and (x, y) for every
  carried x. Re-join with the same hash: 0 evaluations (carry). Changed
  vector: logged as a withdrawal plus a join.
- Withdrawal: 0 evaluations. Removing y from every dominator set re-admits
  exactly the items y blocked (Lean: `Cone.front_withdraw`).
- Checker: `naive_frontier`, separate code, every ordered pair.
- Lean: `Cone.front_join` (the frontier after a join is the old frontier
  filtered by y plus y if undominated), `Cone.front_withdraw`, `Cone.any_dup`.

Trade-off, stated: the online archive already on srce main (decide.Archive,
PR 7) and the semantic axes front (branch claude/project-thread-uczhtq)
compare a new item with frontier members only, which is cheaper per join. They
cannot withdraw: a dropped item is gone. The carried matrix pays 2(n-1) per join
to make withdrawal and score change exact at 0 evaluations.

## System 1, meta-search (metasearch.py)

- Carried state: each instance's frontier (frontier.py), each (configuration,
  instance) selection as (minimum score, winners), each configuration's measure
  vector, and the meta frontier over configurations (frontier.py).
- Cones: a selection reads its instance's frontier members only; a meta pair
  reads two measure vectors.
- Configuration join: score it on each frontier, measure, join the meta
  frontier.
- Instance candidate join: if the instance frontier set is unchanged, every
  selection carries. Otherwise entering members are scored against the
  carried minimum, a selection is rescored in full only when a member that
  left was one of its winners, and a configuration re-joins the meta frontier
  only when its measure vector changed.
- Checker: meta.py's own `main()`, unmodified, on the same instances and
  configurations, with its printed meta-frontier and rows parsed back.

## System 2: synthesis (synthesis.py)

- Wraps `certified_decode` from the PRLM harness unmodified. It reads the table
  only through `table.get` (via `row_of`). A TrackedTable records each key read
  and a hash of the row seen, or `missing` when no row was there.
- Cone of a query: that key to hash map. A missing row is a premise.
- Edit at one row key (overlay, insert or remove): re-derive exactly the
  queries whose cones hold the key. Every other verdict carries only after
  every hash in its cone is re-checked against the edited table (asserted).
- Unit of state: a distinct (prefix, bound) query. The harness query list
  repeats the root prefix (8 times at seeds 11 and 23); repeats share a verdict.
- Resume (ResumeEngine): an affected query restarts at the checkpoint taken just
  before its first read of the edited key (heap, tie counter, unresolved bounds,
  best, cost), from a replica decoder that records those checkpoints. Lean:
  `Cone.resume`.
- Checker: the decoder run whole on a plain dict copy of the edited table.
- Lean: `Cone.run_cone` (a lookup program agreeing on its cone gives the same
  answer and the same cone), `Cone.edit_outside`, and the control
  `Cone.missing_is_a_premise` (drop missing keys from the cone and the rule
  fails). Premise, not proved: the Python decoder is such a program, i.e. it
  reads nothing but `table.get`. The tracked run observes this; it is not a
  theorem about Python.

## System 3: bounded search (axis.py)

- Wraps the HMA solver's strict input model (model.load_table); the checker is
  solver.solve, unmodified.
- Carried state: per difference set m (as a bitmask of axes), the components
  some row pair with difference set m distinguishes; per subset S, its live
  set and (engaged, mu, lambda).
- Cone: S depends exactly on the pairs whose difference set is inside S
  (Lean: `HmaJoin.agreeoff_iff_diff`, over Hma.lean's own `agreeoff`).
- Join (append contract rows): only pairs with a new row are computed. A pair
  that adds components to dc[m] re-measures exactly the subsets containing m
  whose live set grows. Minimality and the highest selection are re-derived
  from carried measures over 2^n subsets; no pair is rescanned.
- Not a join: a duplicate row or a changed behavior at an existing
  configuration. Refused by name.
- Lean, over Hma.lean unchanged: `HmaJoin.join_live` (live after the join iff
  live before or a witness pair with a new row), `HmaJoin.scoped_live`,
  `HmaJoin.witness_mono` (superset rule), `HmaJoin.scoped_rho` (unchanged
  liveness gives unchanged live list, lambda and mu). Generic pair half:
  `Cone.pairs_join`, `Cone.pairs_count`.

## Gate (gate.py) and Lean gate (lean/check.sh)

`python3 -B gate.py <reversible> <prlm> <hma> [counts.json]` runs every engine
against its checker, every control, and one mutant per engine that breaks its
cone rule in one place; a mutant that agrees with its checker fails the gate.
`LEAN=... sh lean/check.sh <hma proof dir>` builds Hma.lean unchanged, then
Cone, HmaJoin and Audit with warnings as errors, scans for escape tokens and
requires 13 axiom printouts within {propext, Classical.choice, Quot.sound}.
