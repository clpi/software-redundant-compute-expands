# Incremental recomputation: results and the record's claims checked

Run: 2026-11-22, this container. `receipts/gate.txt` (55 checks, GATE: PASS,
repeated byte-identical apart from wall-clock), `receipts/lean-gate.txt` (13
theorems, LEAN GATE: PASS), `receipts/counts.json`, `receipts/SHA256SUMS.txt`.
Pins are in SPEC.md. Counts are the claims; wall times are single runs and
indicative.

Where the record's engines live: `~/workspace/incremental-scratch/` on another
machine. Not on GitHub (code search over clpi), not in /mnt/project-files. All
three engines and the gate here are rebuilds from the record's spec text.

## The record's claims

| Claim in the record | Verdict | What was found |
| --- | --- | --- |
| s1: full frontier over 18 items = 306 ordered evaluations | HOLDS (arithmetic) | 18 x 17. True of any 18 items. Reproduced on a real 18-item instance (semantic axes ax-a held-out). |
| s1: 19th/18th join = 34 | HOLDS (arithmetic) | 2(n-1). Same caveat. |
| s1: build of first 17 = 272 | HOLDS (arithmetic) | 2(0+...+16). Same caveat. |
| s1: frontier agrees with checker on the register's 18 items, equals its printed nine | CANNOT REPRODUCE | The net-new frontier register's score table is nowhere reachable. software-estate-is-censused cites it (item 4) but does not carry it. |
| s1: unchanged re-join carries at 0 | HOLDS | Own engine, all four real instances. |
| s1 census: "no machinery implements" pair-local frontier entry | CORRECTED | srce main already has an online archive (decide.Archive, PR 7) checked against cold recompute at every append prefix, and the semantic axes branch has a point-append front exact at every step (2,000 vs 34,679 scalar compares). Neither carries a matrix, so neither can withdraw. True of the register itself, not of the candidate space. |
| s2: seed 11, 22 queries, 15 distinct prefixes | HOLDS | |
| s2: every verdict agrees with the from-scratch decoder | HOLDS | Seeds 11 and 23. |
| s2: one edit re-derived 1, carried 14; 12 vs 43 lookups | HOLDS, but cherry-picked | Reproduced exactly by 3 of 294 single-key edits, all at the root row key. "1 of 15" counts distinct prefixes: in the harness's own list that prefix is 8 of 22 queries. Over all 294 single-key edits at seed 11: mean 1.86 of 15 re-derived, max 3; 3,113 lookups vs 12,784 from scratch (24%). Seed 23: 212 edits, 2,167 vs 7,366 (29%). |
| s2: carried verdicts' cone hashes re-checked | HOLDS | Asserted in the carry path. |
| s2: a missing row is a premise | HOLDS | 5 row insertions where a cone saw none agree; the mutant that drops missing keys is caught. Lean: `Cone.missing_is_a_premise`. |
| s3: 220 rows = 24,090 pairs, 64 subsets | HOLDS (arithmetic) | C(220,2), 2^6. |
| s3: 200 to 220 join computes 4,190 new pairs | HOLDS (arithmetic) | C(220,2) - C(200,2), true of any such join. |
| s3: four registered instances agree with solver.py | HOLDS | Checked at every row-append prefix, full JSON result. The record names them instance_x.json etc.; the repo's fixtures are x, d, e-empty, e-singleton. |
| s3: 121.6 ms vs 1,282.7 ms | NOT REPRODUCED (wall) | Here 6.0 ms vs 690.9 ms on a 6-axis 200 to 220 join. Different machine and a different engine (pairs indexed by difference set, no per-subset rescan). Indicative only. |
| s3: scoped 2-axis join re-measured 3 of 4, "neither zero nor all" | CORRECTED | 3 of 4 is the most any 2-axis join can re-measure: the empty subset is never live because contract configurations are distinct. It shows nothing about scoping. Replaced by a 2-axis join that re-measures 2 of 4, and a staged 6-axis join that re-measures 24 of 64, every one containing the newly varied axis. |
| s3: saturated join re-measured 0 of 64 | HOLDS | Dense synthetic 200 to 220: 0 of 64; binary 40 to 60: 0 of 64. |
| Gate: PASS | HOLDS for the rebuild | 55 checks. The record's gate could not be run (not here). |

## Added here

- One mutant per engine (reverse dominance skipped; missing keys dropped from
  the cone; supersets of a grown difference set skipped). Each is caught.
- s1: agreement at every append prefix, shuffled join order gives the same
  frontier and the same matrix, withdrawal of frontier members at 0
  evaluations, score change as withdrawal plus join.
- s2: every single-key edit and its revert at two seeds, an edit no cone holds
  (0 re-derived, 0 lookups), 60 chained edits never reset.
- s3: every append prefix of the registered instances, refusal of a changed
  behavior cell as not a join.

## The not-landed list

- Meta-search, 39 configurations: CONVERTED. Build by joins costs 1,482 meta
  evaluations, the same as one full recompute (39 x 38): building saves
  nothing. A 40th configuration joins at 78 meta and 9 score evaluations vs
  1,560. A dominated decoding candidate: 0 rescored, 0 meta evaluations. A
  frontier-entering candidate (3, 8): 0 full rescores, 40 score evaluations,
  2 configurations change measures, 156 meta evaluations. (5, 5), which knocks
  'balanced' off: 12 selections rescored in full, 18 change measures. All agree
  with meta.py's own output.
- Exact assignment enumeration (209,352 of 209,952): UNMEASURED. The closed-loop
  synthesis at 3be6373 records the recomputation (nine-run, six-venue ordering
  instance, bound-map hash e4ded389), but no table or enumerator is in
  software-is-a-closed-loop, software-frontier-is-solvable (307dffc) or the
  project files. Gap: the instance table and its enumerator.
- Solver-dominance bounded searches: UNMEASURED. The only artifact found is
  idol-theses SolverDominance.lean: proofs about bounded fixed points and the
  contract axes, not an executable search. Its measured axes are owed to a
  same-contract run at an Idol compiler seat.
- Emergence family optimization: not touched; no claim.
- Lean forms of the three cone rules: DONE, 13 theorems (lean/), cold gate
  pass, axioms within propext, Classical.choice, Quot.sound; a planted sorry is
  rejected. What they prove: the cone rules of the models (Bool dominance on
  lists; lookup programs; Hma.lean's own live, lambda, mu). What they do not
  prove: that the Python engines implement those models. That link is the
  executed agreement in gate.py, per instance.

## Landing state

Nothing pushed. Local branches only (see the ledger entry). The HMA repo has an
in-flight branch (codex/hma-solver-lean-agreement-20261121, 0f8b8c3, off
63d9d3f) that replaces solver.py and model.py with solve.py and verify.py and
adds an arena; the s3 landing wraps main's solver.py and would need
re-pointing if that branch lands.
