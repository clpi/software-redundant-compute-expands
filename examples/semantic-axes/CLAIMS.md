# Semantic axes over the candidate space: claims ledger

2026-11-20. Ask: Chris 10:45Z, find where any approach Pareto-dominates on
semantic axes (visibility, work saving, compositionality, and so on), weight
that space so it stays searchable, implement and prove clear candidates only
after empirical tests pass, all on the hypergraph, no benchmark gaming.

Same contract, log discipline and Pareto rule as `examples/algorithm-search`
(PR 7). Python 3, one container, Lean 4.19.0. Verdicts: VERIFIED, CORRECTED,
REFUTED, UNMEASURED.

## Axes (`AXES.json`, declared before scoring)

Six semantic axes, each with an operational measure, a do-nothing control,
a gamed control and a refutation test: visibility (an independent checker
accepts a witness for every result), work saved (against cold recomputation,
counted only when every prefix is correct), compositionality (two states
built on halves merge into the whole), reversibility (the last append undone
exactly), order invariance, robustness. Plus the classic axes: ops, wall time,
peak memory.

An axis is admitted for selection only if, on every input, the do-nothing
control scores 0 and every gamed control scores no higher than the best honest
candidate. All 12 axis/family pairs passed on dev and again on held-out data.

Two amendments, both disclosed in the log:
1. After a single-repeat smoke run: compositionality, reversibility and order
   invariance had been divided by the candidate's own cost, so padding an engine
   with extra work raised its score. They now use common baselines.
2. After the held-out run: under the common baseline, a "merge" that rebuilds
   from empty with a cheaper engine scored above 0 (watch: 0.21). Compositionality
   is now `correct * (1 - merge cost / min(same engine's whole build, common
   baseline))`, re-scored from the raw counts already in each receipt (no
   candidate re-run), and every rebuild merge is checked to score exactly 0.
   Because this came after the held-out run, the held-out confirmation of the
   compositionality axis is weaker than the others.

## Space

67 candidate terms: closure 32 generated (engine counter, watch or rounds x
undo none, journal or snapshot x witness on or off x merge propagate or
recompute; rounds has no journal) plus 4 controls (null, lookahead, firsthead,
lastwitness); front 21 generated (archive or cold x undo none, residual,
snapshot or recompute x witness off, on or repoint; cold has no residual) plus
2 controls (null, allfront); joint plans 2; selection 6. Current approach (PR 7 survivors) entered as
second derivations of their terms.

Dev: estate, v2, idol-eyes campaigns 1 to 4. Held-out (built after
`downselect:ax-dev`): refs, v2-rr, campaigns 5 and 6.

Rerun: `python3 axes_run.py dev out && python3 fix_joint.py out/space.jsonl dev 1,2,3,4 && python3 axes_select.py out/space.jsonl dev && python3 axes_heldout.py out IDOL_LIB && python3 rescore.py out/space.jsonl && python3 axes_select.py out/space.jsonl dev && python3 axes_select.py out/space.jsonl heldout && python3 axisfront.py out/space.jsonl dev && python3 axisfront.py out/space.jsonl heldout`. Gate: `proof/check.sh`.

## What dominates the current approach

| # | Claim | Numbers | Verdict |
|---|---|---|---|
| S1 | The journaled counter (undo by replaying a per-append change log backwards) dominates the current counter on all six semantic axes | dev: reversibility 0.997 and 0.996 vs 0; same premise ops (4,299 and 6,280), same visibility, compositionality and order invariance. Held-out: reversibility 0.992 (refs) and 0.955 (v2-rr) vs 0. Cost on the classic axes: wall about 5 to 15% higher on dev, peak memory 0 to 4% higher | VERIFIED on dev and held-out. It does not dominate on all nine axes: it pays in wall time and memory |
| S2 | The journaled watch closure dominates the current watch closure on all six semantic axes | dev reversibility 0.998 and 0.996; held-out 0.995 and 0.955; ops identical (2,652, 4,914, 662) | VERIFIED; same classic-axis cost as S1 |
| S3 | An archive that keeps what each insert removed (the retained residual) dominates the current archive on the semantic axes | undo exact at every tested arrival (reversibility 0.997 to 1.0 dev, 0.998 and 0.999 held-out) vs 0; same dominance tests (3,291 dev, 896 held-out). With witnesses: visibility 0.77 to 1.0 (witnesses go stale when their dominator is later removed); re-pointing them reaches 1.0 on every input for 72 more tests on dev (2%) | VERIFIED; proved: `undo_residual`, `ins_accept`, `ins_reject` |
| S4 | Cold sort-filter recomputation is dominated on every axis | by every archive variant without snapshot, dev and held-out: dominance tests 3,291 vs 314,184 dev; reversibility and compositionality 0 for cold under the common baseline | VERIFIED |
| S5 | Selection picks compose only under a fixed frame | pick(A u B) = pick of the two halves' picks for 100% of weight vectors with a fixed normalization frame (weighted sum, Chebyshev, augmented Chebyshev), and 79%, 58% and 62% on average (worst 44%, 30%, 30%) when each subset is normalized on its own data | VERIFIED: normalize once, globally, or picks stop composing |
| S6 | Merging two closure states by propagation is correct and cheaper than rebuilding | correct on every dev and held-out input for every engine (0 incorrect propagate merges). Saving under amendment 2: counter 0.25 (v2) to 0.8 (estate); watch 0.20 to 0.37 on v2; 0 for counter on v2-rr, where its merge cost 7,589 ops against a whole build of 6,280 | VERIFIED correct (spec proved: `merge_spec`). The saving depends on the trace and is a loss for the counter on v2-rr |
| S7 | Sequential versus tree-shaped fold for joint plans | both correct on all 32 dev instances (46 against brute force, 18 against the unpruned fold); the tree fold lost on held-out ops and dropped out | VERIFIED; no change to the current approach |

## The space as one searchable front

| # | Claim | Numbers | Verdict |
|---|---|---|---|
| F1 | Appending an axis or a trace updates the front over candidates exactly, without a cold recompute | after every one of 18 (closure) and 32 (front) column appends, the incremental front equals a cold recompute; scalar comparisons 3,650 vs 34,740 and 2,240 vs 21,475. Held-out: 896 vs 12,208 and 172 vs 1,170 | VERIFIED; proved: `front_ext` (no front point is lost when a coordinate is appended) and `dom_ext_le` (only previous weak dominators need re-checking) |
| F2 | Appending a candidate updates it exactly | equal to cold after every candidate: 2,000 vs 34,679 and 746 vs 7,255 comparisons | VERIFIED; proved: `mem_arch` (PR 7) |
| F3 | Every front point is reachable by weights solved from the front | 24 of 24 and 11 of 11 dev front points, 18 of 18 and 6 of 6 held-out, each picked by its own solved Chebyshev weights; the weights are appended as weight-coloring records on the candidate's edges | VERIFIED; proved up to ties: `cheb_target` (PR 7). The front here uses exact values, not the 10% wall-time tie rule, so it is larger than the down-select's survivor set |

## Losses and limits

| # | Finding | Verdict |
|---|---|---|
| L1 | The firsthead gamed control (witness = first record with that head) is indistinguishable from the honest counter on every trace here, because every head has exactly one producing record. It survived the dev down-select, and on held-out data it "dominated" the current counter on all nine axes through wall and memory noise | The visibility axis cannot detect this gaming on these traces. A trace where heads have several producing records is needed |
| L2 | Variants that differ only in a component that changes nothing (merge=recompute on an engine whose merge is never exercised for ops, dedup on traces with no repeats) survive or drop by wall-time noise under the 10% tie rule | Noise, not a finding |
| L3 | Snapshot undo is exact but costs 4.9M to 33M ops (copying state before every append) against 4,299 to 6,280 | Dominated on work saved; survives only where nothing else scores 1.0 on reversibility |
| L4 | Work saved is a monotone rescaling of ops within one family and trace; it adds the correctness gate and a cross-family baseline, nothing else | Not an independent axis inside a family |

## UNMEASURED

- Binding resolution on every axis: no compiler-resolved bindings exist here to check a witness against.
- Stop rules: no new axis; their certified flag (PR 7) is already their visibility.
- Any axis from "etc." without an operational measure here: semantic coherence, intent fidelity, generality to pages not written for the test.
- Lean proofs of the journaled counter and watch undo; the archive's residual undo is proved, the closure journals are tested only.
- Native timings: all wall times are Python.

## Proofs (`proof/Axes.lean`; gate cold, exit 0, 252 axiom printouts, no sorry, axioms within propext, Classical.choice, Quot.sound)

`dom_ext_le`, `front_ext`, `front_union` (archives merge exactly), `undo_residual`, `ins_accept`, `ins_reject`, `seeded_eq`, `merge_spec` (closure merge by seeding equals the closure of the whole log).

## For H1 and H2

- H1: incremental and compositional maintenance holds for closures and fronts with exact undo and exact merge; appending axes, traces or candidates updates the decision front exactly. Compounding is still not shown.
- H2: weights solved from the front reach every front point, and the space stays solvable as axes are appended. Picks only compose under a fixed normalization frame (S5), so a weight-to-view map must fix its frame.
