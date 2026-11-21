# Algorithm search over the one hypergraph: claims ledger

2026-11-20. Python 3 (no third-party packages) for every candidate, in
one process per family, on one 4-vCPU container; Lean 4.19.0 for the
proofs. Verdicts: VERIFIED (run or proved here), CORRECTED, REFUTED,
UNMEASURED (with the reason).

## How the space is built

Everything is a record of one append-only log, `out/space.jsonl`, in the
shape of `Canon.Rec` (id, level, colors, premises, head) plus a receipt.
Each line carries the sha256 of the line before it. Components, the
structural constraints, the generated candidates, the traces (by sha256),
the declared objectives (by sha256), every measurement, every verdict and
every validation are records. `report.py` rebuilds every number below
from the log alone and fails if the chain is broken.

Candidates are generated, not hand-listed: each family's component axes
are multiplied out, then canonicalized by the constraint records (a
readiness-check component does not apply to counter or watch triggers).
A candidate generated twice, or a reused seed that the product also
produced, is two derivations of one term and counts once.

- 57 candidate terms: 54 from component products, 3 from the stop-rule
  delta parameter. 5 reused seeds collapsed onto generated terms (the
  proved counter worklist, PR 19's frontier-first Chebyshev act and its
  exhaustive stop, the joint-plan fold, and the threshold stop).
- 56 measured. `cand:c/stop=threshold` is measured only through its three
  delta parameters.

Families: (a) incremental closure, 16; (b1) static front, 3; (b2) joint
plans, 4; (b3) selection, 10; (c) stop rules, 4 + 3 parameters; (d)
incremental re-scoring, 3; (e) weight meta-search, 10; (f) binding
resolution, 4 (added after Chris's 10:00Z message).

## Contract

Declared in `OBJECTIVES.json` (sha256 be3ac745) before the contract run.
Same inputs, same reference check, same machine, same run for every
candidate of a family. Pareto down-selection uses only the declared
objectives; wall-time medians within 10% or with overlapping quartiles
are ties; an incorrect candidate is removed whatever else it scores.

Disclosed deviations: a smoke run of all families (one repeat) came
before the contract run. After it, two things changed: best-first's
operation count was raised to charge one look per option (it had been
charged 1), and a second unsupportedness column (zero weights allowed)
was added as reported-only. Neither changes which objectives select.
The first held-out attempt crashed at its verdict step (a local module
named `select` clashed with Python's); its records stay in the log under
`attempt:heldout-1` and are superseded key by key by the second attempt.

Traces. Dev: the 1,641-record estate log and the 3,630-record idol-lib v2
log (`examples/worklist`, as proved against in c49c546); idol-eyes
campaigns 1 to 4 raw runs. Held-out, built only after the
`downselect:dev` record: the idol-lib v2 reference graph at master
578b8b3 (444 definitions, one record each, premises = every candidate of
every reference, roots = definitions with no references; it has
reference cycles, so 343 of 444 derive), the v2 log with libraries
interleaved round-robin, and idol-eyes campaigns 5 and 6 (new tasks, new
driver). idol-map carries the color disqualified everywhere (CLAIMS.md
E3, replay) and is filtered before any front.

Controls, on every closure survivor over all four traces: every record
twice, every premise twice, disqualified and level-1 records that would
otherwise derive, reversed order, three fixed-seed shuffles (28 inputs
per candidate). Decision controls: Chris's (0,4), (4,0), (3,3); all-equal
vectors; duplicate options.

Rerun: `python3 run_search.py dev out IDOL_LIB && python3 downselect.py out/space.jsonl dev && python3 heldout.py out IDOL_LIB && python3 report.py out/space.jsonl`. Gate: `proof/check.sh`.

## Results

| # | Claim | Numbers (from the log) | Verdict |
|---|---|---|---|
| A1 | Counter worklist (proved, c49c546) survives incremental closure | dev premise ops 4,299 (estate) and 6,280 (v2); wall 2.8 and 7.2 ms; peak 459 and 1,021 KiB. Held-out 1,507 (refs) and 6,280 (v2-rr). Correct at every prefix on 2 dev, 2 held-out and 28 control inputs | VERIFIED |
| A2 | New variant: watched-premise closure (two-watched-literal idea, Moskewicz et al. 2001, adapted to Horn rules) survives, with fewer premise ops than counter | dev 2,652 and 4,914 ops (38% and 22% fewer); wall 2.8 and 7.0 ms (tie); peak 572 and 1,277 KiB (25% more). Held-out 662 and 4,914. Correct on all 32 inputs | VERIFIED (correctness by test, not by proof) |
| A3 | Watch's op count does not depend on append order | 662 (refs) and 4,914 (v2-rr) in forward, reversed and all three shuffles; counter ranged 1,507 to 1,570 and 6,280 to 9,828 | VERIFIED on these traces; not proved |
| A4 | Counter and watch are each Pareto-optimal; neither dominates | watch wins ops, counter wins memory, wall ties | VERIFIED |
| A5 | Dedup choice | No premise repeats in any dev or held-out trace, so on/off measured the same ops; the dev down-select dropped watch with dedup on and kept watch with dedup off on noise-level wall and memory. Under the duplicate-premise control watch without dedup doubles (9,828 on v2-rr) while counter with dedup stays at 6,280. counter on/off split on held-out by 3 KiB | CORRECTED: the dev data never exercised duplicates, so the dedup verdicts are noise. Prefer dedup on where duplicates can occur |
| A6 | Naive scratch, naive rounds and semi-naive delta are dominated | scratch 7.8M and 13.0M ops (1.3 and 2.5 s); rounds 0.40M and 1.48M (149 and 526 ms); delta 6,039 and 8,518 ops but 870 and 1,905 KiB | VERIFIED |
| B1 | Static front: sort-then-filter (Kung, Luccio, Preparata 1975) and the online archive survive; pairwise is dominated | dominance tests over 4 campaigns: sortfilter 1,992, archive 3,291, pairwise 31,402; wall tie between the first two. Held-out 769 vs 896 | VERIFIED |
| B2 | Joint plans: per-factor pruning before composing is what matters | brute with pruning 4,927 ops on 23 brute-feasible instances; fold with pruning 89,712 ops on all 32 (includes plans beyond 100,000, where brute cannot run); unpruned brute 5.68M ops, 6.5 MB peak. Held-out correct 12/12 and 22/22 | VERIFIED. Prior work: multi-objective dynamic programming (Hansen 1980) |
| B3 | Selection (narrow contract: a 10-step weight grid) | lex over the 24 objective orders, applied to the front, survived (coverage 12.35 of 17 instances vs 8.2 to 11.6). Front-first dominated direct for every rule (same picks, 6 to 120 times fewer evaluations) | VERIFIED for front-first over direct. REFUTED for lex as a general selector: on Chris's counterexample it reaches 2 of 3 front points and misses (3,3) |
| C1 | Stop rules on separable objectives | best-first (per-factor minima) is optimal and certified in 8 to 25 looks; bound-certified 18 to 9,534; exhaustive 16 to 4,096. Thresholds survive only as cheaper and uncertified: delta 0.2 took 2 to 85 looks with regret up to 0.197 | VERIFIED. Best-first's win is the separability of the weighted-sum score (`fmin_le_plan`, `fmin_plan`); it does not carry over to a Chebyshev score |
| D1 | Incremental re-scoring beats cold | after every append: archive 3,291 dominance tests vs 314,184 (cold sortfilter) and 4.16M (cold pairwise); identical fronts at every prefix, also reversed (6/6) | VERIFIED, proved: `mem_arch`, `arch_perm` |
| E1 | Weight meta-search: Chebyshev weights solved per front point reach the whole front, unsupported points included | coverage 17/17 dev and 8/8 held-out instances; 905 evaluations total (dev); reached 55 grid-unsupported points. Weighted-sum grids reached 0 unsupported at 10 or 20 steps. Chebyshev grids reached 0 and 2. Epsilon-constraint 20 at 126,445 evaluations | VERIFIED, proved: `cheb_target` (every point not beaten in all coordinates is a minimizer of its aimed weights). Prior work: Bowman 1976; Steuer and Choo 1983 |
| E2 | Augmented Chebyshev with fixed rho = 1e-4 and solved weights | coverage dropped to 0.6 on some instances (14.37 of 17) | VERIFIED as a loss. It reaches only properly efficient points within the trade-off bound rho sets (consistent with Steuer and Choo) |
| E3 | Chris's counterexample (0,4), (4,0), (3,3) | solved Chebyshev reaches all 3; no positive weighted sum picks (3,3) (`chris_ws_miss`); the aimed weights make it a minimizer (`chris_unsupported_reached`) | VERIFIED, proved |
| E4 | Identical vectors | all-equal and duplicate sets: solved Chebyshev reaches every distinct vector (coverage by id 1/6 and 3/5) | VERIFIED limit: no scalarization separates identical vectors |
| F1 | Binding resolution | name match: 57 lexically unsound edges (to nested locals outside the referrer's scope), 95 ambiguous references. Scope-visible: 0 unsound, 79 ambiguous, 37 unresolved. Nearest binding: 0 unsound, 50 ambiguous, 37 unresolved. jq `shape` reach (reported only): 56, 56, 54 | The declared objectives were wrong: the "enclosing link only" resolver drops every reference and so scored 0 on all three. It "survived" vacuously. REFUTED as a selection; the measured counts stand. Correctness is UNMEASURED: no compiler-resolved bindings are reachable here |
| F2 | Chris's 48-to-3 sensitivity figure | Not reproduced: this encoding counts 56 dependents under name matching and 0 under the enclosing link | UNMEASURED: different encoding; Chris's script is not in this project |
| X1 | software-is-reversible results (5 vs 10 bits; front over 24,576 designs; 1,760 vs 3,488 extensions; weights are not intent) | recorded as `ext:` records colored unverified, with Bennett 1989, Revolve (Griewank and Walther 2000) and rr (O'Callahan et al. 2017) as `prior:` records | UNMEASURED: the bundle did not reach this project |

## Proofs (`proof/AlgoSearch.lean`; gate `proof/check.sh` cold, exit 0, 246 axiom printouts, 20.7 s; no sorry; axioms within propext, Classical.choice, Quot.sound)

- `mem_arch`: after any arrivals, the archive holds exactly the Pareto front of what arrived; `arch_perm`: the arrival order does not change it.
- `fmin_le_plan`, `fmin_plan`: for an additive score over independent factors, per-factor minima form a plan and no plan scores lower.
- `cheb_target`: aimed Chebyshev weights give the target the score K and every point not beating it everywhere at least K. Ties are not excluded; the runs break them with a 1e-9 offset.
- `chris_unsupported_reached`, `chris_ws_miss`.
- Counter worklist: `Worklist.mem_run`, `run_eq_clos`, `mem_prefix` (c49c546, merged into this branch, rebuilt cold here).
- Not proved: the watch variant's correctness and its order-invariant op count; sort-then-filter's correctness. Both are checked by test only.

## What this does and doesn't establish for the hypotheses

- H1 (incremental, compounding): established for the derived closure and for the Pareto front: both are maintained exactly after every append, at cost bounded by what was appended (counter: proved; archive: proved; watch: tested), with no drift across orders. Not established: compounding (an increment revealing more than its own cone), any measure of intelligence, or concurrency.
- H2 (weights map deterministically into views): a positive linear weight map cannot reach every Pareto point (E3, proved), and grids of linear or Chebyshev weights reach few unsupported points. Solving the weights per target point from the front reaches all of them (E1, proved up to ties). So the map works when the front is solved first and the weights are derived from it, not when the weights are searched blindly. Not established: learned (model) weights.
- H3 (drift excluded): every number here rebuilds from one hash-chained log. Drift found anyway: one objective set rewarded doing nothing (F1), and the dev data hid the duplicate-premise case (A5).

## Correction, 2026-11-20 11:35Z (two Codex review findings on PR 7, both confirmed)

- B2 overstated held-out correctness. The held-out "22/22 correct" for the pruned fold rested on "cross-agreement", and on the 10 instances too large for brute force only the fold ran, so it was compared with itself. On the other 12 the reference was the agreement of two independent algorithms (pruned brute force and the fold), not brute force as my review reply said. `run_search.py` now computes its own reference when the unpruned brute force did not run: brute force where it fits, else the unpruned fold (which shares the merge code but not the pruning; recorded as basis). Re-run (`attempt:heldout-3`): 12/12 against brute force, 10/10 against the unpruned fold. Verdict for B2: VERIFIED for the 12; the 10 are checked against a partly shared implementation, not an independent one.
- B3's counterexample numbers did not come from the pipeline. `decision_controls` never measured `b3` candidates; the lex coverage on Chris's counterexample was appended by a one-off script. `heldout.py` now measures them. Re-run reproduces it: lex reaches 2 of 3 points on (0,4), (4,0), (3,3) and misses (3,3); on duplicates it reaches 2 of 3 distinct vectors (by id, 2 of 5). Verdict unchanged: REFUTED as a general selector.
- A5 again: in the re-run, counter with dedup off held on held-out data, where attempt 2 said it lost by 3 KiB. The dedup verdict flips between runs, which confirms it is noise.
