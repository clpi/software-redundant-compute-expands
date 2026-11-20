# Claims audit, 2026-11-20

Adversarial audit of every quantitative and proof claim this project reported from Nov 17 to Nov 20 09:40Z. Each claim gets one row: where it was stated, the pinned commits, the command that reproduces it, the rerun result here, a verdict, and what was unfair about the comparison.

Verdicts:
- **VERIFIED**: rerun here, same result.
- **CORRECTED**: the number or its meaning was wrong; the right one is given.
- **REFUTED**: the claim does not hold as stated.
- **UNMEASURED**: could not be rerun here; the reason is given.

No number below was copied from an earlier report. Every number in the "Rerun here" column comes from a run in this audit, with its raw output under `audit/` (paths below are relative to `/mnt/project-files/claims-audit/`).

## Machine and environment

One cloud container: 4 vCPU Intel Xeon @ 2.30 GHz, Linux 6.18.44 x86-64, Python 3, Lean 4.19.0 (release tarball from GitHub, commit 6caaee842e94), Chromium 157.0.8103.78 `chrome-headless-shell` (the campaigns used Chromium 153.0.8010.0), Playwright 1.48.0 for Python.

This session cannot read clpi/idol, so there is no Idol compiler and no Idol binary here. Any claim that needs Idol to run is UNMEASURED here. Its raw files were checked for internal consistency, and the comparator side was rerun.

## Summary

| Verdict | Count |
|---|---|
| VERIFIED | 8 |
| CORRECTED | 9 |
| REFUTED | 2 |
| UNMEASURED | 9 |

The worst problems:
1. **The idol-eyes "200 to 300 times faster" figure measures "no browser" against "a browser", not a better engine.** The Idol face fetches HTML and parses it. The comparators launch Chromium on every cold run, then lay out, render and run script. Here, launching and closing Chromium took about 400 of Playwright's 480 to 640 ms. A 150-line Python standard-library script doing the same work as the Idol face finished each static task in 1.5 to 3.0 ms in-process (p50), the same range as Idol's reported 1.7 to 3.1 ms warm. That was not measured in the same run.
2. **idol-map was admitted over every browser, but it does not do the task.** It replays HTTP requests recorded by an earlier full run and prints the answer it was handed in its input. The recording run is excluded from timing.
3. **The idol-eyes fixtures were written alongside the engine.** All 5 commits that add tasks also add the engine feature that solves them. The script engine accepts a stated JavaScript subset (no loops, object or array literals, template strings, floats, `try` or `new`), and all 3 script fixtures sit inside that subset. "Admits on JS pages" holds for those 3 pages only.
4. **The candidate ranking's top result was a loop variable.** jq `n` (number.id:281) is a local inside `threshold`. 29 of 444 "definitions" are nested locals, and 70 of 827 resolved references point at them. References are matched by spelling, without scope.
5. **The gate dimensions leave out every axis a browser wins.** These are generality (pages not written for the test), JavaScript conformance, rendering fidelity, TLS and real network. The ceiling-aware beat was added (199aa95) after the strict beat was refused. That was disclosed, but it is still a criterion loosened after a failure.
6. **No Lean theorem touches measured reality without a named, unproved premise.** All gates build cold with standard axioms only. Several "proofs" are kernel checks of numbers typed into a data file: for example, `lz4_measured_loss` checks literal timings against each other.

## Ledger

### idol-eyes browser face

| # | Claim as stated | Where | Pins | Reproduce | Rerun here | Verdict | What was unfair |
|---|---|---|---|---|---|---|---|
| E1 | Idol is "200 to 300x faster" than Playwright, Selenium and agent-browser | timeline reports Nov 20; idol-eyes/RESULTS.md | idol-eyes 1dc24f4; campaigns 1 to 5 raw.jsonl | `python3 audit/eyes/recompute.py` (ratios from raw); `python3 audit/eyes/run_audit.py OUT 10` (comparator split) | Raw ratios across campaigns 1 to 5: cold 91x to 374x, warm 14x to 220x. Summaries match raw in all 276 cells. Playwright here: cold p50 479 to 641 ms, of which interpreter plus import is 90 to 103 ms, and launch plus close is 383 to 416 ms. The task itself with Playwright waits takes 47 to 203 ms; with direct DOM dispatch in the same browser, 25 to 71 ms. Same-work stdlib driver: cold 66 to 75 ms (11 ms of that is the bare interpreter), warm in-process 1.5 to 3.0 ms | **CORRECTED** | The range is 91x to 374x cold and 14x to 220x warm, not 200 to 300x. The gap comes from launching and running a browser, not from doing the same work better. Cold cells include Chromium launch for the comparators and a static binary's exec for Idol. Playwright's warm time includes its actionability waits. |
| E2 | Idol "admits on all 9 tasks incl. JS pages" | timeline Nov 20; RESULTS.md campaign 2 | idol-eyes 1dc24f4, protocol/script.id | raw check as E1; source: `sed -n 1,25p protocol/script.id`; `git show --stat cd2ca38 f5a2329 ed549f3 c127965 9aee721` | Raw data agrees (10/10 per cell). Idol not rerun (no compiler). 5 of 5 task-adding commits change the engine in the same commit. The subset excludes loops, objects, arrays, template strings, floats, `try` and `new`. | **CORRECTED** | It holds on 9 owned fixtures written inside the subset. Nothing about JS pages in general was measured. Pages not written for the test: UNMEASURED. |
| E3 | idol-map admitted over each incumbent and their union | RESULTS.md campaigns 2 to 4 | protocol/page.id `replay`, bench/browser/run.py `record_maps` | `sed -n 1058,1095p protocol/page.id` | Replay issues the recorded requests, compares a 28-bit hash of each body, and prints the answer line from its input. Recording runs before timing. | **REFUTED** | Not the same task. It is a cache replay compared with tools that solve the task from scratch. |
| E4 | Gate admission means Idol beats every incumbent | RESULTS.md, decisions.txt | proof/Certify.lean, Union.lean | `sh proof/check.sh` | The gate proofs build cold (1.5 s, exit 0, propext and Quot.sound only). Dimensions: verified, cold, warm, tree memory, CPU, determinism (plus work for Idol only). | **CORRECTED** | The proof is of the decision rule only. The dimension set leaves out generality, conformance, rendering, TLS and network. The ceiling beat was introduced in 199aa95, after campaign 1's strict beat was refused. |
| E5 | Comparator cold latency is about 500 to 900 ms | RESULTS.md | as above | `run_audit.py` | Playwright cold p50 479 to 641 ms, p95 597 to 740 ms on 5 static tasks, 50/50 correct | **VERIFIED** (Playwright only; Selenium and agent-browser not rerun) | Different Chromium build (157 vs 153) |
| E6 | Idol cold 2 to 7 ms, about 1 to 2 MB tree memory | RESULTS.md | campaigns 1 to 5 | needs `make page` with an Idol compiler | Raw is internally consistent; Idol was not run | **UNMEASURED** | No clpi/idol access, no compiler |
| E7 | Campaigns 5 and 6: idol-act admitted on 72 dimensions | ledger/idol-eyes.md 09:17Z and 09:45Z | eyes/action-pipeline fbd482e | as E1 | Not rerun | **UNMEASURED** | Same contract as E1 to E4, so the same caveats apply |

### Lean gates

| # | Claim as stated | Where | Pins | Reproduce | Rerun here | Verdict | Notes |
|---|---|---|---|---|---|---|---|
| L1 | software-redundant-compute-expands gate cold PASS, "189 theorems" | PR 1, commit 0e52b38 | 559f308 | `sh proof/check.sh` in a fresh clone | exit 0, 9.9 s, 189 axiom printouts (174 with axioms, 15 axiom-free). 195 theorem declarations, so 6 are not printed. Axioms: propext, Quot.sound, Classical.choice | **VERIFIED** | Six unprinted theorems are still covered by the escape-token grep, which rejects `axiom` and `sorry` |
| L2 | main after PRs 2 to 4 passes; PR 5 passes | PRs 2 to 5 | 7b51646 (main), 1f9444a (PR 5) | same | exit 0, 220 and 231 printouts, 11 s and 12 s | **VERIFIED** | |
| L3 | idol-eyes certification proofs build cold | PR 18 | 1dc24f4 | `sh proof/check.sh` | exit 0, 29 theorems printed, propext and Quot.sound only | **VERIFIED** | |
| L4 | idol-lib Lean space cold pass, 53 s | ledger/merge-and-qualify.md 08:45Z | f9f9de2; PR 20 head 1541349 | `sh space/check.sh` | exit 0 in 57 s at f9f9de2 and 117 s at 1541349; data file regenerated without drift | **VERIFIED** (pass; time is machine-dependent) | The 578b8b3 merge (3 min 26 s) was not rerun |
| L5 | candidate-space builds, standard axioms only | candidate-space/RESULTS.md | project folder lean/ | `lake build layers` | exit 0, 63 s | **VERIFIED** | |
| L6 | The theorems are "proofs over the behavioral hypergraph" | idol-lib PR 18, space README | f9f9de2 | `python3 audit/lean/theorem_scan.py` | 11 of 33 (f9f9de2) and 13 of 34 (1541349) idol-lib space theorems are `decide` checks of literal data in generated Data.lean (for example `def_count : defs.length = 444`, `lz4_measured_loss` compares typed-in timings). software-redundant-compute-expands: 18 of 201; candidate-space: 5 of 138. 4, 3 and 6 theorems hold by `rfl` or `simp`. | **CORRECTED** | These are checks of a generated data file, and of numbers typed by hand in the timing case. They are correct but are not general theorems, and they certify nothing about how the numbers were measured. |
| L7 | Results such as "Pareto optimal" and "admitted" are proved | Resolve.lean, Certify.lean, ActionVector.lean | as above | read the statements | Every link from a theorem to real behavior goes through a named premise. These are antitone cost, cost-model fidelity, `up`-map fidelity, faithful score normalization, same-contract measurements, and checker soundness. Resolve's Pareto optimality is over a one-dimensional chain, where the finest affordable level is the only possible optimum. | **CORRECTED** | Proved: the rules. Not proved: that the inputs describe reality |

### Redundant compute (gap register)

| # | Claim as stated | Where | Pins | Reproduce | Rerun here | Verdict | Notes |
|---|---|---|---|---|---|---|---|
| R1 | G1: symbol 0, content 265 (173 groups), joined-name 311 (208/519) | redundant-compute/RESULTS.md | idol-lib 4652833, 4b2d5f8, f9f9de2 | `python3 audit/rc/canon_measure.py IDOL_LIB 4652833,4b2d5f8,f9f9de2` | Identical to the recorded JSON except one pin label ("pr18" vs f9f9de2) | **VERIFIED** | The three pins carry identical graphs, so this is one measurement, not three. Content-level behavior duplicates are repeated test inputs. |
| R2 | G6: 0, 4,281, 4,602, 4,602 redundant records | same | 69ee40e, 4652833, 4b2d5f8, f9f9de2 | `python3 audit/rc/record_layer.py IDOL_LIB 69ee40e,4652833,4b2d5f8,f9f9de2` | identical | **CORRECTED** (meaning) | The 0 at 69ee40e is vacuous: that pin has no graphs/ directory. 4,281 is universal.json storing joined.json again, a file copy rather than redundant compute. |
| R3 | G2: yield 2.93, 2.47, 1.75 at 5, 20, 50% | same | traceability graph 8f6a1280 | `python3 trace_yield.py graph.json` | not rerun | **UNMEASURED** | That graph's repository isn't reachable from this session |
| R4 | G3: premise-closed runs, 9 of 9 | same | 8f6a1280 | same | not rerun | **UNMEASURED** | same |
| R5 | G4: implication 1 | same | b14fc92 | `impl1.py` | not rerun | **UNMEASURED** | Pin not reachable |
| R6 | PR 3 and PR 4 controls: 160 fronts match, 6,561 plans, 1,771 vs 2,835 relaxations, oracle agreement | PRs 3 and 4 | 7b51646 | `python3 examples/action-vector/action-experiment.py`, `coalitions.py`, `examples/closure-worklist/replay.py`; `python3 -m unittest test_action_support` | Rerun output equals the committed receipt for all three; unit test OK | **VERIFIED** | Synthetic fixtures, as the PRs say |

### Candidate ranking

| # | Claim as stated | Where | Pins | Reproduce | Rerun here | Verdict | Notes |
|---|---|---|---|---|---|---|---|
| C1 | Pareto front is one candidate, jq `n`; idol-eyes first at position 993 of 1,396 | candidate-space/RESULTS.md round 2 | idol-lib 4dee231, idol-eyes 036df3b, project-folder page.id and certify.id | `python3 audit/cand/gen_estate2_audit.py ...; lake build layers; .lake/build/bin/layers` | Reproduces: layer 1 jq `n` [1,2,1,1,50,0], 32 layers, position 993 of 1,396 | **REFUTED** (meaning) | `n` is a loop-local in `threshold`. 29 of 444 definitions are nested locals, and 70 of 827 single-candidate references resolve to them. References are matched by spelling, without scope. |
| C2 | (correction) top-level only: layer 1 jq `shape`, 1,272 candidates, idol-eyes from layer 23 | ledger/merge-and-qualify.md 09:35Z | same inputs, nested definitions removed | `TOPLEVEL_ONLY=1 python3 audit/cand/gen_estate2_audit.py ...` then layers | Layer 1 jq `shape` [1,2,1,1,39,0]; 29 layers; idol-eyes first at layer 23; best idol-eyes position 885 of **1,270** (the other run said 1,272; one idol-eyes candidate differs at layer 25, which traces to the unpinned page.id input, C3). Output 11478ecbe8f9df4b | **CORRECTED** (1,270, not 1,272) | Generated independently of the other thread's gen_estate3_toplevel.py. References are still matched by spelling without scope, so `shape` leading is not yet trustworthy either. |
| C3 | Inputs pinned | RESULTS.md | project-folder idol-eyes/page.id | regenerate | Regenerated estate has 2,325 records against the reported 2,299, because page.id in the project folder was later overwritten in place. The ranking still reproduces. | **CORRECTED** | Inputs were not pinned by hash. Round 2's exact estate can no longer be rebuilt. |
| C4 | Scores rank work across areas | RESULTS.md | as C1 | read Layers.lean, Space.lean | "supply qual:X" and "observe X" are the same work counted twice (layer 2 is 12 copies of `n`). `unblocks` counts registered demands, so the cross-area order (444 idol-lib demands against about 11 for idol-eyes) reflects how many demands were declared | **CORRECTED** | Partly disclosed in RESULTS.md |
| C5 | 1,398 candidates on master 0052f16 and main 1dc24f4 | ledger 08:45Z | those pins | as C1 | not rerun (C1 used other pins) | **UNMEASURED** | Superseded by C2 in any case |

### Elsewhere

| # | Claim | Where | Verdict | Reason |
|---|---|---|---|---|
| N1 | n-body: Idol's C route beats clang (kernel about 24 ms vs 33 ms) | timeline Nov 17; idol PRs 2284, 2293 | **UNMEASURED** | No clpi/idol access. As stated it times the kernel only, and the C route runs Idol's emitted C through a C compiler. Startup, text size and bss lost at the time. "Beat clang" should read "Idol-emitted C, compiled by a C compiler, ran the kernel faster than the reference C". |
| S1 | software-is-incrementally-safe PRs 9 and 11 | merges Nov 20 | **UNMEASURED** | Repository not reachable from this session; its earlier audit (software-audit/REAUDIT.md) built it at 10:01Z Nov 18 |
| I1 | idol PRs 2356, 2357, 2358 merged and measured | ledger 08:45Z | **UNMEASURED** | No clpi/idol access |

## Chris's hypotheses (stated 2026-11-20 09:28Z)

All three have status **HYPOTHESIS**. Nothing in this ledger proves any of them, and none has been refuted.

### H1. Intelligence is incremental and compounding

Intelligence can be handled and even produced deterministically, structurally and incrementally. Each addition to one append-only, eventually consistent hypergraph compounds, so a short clarification can reveal many connections and nothing has to be carried between chats.

- Supporting (within their models): Canon append monotonicity and order invariance (L1); `Intent` no-fork composition; `incremental_eq_scratch` (candidate-space, PR 4 closure); PR 5's set-union convergence at named cuts (L2); the PR 4 waiter index, which visited 512 waiters against 659,206 rule checks for recomputation (R6, synthetic).
- Limiting: PR 5 detects a missing tail only at a trusted named cut, so omission without a cut is undetectable; the mixed-premise control shows the closure of a join is not the union of closures, so compounding needs joint recomputation; R1 shows that cross-pin "increments" can be no change at all.
- Untested: any compounding measured on real work rather than synthetic logs; any measure of "intelligence".
- Refutation test: on a real project log, find an appended record that changes an earlier derived answer without being a retraction, or show that the cost of recomputing after k appends grows faster than the appended cone. Either would refute "incremental".

### H2. Weight vectors map deterministically into hypergraph views

Structured weight vectors map structurally, parametrically and deterministically to semantic and action vectors, and so into hypergraph views across resolutions, and can be rewritten incrementally.

- Supporting: `reweight` and `rank_perm` (Search.lean): reweighting changes order, never front membership; `stop_invariant_under_reweight` (PR 3); deterministic tie-breaking (`rank_sorted`).
- Limiting: Chris's own counterexample in PR 3 (coalitions.json, rerun here): with 1,024 weight pairs checked, positive linear weights pick only 2 of 3 Pareto-optimal plans (`weighted_winners` a and c). proof/Plan.lean `weights_miss` on eyes/action-pipeline states the same. So weights cannot be the selector: the front has to be solved apart from them, and then weights or Chebyshev scalarization pick within it.
- Untested: any learned weights (model weights) mapped into the graph; determinism across machines for weight-derived views.
- Refutation test: exhibit two weight vectors that the mapping sends to the same view while their behaviors differ on a held-out input, or a Pareto-optimal plan that no admissible scalarization reaches. The second already holds for linear weights.

### H3. Idol is the native one-hypergraph harness, and drift is excluded by construction

- Supporting: one append-only record log with views as projections (Canon); levels appended and reconciled on one graph (idol-lib PR 20, per its ledger entry; not rerun here).
- Limiting: this audit found drift. The project-folder page.id was overwritten in place, so round 2's estate cannot be rebuilt (C3). Two threads reported different candidate counts from different unpinned inputs (C1, C5). The reference resolver matches names without scope (C1). Every proof is conditional on named premises about how records were produced (L7). Drift is excluded inside the model, not in the tooling that feeds it.
- Untested: Idol as the harness itself. Every run in this audit used Python and Lean, because no Idol compiler is reachable here.
- Refutation test: rebuild every reported number from the record log alone, by hash, with no other inputs. Any number that cannot be rebuilt is drift. Today C3 and the round 2 estate fail this test.

## Reproducing

Everything here was run from fresh clones. Scripts and raw outputs are under `audit/`:

- `audit/eyes/`: `stdlib_driver.py` (same-work baseline), `stdlib_warm.py`, `pw_decompose.py` (Playwright cost split), `run_audit.py`, `recompute.py`, raw.jsonl (189f9f23e8575dcd), summary.json (63896840e1f04a99), stdlib_warm.json (8d8ece9b424b87d4).
- `audit/rc/`: rerun G1 (33279795c6b75f0a) and G6 (307f73baa20d1068) outputs plus the unchanged scripts.
- `audit/cand/`: `def_audit.py`, `gen_estate2_audit.py` (adds `TOPLEVEL_ONLY`), layer outputs.
- `audit/lean/`: `theorem_scan.py`, gate logs for every pin above.

To rebuild the comparator side: `EYES=<idol-eyes clone> CHROMIUM=<chrome-headless-shell> python3 audit/eyes/run_audit.py OUT 10`.
