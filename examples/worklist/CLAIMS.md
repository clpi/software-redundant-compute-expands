# Worklist closure: claims ledger

2026-11-20. Lean 4.19.0, no dependencies. Proof in `proof/Worklist.lean`
(naive baseline `proof/Closure.lean`, taken unchanged from the
candidate-space work). Measurement in this folder.

Scope: a derived-closure optimization. It computes exactly the
derivable set of `viewC ch L r q` with less work. It is not the
canonical behavioral hypergraph and not the action Pareto search.
The algorithm is prior art: the counter-and-watch-list forward
chaining of Dowling and Gallier (1984), also the core of semi-naive
Datalog evaluation. What is new here is the proof against the exact
`viewC` semantics, incrementally, at every append prefix of the one
log.

Rerun: `./run.sh` (Lean 4.19.0 `lean` and `leanc` on PATH). Gate:
`proof/check.sh`. Verdicts: VERIFIED (proved, or run and checked here),
CORRECTED, REFUTED, UNMEASURED.

## Proved (gate cold green, no sorry, axioms within {propext, Classical.choice, Quot.sound})

| Claim | Theorem | Verdict |
|---|---|---|
| After any log, the derived set is exactly derivability in `viewC ch L r q` | `Worklist.mem_run` | VERIFIED |
| Same members as the naive closure `Closure.clos` | `Worklist.run_eq_clos` | VERIFIED |
| At every append prefix | `Worklist.mem_prefix` | VERIFIED |
| Incremental: state of `L ++ M` is the state of `L` continued over `M` | `Worklist.run_append` | VERIFIED |
| Continuing the stored state is exact, including rules admitted before the append that only appended records complete | `Worklist.mem_continue`, `Control.pending_then_fire` | VERIFIED |
| Queue empties within the fuel `nu`, and `nu` ≤ 2 × admitted rules (finite term bound: every derived term is the head of an admitted rule) | `Worklist.drain_empty`, `Worklist.nu_le` | VERIFIED |
| Each derived term is derived once and dequeued exactly once | `Worklist.nodup_run`, `Worklist.pops_eq` | VERIFIED |
| Admitted rules are exactly the records `viewC` keeps | `Worklist.rules_run` | VERIFIED |
| Total waiter visits ≤ total distinct premises of admitted records, whatever the append order | `Worklist.visits_le`, `Worklist.scans_run` | VERIFIED |
| Duplicate premises count once | `Worklist.prem_nodup`, `Worklist.mem_prem`, `Control.duplicate_once` | VERIFIED |
| Premise identity is the level-`r` class (two level-0 terms merged at level 1 count once) | `Control.merged_premises` | VERIFIED |
| A record failing the color test, or finer than the view level, never fires and is not derivable | `Control.filtered_color`, `Control.filtered_level` | VERIFIED |

Every premise is a hypothesis of the stated theorem; the invariant
`Worklist.Inv` lists every maintained fact as a named field.

## Measured (`run.txt`, `results.jsonl`)

Same contract on every run: same log, level `r = 0`, color test `live`
(drops disqualified, demanded and proposal colors, as candidate-space
`Space.lean`), same output set. Counted units, not machine time.

Traces:
- estate: the candidate-space canonical log, 1,641 records
  (`EstateData.lean`, sha256 bf0247f6…; built by that work's
  `gen_estate2.py` from the proof estate, idol-lib v2 graphs and
  idol-eyes sources).
- idol-lib v2: 14 library source graphs at idol-lib master 0052f16,
  3,630 records (`V2Data.lean`, sha256 7e414a2d…, from `gen_v2.py`).
  Encoding stated in `gen_v2.py`: one record per hyperedge, and one
  zero-premise record per `file` node, the only nodes no edge
  concludes (the graphs set roots to null).
- Orders: the artifact's serialization order (forward), reversed, and
  a fixed-seed shuffle. These are not time-stamped histories of real
  appends.

| Trace | Derived | Worklist premise ops, all prefixes | Naive incremental checks, all prefixes | Naive scratch checks, final log only |
|---|---|---|---|---|
| estate forward | 1,150 | 7,117 | 4,605,032 | 37,478 |
| estate reversed | 1,150 | 7,532 | 1,636,524 | 37,478 |
| estate shuffled | 1,150 | 7,432 | 1,845,426 | 37,478 |
| idol-lib v2 forward | 3,630 | 11,194 | 19,031,994 | 17,577 |
| idol-lib v2 reversed | 3,630 | 14,742 | 7,962,880 | 17,577 |
| idol-lib v2 shuffled | 3,630 | 11,908 | 16,214,009 | 17,577 |

Worklist premise ops = raw premises read for deduplication + distinct
premises tested at admission + waiter visits. Naive checks = premise
membership tests with short-circuit, one `fire` pass per round (fairer
than `Closure.iterE`, which evaluates `fire` twice per round). Naive
incremental is `closFrom` from the previous closure at every append,
which rescans the whole log at least once per append.

| Claim | Verdict |
|---|---|
| Worklist output equals naive closure at every prefix of all six runs, and equals naive scratch and the proved `Closure.clos` on each final log | VERIFIED (run) |
| Over all prefixes, the worklist uses 217x to 1,700x fewer premise operations than naive incremental closure on these traces (exact counts above; naive incremental rescans the whole log at every append) | VERIFIED (run) |
| Maintaining the closure at every prefix costs fewer premise operations than one scratch closure of the final log, on all six runs | VERIFIED (run); on idol-lib v2 reversed the margin is narrow (14,742 vs 17,577 checks, plus 14,520 naive record examinations) |
| Visits ≤ distinct premises and pops = derived on all runs | VERIFIED (run; also proved) |
| Duplicate or merged premises on real traces | UNMEASURED: no record in either trace has duplicate projected premises at level 0 (raw = distinct on all runs); the semantics are covered by the kernel controls only |
| Wall-clock time | UNMEASURED: the proved state uses closures for counts and waiters, so its time is not an implementation's time; membership tests are list scans in the worklist and hash lookups in the naive harness, uncosted on both sides |
| An Array or HashMap implementation equal to the proved one | UNMEASURED: not written or proved |

## What this does and does not establish for H1 (incremental and compounding)

Does: for the derived-closure layer of the one append-only log, the
least closure can be maintained incrementally with no drift. The
incremental result equals the scratch result at every prefix by
construction (`mem_continue`), nothing is recomputed (`run_append`),
and the total work is bounded by the distinct premises appended,
independent of order (`visits_le`). That is the "incremental" half of
H1, proved for this layer.

Does not: it says nothing about intelligence, weights, semantic or
action vectors, or the colorings beyond one fixed color test. The
level `r` and test `q` are fixed per run; changing the resolution or
the coloring is a separate run with no reuse proved. Resolution levels
appended to the same log are admitted only when at or finer than `r`;
no cross-level reconciliation is proved here. The log is one
sequential list; concurrent appends and their merge are not modeled.
The cost bound is additive, not compounding: nothing here shows that
one appended record reveals more than its own consequences. The
compounding half of H1 stays open.
