# Abduction on the canonical hypergraph

Observations come in (gate runs, pending artifacts, planted cases). The engine proposes the
minimal sets of causes that would explain them over the one record log, ranks them, checks each
survivor (a Lean certificate when the claim is formal, a controlled rerun when it is
empirical), and appends only checked results to the store. `run.sh` reruns every claim below.

## How it works

| Stage | Where | What it does |
|---|---|---|
| Spec | `proof/Abduce.lean` | Hypotheses are root records appended to the log. `Explains`: every observation derivable, `bot` not. `Minimal`: no proper subset explains. Negative observations are records `term -> bot`. |
| Generation | `engine.py` `ATMS` | Incremental label propagation: for every term, the minimal consistent sets of abducibles (size ≤ k) that derive it. Records are appended one at a time; nogoods are pruned when they appear. |
| Reference | `engine.py` `brute` | Line-by-line mirror of Lean `abduce` (every sublist up to k, erase-one minimality). Used to check ATMS completeness. |
| Ranking | `engine.py` `front` | Pareto front over (observations covered, cost). Same order as Lean `front`. |
| Formal check | `certify.py` | Emits a Lean file with the whole log and checks `certificate_fast` by `decide +kernel`: the cone is closed over every record, then a derivation trace, a closed set without `bot`, and one closed set per removed hypothesis that misses an observation. |
| Causes from symptoms | `gates.py` `theory` | Static reads of the gate script (required variables, positional arguments, argv, tools) and the run's symptoms (missing paths, failed fetches). Each cause predicts symptoms; one that predicts something absent is inconsistent. |
| Causes from the tree | `gates.py` `harvest`, `bisect` | Read from the repository, never from the failure text: the gate run first (not idempotent from a clean tree), the build of every package that builds the gate's folder, shell lines of the folder's README, tracked files missing from the tree, scripts whose source names a file the failing run lacks (producers), scripts that take the gate's argument and write into the directory the gate reads (sibling producers), tracked files in that directory the producer does not write (strays, set aside), a missing Python module found as a same-named file in the tree, and the commit that broke the gate (its folder walked back through history). A producer that itself fails is abduced as a gate of its own, one level deep, and its repair is carried into the parent's prerequisite step. Each action is probed once; the names it creates that the failing log mentions become observations it explains, so it ranks first. |
| Empirical check | `gates.py` `experiment` | Control, intervention and placebo runs, 2 each (placebo: an unread variable, or a no-op in the same slot). VERIFIED = target in every control and placebo, in no intervention; REPAIRED = also exit 0. Causes from the tree target the exit status, or the run's final signature when they fix one failure and expose the next. A gate whose controls disagree is flaky: every arm goes to 12 runs and both control and placebo must beat the intervention by a one-sided Fisher exact test at 0.05. |
| Narrowing | `gates.py` `narrow`, `ddmin` | A verified tree cause is cut down by delta debugging (hierarchical, into directories) to a 1-minimal set of paths that, restored alone on a fresh tree, repairs; for a regression, to the files of that commit whose old versions alone repair. The set is verified again with controls. |
| Cross-check | `crosscheck.py` | The D0 logs through #16's engine (`examples/abduction`) and its independent checker; the two minimal explanation sets must be equal. A mutant of each input must be caught. |
| Admission | `admit.py` | Second implementation: own closure, own chain check, verdicts re-decided from stored run logs (the Fisher rule and the signature rule written again, not imported), every stored log ends with its exit status, so the hash binds the status and admission reads it from the log, prerequisite logs hash-checked, 1-minimality of a narrowed set re-derived from the delta-debugging runs. Appends to `receipts/hypergraph.jsonl` only; checks append only and monotone. |

## Proved (Lean 4.19.0, `proof/check.sh` cold, standard axioms only)

`proof/Abduce.lean`: `derivesWith_iff` (appending hypothesis records = adding roots),
`mem_closWith`, `explainsB_iff`, `explains_congr`, `consistent_sub`, `minimal_iff_erase`
(for duplicate-free H, minimality is decided one removal at a time), `minimalB_iff`,
`mem_subs`, `mem_abduce`, `abduce_complete` (every minimal explanation within the bound has a
member of `abduce` with its terms), `cone_derivesWith`, `explains_cone`, `minimal_cone`,
`certificate`, `certificate_lit`, `closedB_sound`, `traceOk_sound`, `certB_sound`,
`certificate_fast`, `derivesWith_grow`, `inconsistent_persists` (a refutation never needs
retracting), `explains_persists`, `admitLog_prefix`, `admitLog_monotone`, `admitLog_refuses`,
`admitLog_explains`, `admitLog_consistent`, `mem_front`, `front_nonempty`.

`proof/AbduceControls.lean`, kernel-checked on a concrete log: C1 consistency matters, C2
minimality matters, C3 the enumerator returns exactly the planted causes `{5}` and `{3,4}`, C4
the size bound is real, C5 minimality does NOT persist when the log grows (so a minimality
claim is tied to the log head it was checked on), C6 refutations persist, C7 duplicate lists
are refused, C8 the cone must be closed backwards, C9 admission refuses unverified and
non-minimal explanations, C10 the front drops a dominated candidate, C11 the certificate path
end to end.

`mutants.sh`: 10 mutants of the definitions (drop consistency, drop the abducible check, drop
erase-one minimality, drop duplicate freedom, unclosed cone, closed set skipping roots, trace
accepting anything, admission ignoring the verdict, non-strict dominance, certificate skipping
`bot`); each breaks a proof.

## Measured (`receipts/SUMMARY.json`, written by `summary.py`)

**D0, planted causes on 200 random logs** (123 used; 77 skipped because the planted cause
derives nothing observable). Incremental ATMS = scratch rebuild = brute mirror of `abduce` after
every one of 5,260 appends. Planted core recovered 123/123; unique cheapest explanation 91/123
(53/74 with one observation, 8/11 with four: more observations discriminate more). Planted
false hypotheses rejected 291/291 (does not explain 122/122, inconsistent 46/46, not minimal
123/123). Work: 47,532 label operations incrementally vs 536,292 rebuilding after every append.

**D1, monotone-synthesis stream** (`../monotone-synthesis/receipts/stream.jsonl`, 1,044 records).
Strict verifier: 96 pending (loop.py's count), 79 of them live artifacts. Every one of the 79 is
explained; 29 independent components: 26 (54 artifacts) by qualifying artifacts only, and the
3 cycle components (cbor, msgpack, flatbuf; 25 artifacts) also need one assumed capability each. Cheapest first step: 2
hypotheses unblock 10 artifacts; the whole set: 163 hypotheses (160 direct battery checks, 3
cycle breaks). Raw mode (no cycle grouping): the 10 pending artifacts are explained by exactly
3 assumptions, `cbor:get`, `flatbuf:verify`, `msgpack:get`, one per mutual-recursion group,
typed `cycle`. Lean certificates on the whole 1,044-record log: 36/36 (1 raw, 29 strict
components, 6 planted cores); 6/6 planted false hypotheses refused by the kernel.

**Cross-check with #16** (`crosscheck.py`): the 123 D0 logs through #16's engine and its
independent checker. Minimal explanation sets equal on 123/123 (239 explanations, all sizes);
#16's checker accepts 123/123 certificates; with one used abducible deleted from #16's input
only, 123/123 mutants disagree, so the agreement is not vacuous.

**D2, gates of this repository** (`gates-public.json`). `examples/monotone-synthesis/run.sh`
fails with no inputs; the engine abduces `OPT` unset (the only consistent cause), sets it from
the message's own pin, then `IL`, then `IQ`, and ends REPAIRED: exit 0 in both intervention
runs; the planted unread variable is refuted every round. `examples/admission/run.sh`: missing
argument 2 VERIFIED, then `/sha256/sha256.id`; the next failure (the compiler aborts) has no
cause in either source and stays unexplained.

At 4ebcfa0 (receipts in commit 4187e37) the same gate failed after those three repairs on
its own control ("a state that lost a live artifact is refused", 21/22). No symptom cause and
no tree action applied, so the engine walked the folder back through history: the folder as it
was before the #14 merge passes, and delta debugging cut the difference to `ingest.py` alone.
REPAIRED with controls and placebo. #14 had changed the state's `seen` field from a list to a
map and the gate's control still rebuilt it as a list; 5ed0332 fixes the control, and these
receipts are from that commit.

Planted cases, 9/9 recovered and REPAIRED: `lean` off PATH, `IQ` removed, `gate.py` removed
(by its missing path and, separately, as a tracked file missing from the tree), a removed Lean
module (no symptom names it; recovered as a tracked file missing from the tree, unexplained
before), a folder whose build generates the table its gate reads (narrowed to
`gen/table.txt`), a gate that only passes on its second run (narrowed to `.cache/warm`, and
the first run's only extra output line, `cold start`, reported), and a flaky gate that fails
about 3 runs in 4 unless its build ran (12 runs per arm, Fisher test, narrowed to `gen/ok`),
and a gate that reads `data/out.json`, which only `tools/gen.py` writes, while `gen.py` itself
fails on a missing module. The engine finds `gen.py` as the producer (and `tools/report.py`,
which only reads the file, as a decoy), abduces `gen.py`'s own failure as a sub-gate
(`planted_helper` missing; the same-named file under `lib/` put on `PYTHONPATH`, REPAIRED),
then runs the repaired producer first and the parent is REPAIRED, narrowed to `data/out.json`.
A last planted case has a checker that reads every `.json` in `results/NAME` as a run: the runs
are written by `gen.py NAME` and not kept in git, and the tracked `results/a/summary-compact.json`
is not a run. The engine supplies the argument from the directory's entries, finds `gen.py` as
the script that writes the same directory, finds the two tracked files `gen.py` does not write,
and tests the pair (run `gen.py a`, set both files aside): REPAIRED. With the producer run held
fixed, delta debugging cuts the set-aside files to `summary-compact.json`; `notes.txt`, which the checker skips, is dropped.
Planted false causes refuted 7/7, including the README decoy `touch decoy.txt` and the
`report.py` decoy.

The 13 gates of the consolidated `clpi/software-*` tree were run the same way (receipts kept
out of this public repository). Real gates repaired by the engine alone: 6 of 9, against 3 of 9
in the previous version and 1 of 9 before that.

* `is-incrementally-safe/examples`: run the package build first (narrowed to the built library
  and its three dependency checkouts).
* `doesnt-need-review`: the gate run first; its first run clones two dependencies and lake's
  clone lines land in the captured version string.
* `emergence/rung4` and `rung5`: each checker reads a results file that only its harness
  writes. The engine finds the harness by the file's name in its source; `harness4.py` itself
  fails on a missing module, so it is abduced as a sub-gate (rung 3's folder on `PYTHONPATH`,
  REPAIRED), and the repaired harness run first repairs the checker.
* `emergence/rung3`: the checker needs a battery name (taken from `results/`), then the runs
  `harness3.py field3` writes into the same directory (found as the script with the same
  argument and directory), and then it still fails because it reads every `.json` there as a
  run, including the committed `summaries-compact.json` and `view3.json`. The pair (harness
  first, those set aside) repairs it with all 72 runs checked (cuts 504/504, restarts 48/48);
  narrowing drops `checks.json`. This gate is measured at the commit that added these causes;
  the other five at the one before.

The rest stop at a verified fail point with no producer in the tree: `srce/admission` (the
compiler aborts; no source explains it), `emergence/rung6` (a file under the author's home
directory), and `has-a-highest-minimal-axis` (its README says the gate fails on purpose until
someone supplies the real arena table; the engine finds no producer and claims none).

**Admission**: only re-decided verdicts, re-derived minimal sets and clean certificates are
appended (66 admitted, 34 refused, 2,218 records); the store is hash-chained, append only and
monotone; 12/12 tamper controls caught (relabeled verdict, fabricated run symptoms, certificate
output with `sorryAx`, claim naming another H, planted false hypothesis whose refusal was
replaced, a delta-debugging run relabeled, a prerequisite step's log deleted, a passing run's
log swapped for a failing one, a run's exit status edited to 0, history rewrite, re-admission
appends nothing).

## Premises and limits

* Two cause sources: a fixed set of symptom patterns (`gates.py` `RX`), and actions read from the
  tree (the gate itself, package builds, README shell lines, tracked deletions, producers of a
  missing file, sibling producers and the strays they leave, same-named modules, the folder's
  history). Producers are found by name: a script
  that builds the path at run time from pieces the source never spells out is not found. Sub-gates
  go one level deep, at most three producers per missing file. A failure that neither reaches stays unexplained: the admission gate's compiler
  abort is one.
* Setting tracked files aside can make a checker vacuous: with its inputs gone it checks nothing
  and passes. So a stray cause exists only next to a step that writes new files into the same
  directory, and narrowing keeps that step fixed. In an earlier version narrowing was free to drop
  the step, and on the rung 3 checker it found a "repair" that checked 0 runs; that is how this
  rule came in.
* A verified cause is a cause of one failure, not of all of them; the loop then abduces again
  with the intervention kept. An empty placeholder file only tests the fail point, and is
  admitted only as a fail-point claim.
* Narrowing is 1-minimal within its run budget (80 gate runs, 30 for a regression): a set is
  claimed minimal only when admission finds, for each of its paths, a recorded run without that
  path that failed. Where the budget ran out the set is reported, not claimed minimal.
* A regression names the commit after which the folder fails and the files whose old versions
  repair; the repair a person makes may be elsewhere (here the stale control in `gate.py`, not
  `ingest.py`).
* The flaky rule assumes runs are independent; it controls the false-positive rate per test,
  not over every test in a run.
* ATMS completeness is tested against the brute mirror (every prefix of every planted log), not
  proved. Explanations are bounded at k = 3 per observation; for components with no
  qualify-only explanation the joint explanation is erase-one minimal, not proven cheapest.
* D1 hypotheses are counterfactual: `qualify#N` means "add a direct battery check for artifact
  N". No battery was written or run for them.
* Admission shares one piece with the gate runner: the symptom extractor, used to re-derive
  symptoms from each stored log.
* Timings are wall clock on one machine and are not claims.
