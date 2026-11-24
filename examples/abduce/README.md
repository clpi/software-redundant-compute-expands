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
| Causes from the tree | `gates.py` `harvest`, `bisect` | Read from the repository, never from the failure text: the gate run first (not idempotent from a clean tree), the build of every package that builds the gate's folder, shell lines of the folder's README, tracked files missing from the tree, and the commit that broke the gate (its folder walked back through history). Each action is probed once; the names it creates that the failing log mentions become observations it explains, so it ranks first. |
| Empirical check | `gates.py` `experiment` | Control, intervention and placebo runs, 2 each (placebo: an unread variable, or a no-op in the same slot). VERIFIED = target in every control and placebo, in no intervention; REPAIRED = also exit 0. Causes from the tree target the exit status, or the run's final signature when they fix one failure and expose the next. A gate whose controls disagree is flaky: every arm goes to 12 runs and both control and placebo must beat the intervention by a one-sided Fisher exact test at 0.05. |
| Narrowing | `gates.py` `narrow`, `ddmin` | A verified tree cause is cut down by delta debugging (hierarchical, into directories) to a 1-minimal set of paths that, restored alone on a fresh tree, repairs; for a regression, to the files of that commit whose old versions alone repair. The set is verified again with controls. |
| Cross-check | `crosscheck.py` | The D0 logs through #16's engine (`examples/abduction`) and its independent checker; the two minimal explanation sets must be equal. A mutant of each input must be caught. |
| Admission | `admit.py` | Second implementation: own closure, own chain check, verdicts re-decided from stored run logs (the Fisher rule and the signature rule written again, not imported), prerequisite logs hash-checked, 1-minimality of a narrowed set re-derived from the delta-debugging runs. Appends to `receipts/hypergraph.jsonl` only; checks append only and monotone. |

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
about 3 runs in 4 unless its build ran (12 runs per arm, Fisher test, narrowed to `gen/ok`).
Planted false causes refuted 6/6, including the README decoy `touch decoy.txt`.

The 13 gates of the consolidated `clpi/software-*` tree were run the same way (receipts kept
out of this public repository). The engine alone repaired the two that had needed a hand
diagnosis: `is-incrementally-safe/examples` (run the package build first; narrowed to the
built library and its three dependency checkouts) and `doesnt-need-review` (the gate run
first: its first run clones two dependencies in `statement/` and lake's clone lines land in
the captured version string; narrowed to those two checkouts, and the clone lines are the
first run's only extra output). Real gates repaired: 3 of 9, against 1 of 9 before. The rest
stop at a verified fail point whose producer is outside the repository (an experiment output,
a fixture, a file under the author's home directory) or at a failure no source explains.

**Admission**: only re-decided verdicts, re-derived minimal sets and clean certificates are
appended (55 admitted, 22 refused, 2,197 records); the store is hash-chained, append only and
monotone; 10/10 tamper controls caught (relabeled verdict, fabricated run symptoms, certificate
output with `sorryAx`, claim naming another H, planted false hypothesis whose refusal was
replaced, a delta-debugging run relabeled, a prerequisite step's log deleted, history rewrite,
re-admission appends nothing).

## Premises and limits

* Two cause sources: a fixed set of symptom patterns (`gates.py` `RX`), and actions read from the
  tree (the gate itself, package builds, README shell lines, tracked deletions, the folder's
  history). A failure that neither reaches stays unexplained: the admission gate's compiler
  abort is one.
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
