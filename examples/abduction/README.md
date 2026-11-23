# Abduction on the canonical hypergraph

Observations come in (gate runs, pending artifacts, planted cases). The engine proposes the
minimal sets of causes that would explain them over the one record log, ranks them, checks each
survivor (a Lean certificate when the claim is formal, a controlled rerun when it is
empirical), and appends only checked results to the store. `run.sh` reruns every claim below.

## How it works

| Stage | Where | What it does |
|---|---|---|
| Spec | `proof/Abduction.lean` | Hypotheses are root records appended to the log. `Explains`: every observation derivable, `bot` not. `Minimal`: no proper subset explains. Negative observations are records `term -> bot`. |
| Generation | `engine.py` `ATMS` | Incremental label propagation: for every term, the minimal consistent sets of abducibles (size ≤ k) that derive it. Records are appended one at a time; nogoods are pruned when they appear. |
| Reference | `engine.py` `brute` | Line-by-line mirror of Lean `abduce` (every sublist up to k, erase-one minimality). Used to check ATMS completeness. |
| Ranking | `engine.py` `front` | Pareto front over (observations covered, cost). Same order as Lean `front`. |
| Formal check | `certify.py` | Emits a Lean file with the whole log and checks `certificate_fast` by `decide +kernel`: the cone is closed over every record, then a derivation trace, a closed set without `bot`, and one closed set per removed hypothesis that misses an observation. |
| Empirical check | `gates.py` | Control runs, intervention runs, placebo runs (an unread variable set), 2 repeats each. VERIFIED = target symptom in every control, in no intervention, in every placebo. REPAIRED = also exit 0. |
| Admission | `admit.py` | Second implementation: own closure, own chain check, verdicts re-decided from stored run logs. Appends to `receipts/hypergraph.jsonl` only; checks append only and monotone. |

## Proved (Lean 4.19.0, `proof/check.sh` cold, standard axioms only)

`proof/Abduction.lean`: `derivesWith_iff` (appending hypothesis records = adding roots),
`mem_closWith`, `explainsB_iff`, `explains_congr`, `consistent_sub`, `minimal_iff_erase`
(for duplicate-free H, minimality is decided one removal at a time), `minimalB_iff`,
`mem_subs`, `mem_abduce`, `abduce_complete` (every minimal explanation within the bound has a
member of `abduce` with its terms), `cone_derivesWith`, `explains_cone`, `minimal_cone`,
`certificate`, `certificate_lit`, `closedB_sound`, `traceOk_sound`, `certB_sound`,
`certificate_fast`, `derivesWith_grow`, `inconsistent_persists` (a refutation never needs
retracting), `explains_persists`, `admitLog_prefix`, `admitLog_monotone`, `admitLog_refuses`,
`admitLog_explains`, `admitLog_consistent`, `mem_front`, `front_nonempty`.

`proof/AbductionControls.lean`, kernel-checked on a concrete log: C1 consistency matters, C2
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

## Measured

See `receipts/SUMMARY.json` (written by `summary.py`; every number here comes from it).

## Premises and limits

* Symptoms come from a fixed set of patterns (`gates.py` `RX`). A failure outside that
  vocabulary stays unexplained; the planted removal of a Lean module shows this (no hypothesis,
  nothing admitted).
* A verified cause is a cause of one symptom, not of the whole failure; the loop then abduces
  the next symptom with the intervention kept. An empty placeholder file only tests the fail
  point, and is admitted only as a fail-point claim.
* ATMS completeness is tested against the brute mirror (every prefix of every planted log), not
  proved. Explanations are bounded at k = 3 per observation; for components with no
  qualify-only explanation the joint explanation is erase-one minimal, not proven cheapest.
* D1 hypotheses are counterfactual: `qualify#N` means "add a direct battery check for artifact
  N". No battery was written or run for them.
* Admission shares one piece with the gate runner: the symptom extractor, used to re-derive
  symptoms from each stored log.
* Timings are wall clock on one machine and are not claims.
