# Admission: a gamed claim cannot be appended (2026-11-21)

Ask: Chris, 2026-11-21 15:43Z, "Improve the hypergraph model and eliminate all gaming by construction
end to end."

The change: on the one append-only log, a claim is a record like any other, and it is accepted only
when its premises are bound to recorded behavior at append time. Nothing is detected afterwards.
`proof/Admission.lean` states the rule and proves what an accepted claim means;
`proof/AdmissionControls.lean` refuses one control per gaming route; `kernel.id` is the same rule in
Idol, extended from rung 0's kernel (which it keeps whole), and it is what runs on real logs.

## The rule

A log is a list of records; every reference points backward. The kinds that carry claims:

| record | accepted only if |
|---|---|
| `dim dom d`, `work dom w`, `config dom c`, `null dom n` | anyone may add them; never removed |
| `contract dom h s f r` | first contract of the domain; binds harness hash `h`, held-out seal `s`, absolute floor `f`, repeats `r` |
| `build dom s inputs` | a contract exists already; nothing it was built or derived from is a run trace or held-out bytes of that contract |
| `run k s w d harness trace` | the harness hashes to the contract's; `w` and `d` are registered; `s` is built, a config or the do-nothing subject. There is no value field: correctness and samples are read from the trace |
| `reveal k w bytes` | the bytes hash to the contract's seal |
| `derive gen inputs` | inputs are earlier; the output is not stored |
| `fact evidence` | every piece of evidence is a run (or a standing rung 0 receipt), or derived only from such |
| `claim dom s` (`beats` in the kernel) | see below |

A claim that `s` beats domain `dom` is accepted only if: held-out bytes were revealed after `s` was
built (heldout); every registered workload, held-out included, times every registered dimension has the
contract's repeats (cover); every subject run says its output was correct (correct); every cell has a
correct comparator run (peak); every subject sample plus the floor is below every correct sample of
every comparator configuration, so the target is the merged peak, not one chosen comparator (margin,
merged); and the do-nothing subject ran on every workload and failed every time (nullBase).

Lean (`claims_sound`): in any log reachable by appends, every claim satisfies `ClaimSpec`, a statement
of the above written without the checker, over the log as it stood when the claim was appended.
`reach_admitted` is the "by construction" part: every record was accepted against exactly its prefix.
`facts_grounded`: every fact's evidence is grounded in runs. Gate: `proof/check.sh` cold, exit 0,
standard axioms only.

## Gaming routes and their controls

Each control is a log whose prefix is itself accepted and whose last record is refused. Lean shows,
by evaluation, that switching off exactly the named check accepts it. The kernel shows the same with
mutants (each check's line replaced by `if false`). Lean and kernel run the same 17 controls plus the
honest log.

| route (where it was found) | how it is closed | control | check |
|---|---|---|---|
| Goodhart: leave out a dimension where you lose (claims audit E4) | dimensions are registered by anyone and a claim covers all of them | goodhart, c01 | cover |
| benchmark selection after results | one contract per domain; workloads and dimensions only accumulate | reselect, c02 | contractOnce |
| held-out leakage: tune after seeing it | the reveal must come after the build | tuned_after_reveal, c03 | heldout |
| held-out swapped for an easier one | reveal bytes must hash to the seal | seal_swap, c04 | revealSeal |
| no held-out; fixtures written with the engine (E2) | a claim needs a reveal | no_heldout, c14 | heldout |
| seal chosen after seeing the subject | builds only after the domain's contract | build_before_contract, c16 | buildAfterContract |
| measurement contract mismatch: browser start-up in one side's window (E1) | the harness is bound by hash in the contract | harness_mismatch, c05 | runHarness |
| proof over transcribed data (L6, `lz4_measured_loss`) | facts cite runs or data derived only from runs | transcribed, c06 | factGrounded |
| name-matched identity (C1, jq `n`) | runs bind subjects built in the domain; definitions bind (file bytes, compiler-resolved root) | name_match, c07; rung 0 k2, k9 | runSubject; rung 0 root/join |
| self-reported receipts | runs have no value field; verdicts are re-derived from traces | unrepresentable; rung 0 k1, k1b, k4, k8 | rung 0 verdict/trace |
| timing-only win: fast but wrong | every subject run must be correct; incorrect comparator runs do not set the peak | fast_but_wrong, c08 | correct |
| do-nothing baseline passes (G6's vacuous 0) | the do-nothing subject must fail every workload | do_nothing_passes, c09 | nullBase |
| win inside the noise (round 2 L5) | worst subject sample plus an absolute floor below every correct comparator sample | inside_floor, c10 | margin |
| beating a dimension nobody else measured (E4's Idol-only `work`) | a cell needs a correct comparator run | unmeasured_peak, c11 | peak |
| answer replay (E3, idol-map) | a subject built from a run trace of its own domain is refused | answer_replay, c12 | buildLeak |
| choosing the weak comparator; ceiling rule after the strict one refused (E4) | the target is every configuration; the decision rule is the kernel, not a field | weak_comparator, c13 | merged |
| one lucky run | the contract fixes repeats | lucky_run, c15 | cover |
| a run on an unregistered workload or dimension | runs need registered workloads and dimensions | unregistered_run, c17 | runRegistered |
| history rewritten, stale bytes, C route claimed native, compiler without premise | rung 0, unchanged | rung 0 k5, k3, k7, k10 | rung 0 |
| a run under a contract that does not exist yet; a rule changed after results | unrepresentable: references point backward; no rule field | none possible | none |

Kernel run (receipts/run.txt): 18 of 18 controls, 12 of 12 rung 0 controls on the extended kernel,
and every mutant flips its control. Two mutants flip two controls each because two controls share the
check (heldout: c03 and c14; cover: c01 and c15; margin: c10 and c13). Switching the merged peak off also
lets c10 through, because c10's tight comparator is the second configuration; Lean agrees.

## Replay of real claims

- idol-eyes campaigns 1 to 6 (raw.jsonl of each campaign; encoding in replay_eyes.py). 15 admission
  claims (campaign 1: idol; 2 to 4: idol, idol-v1, idol-map; 5 and 6: idol, idol-act, idol-map).
  **0 accepted.** idol-map's build is refused (buildLeak: run.py's record_maps pass runs idol on each
  task and feeds the output to idol-map), so all its runs (450, 260, 286, 300 and 300 in campaigns 2 to 6)
  are refused and its claim has no subject; this is the claims audit's E3 refutation, now refused at
  append. Every other claim fails heldout (no held-out was ever sealed) and nullBase (no do-nothing run),
  plus correct and peak: run.py checks no answer in warm mode, so warm timings are unverified for every
  driver; in campaigns 2 to 4 the `work` dimension has no comparator runs; idol's `spa` runs in campaign 1
  are unverified; idol-v1 has 4 to 6 unverified tasks per campaign; and in campaigns 5 and 6 every driver
  but idol-act fails `pick`, so that task has no comparator peak. With the audit's five missing dimensions
  registered, cover and peak fail on those as well. What survives: margin passes in every cell where a browser
  ran correctly (cold, tree, cpu), against all three at floor 0. The data show Idol faster and smaller on what
  was verified; they do not support the admission claims as made.
- idol-lib level 3 (rung 0's replay log of run e5ade0aa at 0be14af): **106 closed, 174 refused,
  identical to rung 0 and qualify.py**; all 174 are "not an observed root".
- idol-lib space data theorems: the level 3 family (`Level3.*`, data from gen.py over the 15 receipts)
  is accepted as grounded; the level 1 family (`WitnessedV1`, scanner output over source bytes) and
  `Economics.lz4_measured_loss` (timings typed in from `port/lz4.md`) are refused (factGrounded). They may
  still be true; they are not evidence about behavior.
- software-redundant-compute-expands algorithm search (3,458 measurement records) and semantic axes
  (6,766): every value is written into the record's receipt and no trace bytes are kept, so none of them
  is a run and no claim on them can be appended. The engines are deterministic Python; rerunning them with
  traces is UNMEASURED here. Round 2's adaptive merge (cheaper on 8 of 8 dev pairs, 4 of 16 held-out) would
  fail margin on held-out cells; that is read from the ledger, not run.

## Not established; premises that remain

- P1 hash: the Lean model's `H` is a toy and not collision resistant; the kernel uses idol-lib's sha256.
- P2 harness: the harness is bound by hash, but a trace says what the harness wrote. The replay ingest
  scripts transcribe recorded rows into traces and are trusted for that (elimination order: at rung 1 the
  harness appends its own runs). The campaigns did not hash their harness at run time, so the replay binds
  run.py at idol-eyes main 4586347.
- P3 held-out secrecy: a seal binds bytes, not secrecy. Private experiments before a contract cannot be
  refused; only what is appended is judged.
- P4 completeness of dimensions: a claim speaks only about dimensions registered so far, and a claimant can
  open a new domain with fewer dimensions; its claims then speak only of that domain. No correction is made
  for many attempts across domains.
- The kernel runs through the compiler's C route (`idol dump-c`, then cc), which is a diagnostic route, as
  in rung 0. The kernel is checked against Lean on the 18 controls only; no proof that it computes the same
  function as `acceptW`.
- Model limits: repeats are per contract, not per dimension (a deterministic counter read once fails cover);
  "beats on every dimension" refuses ties, so a dimension both sides max out (determinism) can never be won;
  determinism is not encoded in the replay.
- The idol binary built here at e5ade0aa hashes to fe5096a4..., not rung 0's 4e0e1362...; the level 3 replay
  and rung 0 controls give identical results.
- UNMEASURED: any held-out or do-nothing run for idol-eyes; the stdlib driver under the campaigns' harness (it
  ran under another harness, so it cannot enter these contracts); native timings; any speed claim for the
  kernel.

## Rerun

    sh proof/check.sh                                          # Lean 4.19.0
    python3 -I controls.py OUT/ctl
    python3 -I replay_eyes.py <campaign dir> <run.py> OUT/eyes/c<N>-a<0|1> <0|1>   # for N in 1..6
    python3 -I replay_space.py <rung0 replay-0be14af.tsv> OUT/root OUT/space.tsv
    sh run.sh <idol at e5ade0aa> <idol-lib checkout at 0be14af> OUT

kernel.id is rung 0's kernel (/mnt/project-files/rung0/kernel.id) with the claim kinds added; its hashing is
idol-lib's own sha256/sha256.id, prepended at build time.

Inputs and outputs with their hashes: receipts/SHA256SUMS.txt.
