# Monotone synthesis: an admission loop that only grows

A loop that runs unattended, takes in candidate software artifacts with their receipts, and keeps
one append-only library whose reachable capabilities never shrink. This directory holds the spec,
the Lean proof of its monotone and compounding core, controls, and a first run on real data
(idol-lib's compiler-resolved call graphs and Idol battery receipts).

## The spec

An **artifact** has an id, the capabilities it composes (premises) and the one it provides (head).
The **library** is one log of entries: `add x`, or `retire i n` (retire artifact `i`, replaced by `n`).
Nothing is deleted. **Reach** is the least closure of the host primitives under the live artifacts
(`Qualification.Derives` from clpi/software-optimality, imported at a pin).

Admission, the only way an entry reaches the log:
- `add x`: the verifier accepts `x` (a receipt verdict), the id is fresh and never retired, every premise is reachable now.
- `retire i n`: `i` and `n` live, `n ≠ i`, and everything reachable before is reachable after. The executable check is `replaceB`: same head, the replacement's premises reachable without `i`.

What the words mean, and which are theorems:

| Word | Meaning here | Status |
|---|---|---|
| monotone | reach never shrinks along a run; a capability once provided is never lost, even if its artifact is retired | proved: `run_monotone`, `capability_never_lost`, `live_heads_reach` |
| no invalidation without a proved replacement | a retirement needs a live distinct replacement and preserved reach | proved: `retire_has_replacement`; executable check proved sound: `replaceB_sound` via `replace_covers` |
| compounding | readiness persists; an admission makes ready every candidate whose missing premises it supplies, strictly when its head was new; libraries compose with nothing lost after one reclosure, also for indexed families | proved: `ready_persists`, `enables`, `enables_strict`, `compose` (from `ClosureStrength.compounding_sources`), `compose_family` (from `ClosureStrength.compounding_family`) |
| generalizable | an abstraction (composed rule whose head is already derivable from its premises) changes nothing reachable | proved: `abstract_conservative` |
| autonomous, order free | every saturated run reaches exactly the closure of the verified pool, whatever the order of offers, retries and retirements; saturation persists | proved: `saturated_exact`, `order_independent`, `saturated_persists` |
| sound | if the verifier is faithful, everything reached is true | proved conditionally: `reach_sound`; faithfulness is a premise |
| generates and composes | new implementations are generated (inline a single-expression helper at its call site), verified by their home's battery and by every home built on it, and admitted only as covering replacements; a home built on another's library is admitted on that library's capabilities | measured on idol-lib, not proved: generation and the battery are outside the proof; what the proof covers is that admitting them can never lose a capability |
| 24/7 | the loop is event driven and saturated after every event; `ingest.py` runs it as a resumable process (one batch of receipts per invocation, state replaced atomically, re-ingest is a no-op, a state that would lose a capability is refused) | operational claim: measured (19 commit batches in 19 processes equal the one-shot run), not proved; nothing schedules it yet |

Controls (`MonotoneSynthesisControls.lean`), each a kernel-checked pair of refusal and harm:
uncovered retirement refused although both are live (C1); covering replacement admitted (C2);
verifier off admits a false capability (C3); premise check off leaves a live artifact with an
unreachable head (C4); one pass without retry is not saturated (C5); an underived "abstraction"
changes reach (C6); composition needs reclosure (C7, plus optimality's own control reused);
strict compounding (C8); two orders with a retirement reach the same set (C9).

## What needs Chris, what does not

Unattended: offering candidates as receipts arrive, admitting, retrying pending ones when a premise
lands, covering replacements. Needs Chris: a retirement with no covering replacement (the loop
refuses it and keeps the old artifact live), anything that changes the verifier, publishing
(pushes, PRs, releases), and a capability-identity change (heads are named `home:path`).

## The run on real data

`gen_idol.py` builds 361 artifacts from the Idol compiler's graphs of idol-lib (306 functions at
0be14af, 55 at f754884 for the three homes PR 24 changed or added), premises from the compiler's
resolved applications, verdicts from the battery receipts of exactly those bytes. Order: the
commit time each definition first appears in its file. `loop.py` runs the incremental loop and
checks it against a from-scratch spec at every prefix; `gate.py` adds an independent reference,
controls and mutants. `run.sh` reruns everything.

Encoding premises, stated: capability identity is `(home, path)`; the 0be14af bytes are offered at
the time their name first appeared (receipts exist only for 0be14af and f754884); a mutually
recursive group is one artifact verified by its home's receipt, with one projection per member
(without grouping, 10 artifacts stay blocked: the least closure refuses a recursive group with no base).

## Continuous ingest

`ingest.py STATE EVENTS --batch COMMIT` applies one batch (one commit's receipts) to a persisted
state and refuses to write the state unless reach equals the from-scratch closure of the live
rules and of the verified pool, and contains the previous reach. `loop.py --emit-events` writes the
ordered events. `run.sh` replays idol-lib's 19 commit batches as 19 separate processes; the final
state equals the one-shot run (same reach and live ids). A scheduler that calls `ingest.py` on each
new set of receipts is what makes it run unattended; none is set up here.

## Composition across homes and generated code

Both need the Idol compiler (`IDOL`, built from clpi/idol bf96bd3, sha256 822dcb04…) and
idol-lib at 4ff0c5d; `run.sh` runs them when `IDOL` is set.

`gen_cross.py` admits idol-lib's `kernel` home, whose unit is sha256's library followed by its
own file. Its artifacts' premises come from `idol graph` of that unit, so four premises are
sha256 capabilities; its verdict is the kernel's own run.sh. Flipping sha256's receipt blocks
exactly the 7 kernel capabilities that reach sha256 (gate check).

`gen_rewrite.py` generates code. For each single-expression function whose bytes are the ones
offered, it inlines each call to another single-expression function of the same unit
(parameters substituted, an argument evaluated only as often as before). It also writes a
deliberately wrong variant (first two arguments swapped). Each rewrite is written into a scratch
clone and verified by its home's run.sh and by the run.sh of every home built on it (sha256's
rewrite also runs the kernel's battery). Homes whose battery ends with a network fetch that only
prints an incumbent's line count run without that tail; homes whose fetched incumbent feeds a
check (base64, qoi, xxhash) and lz4 (its unmodified library fails here) are skipped. The loop
offers each rewrite as a replacement of the artifact it came from; it is admitted only if
verified and covering.

Measured at 4ff0c5d: 12 rewrites generated, all 12 pass; all 6 wrong variants fail and are
refused; 9 capabilities replaced (two rewrites were never observed reached by a battery, one was
superseded); reach unchanged (329); derivation depth shorter for 9 capabilities, including two
kernel capabilities through sha256's replacement (sum 824 → 815). The rewrites are small and
semantics-preserving by construction; the battery is the only evidence that they are correct,
and running time is not measured.
