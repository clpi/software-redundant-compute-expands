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
| 24/7 | the loop is event driven and saturated after every event; it needs no human for adds and covering replacements | operational claim, measured on one replay, not proved |

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
