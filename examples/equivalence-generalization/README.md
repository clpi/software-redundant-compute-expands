# Does the equivalence graph generalize across software?

Target model: the canonical hypergraph of `clpi/software`,
`theses/redundancy-is-equivalence/spec.md` (ruling of 2026-11-19).
One graph; edges are total equivalence classes of terms; a join is
admitted only on a witness (a proof, a derivation, or a measurement
at a named pin); edges merge and never split; one partition, with no
private equivalence per level or qualification.

## What "generalizes" has to mean

The structure generalizes trivially: any artifact can be spelled as
terms, so any software fits in the graph. That is not the question.
The question is whether its joins can be **sound** (two terms in one
edge really behave the same) and **complete** (terms that behave the
same end up in one edge), for every kind of software, at a finite
resolution. Three things have to be fixed before that has an answer:

- **Semantics.** Behavior is what an observer sees: outputs for pure
  code, output sequences for objects, the set of outcomes over every
  schedule for concurrent and distributed code, bytes or values for
  floats, content or calls or traces for I/O, DOM or text or handler
  work for UI, source value for compiled code.
- **Equivalence.** Equal observations under a named observer. A
  tolerance ("within 1e-9") is a relation, not an equivalence.
- **Resolution.** A finite input list, a fuel bound and a schedule
  set. A measurement witnesses agreement at that resolution and no
  further.

## The answer

The model generalizes **soundly** to every kind tested, and to any
software in principle, once a measured fact is a join of
observer-applied terms `o@r(p) = o@r(q)` (the form term whose head
names the observer and the resolution) and a bare join `p = q` is
admitted only on a proof or an exhaustive measurement. Read
literally, with a bounded measurement as the witness for a bare join
of two program terms, it is unsound in all eight kinds tested.

It cannot generalize **completely**. No procedure decides behavioral
equivalence for a Turing-complete language (proved here under the
recursion premise), so no computable total-equivalence key is exact.
What bounded resolution recovers is one-sided: a separation between
two halted outputs, once seen, is final and survives every
refinement; an agreement is only a fact about its resolution. Halting
against running forever is never separated at any finite resolution.

Completeness of bare joins therefore comes from proofs, and from
exhaustive measurement where the domain is finite. In the corpus,
exhaustive measurement recovered every bare join for the finite
domain (8-bit pure functions); proof witnesses recovered 24 of 66 for
the compiler; elsewhere the qualified facts hold the information and
the bare joins wait for proofs.

## Proved (`proof/Generalize.lean` at the repo root, plain Lean 4.19, standard axioms)

| Theorem | Statement |
|---|---|
| `noDecider`, `noExactKey` | Under the recursion premise `Diag` (Kleene's second recursion theorem; not proved here), no exact equivalence decider and no exact computable key exist |
| `run_mono`, `outcome_unique` | Any deterministic step machine: outputs found at a fuel bound persist; eventual output is unique |
| `decisive_persists`, `decisive_sound`, `decisive_complete` | A separation of two halted outputs survives every refinement of inputs and fuel, refutes equivalence, and every such difference is found at some finite resolution |
| `diverge_never_decisive`, `no_uniform_bound` | Halting against running forever is never decisively separated; for every bound K an inequivalent pair agrees at every fuel up to K |
| `leak_example`, `qualified_sound`, `qualified_example` | Two observers poured into one partition relate terms neither observer relates; joining observer-applied terms never leaks |
| `refine_join`, `applied_inj` | A finer observer's join derives the coarser one's; observer-applied terms are injective form terms of the spec's grammar |
| `tolerance_collapse` | A symmetric transitive relation relating each grid point to its neighbour relates every pair |
| `solo_equal`, `par_breaks` | Atomic and split increments are equal alone and different in parallel: sequential equivalence is not a congruence for parallel composition |
| `exhaustive_iff`, `nonexhaustive_gap` | Agreement on a list holding every input is equality; on a list that misses one, it says nothing about it |
| `compile_run`, `fold_sound`, `rewrite_sound`, `rewrite_needs_law` | A stack compiler is correct for every value type; folding is sound with no premise; a rewrite is sound exactly when its law holds |

## Measured (this folder)

78 programs I wrote across eight kinds, each with an executable
semantics. These were chosen to contain edge cases; the counts show
that each failure mode exists in each kind, not how often it happens
in real code. Truth is computed over a universe larger than any
measured resolution, with every schedule; it is truth relative to
that universe. For infinite domains the qualified policy makes no
bare join at all, so its soundness does not depend on the universe.

`v0` is the spec read literally (bounded measurement witnesses a bare
join). `v1` turns on the five fixes. `v1+proofs` adds proof
witnesses. Counts are pairs of terms in one edge.

| Kind | truly equal pairs | v0 false bare | v1 false | v1 qualified facts | v1 bare missed | v1+proofs missed |
|---|---|---|---|---|---|---|
| Pure (8-bit) | 5 | 16 | 0 | 52 | 0 | 0 |
| Stateful | 1 | 14 | 0 | 28 | 1 | 1 |
| Concurrent | 2 | 3 | 0 | 4 | 2 | 2 |
| Distributed | 1 | 2 | 0 | 2 | 1 | 1 |
| Float | 4 | 106 | 0 | 78 (+60 relation facts) | 4 | 4 |
| I/O | 1 | 9 | 0 | 10 | 1 | 1 |
| UI | 1 | 9 | 0 | 44 | 1 | 1 |
| Compiler | 66 | 24 | 0 | 468 | 66 | 42 |

Gates (`gate.py`): each fix fails without it and passes with it.

| Fix | false facts without | with |
|---|---|---|
| Observer-applied terms | 48 | 0 |
| Resolution in the head; bare join only when exhaustive | 233 | 0 |
| Schedule sets for nondeterministic kinds | 7 | 0 |
| Tolerance as a relation term `near(p,q) = true` | 36 | 0 |
| Congruence only for compositional observers | 2 | 0 |

With resolution heads on, the schedule set is part of the head, so
enumerating schedules adds strength to facts but is no longer needed
for soundness.

Cost: v1 runs the same number of program executions as v0 except on
nondeterministic kinds, where every schedule is run (Concurrent 25 to
55, Distributed 16 to 400, I/O 40 to 130).

`premises.py` checks the laws behind compiler rewrites on the
universe: doubling (`u*2 = u+u`) holds on all 19 points (a check, not
a proof; the proof witness names it as a premise); zero absorption
fails at -1.0, -2.5, -0.0 and inf; self-subtraction fails at inf, -inf
and nan. So only the doubling rewrite gets a proof witness.

## Not established

- Prevalence in real code: the corpus is hand-written.
- The link from the Python passes to the Lean passes is by reading,
  not by proof.
- The recursion premise is assumed, not proved for a concrete
  language.
- Proof witnesses for stateful, UI, I/O and distributed equivalences
  (bisimulation, CRDT convergence) were not attempted, so those bare
  joins stay missed.
- The existing registry's one join (cbor and msgpack `uval`, byte
  identical texts) is a spelling-level witness and is sound; nothing
  here says it is wrong.

## Reproduce

```
LEAN=lean sh gate.sh       # Lean, measure twice, gates
python3 measure.py results.json
python3 gate.py results.json
python3 premises.py
```
