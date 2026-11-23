# Constructive canonical progress

The one graph stores observations, including counterexamples. It is not the
sequence of canonical releases. A release successor is an inhabitant of
`Progress log contract check predecessor successor`. There is no constructor
for regressions: the constructor requires a checked exact predecessor/contract
edge, preservation of every qualified configuration/ordering observation,
admissibility in the declared possible relation, and pointwise non-worsening
of the cost vector. The all-record join can still retain rejected candidates.

`CanonicalProgress.lean` imports the repository's actual `Canon` graph and
`AlgoSearch` implementation. It proves constructor soundness/completeness,
qualified and allowed behavior, monotonicity across arbitrarily long admitted
sequences, append preservation of historical witnesses, support-based
derivability, exact Pareto frontier membership and coverage over generated
candidates, and cold equivalence for ordered-cut tasks. Kernel controls exhibit
two independently acceptable rewrites with an unacceptable interaction and
two distinguishable orderings of the same configuration. The current contract
must bind the meaning of its IDs and receipt colors to a trusted checker; the
Lean module does not prove that an arbitrary receipt emitter is faithful.
Scope growth is evidence growth; carrying an old model into a new contract
or new observation resolution requires a new exact applicability witness.

`python3 verify.py` exercises an independent cold semantics and exhaustive
frontier oracle over 8,640 candidates in 960 rounds. It tests configuration
changes, schedule changes, modeled signing, joined effects, cost tradeoffs,
stale selections, and immutable evidence prefixes. Red setups: a harmful
joint effect cannot construct a successor; the same proposal cannot be
published twice from one predecessor; disallowing a new behavior cannot be
bypassed by its lower cost. On 200→250, one recheck becomes unchanged before
its consumers are awakened: 4 executions versus 43 cold, with all receipts
matching. Counter totals include rule evaluations, not wall time, receipt
copying, serialization, or signing overhead.

This is a reference model, not a deployed compiler or release service. Real
compiler/target capture, graph extraction completeness and operational signing
remain outside the proof. New components, systems and cost axes must be
described by the same exact input and observation interface. Pareto closure
is exact for the represented candidate pool, not a proof about unseen code.

## Exact receipt scope

`proof/ProgressBinding.lean` adds a versioned witness format on the same
`Canon.Rec`. The ordered premise vector contains a lossless, length-framed
encoding of the contract, check identity, predecessor and candidate, including
both ordered observation sequences and cost vectors. The original three
anchor terms remain first; payload terms use a disjoint residue. The
encoding is injective over the exact finite model and requires no hash
assumption. Proofs use the full anchored edge, not a projection that drops the
body. An exact receipt remains valid for that same claim at every append
prefix; no additional current authority is inferred.

Standing kernel controls demonstrate that the prior constructor reuses one
receipt after substituting a cost vector, observation row order, or contract
payload with unchanged IDs. The new constructor admits the original exact
body and refuses all three substitutions and the legacy record. This does
not claim that a physical measurement is authentic or that production callers
already use the new constructor. Physical producer validation and operational
adoption are separate.
