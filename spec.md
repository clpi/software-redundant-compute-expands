# Redundant compute expands: the specification

## The claim

Settled intent, in the author's terms (directive of
2026-11-19, the universal behavioral hypergraph campaign):
any software can be proven redundant in its compute as
represented in its overarching incremental append-only
behavioral hypergraph, and a measurement overlapping any
piece of that hypergraph yields compounding constructed
measures. This repository formalizes the growth half of
that claim: what happens to redundant compute as the
hypergraph grows by expansion only.

Four states are kept distinct throughout this document:
settled intent, proposed semantics, implemented behavior,
verified behavior. The claim above is settled intent. The
Lean development in `proof/` is implemented behavior; what
the family gate checks at the landed pin is verified
behavior. Nothing below upgrades a claim's state on the
strength of prose.

## What the campaign measured (evidence, not theorems)

The empirical lane of the campaign (record of 2026-11-19,
subjects at their named pins) measured redundant compute
by exact duplicates: 47 duplicate file groups and 16
duplicate theorem groups across the estate, witnessed for
18 of 19 readable subjects. The one counterexample is the
closed loop subject at f2c3b6d6: zero duplicate file
groups, zero duplicate theorem groups. The universal form
of the claim — every system is redundant — is therefore
falsified as stated, and survives only in witnessed form.
This development carries that counterexample in its own
tree as the standing controls `Control.zero` and
`Control.universal`: a concrete graph of measure zero
exists in the model, so no theorem here states or implies
universal existence.

The same lane measured witness reconstruction on the
traceability hypergraph at 8f6a1280 (20,480 nodes, 9,356
hyperedges): a uniform sample of 20 percent of the nodes
touches about half of all hyperedges, a yield multiplier
of about 2.5 against the overlap fraction, with
kind-proportion error falling to under one percent; while
hyperedges fully inside the sample stay below a tenth of
a percent even at that overlap, so exact reconstruction
from a random overlap is refuted at those sizes. The
proved skeleton of that measurement is in this
development (touch monotonicity in the sample and in the
graph, and the inside count bounded by the touched
count); the rate itself is not a theorem and is carried
as a premise, named below.

## The executable method

1. **Record the hypergraph.** Fix the node list and the
   hyperedge list of the system at its pin. Measure
   carried: the redundancy measure of the graph
   (`measure`), split by component.
2. **Witness before claiming.** A redundancy claim names
   its witness: either an explicit duplicate
   (`Repeat`, characterized exactly by `Red.witness`)
   or a derivation of the computation's conclusion from
   the store (`Deriv`, the persistence criterion).
3. **Grow by expansion only.** Every growth step appends
   nodes and hyperedges; removals are outside the method
   and outside the theorems (control: `Control.shrink`).
4. **Carry witnesses forward, never re-derive them.** By
   `Graph.witness` and `Graph.deriv`, a witness at any
   step of a chain is a witness at every later step, and
   by `Graph.grow` the measure at the end of the chain is
   at least the measure at its start. Measure carried:
   the measure at each step, non-decreasing by theorem.
5. **Join by append, and read the compounding.** The
   joined measure is at least the sum of the parts
   (`Join.sum`), at least each part (`Join.left`,
   `Join.right`), and one unit more wherever the parts
   share a node (`Join.strict`) or an incidence value
   (`Join.edge`). Measure carried: the three bounds
   at each join.
6. **Reconstruct from overlaps by touching.** From a
   sample of nodes, the touched set is computed at zero
   subject runtime; enlarging the sample or expanding the
   graph never loses a touched hyperedge (`Touch.mono`,
   `Touch.grow`), and the fully-inside set is always part
   of the touched set (`Touch.bound`). Exact
   reconstruction is claimed only where the inside count
   is itself the measure wanted; control `Control.exact`
   keeps the distinction standing.

## Theorem inventory, at honest strength

All theorems below are proven outright in the Lean
development — full proofs, no premises inside the model,
printed axioms a subset of {propext, Quot.sound} as the
gate log shows; several depend on no axioms at all. The
premises that remain are campaign-level, outside the Lean
development, named after the inventory.

The measure (`proof/Core.lean`):

- `Aux.append` — the counter splits exactly over append,
  the second part counted against the first part as seen
  list. Proven outright.
- `Aux.mono` — the counter is monotone in the seen list.
  Proven outright.
- `Aux.pos` — a seen element occurring in the list is
  counted at least once. Proven outright.
- `Aux.witness` — a positive count yields a split of the
  list at an occurrence whose value lies in the seen list
  joined with the part before it. Proven outright.
- `Split.first` — a list splits at the first occurrence
  of any of its elements, the head part free of it.
  Proven outright.
- `Red.append` — the measure of a joined list is the
  measure of the first part plus the count of the second
  part against the first. Proven outright.
- `Red.left`, `Red.right` — each part's measure is at
  most the joined measure. Proven outright.
- `Red.sum` — superadditivity: the joined measure is at
  least the sum of the parts. Proven outright.
- `Red.strict` — an element in both parts adds one
  further unit beyond the sum. Proven outright.
- `Red.appear` — a shared element makes the joined list
  redundant even when each part alone is not. This is
  the appearance theorem of the model: redundancy has a
  threshold, and the threshold is one shared element at
  a join. Proven outright.
- `Red.witness` — the measure is positive exactly when
  an explicit duplicate witness exists. Proven outright.

Derivability and graphs (`proof/Core.lean`):

- `Deriv.store`, `Deriv.edges` — derivability is
  monotone in the store and in the recorded edges.
  Proven outright (mirrored, see the synthesis note).
- `Graph.grow` — the graph measure is monotone under
  expansion. Proven outright.
- `Graph.witness` — witnessed redundancy persists under
  expansion. Proven outright.
- `Graph.trans` — expansion is transitive. Proven
  outright, no axioms at all.
- `Graph.chain` — along any expansion chain the measure
  is non-decreasing (the two-step form; every finite
  chain follows by transitivity). Proven outright.
- `Graph.deriv` — a derivable fact stays derivable
  under expansion: the derivability form of witnessed
  redundancy is monotone under expansion. Proven
  outright, no axioms beyond propext.

Joining and touching (`proof/Join.lean`):

- `Join.inc`, `Join.eq` — the incidence and the
  measure of a join, in components. Proven outright.
- `Join.left`, `Join.right` — each part's measure is at
  most the joined measure. Proven outright.
- `Join.sum` — the joined measure is at least the sum
  of the parts: compounding into the joined structure,
  in the strongest form the model supports without a
  rate. Proven outright.
- `Join.strict`, `Join.edge` — a shared node, or
  a shared incidence value, adds one further unit.
  Proven outright.
- `Filter.mono` — filtering is monotone in the
  predicate. Proven outright.
- `Touch.mono` — enlarging the sample never un-touches
  a hyperedge. Proven outright.
- `Touch.grow` — expanding the graph never un-touches
  a hyperedge at a fixed sample. Proven outright.
- `Touch.bound` — the inside count never exceeds
  the touched count. Proven outright.

Controls (`proof/Controls.lean`): `Control.zero` and
`Control.universal` (no universal existence; the
closed-loop analogue), `Control.shrink` (removal
destroys redundancy; expansion is necessary),
`Control.free` (no overlap, no strict gain; the overlap
hypothesis is necessary), `Control.exact` (touching is
not containing; exact reconstruction refuted on the
instance), `Control.sample` (the empty sample touches
nothing; sample growth is necessary). Each is a proved
statement over concrete data.

Synthesis (`proof/Synthesis.lean`): `Synthesis.joined`
assembles the chain monotonicity, both witness
persistence forms, both compounding forms, and the
touch kernel into one statement whose only unproved
antecedent is the named empirical premise below.

## Premise labels

Three premises remain, all outside the Lean development.
No theorem's proof uses any of them; the first is carried
as an explicit antecedent of the joined theorem, the
linter silence there covering exactly that antecedent.

1. **Yield (empirical rate).** The touched yield of a
   random overlap compounds at a measured multiplier of
   about 2.5 at a fifth overlap on the traceability
   hypergraph at 8f6a1280. This is campaign evidence at a
   pin, not a theorem: the development proves the
   multiplier is at least one in the only sense the model
   states without a distribution (monotonicity and the
   inside bound), and no rate above one is claimed in
   Lean. Falsification route: recompute the touch yield
   on a pinned hypergraph at growing uniform overlaps;
   a multiplier at or below one at a fifth overlap, on a
   store whose hyperedges span more than one node on
   average, refutes the rate as a campaign claim.
2. **Listing (modeling premise).** Growth is read in
   append order. A growth step that interleaves new
   elements among old ones is represented by the append
   of the new elements in their recorded order; the
   development does not prove the measure invariant
   under re-listing, so a reading of a real system's
   growth as expansion rests on the recorded order being
   the growth order. This binds where the method is
   applied, not what the theorems say.
3. **Mirror fidelity (reading premise).** `Deriv` and
   its two monotonicity theorems are the persistence
   home's definitions and statements at eb01cf2e,
   mirrored verbatim and proved again here from the
   definitions. The proofs are this development's own;
   only the claim that the mirror is faithful rests on
   reading, as in the family's other synthesis files.

## Falsification protocols for the unproved forms

- **Universal existence** (any software is redundant):
  already refuted, twice over — by the closed loop
  subject under the campaign protocol at f2c3b6d6, and
  in the model by `Control.universal`. It is not a claim
  of this development in any form.
- **A rate for compounding of the measure itself**
  (for example, that joined redundancy grows by a fixed
  factor per shared element beyond the first): not
  claimed. The proved strict form is one unit per join
  per shared component kind; whether real joins of many
  overlapping parts compound the measure faster than the
  sum-plus-shared-units bound is an empirical question
  for the campaign's next round, settled per subject by
  computing the measure on the joined hypergraphs the
  campaign already artifacts.
- **Premise-closed reconstruction** (a sample closed
  under premises reconstructs exactly): proposed by the
  empirical lane as its next protocol, not run there and
  not formalized here. Its closing condition is a Lean
  statement of the fold form over premise-closed samples
  or a measured run of that protocol at a named pin.
