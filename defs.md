# Definitions

Every term of the model, defined at implementer resolution.
Each definition names its Lean counterpart in `proof/`; the
Lean development is the authority wherever prose and code
could drift. Four states are kept distinct throughout:
settled intent, proposed semantics, implemented behavior,
verified behavior. Everything below is implemented behavior
in the Lean development unless a line says otherwise.

## Behavioral hypergraph

A graph is a node list together with a hyperedge list; a
hyperedge is a pair of a premise list and a conclusion
node. Lean: the structure `Graph` in `proof/Core.lean`,
with fields `nodes` and `edges`. This is the list form of
the campaign's behavioral hypergraph: nodes are the
recorded facts and states, hyperedges carry full premise
sets.

## Incidence list

The incidence list of a graph flattens every hyperedge to
its premises followed by its conclusion, in edge order.
Lean: `incidence` in `proof/Core.lean`. It is the explicit
sparse content of the incidence matrix, read as a list:
every entry is one incidence of a node in a hyperedge.

## Redundancy measure of a list

The measure of a list counts its non-first occurrences:
scanning with a seen list, each element already seen
counts one. Equivalently, summed over each distinct value
of the list, its occurrence count minus one; summed over
duplicate groups, the redundant mass of the group. Lean:
the counter `aux` and the measure `red` in
`proof/Core.lean`, with `red l = aux [] l`.

## Redundancy measure of a graph

The measure of a graph is the measure of its node list
plus the measure of its incidence list. Lean: `measure`
in `proof/Core.lean`. Both components are duplicate mass
in the campaign protocol's sense: at the positivity level
the correspondence is a theorem, not a reading — the
measure is positive exactly when an explicit duplicate
witness exists (`Red.witness`).

## Duplicate witness

A duplicate witness in a list is a split of the list at an
occurrence whose value already occurs in the part before
it. Lean: `Repeat` in `proof/Core.lean`.

## Expansion

Expansion is append-only growth: the larger graph is the
smaller graph with a node list and a hyperedge list
appended, in that order, and nothing removed. Lean:
`Expands` in `proof/Core.lean`. A chain is a sequence of
graphs related by expansion step by step; expansion is
transitive (`Graph.trans`), so a chain is one expansion.

## Witnessed redundancy

A graph is witnessed redundant when its measure is at
least one: some node or some incidence occurs beyond its
first occurrence. Lean: `Witnessed` in `proof/Core.lean`.
The derivability form of a witness — a computation whose
conclusion is already derivable — is the persistence
home's criterion, mirrored here as `Deriv` (see the
specification's synthesis note).

## Join

The join of two graphs appends their node lists and their
hyperedge lists. Lean: `join` in `proof/Join.lean`, with
its incidence and measure computed by `Join.inc` and
`Join.eq`. The join is the joined structure of the
campaign: two libraries, two subjects, or a graph and its
own growth, read as one graph.

## Touched and inside

At a sample of nodes, a hyperedge is touched when its
premise-and-conclusion list meets the sample, and inside
when its whole list lies in the sample. Lean: `touched`
and `inside` in `proof/Join.lean`, as filtered edge lists;
their lengths are the touched count and the inside count
of the reconstruction protocol.
