/-
  The synthesis: the joined theorem for redundant compute
  under expansion.

  One assembly of the proved parts. Every hypothesis is an
  explicit argument. The first argument group carries the
  campaign's empirical yield claim as a named premise: the
  measured compounding rate of touched hyperedges against
  overlap fraction (about 2.5 at a fifth overlap, on the
  traceability hypergraph at 8f6a1280). It is a premise
  label, not a theorem: no conjunct's proof uses it, and
  the linter silence on the theorem covers exactly that
  antecedent. What the proofs do establish is the rate's
  proved skeleton: superadditivity of the measure over
  joins, one strict unit per shared element, monotonicity
  of the touched count in the sample and in the graph, and
  containment of the inside count in the touched count.
-/

import Join

namespace Redundant

namespace Synthesis

set_option linter.unusedVariables false in
/-- The joined theorem. Read the conjuncts in order: along
    an expansion chain the measure never decreases;
    witnessed redundancy persists to the end of the chain;
    a computation redundant at the start stays redundant at
    the end; the first two graphs of the chain compound
    into their join at least additively, and strictly by
    one further unit where they share the named node; and
    the reconstruction kernel holds at the first graph —
    a larger sample touches at least as much, and what is
    fully inside a sample is always among what it touches. -/
theorem joined
    (Yield : Prop)
    (hyield : Yield)
    (g h i : Graph)
    (h1 : Expands g h) (h2 : Expands h i)
    (x : Nat) (hxg : x ∈ g.nodes) (hxh : x ∈ h.nodes)
    (c : Nat) (hder : Deriv g.edges g.nodes c)
    (s s' : List Nat) (hsub : ∀ y ∈ s, y ∈ s') :
    measure g ≤ measure i
    ∧ (Witnessed g → Witnessed i)
    ∧ Deriv i.edges i.nodes c
    ∧ measure g + measure h ≤ measure (join g h)
    ∧ measure g + measure h + 1 ≤ measure (join g h)
    ∧ (touched g s).length ≤ (touched g s').length
    ∧ (inside g s).length ≤ (touched g s).length :=
  ⟨Graph.chain h1 h2,
   fun hw => Graph.witness hw (Graph.trans h1 h2),
   Graph.deriv hder (Graph.trans h1 h2),
   Join.sum g h,
   Join.strict hxg hxh,
   Touch.mono hsub,
   Touch.bound g s⟩

#print axioms joined

end Synthesis

end Redundant
