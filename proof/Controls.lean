/-
  Standing controls for the redundant-compute model.

  Each control is a proved statement over concrete data: a
  load-bearing condition of the model is removed, varied,
  or pushed to its boundary, and the failure or the exact
  boundary is exhibited. The controls stand in the tree
  permanently; a change that breaks one has broken the
  condition it guards.
-/

import Join

namespace Redundant

namespace Example

/-- The zero graph of the first control: four distinct
    nodes, two hyperedges over disjoint node pairs, so the
    incidence list is also four distinct values. This is
    the closed-loop analogue: the family subject with zero
    duplicate groups under the campaign protocol (the
    closed loop home at f2c3b6d6). -/
def zero : Graph := ⟨[1, 2, 3, 4], [([1], 2), ([3], 4)]⟩

/-- The sample graph of the exactness control: one
    hyperedge spanning three nodes. -/
def span : Graph := ⟨[1, 2, 3], [([1, 2], 3)]⟩

end Example

namespace Control

/-- Control zero: a graph with no redundancy at all exists
    in the model. Its measure is zero and it is not
    witnessed redundant. -/
theorem zero : measure Example.zero = 0 ∧ ¬ Witnessed Example.zero := by
  refine ⟨by decide, ?_⟩
  intro hw
  have hw' : 1 ≤ measure Example.zero := hw
  have hz : measure Example.zero = 0 := by decide
  omega

/-- The universal existence claim is false in the model:
    not every graph is witnessed redundant. Any restatement
    of the campaign claim must answer this control, exactly
    as the estate claim must answer the closed-loop
    subject. -/
theorem universal : ¬ ∀ g : Graph, Witnessed g :=
  fun h => zero.2 (h Example.zero)

/-- Control shrink: removal destroys redundancy. The list
    with a duplicate has measure one; the same list with
    the duplicate removed has measure zero. Monotonicity
    is a theorem of expansion only, and this control is
    the boundary that keeps it so. -/
theorem shrink : red [1, 1] = 1 ∧ red [1] = 0 := by
  constructor <;> decide

/-- Control free: with no overlap, the strict compounding
    gain is absent. Two single-node graphs on distinct
    nodes join to a graph of measure zero, and the
    sum-plus-one bound fails. The overlap hypothesis of
    the strict theorem is necessary. -/
theorem free :
    measure (join ⟨[1], []⟩ ⟨[2], []⟩) = 0
      ∧ ¬ (measure ⟨[1], []⟩ + measure ⟨[2], []⟩ + 1
          ≤ measure (join ⟨[1], []⟩ ⟨[2], []⟩)) := by
  constructor <;> decide

/-- Control exact: touching is not containing. The sample
    node touches the single hyperedge, yet no hyperedge is
    fully inside the sample. Exact reconstruction from a
    touched overlap is refuted on this instance, matching
    the campaign measurement at every sampled size. -/
theorem exact :
    (touched Example.span [1]).length = 1
      ∧ (inside Example.span [1]).length = 0 := by
  constructor <;> decide

/-- Control sample: the touched count depends on the
    sample. The empty sample touches nothing in the sample
    graph, so the sample-growth hypothesis of the touch
    monotonicity theorem cannot be dropped. -/
theorem sample : (touched Example.span []).length = 0 := by
  decide

end Control

#print axioms Control.zero
#print axioms Control.universal
#print axioms Control.shrink
#print axioms Control.free
#print axioms Control.exact
#print axioms Control.sample

end Redundant
