/-
  Joining and touching: compounding into the joined
  structure, and the witness reconstruction kernel.

  The join of two graphs appends their node lists and their
  hyperedge lists. The core file proves the joined measure
  is at least the sum of the parts (superadditivity) for a
  single list; here that lifts to graphs, in both components,
  and an element shared by the two parts — in the node lists
  or in the incidence lists — adds one further unit.

  The touch kernel is the proved part of witness
  reconstruction: a sample of nodes touches the hyperedges
  that meet it, and the hyperedges fully inside the sample
  are always among the touched ones. Enlarging the sample
  never un-touches a hyperedge, and expanding the graph
  never un-touches one either. What touching does not give
  is containment: the controls file carries the concrete
  refutation. The rate at which touching compounds (the
  campaign's measured yield of about 2.5 at a fifth overlap)
  is campaign evidence, not a theorem; it is carried as a
  premise label in the synthesis file.
-/

import Core

namespace Redundant

/-- The join of two graphs: node lists appended, hyperedge
    lists appended. -/
def join (g h : Graph) : Graph :=
  ⟨g.nodes ++ h.nodes, g.edges ++ h.edges⟩

namespace Join

/-- The incidence of a join is the append of the
    incidences. -/
theorem inc (g h : Graph) :
    incidence (join g h) = incidence g ++ incidence h := by
  simp [join, incidence, List.flatMap_append]

/-- The measure of a join, in components. -/
theorem eq (g h : Graph) :
    measure (join g h)
      = red (g.nodes ++ h.nodes)
        + red (incidence g ++ incidence h) := by
  have hi := inc g h
  show red (join g h).nodes + red (incidence (join g h)) = _
  rw [hi]
  rfl

/-- The measure of the first part never exceeds the measure
    of the join. -/
theorem left (g h : Graph) : measure g ≤ measure (join g h) := by
  rw [eq]
  exact Nat.add_le_add (Red.left _ _) (Red.left _ _)

/-- The measure of the second part never exceeds the measure
    of the join. -/
theorem right (g h : Graph) : measure h ≤ measure (join g h) := by
  rw [eq]
  exact Nat.add_le_add (Red.right _ _) (Red.right _ _)

/-- Compounding: the measure of the join is at least the
    sum of the measures of the parts. Redundancy in the
    parts compounds into the joined structure; none of it
    cancels. -/
theorem sum (g h : Graph) :
    measure g + measure h ≤ measure (join g h) := by
  have h1 : red g.nodes + red h.nodes ≤ red (g.nodes ++ h.nodes) :=
    Red.sum _ _
  have h2 : red (incidence g) + red (incidence h)
      ≤ red (incidence g ++ incidence h) := Red.sum _ _
  rw [eq]
  simp only [measure]
  omega

/-- Strict compounding under node overlap: a node occurring
    in both parts adds one further unit to the joined
    measure, beyond the sum of the parts. -/
theorem strict {g h : Graph} {x : Nat}
    (hg : x ∈ g.nodes) (hh : x ∈ h.nodes) :
    measure g + measure h + 1 ≤ measure (join g h) := by
  have h1 : red g.nodes + red h.nodes + 1
      ≤ red (g.nodes ++ h.nodes) := Red.strict hg hh
  have h2 : red (incidence g) + red (incidence h)
      ≤ red (incidence g ++ incidence h) := Red.sum _ _
  rw [eq]
  simp only [measure]
  omega

/-- Strict compounding under incidence overlap: a value
    occurring in the incidence of both parts adds one
    further unit to the joined measure. -/
theorem edge {g h : Graph} {x : Nat}
    (hg : x ∈ incidence g) (hh : x ∈ incidence h) :
    measure g + measure h + 1 ≤ measure (join g h) := by
  have h1 : red g.nodes + red h.nodes ≤ red (g.nodes ++ h.nodes) :=
    Red.sum _ _
  have h2 : red (incidence g) + red (incidence h) + 1
      ≤ red (incidence g ++ incidence h) := Red.strict hg hh
  rw [eq]
  simp only [measure]
  omega

end Join

namespace Filter

/-- Filtering with a weaker predicate keeps at least as
    many elements: the length of the filtered list is
    monotone in the predicate. -/
theorem mono {p q : (List Nat × Nat) → Bool}
    (h : ∀ e, p e = true → q e = true) :
    ∀ l : List (List Nat × Nat),
      (l.filter p).length ≤ (l.filter q).length := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases hp : p a = true
    · have hq : q a = true := h a hp
      simp [List.filter_cons, hp, hq]
      omega
    · by_cases hq : q a = true
      · simp [List.filter_cons, hp, hq]
        omega
      · simp [List.filter_cons, hp, hq]
        exact ih

end Filter

/-- The hyperedges of a graph touched by a sample of nodes:
    those whose premise-and-conclusion list meets the
    sample. -/
def touched (g : Graph) (s : List Nat) :
    List (List Nat × Nat) :=
  g.edges.filter (fun e => (e.1 ++ [e.2]).any (fun n => decide (n ∈ s)))

/-- The hyperedges of a graph fully inside a sample of
    nodes: every premise and the conclusion in the sample. -/
def inside (g : Graph) (s : List Nat) :
    List (List Nat × Nat) :=
  g.edges.filter (fun e => (e.1 ++ [e.2]).all (fun n => decide (n ∈ s)))

namespace Touch

/-- Enlarging the sample never un-touches a hyperedge: the
    touched count is monotone in the sample. Reconstruction
    from a larger overlap keeps every touched fact of the
    smaller one. -/
theorem mono {g : Graph} {s s' : List Nat}
    (hsub : ∀ x ∈ s, x ∈ s') :
    (touched g s).length ≤ (touched g s').length := by
  simp only [touched]
  apply Filter.mono _ g.edges
  intro e he
  rw [List.any_eq_true] at he ⊢
  obtain ⟨n, hn, hdec⟩ := he
  refine ⟨n, hn, ?_⟩
  have hns : n ∈ s := of_decide_eq_true hdec
  have hns' : n ∈ s' := hsub n hns
  simp [hns']

/-- Expanding the graph never un-touches a hyperedge at a
    fixed sample. -/
theorem grow {g h : Graph} (hexp : Expands g h) (s : List Nat) :
    (touched g s).length ≤ (touched h s).length := by
  obtain ⟨dn, de, hn, he⟩ := hexp
  simp only [touched]
  rw [he, List.filter_append, List.length_append]
  exact Nat.le_add_right _ _

/-- Every hyperedge fully inside a sample is touched by it:
    the inside count never exceeds the touched count. -/
theorem bound (g : Graph) (s : List Nat) :
    (inside g s).length ≤ (touched g s).length := by
  simp only [inside, touched]
  apply Filter.mono _ g.edges
  intro e he
  rw [List.all_eq_true] at he
  rw [List.any_eq_true]
  have h2 : e.2 ∈ e.1 ++ [e.2] :=
    List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
  exact ⟨e.2, h2, he e.2 h2⟩

end Touch

#print axioms Join.inc
#print axioms Join.eq
#print axioms Join.left
#print axioms Join.right
#print axioms Join.sum
#print axioms Join.strict
#print axioms Join.edge
#print axioms Filter.mono
#print axioms Touch.mono
#print axioms Touch.grow
#print axioms Touch.bound

end Redundant
