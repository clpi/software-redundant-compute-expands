/-
  Redundant compute expands: the proved model.

  A behavioral hypergraph is a list of nodes together with a
  list of hyperedges, each hyperedge a premise list and a
  conclusion node. Growth is expansion only: the larger graph
  is the smaller graph with a list of nodes and a list of
  hyperedges appended; nothing is removed. The redundancy
  measure of a list counts its non-first occurrences: every
  occurrence of a value that already occurred earlier in the
  list is one unit of redundant incidence mass. The measure
  of a graph is the measure of its node list plus the measure
  of its incidence list (every hyperedge flattened to its
  premises followed by its conclusion).

  What is proved here: the measure splits exactly over append;
  it is monotone under append on both sides; it is
  superadditive over append; an element shared by both parts
  adds one further unit in the join, so redundancy appears in
  a join of two parts that may each carry none; the measure
  is positive exactly when an explicit duplicate witness
  exists. Derivability, mirrored from the persistence home at
  its pin (see the specification), is monotone in the store
  and in the recorded edges, so a witnessed redundant
  computation stays redundant under every expansion, and the
  graph-level measure is monotone along every expansion
  chain. Every theorem below is proved in full.
-/

namespace Redundant

/-- The backward duplicate counter: scanning a list with a
    seen list, count each element that is already seen. -/
def aux : List Nat → List Nat → Nat
  | _, [] => 0
  | seen, x :: xs => (if x ∈ seen then 1 else 0) + aux (x :: seen) xs

/-- The redundancy measure of a list: the number of non-first
    occurrences, computed as the backward count from the
    empty seen list. -/
def red (l : List Nat) : Nat := aux [] l

/-- An explicit duplicate witness in a list: a split of the
    list at an occurrence whose value already occurs in the
    part before it. -/
def Repeat (l : List Nat) : Prop :=
  ∃ x s t, l = s ++ x :: t ∧ x ∈ s

namespace Aux

/-- The counter splits exactly over append: counting over a
    joined list is counting over the first part, then counting
    over the second part with the first part's elements added
    to the seen list. -/
theorem append (seen : List Nat) (a b : List Nat) :
    aux seen (a ++ b) = aux seen a + aux (a.reverse ++ seen) b := by
  induction a generalizing seen with
  | nil => simp [aux]
  | cons x xs ih =>
    simp only [List.cons_append, aux, List.reverse_cons]
    rw [ih, List.append_assoc]
    ac_rfl

/-- The counter is monotone in the seen list: a larger seen
    list counts at least as much over the same list. -/
theorem mono {s s' : List Nat} (h : ∀ x ∈ s, x ∈ s') (l : List Nat) :
    aux s l ≤ aux s' l := by
  induction l generalizing s s' with
  | nil => simp [aux]
  | cons x xs ih =>
    have h' : ∀ y ∈ x :: s, y ∈ x :: s' := by
      intro y hy
      cases List.mem_cons.mp hy with
      | inl he => subst he; exact List.mem_cons.mpr (Or.inl rfl)
      | inr he => exact List.mem_cons_of_mem x (h y he)
    have hih := ih h'
    simp only [aux]
    by_cases hx : x ∈ s
    · have hx' : x ∈ s' := h x hx
      simp [hx, hx']
      omega
    · by_cases hx' : x ∈ s'
      · simp [hx, hx']
        omega
      · simp [hx, hx']
        exact hih

/-- A seen element that occurs in the list is counted at
    least once. -/
theorem pos {x : Nat} : ∀ (seen l : List Nat),
    x ∈ seen → x ∈ l → 1 ≤ aux seen l := by
  intro seen l
  induction l generalizing seen with
  | nil => intro _ h; simp at h
  | cons y ys ih =>
    intro hseen h
    simp only [aux]
    cases List.mem_cons.mp h with
    | inl he =>
      subst he
      rw [if_pos hseen]
      exact Nat.le_add_right 1 _
    | inr he =>
      have hih := ih _ (List.mem_cons_of_mem y hseen) he
      omega

/-- One direction of the witness characterization at the
    counter level: a positive count over any seen list yields
    a split of the list at an occurrence whose value lies in
    the seen list joined with the part before it. -/
theorem witness {seen : List Nat} :
    ∀ l : List Nat, 1 ≤ aux seen l →
      ∃ x s t, l = s ++ x :: t ∧ x ∈ seen ++ s := by
  intro l
  induction l generalizing seen with
  | nil => intro h; simp [aux] at h
  | cons y ys ih =>
    intro h
    simp only [aux] at h
    by_cases hy : y ∈ seen
    · refine ⟨y, [], ys, by simp, ?_⟩
      rw [List.append_nil]
      exact hy
    · have hpos : 1 ≤ aux (y :: seen) ys := by
        simp [hy] at h
        exact h
      obtain ⟨x, s, t, he, hx⟩ := ih hpos
      refine ⟨x, y :: s, t, ?_, ?_⟩
      · rw [List.cons_append, ← he]
      · have hx' : x ∈ y :: (seen ++ s) := hx
        cases List.mem_cons.mp hx' with
        | inl he2 =>
          subst he2
          exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
        | inr he2 =>
          cases List.mem_append.mp he2 with
          | inl h3 => exact List.mem_append.mpr (Or.inl h3)
          | inr h3 =>
            exact List.mem_append.mpr
              (Or.inr (List.mem_cons_of_mem y h3))

end Aux

namespace Split

/-- Splitting a list at the first occurrence of an element:
    the part before the split does not contain the element. -/
theorem first {x : Nat} :
    ∀ l : List Nat, x ∈ l →
      ∃ s t, l = s ++ x :: t ∧ x ∉ s := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons y ys ih =>
    intro h
    by_cases hxy : x = y
    · subst hxy
      exact ⟨[], ys, by simp, by simp⟩
    · have he : x ∈ ys := (List.mem_cons.mp h).resolve_left hxy
      obtain ⟨s, t, hst, hx⟩ := ih he
      refine ⟨y :: s, t, ?_, ?_⟩
      · rw [List.cons_append, ← hst]
      · intro hm
        cases List.mem_cons.mp hm with
        | inl he2 => exact hxy he2
        | inr he2 => exact hx he2

end Split

namespace Red

/-- The measure splits over append: the measure of a joined
    list is the measure of the first part plus the count of
    the second part against the first part as seen list. -/
theorem append (a b : List Nat) :
    red (a ++ b) = red a + aux (a.reverse) b := by
  show aux [] (a ++ b) = aux [] a + aux (a.reverse) b
  rw [Aux.append, List.append_nil]

/-- The measure of the first part never exceeds the measure
    of the joined list. -/
theorem left (a b : List Nat) : red a ≤ red (a ++ b) := by
  rw [append]
  exact Nat.le_add_right _ _

/-- The measure of the second part never exceeds the measure
    of the joined list: enlarging the seen list only adds
    counts. -/
theorem right (a b : List Nat) : red b ≤ red (a ++ b) := by
  rw [append]
  have hm : red b ≤ aux (a.reverse) b :=
    Aux.mono (s := []) (s' := a.reverse)
      (fun x hx => by simp at hx) b
  omega

/-- Superadditivity: the measure of a joined list is at
    least the sum of the measures of its parts. Redundancy
    compounds into the joined structure; it never cancels. -/
theorem sum (a b : List Nat) : red a + red b ≤ red (a ++ b) := by
  rw [append]
  have hm : red b ≤ aux (a.reverse) b :=
    Aux.mono (s := []) (s' := a.reverse)
      (fun x hx => by simp at hx) b
  omega

/-- Strict compounding under overlap: an element occurring
    in both parts contributes one further unit to the joined
    measure, beyond the sum of the parts. -/
theorem strict {x : Nat} {a b : List Nat}
    (ha : x ∈ a) (hb : x ∈ b) :
    red a + red b + 1 ≤ red (a ++ b) := by
  obtain ⟨s, t, rfl, hxnot⟩ := Split.first b hb
  have hxr : x ∈ a.reverse := List.mem_reverse.mpr ha
  have hxrs : x ∈ s.reverse ++ a.reverse :=
    List.mem_append.mpr (Or.inr hxr)
  have hxns : x ∉ s.reverse :=
    fun h => hxnot (List.mem_reverse.mp h)
  have e1 : aux (a.reverse) (s ++ x :: t)
      = aux (a.reverse) s + (1 + aux (x :: (s.reverse ++ a.reverse)) t) := by
    rw [Aux.append]
    simp only [aux]
    rw [if_pos hxrs]
  have e2 : red (s ++ x :: t) = red s + aux (x :: s.reverse) t := by
    rw [append]
    simp only [aux]
    rw [if_neg hxns, Nat.zero_add]
  have hm1 : red s ≤ aux (a.reverse) s :=
    Aux.mono (s := []) (s' := a.reverse) (fun y hy => by simp at hy) s
  have hm2 : aux (x :: s.reverse) t ≤ aux (x :: (s.reverse ++ a.reverse)) t :=
    Aux.mono (fun y hy => by
      cases List.mem_cons.mp hy with
      | inl he => subst he; exact List.mem_cons.mpr (Or.inl rfl)
      | inr he =>
        exact List.mem_cons_of_mem x
          (List.mem_append.mpr (Or.inl he))) t
  have e3 : red (a ++ (s ++ x :: t))
      = red a + aux (a.reverse) (s ++ x :: t) := append a (s ++ x :: t)
  rw [e3, e1, e2]
  omega

/-- Appearance: an element shared by two parts makes the
    joined list redundant, even if each part alone carries
    no redundancy at all. -/
theorem appear {x : Nat} {a b : List Nat}
    (ha : x ∈ a) (hb : x ∈ b) : 1 ≤ red (a ++ b) := by
  have h := strict ha hb
  omega

/-- The measure is positive exactly when an explicit
    duplicate witness exists. -/
theorem witness (l : List Nat) : 1 ≤ red l ↔ Repeat l := by
  constructor
  · intro h
    have h' : 1 ≤ aux [] l := h
    obtain ⟨x, s, t, he, hx⟩ := Aux.witness l h'
    refine ⟨x, s, t, he, ?_⟩
    simpa using hx
  · rintro ⟨x, s, t, rfl, hx⟩
    have hxr : x ∈ s.reverse := List.mem_reverse.mpr hx
    have e : aux (s.reverse) (x :: t)
        = 1 + aux (x :: s.reverse) t := by
      simp only [aux]
      rw [if_pos hxr]
    rw [append, e]
    omega

end Red

/-- Derivability of a fact from a store of base facts through
    a list of recorded hyperedges. An edge is a pair of a
    premise list and a conclusion. Mirrored from the
    persistence home (software-persistence-is-minimal at
    eb01cf2e), where the same definition carries the
    fixed-store redundancy criterion; the statements proved
    from it here are the expansion forms this home adds. -/
inductive Deriv (edges : List (List Nat × Nat)) (base : List Nat) :
    Nat → Prop where
  | base {c : Nat} : c ∈ base → Deriv edges base c
  | step {ps : List Nat} {c : Nat} : (ps, c) ∈ edges →
      (∀ p ∈ ps, Deriv edges base p) → Deriv edges base c

namespace Deriv

/-- Derivability is monotone in the store: a larger store
    derives at least as much. -/
theorem store {edges : List (List Nat × Nat)}
    {base base' : List Nat}
    (hsub : ∀ x ∈ base, x ∈ base') {c : Nat}
    (h : Deriv edges base c) : Deriv edges base' c := by
  induction h with
  | base hmem => exact Deriv.base (hsub _ hmem)
  | step hedge _ ih => exact Deriv.step hedge ih

/-- Derivability is monotone in the recorded edges: recording
    more edges derives at least as much. -/
theorem edges {edges edges' : List (List Nat × Nat)}
    (hsub : ∀ e ∈ edges, e ∈ edges') {base : List Nat} {c : Nat}
    (h : Deriv edges base c) : Deriv edges' base c := by
  induction h with
  | base hmem => exact Deriv.base hmem
  | step hedge _ ih => exact Deriv.step (hsub _ hedge) ih

end Deriv

/-- A behavioral hypergraph: a node list and a hyperedge
    list, each hyperedge a premise list and a conclusion. -/
structure Graph where
  nodes : List Nat
  edges : List (List Nat × Nat)

/-- The incidence list of a graph: every hyperedge flattened
    to its premises followed by its conclusion, in edge
    order. -/
def incidence (g : Graph) : List Nat :=
  g.edges.flatMap (fun e => e.1 ++ [e.2])

/-- The redundancy measure of a graph: redundant node
    occurrences plus redundant incidence occurrences. -/
def measure (g : Graph) : Nat := red g.nodes + red (incidence g)

/-- Expansion: the second graph is the first with a node
    list and a hyperedge list appended. Nothing is removed;
    this is the append-only growth of the campaign model. -/
def Expands (g h : Graph) : Prop :=
  ∃ dn de, h.nodes = g.nodes ++ dn ∧ h.edges = g.edges ++ de

/-- Witnessed redundancy of a graph: its measure is at
    least one, which by the witness characterization is an
    explicit duplicate in the node list or the incidence
    list. -/
def Witnessed (g : Graph) : Prop := 1 ≤ measure g

namespace Graph

/-- The measure is monotone under expansion: appended nodes
    and appended hyperedges never decrease the redundancy
    of a graph. -/
theorem grow {g h : Graph} (hexp : Expands g h) :
    measure g ≤ measure h := by
  obtain ⟨dn, de, hn, he⟩ := hexp
  simp only [measure, incidence]
  rw [hn, he, List.flatMap_append]
  exact Nat.add_le_add (Red.left _ _) (Red.left _ _)

/-- Witnessed redundancy persists under expansion: once a
    graph carries a duplicate witness, every expansion of
    it carries one. -/
theorem witness {g h : Graph} (hw : Witnessed g)
    (hexp : Expands g h) : Witnessed h :=
  Nat.le_trans hw (grow hexp)

/-- Expansion is transitive: expansions compose into an
    expansion. -/
theorem trans {g h i : Graph} (h1 : Expands g h)
    (h2 : Expands h i) : Expands g i := by
  obtain ⟨dn, de, hn, he⟩ := h1
  obtain ⟨dn', de', hn', he'⟩ := h2
  refine ⟨dn ++ dn', de ++ de', ?_, ?_⟩
  · rw [hn', hn, List.append_assoc]
  · rw [he', he, List.append_assoc]

/-- Along any expansion chain the measure is
    non-decreasing: the two-step form, from which every
    finite chain follows by the transitivity above. -/
theorem chain {g h i : Graph} (h1 : Expands g h)
    (h2 : Expands h i) : measure g ≤ measure i :=
  Nat.le_trans (grow h1) (grow h2)

/-- A derivable fact stays derivable under expansion: a
    computation witnessed redundant against a graph stays
    redundant against every expansion of that graph. -/
theorem deriv {g h : Graph} {c : Nat}
    (hder : Deriv g.edges g.nodes c) (hexp : Expands g h) :
    Deriv h.edges h.nodes c := by
  obtain ⟨dn, de, hn, he⟩ := hexp
  apply Deriv.store (base' := h.nodes)
  · intro x hx
    rw [hn]
    exact List.mem_append.mpr (Or.inl hx)
  · apply Deriv.edges (edges' := h.edges)
    · intro e he2
      rw [he]
      exact List.mem_append.mpr (Or.inl he2)
    · exact hder

end Graph

#print axioms Aux.append
#print axioms Aux.mono
#print axioms Aux.pos
#print axioms Aux.witness
#print axioms Split.first
#print axioms Red.append
#print axioms Red.left
#print axioms Red.right
#print axioms Red.sum
#print axioms Red.strict
#print axioms Red.appear
#print axioms Red.witness
#print axioms Deriv.store
#print axioms Deriv.edges
#print axioms Graph.grow
#print axioms Graph.witness
#print axioms Graph.trans
#print axioms Graph.chain
#print axioms Graph.deriv

end Redundant
