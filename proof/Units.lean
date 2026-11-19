/-
  Measurement units beside the graph measure, and resolution.

  The campaign protocol counts duplicate files and duplicate
  theorem statements. Two further units are stated here and
  tied to the graph measure by theorem, so that rows measured
  in them carry proven properties.

  The behavior unit (gap G1) counts redundant hyperedge
  realizations: hyperedges whose signature, a key of the
  hyperedge, already occurred. It is monotone under expansion,
  exact over joins, invariant under reordering, and it never
  exceeds the incidence component of the graph measure when
  the signature determines the conclusion. Resolving
  signatures more coarsely (merging per-library identities)
  never lowers it.

  The record unit (gap G6) counts redundant records across a
  store of files. It is monotone under appending files, exact
  over joins, and it bounds the file unit from above whenever
  files are nonempty: a duplicate file is at least one
  duplicate record, while records can repeat across distinct
  files (control `Control.records`).

  Resolution. A drill-down replaces each item by its finer
  decomposition (a file by its symbol records). Drilling down
  never lowers redundancy when equal coarse keys have equal
  decompositions and no decomposition is empty; the symbol is
  the floor, where drilling down is the identity; along a
  drill-down chain the measure is non-decreasing and bounded
  by the length of the finest list, so it settles. Coarser
  views of the same items are projections and count at least
  as much as finer ones; that direction is the opposite of
  drill-down, and the controls keep both directions standing.
  Appending a finer layer beside the coarse one is an
  expansion, so every persistence theorem applies to it.
-/

import Color

namespace Redundant

/-- The conclusions of a graph's hyperedges are a sublist of
    its incidence list. -/
theorem concl_sublist : ∀ es : List (List Nat × Nat),
    (es.map Prod.snd).Sublist (es.flatMap (fun e => e.1 ++ [e.2])) := by
  intro es
  induction es with
  | nil => exact List.Sublist.slnil
  | cons e es ih =>
    simp only [List.map_cons, List.flatMap_cons]
    have h1 : [e.2].Sublist (e.1 ++ [e.2]) := List.sublist_append_right _ _
    have := List.Sublist.append h1 ih
    simpa using this

/-- The behavior unit: redundant hyperedge realizations under
    a signature key. -/
def sigRed (key : (List Nat × Nat) → Nat) (g : Graph) : Nat :=
  red (g.edges.map key)

namespace Sig

theorem grow (key : (List Nat × Nat) → Nat) {g h : Graph}
    (hexp : Expands g h) : sigRed key g ≤ sigRed key h := by
  obtain ⟨_, _, _, he⟩ := hexp
  simp only [sigRed, he, List.map_append]
  exact Red.left _ _

/-- The behavior unit over a join, exactly: the sum of the
    parts plus the signatures they share. -/
theorem join (key : (List Nat × Nat) → Nat) (g h : Graph) :
    sigRed key (Redundant.join g h)
      = sigRed key g + sigRed key h + shared (g.edges.map key) (h.edges.map key) := by
  simp only [sigRed, Redundant.join, List.map_append]
  exact Exact.join _ _

theorem witness (key : (List Nat × Nat) → Nat) (g : Graph) :
    1 ≤ sigRed key g ↔ Repeat (g.edges.map key) := Red.witness _

theorem relist (key : (List Nat × Nat) → Nat) {g h : Graph}
    (p : g.edges.Perm h.edges) : sigRed key g = sigRed key h :=
  Red.perm (p.map key)

/-- Resolution never lowers the behavior unit: a resolved key
    that merges what the raw key separates counts at least as
    much. -/
theorem resolve (raw res : (List Nat × Nat) → Nat) (g : Graph)
    (hfac : ∀ e ∈ g.edges, ∀ f ∈ g.edges, raw e = raw f → res e = res f) :
    sigRed raw g ≤ sigRed res g :=
  Red.key_le raw res g.edges hfac

/-- The behavior unit never exceeds the incidence component
    of the graph measure, when the signature determines the
    conclusion. -/
theorem le_incidence (key : (List Nat × Nat) → Nat) (g : Graph)
    (hk : ∀ e ∈ g.edges, ∀ f ∈ g.edges, key e = key f → e.2 = f.2) :
    sigRed key g ≤ red (incidence g) :=
  Nat.le_trans (Red.key_le key Prod.snd g.edges hk)
    (Red.sublist (concl_sublist g.edges))

theorem le_measure (key : (List Nat × Nat) → Nat) (g : Graph)
    (hk : ∀ e ∈ g.edges, ∀ f ∈ g.edges, key e = key f → e.2 = f.2) :
    sigRed key g ≤ measure g := by
  have := le_incidence key g hk
  simp only [measure]
  omega

end Sig

/-- The file unit: redundant files under a content key. -/
def fileRed (hf : List Nat → Nat) (store : List (List Nat)) : Nat :=
  red (store.map hf)

/-- The record unit: redundant records across the store. -/
def recRed (store : List (List Nat)) : Nat := red store.flatten

namespace Drill

/-- Drill-down at the counter: coarse items against coarse
    seen items, fine records against fine seen records. -/
theorem aux_le {α : Type} (k : α → Nat) (d : α → List Nat) :
    ∀ (l S : List α),
      (∀ a ∈ S ++ l, ∀ b ∈ S ++ l, k a = k b → d a = d b) →
      (∀ a ∈ S ++ l, d a ≠ []) →
      aux (S.map k) (l.map k) ≤ aux (S.flatMap d) (l.flatMap d) := by
  intro l
  induction l with
  | nil => intro _ _ _; simp [aux]
  | cons x xs ih =>
    intro S hkd hne
    simp only [List.map_cons, List.flatMap_cons, aux]
    rw [Aux.append]
    have hsub : ∀ a ∈ (x :: S) ++ xs, a ∈ S ++ x :: xs := by
      intro a ha
      simp only [List.mem_append, List.mem_cons] at ha ⊢
      rcases ha with (h | h) | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    have hih := ih (x :: S) (fun a ha b hb => hkd a (hsub a ha) b (hsub b hb))
      (fun a ha => hne a (hsub a ha))
    simp only [List.map_cons, List.flatMap_cons] at hih
    have hc : aux (d x ++ S.flatMap d) (xs.flatMap d)
        = aux ((d x).reverse ++ S.flatMap d) (xs.flatMap d) :=
      Aux.congr (fun z => by simp [List.mem_append, List.mem_reverse]) _
    rw [hc] at hih
    by_cases hk : k x ∈ S.map k
    · rw [if_pos hk]
      obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hk
      have hx' : x ∈ S ++ x :: xs := by simp
      have hy' : y ∈ S ++ x :: xs := List.mem_append.mpr (Or.inl hy)
      have hdy : d y = d x := hkd y hy' x hx' hyx
      have hnx : d x ≠ [] := hne x hx'
      obtain ⟨z, hz⟩ : ∃ z, z ∈ d x := by
        cases hdx : d x with
        | nil => exact absurd hdx hnx
        | cons z _ => exact ⟨z, by simp⟩
      have hzS : z ∈ S.flatMap d := List.mem_flatMap.mpr ⟨y, hy, hdy ▸ hz⟩
      have := Aux.pos (S.flatMap d) (d x) hzS hz
      omega
    · rw [if_neg hk]
      omega

/-- Drill-down never lowers redundancy: when equal coarse
    keys have equal decompositions and no decomposition is
    empty, the fine records are at least as redundant as the
    coarse items. -/
theorem le {α : Type} (k : α → Nat) (d : α → List Nat) (l : List α)
    (hkd : ∀ a ∈ l, ∀ b ∈ l, k a = k b → d a = d b)
    (hne : ∀ a ∈ l, d a ≠ []) :
    red (l.map k) ≤ red (l.flatMap d) := by
  have := aux_le k d l [] (by simpa using hkd) (by simpa using hne)
  simpa [red] using this

/-- The symbol floor: drilling a symbol down to itself is the
    identity, so no finer view adds anything. -/
theorem floor (l : List Nat) : l.flatMap (fun a => [a]) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- The measure is bounded by the length of the list it is
    taken over. -/
theorem bound (l : List Nat) : red l ≤ l.length := by
  have := Exact.red_add_card l
  omega

/-- A two-step drill-down chain (files to records to
    symbols) is non-decreasing and bounded by the finest
    list's length. -/
theorem chain {α β : Type} (k : α → Nat) (d₁ : α → List β) (k₁ : β → Nat)
    (d₂ : β → List Nat) (l : List α)
    (h₁ : ∀ a ∈ l, ∀ b ∈ l, k a = k b → (d₁ a).map k₁ = (d₁ b).map k₁)
    (n₁ : ∀ a ∈ l, (d₁ a).map k₁ ≠ [])
    (h₂ : ∀ a ∈ l.flatMap d₁, ∀ b ∈ l.flatMap d₁, k₁ a = k₁ b → d₂ a = d₂ b)
    (n₂ : ∀ a ∈ l.flatMap d₁, d₂ a ≠ []) :
    red (l.map k) ≤ red ((l.flatMap d₁).map k₁)
      ∧ red ((l.flatMap d₁).map k₁) ≤ red ((l.flatMap d₁).flatMap d₂)
      ∧ red ((l.flatMap d₁).flatMap d₂) ≤ ((l.flatMap d₁).flatMap d₂).length := by
  have e : (l.flatMap d₁).map k₁ = l.flatMap (fun a => (d₁ a).map k₁) := by
    simp [List.map_flatMap]
  refine ⟨?_, le k₁ d₂ _ h₂ n₂, bound _⟩
  rw [e]
  exact le k (fun a => (d₁ a).map k₁) l h₁ n₁

/-- Appending a finer layer beside the coarse one is an
    expansion: the measure does not drop and every witness
    persists. -/
theorem layer (g : Graph) (fine : List Nat) :
    Expands g ⟨g.nodes ++ fine, g.edges⟩
      ∧ measure g ≤ measure ⟨g.nodes ++ fine, g.edges⟩ := by
  have hx : Expands g ⟨g.nodes ++ fine, g.edges⟩ := ⟨fine, [], rfl, by simp⟩
  exact ⟨hx, Graph.grow hx⟩

end Drill

namespace Rec

theorem grow (store more : List (List Nat)) : recRed store ≤ recRed (store ++ more) := by
  simp only [recRed, List.flatten_append]
  exact Red.left _ _

theorem join (a b : List (List Nat)) :
    recRed (a ++ b) = recRed a + recRed b + shared a.flatten b.flatten := by
  simp only [recRed, List.flatten_append]
  exact Exact.join _ _

/-- The record unit bounds the file unit: with an injective
    file key and nonempty files, every duplicate file is at
    least one duplicate record. -/
theorem file_le (hf : List Nat → Nat) (store : List (List Nat))
    (hinj : ∀ a ∈ store, ∀ b ∈ store, hf a = hf b → a = b)
    (hne : ∀ a ∈ store, a ≠ []) : fileRed hf store ≤ recRed store := by
  have := Drill.le hf id store hinj hne
  simpa [fileRed, recRed, List.flatMap_id'] using this

end Rec

namespace Control

/-- Control records: records repeat across distinct files
    while the file unit is zero, so the record layer sees what
    the file unit cannot. -/
theorem records :
    red ([[1, 2], [2, 3]].map (fun f => f.sum * 100 + f.length)) = 0
      ∧ recRed [[1, 2], [2, 3]] = 1 := by
  constructor <;> decide

/-- Control empty: a drill-down with an empty decomposition
    can lose redundancy, so the nonempty hypothesis is
    necessary. -/
theorem empty : red ([5, 5].map id) = 1 ∧ red ([5, 5].flatMap (fun _ => ([] : List Nat))) = 0 := by
  constructor <;> decide

/-- Control signature: incidence redundancy without any
    behavior duplicate: two hyperedges sharing a conclusion
    with different premises. The behavior unit bound is not an
    equality. -/
theorem signature :
    sigRed (fun e => e.1.sum * 1000 + e.2) ⟨[], [([1], 3), ([2], 3)]⟩ = 0
      ∧ red (incidence ⟨[], [([1], 3), ([2], 3)]⟩) = 1 := by
  constructor <;> decide

/-- Control projection: on the same items a finer key can
    show less redundancy than a coarser one; drill-down and
    projection move the measure in opposite directions. -/
theorem projection : red [10, 11] = 0 ∧ red ([10, 11].map (fun x => x / 10)) = 1 := by
  constructor <;> decide

end Control

#print axioms concl_sublist
#print axioms Sig.grow
#print axioms Sig.join
#print axioms Sig.witness
#print axioms Sig.relist
#print axioms Sig.resolve
#print axioms Sig.le_incidence
#print axioms Sig.le_measure
#print axioms Drill.aux_le
#print axioms Drill.le
#print axioms Drill.floor
#print axioms Drill.bound
#print axioms Drill.chain
#print axioms Drill.layer
#print axioms Rec.grow
#print axioms Rec.join
#print axioms Rec.file_le
#print axioms Control.records
#print axioms Control.empty
#print axioms Control.signature
#print axioms Control.projection

end Redundant
