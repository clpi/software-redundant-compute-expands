/-
  Re-listing, relabeling, sublists and the exact join law.

  The landed specification carried a listing premise: growth
  is read in append order, and the measure was not known to be
  invariant under re-listing. This file discharges it. The
  counter depends on its seen list only through membership,
  and it is invariant under every permutation of the scanned
  list, so the graph measure is invariant under every
  re-listing of the node list and of the incidence list
  (in particular under any reordering of the hyperedges and
  of the premises inside a hyperedge). Expansion therefore
  needs no order: any growth step that interleaves new
  elements among old ones is, up to re-listing, an append,
  and every monotonicity theorem holds for it.

  The same file proves what re-labeling does: an injective
  relabeling leaves the measure fixed, an arbitrary one can
  only raise it (merging identities adds redundancy), and
  more generally a coarser key never counts less. Dropping
  elements never raises the measure (sublist monotonicity).
  Finally the join law is made exact: the measure of a joined
  list is the sum of the parts plus the number of distinct
  values the parts share.
-/

import Join

namespace Redundant

namespace Aux

/-- The counter depends on its seen list only through
    membership. -/
theorem congr {s s' : List Nat} (h : ∀ x, x ∈ s ↔ x ∈ s')
    (l : List Nat) : aux s l = aux s' l :=
  Nat.le_antisymm (mono (fun x hx => (h x).mp hx) l)
    (mono (fun x hx => (h x).mpr hx) l)

/-- The counter is invariant under every permutation of the
    scanned list, for every seen list. -/
theorem perm {l₁ l₂ : List Nat} (p : l₁.Perm l₂) :
    ∀ seen, aux seen l₁ = aux seen l₂ := by
  induction p with
  | nil => intro _; rfl
  | cons x _ ih =>
    intro seen
    simp only [aux]
    rw [ih]
  | swap x y l =>
    intro seen
    simp only [aux]
    have hc : aux (x :: y :: seen) l = aux (y :: x :: seen) l :=
      congr (fun z => by
        simp only [List.mem_cons]
        constructor
        · rintro (h | h | h)
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        · rintro (h | h | h)
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)) l
    rw [hc]
    by_cases hx : x ∈ seen <;> by_cases hy : y ∈ seen <;>
      by_cases hxy : x = y <;> simp_all <;> omega
  | trans _ _ ih₁ ih₂ =>
    intro seen
    rw [ih₁, ih₂]

/-- Dropping elements never raises the counter: the counter
    is monotone along the sublist order, for every seen
    list. -/
theorem sublist {l₁ l₂ : List Nat} (h : l₁.Sublist l₂) :
    ∀ seen, aux seen l₁ ≤ aux seen l₂ := by
  induction h with
  | slnil => intro _; exact Nat.le_refl _
  | @cons l₁ l₂ a _ ih =>
    intro seen
    simp only [aux]
    have h1 := ih seen
    have h2 : aux seen l₂ ≤ aux (a :: seen) l₂ :=
      mono (fun x hx => List.mem_cons_of_mem a hx) l₂
    omega
  | cons₂ a _ ih =>
    intro seen
    simp only [aux]
    have h1 := ih (a :: seen)
    omega

/-- A coarser key never counts less. If, on every pair of
    elements of the seen list and the scanned list, equality
    under the finer key `f` forces equality under the coarser
    key `g`, the coarse count bounds the fine count. -/
theorem map_le {α : Type} (f g : α → Nat) :
    ∀ (l s : List α),
      (∀ a ∈ s ++ l, ∀ b ∈ s ++ l, f a = f b → g a = g b) →
      aux (s.map f) (l.map f) ≤ aux (s.map g) (l.map g) := by
  intro l
  induction l with
  | nil => intro _ _; simp [aux]
  | cons x xs ih =>
    intro s hfg
    simp only [List.map_cons, aux]
    have hsub : ∀ a ∈ (x :: s) ++ xs, a ∈ s ++ x :: xs := by
      intro a ha
      simp only [List.mem_append, List.mem_cons] at ha ⊢
      rcases ha with (h | h) | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    have hih := ih (x :: s) (fun a ha b hb => hfg a (hsub a ha) b (hsub b hb))
    simp only [List.map_cons] at hih
    by_cases hf : f x ∈ s.map f
    · have hg : g x ∈ s.map g := by
        obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hf
        have hx' : x ∈ s ++ x :: xs := by simp
        have hy' : y ∈ s ++ x :: xs := List.mem_append.mpr (Or.inl hy)
        exact List.mem_map.mpr ⟨y, hy, hfg y hy' x hx' hyx⟩
      rw [if_pos hf, if_pos hg]
      omega
    · rw [if_neg hf]
      by_cases hg : g x ∈ s.map g
      · rw [if_pos hg]; omega
      · rw [if_neg hg]; omega

end Aux

namespace Red

/-- The measure is invariant under every permutation. -/
theorem perm {l₁ l₂ : List Nat} (p : l₁.Perm l₂) : red l₁ = red l₂ :=
  Aux.perm p []

/-- Dropping elements never raises the measure. -/
theorem sublist {l₁ l₂ : List Nat} (h : l₁.Sublist l₂) :
    red l₁ ≤ red l₂ :=
  Aux.sublist h []

/-- A coarser key never counts less, on the measure. -/
theorem key_le {α : Type} (f g : α → Nat) (l : List α)
    (hfg : ∀ a ∈ l, ∀ b ∈ l, f a = f b → g a = g b) :
    red (l.map f) ≤ red (l.map g) := by
  have h := Aux.map_le f g l [] (by simpa using hfg)
  simpa [red] using h

/-- Relabeling never lowers the measure: merging identities
    can only add redundancy. -/
theorem relabel_ge (f : Nat → Nat) (l : List Nat) :
    red l ≤ red (l.map f) := by
  have h := key_le id f l (fun a _ b _ hab => by simp at hab; rw [hab])
  simpa using h

/-- An injective relabeling, on the values that occur, leaves
    the measure fixed. -/
theorem relabel_inj (f : Nat → Nat) (l : List Nat)
    (hf : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) :
    red (l.map f) = red l := by
  have h := key_le f id l hf
  simp at h
  exact Nat.le_antisymm h (relabel_ge f l)

end Red

/-- Distinct values of a list, each kept at its last
    occurrence. -/
def uniq : List Nat → List Nat
  | [] => []
  | x :: xs => if x ∈ xs then uniq xs else x :: uniq xs

/-- The number of distinct values of a list. -/
def card (l : List Nat) : Nat := (uniq l).length

/-- The number of distinct values a list shares with a second
    list. -/
def shared (a b : List Nat) : Nat :=
  ((uniq b).filter (fun v => decide (v ∈ a))).length

namespace Uniq

theorem mem {a : Nat} : ∀ l : List Nat, a ∈ uniq l ↔ a ∈ l := by
  intro l
  induction l with
  | nil => simp [uniq]
  | cons x xs ih =>
    simp only [uniq]
    by_cases hx : x ∈ xs
    · rw [if_pos hx, ih]
      constructor
      · intro h; exact List.mem_cons_of_mem x h
      · intro h
        cases List.mem_cons.mp h with
        | inl he => subst he; exact hx
        | inr he => exact he
    · rw [if_neg hx]
      simp only [List.mem_cons, ih]

theorem nodup : ∀ l : List Nat, (uniq l).Nodup := by
  intro l
  induction l with
  | nil => simp [uniq]
  | cons x xs ih =>
    simp only [uniq]
    by_cases hx : x ∈ xs
    · rw [if_pos hx]; exact ih
    · rw [if_neg hx]
      exact List.nodup_cons.mpr ⟨fun h => hx ((mem xs).mp h), ih⟩

/-- The always-false filter keeps nothing. -/
theorem filt_false : ∀ l : List Nat, l.filter (fun _ => false) = [] := by
  intro l
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [List.filter_cons, ih]

/-- Counting a duplicate-free list against a seen list
    extended by one value. -/
theorem filt_cons (x : Nat) (seen : List Nat) :
    ∀ U : List Nat, U.Nodup →
      (U.filter (fun u => decide (u ∈ x :: seen))).length
        = (U.filter (fun u => decide (u ∈ seen))).length
          + (if x ∈ U ∧ x ∉ seen then 1 else 0) := by
  intro U
  induction U with
  | nil => intro _; simp
  | cons u us ih =>
    intro hnd
    have hu : u ∉ us := (List.nodup_cons.mp hnd).1
    have hus : us.Nodup := (List.nodup_cons.mp hnd).2
    have hih := ih hus
    by_cases hux : u = x
    · subst hux
      have hc : us.filter (fun v => decide (v ∈ u :: seen))
          = us.filter (fun v => decide (v ∈ seen)) :=
        List.filter_congr (fun v hv => by
          have hvu : v ≠ u := fun h => hu (h ▸ hv)
          simp [hvu])
      have hp : decide (u ∈ u :: seen) = true := by simp
      rw [List.filter_cons_of_pos (p := fun v => decide (v ∈ u :: seen)) hp, hc]
      by_cases hs : u ∈ seen
      · have hq : decide (u ∈ seen) = true := by simp [hs]
        rw [List.filter_cons_of_pos (p := fun v => decide (v ∈ seen)) hq]
        simp [hs]
      · have hq : ¬ decide (u ∈ seen) = true := by simp [hs]
        rw [List.filter_cons_of_neg (p := fun v => decide (v ∈ seen)) hq]
        simp [hs]
    · by_cases hs : u ∈ seen
      · simp [List.filter_cons, hs, hux, hih]
        by_cases hx : x ∈ us <;> by_cases hxs : x ∈ seen <;>
          simp_all <;> omega
      · simp [List.filter_cons, hs, hux, hih]
        by_cases hx : x ∈ us <;> by_cases hxs : x ∈ seen <;>
          simp_all <;> omega

end Uniq

namespace Exact

/-- The counter, exactly: the measure of the scanned list
    plus the number of its distinct values already seen. -/
theorem aux_eq : ∀ (l seen : List Nat),
    aux seen l = red l + ((uniq l).filter (fun v => decide (v ∈ seen))).length := by
  intro l
  induction l with
  | nil => intro _; simp [aux, red, uniq]
  | cons x xs ih =>
    intro seen
    have h1 : aux seen (x :: xs)
        = (if x ∈ seen then 1 else 0) + aux (x :: seen) xs := rfl
    have h2 : red (x :: xs) = aux [x] xs := by
      show aux [] (x :: xs) = aux [x] xs
      simp [aux]
    rw [h1, h2, ih (x :: seen), ih [x],
      Uniq.filt_cons x seen (uniq xs) (Uniq.nodup xs),
      Uniq.filt_cons x [] (uniq xs) (Uniq.nodup xs)]
    simp only [uniq]
    have hmem := Uniq.mem (a := x) xs
    by_cases hx : x ∈ xs
    · rw [if_pos hx]
      by_cases hs : x ∈ seen
      · simp [hs, hx, hmem, Uniq.filt_false]; omega
      · simp [hs, hx, hmem, Uniq.filt_false]; omega
    · rw [if_neg hx]
      by_cases hs : x ∈ seen
      · simp [List.filter_cons, hs, hx, hmem, Uniq.filt_false]; omega
      · simp [List.filter_cons, hs, hx, hmem, Uniq.filt_false]

/-- Every element is either the first occurrence of its value
    or redundant: measure plus distinct count is length. -/
theorem red_add_card : ∀ l : List Nat, red l + card l = l.length := by
  intro l
  induction l with
  | nil => simp [red, aux, card, uniq]
  | cons x xs ih =>
    have h2 : red (x :: xs) = aux [x] xs := by
      show aux [] (x :: xs) = aux [x] xs
      simp [aux]
    rw [h2, aux_eq xs [x], Uniq.filt_cons x [] (uniq xs) (Uniq.nodup xs)]
    simp only [card, uniq] at ih ⊢
    have hmem := Uniq.mem (a := x) xs
    by_cases hx : x ∈ xs
    · rw [if_pos hx]; simp [hx, hmem, Uniq.filt_false]; omega
    · rw [if_neg hx]; simp [hx, hmem, Uniq.filt_false]; omega

/-- The exact join law: the measure of a joined list is the
    sum of the measures of the parts plus the number of
    distinct values they share. Superadditivity, the strict
    unit and appearance are its corollaries. -/
theorem join (a b : List Nat) :
    red (a ++ b) = red a + red b + shared a b := by
  rw [Red.append, aux_eq b a.reverse]
  simp only [shared, List.mem_reverse]
  omega

/-- Shared distinct values are bounded by either part's
    distinct count. -/
theorem shared_le (a b : List Nat) : shared a b ≤ card b := by
  simp only [shared, card]
  exact List.length_filter_le _ _

end Exact

/-- Re-listing of a graph: its node list and its incidence
    list are each permuted. -/
def Relist (g h : Graph) : Prop :=
  g.nodes.Perm h.nodes ∧ (incidence g).Perm (incidence h)

/-- Re-listing hyperedges one for one, each premise list
    permuted and each conclusion kept. -/
inductive EdgeRelist : List (List Nat × Nat) → List (List Nat × Nat) → Prop
  | nil : EdgeRelist [] []
  | cons {ps ps' : List Nat} {c : Nat} {es es' : List (List Nat × Nat)} :
      ps.Perm ps' → EdgeRelist es es' → EdgeRelist ((ps, c) :: es) ((ps', c) :: es')

/-- Expansion up to re-listing: the larger graph is a
    re-listing of an append-only expansion. This is growth
    with new elements interleaved anywhere. -/
def ExpandsR (g h : Graph) : Prop := ∃ k, Expands g k ∧ Relist k h

namespace Relist

/-- The graph measure is invariant under re-listing. -/
theorem measure_eq {g h : Graph} (r : Relist g h) : measure g = measure h := by
  simp only [measure]
  rw [Red.perm r.1, Red.perm r.2]

theorem refl (g : Graph) : Relist g g := ⟨List.Perm.refl _, List.Perm.refl _⟩

theorem trans {g h k : Graph} (r₁ : Relist g h) (r₂ : Relist h k) :
    Relist g k := ⟨r₁.1.trans r₂.1, r₁.2.trans r₂.2⟩

/-- Reordering hyperedges is a re-listing. -/
theorem edges {g h : Graph} (hn : g.nodes.Perm h.nodes)
    (he : g.edges.Perm h.edges) : Relist g h := by
  refine ⟨hn, ?_⟩
  simp only [incidence]
  exact List.Perm.flatMap_right _ he

/-- Reordering premises inside hyperedges is a re-listing. -/
theorem premises {es es' : List (List Nat × Nat)} (r : EdgeRelist es es') :
    (es.flatMap (fun e => e.1 ++ [e.2])).Perm
      (es'.flatMap (fun e => e.1 ++ [e.2])) := by
  induction r with
  | nil => exact List.Perm.refl _
  | cons hp _ ih =>
    simp only [List.flatMap_cons]
    exact List.Perm.append (List.Perm.append hp (List.Perm.refl _)) ih

/-- Growth with interleaving never lowers the measure. -/
theorem grow {g h : Graph} (hexp : ExpandsR g h) : measure g ≤ measure h := by
  obtain ⟨k, hk, r⟩ := hexp
  rw [← measure_eq r]
  exact Graph.grow hk

/-- Interleaved growth composes. -/
theorem growR_trans {g h i : Graph} (h₁ : ExpandsR g h) (h₂ : ExpandsR h i) :
    measure g ≤ measure i :=
  Nat.le_trans (grow h₁) (grow h₂)

/-- Derivability is invariant under reordering the store and
    the hyperedges. -/
theorem deriv {g h : Graph} (hn : g.nodes.Perm h.nodes)
    (he : g.edges.Perm h.edges) {c : Nat}
    (hd : Deriv g.edges g.nodes c) : Deriv h.edges h.nodes c :=
  Deriv.store (fun _ hx => hn.mem_iff.mp hx)
    (Deriv.edges (fun _ hx => he.mem_iff.mp hx) hd)

end Relist

namespace Control

/-- Control relabel: a relabeling that merges two identities
    raises the measure, so invariance holds for re-listing and
    for injective relabeling only. -/
theorem relabel : red [1, 2] = 0 ∧ red ([1, 2].map (fun _ => 0)) = 1 := by
  constructor <;> decide

/-- Control order: the counter's per-position flags do depend
    on order (the first occurrence moves), while the total does
    not. -/
theorem order : red [1, 2, 1] = red [1, 1, 2] ∧ red [1, 1, 2] = 1 := by
  constructor <;> decide

end Control

#print axioms Aux.congr
#print axioms Aux.perm
#print axioms Aux.sublist
#print axioms Aux.map_le
#print axioms Red.perm
#print axioms Red.sublist
#print axioms Red.key_le
#print axioms Red.relabel_ge
#print axioms Red.relabel_inj
#print axioms Uniq.mem
#print axioms Uniq.nodup
#print axioms Uniq.filt_false
#print axioms Uniq.filt_cons
#print axioms Exact.aux_eq
#print axioms Exact.red_add_card
#print axioms Exact.join
#print axioms Exact.shared_le
#print axioms Relist.measure_eq
#print axioms Relist.refl
#print axioms Relist.trans
#print axioms Relist.edges
#print axioms Relist.premises
#print axioms Relist.grow
#print axioms Relist.growR_trans
#print axioms Relist.deriv
#print axioms Control.relabel
#print axioms Control.order

end Redundant
