/-
  Computable derivability on the canonical hypergraph.

  `clos` computes, by iterated firing, exactly the terms
  derivable in the view at level `r` under a color test `q`.
  Proved: every computed term is derivable (`sound`); a stable
  set holds every derivable term (`complete_of_stable`); the
  iteration is stable after `log.length` rounds from any start
  (`iter_stable`), so `clos` is exact with no side condition
  (`mem_clos`). Starting from an already-derived set gives the
  same exact answer (`mem_closFrom`), which is the incremental
  form used when the log grows. All sets are duplicate free.
-/
import Canon

namespace Canon
namespace Closure

/-- Records that fire from a set of derived terms. -/
def ready (ch : Chain) (r : Nat) (q : List Nat → Bool) (S : List Nat) (e : Rec) : Bool :=
  decide (e.level ≤ r) && q e.colors && (proj ch r e).1.all (fun p => decide (p ∈ S))

def fire (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool) (S : List Nat) : List Nat :=
  L.filterMap (fun e => if ready ch r q S e then some (proj ch r e).2 else none)

/-- Insert without duplicates. -/
def ins (acc : List Nat) (a : Nat) : List Nat := if a ∈ acc then acc else acc ++ [a]

def stepS (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool) (S : List Nat) : List Nat :=
  (fire ch L r q S).foldl ins S

def iter (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool) : Nat → List Nat → List Nat
  | 0, S => S
  | n + 1, S => iter ch L r q n (stepS ch L r q S)

def stable (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool) (S : List Nat) : Bool :=
  (fire ch L r q S).all (fun a => decide (a ∈ S))

/-- The same iteration, stopping as soon as the set is stable. -/
def iterE (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool) : Nat → List Nat → List Nat
  | 0, S => S
  | n + 1, S => if stable ch L r q S then S else iterE ch L r q n (stepS ch L r q S)

/-- Exact derivable set, from scratch. -/
def closFrom (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool) (S : List Nat) : List Nat :=
  iterE ch L r q L.length S

def clos (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool) : List Nat :=
  closFrom ch L r q []

theorem mem_ins (acc : List Nat) (a x : Nat) : x ∈ ins acc a ↔ x ∈ acc ∨ x = a := by
  unfold ins
  split
  · constructor
    · exact Or.inl
    · rintro (h | rfl) <;> assumption
  · simp

theorem mem_foldl_ins : ∀ (l acc : List Nat) (x : Nat), x ∈ l.foldl ins acc ↔ x ∈ acc ∨ x ∈ l := by
  intro l
  induction l with
  | nil => intro acc x; simp
  | cons a l ih =>
    intro acc x
    simp only [List.foldl_cons, ih, mem_ins, List.mem_cons]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h

theorem nodup_ins (acc : List Nat) (a : Nat) (h : acc.Nodup) : (ins acc a).Nodup := by
  unfold ins
  split
  · exact h
  · rename_i hn
    unfold List.Nodup at *
    rw [List.pairwise_append]
    refine ⟨h, by simp, ?_⟩
    intro x hx y hy
    simp at hy
    subst hy
    intro hxy; subst hxy; exact hn hx

theorem nodup_foldl_ins : ∀ (l acc : List Nat), acc.Nodup → (l.foldl ins acc).Nodup := by
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons a l ih => intro acc h; exact ih _ (nodup_ins acc a h)

theorem prefix_foldl_ins : ∀ (l acc : List Nat), ∃ t, l.foldl ins acc = acc ++ t := by
  intro l
  induction l with
  | nil => intro acc; exact ⟨[], by simp⟩
  | cons a l ih =>
    intro acc
    obtain ⟨t, ht⟩ := ih (ins acc a)
    simp only [List.foldl_cons, ht]
    unfold ins
    split
    · exact ⟨t, rfl⟩
    · exact ⟨[a] ++ t, by simp⟩

theorem mem_fire (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool) (S : List Nat) (a : Nat) :
    a ∈ fire ch L r q S ↔ ∃ e, e ∈ L ∧ ready ch r q S e = true ∧ (proj ch r e).2 = a := by
  unfold fire
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨e, he, h⟩
    by_cases hr : ready ch r q S e = true
    · simp [hr] at h; exact ⟨e, he, hr, h⟩
    · simp [hr] at h
  · rintro ⟨e, he, hr, rfl⟩
    exact ⟨e, he, by simp [hr]⟩

theorem mem_stepS (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool) (S : List Nat) (a : Nat) :
    a ∈ stepS ch L r q S ↔ a ∈ S ∨ a ∈ fire ch L r q S := mem_foldl_ins _ _ _

abbrev V (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool) := viewC ch L r q

/-- Each round only adds derivable terms. -/
theorem stepS_sound (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool) (S : List Nat)
    (hS : ∀ a ∈ S, derives (V ch L r q) a) : ∀ a ∈ stepS ch L r q S, derives (V ch L r q) a := by
  intro a ha
  rcases (mem_stepS ch L r q S a).mp ha with h | h
  · exact hS a h
  · obtain ⟨e, he, hr, rfl⟩ := (mem_fire ch L r q S a).mp h
    simp only [ready, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hr
    obtain ⟨⟨hl, hq⟩, hp⟩ := hr
    refine Derives.step (ps := (proj ch r e).1) ⟨e, he, hl, hq, rfl⟩ ?_
    intro p hpm
    exact hS p (hp p hpm)

theorem iter_sound (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool) :
    ∀ n S, (∀ a ∈ S, derives (V ch L r q) a) → ∀ a ∈ iter ch L r q n S, derives (V ch L r q) a := by
  intro n
  induction n with
  | zero => intro S h; exact h
  | succ n ih => intro S h; exact ih _ (stepS_sound ch L r q S h)

/-- A stable set holds every derivable term. -/
theorem complete_of_stable (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool) (S : List Nat)
    (hs : stable ch L r q S = true) : ∀ a, derives (V ch L r q) a → a ∈ S := by
  apply Derives.least (X := fun a => a ∈ S)
  · intro a h; exact h.elim
  · rintro ps a ⟨e, he, hl, hq, hp⟩ hps
    have hf : a ∈ fire ch L r q S := by
      refine (mem_fire ch L r q S a).mpr ⟨e, he, ?_, by rw [hp]⟩
      simp only [ready, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
      refine ⟨⟨hl, hq⟩, ?_⟩
      rw [hp]; exact hps
    simp only [stable, List.all_eq_true, decide_eq_true_eq] at hs
    exact hs a hf

/-! Termination: the potential is the number of records whose
    projected head is already derived. -/

def pot (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool) (S : List Nat) : Nat :=
  (L.filter (fun e => decide (e.level ≤ r) && q e.colors && decide ((proj ch r e).2 ∈ S))).length

theorem filter_len_mono {α : Type} : ∀ (l : List α) (p p' : α → Bool),
    (∀ x ∈ l, p x = true → p' x = true) → (l.filter p).length ≤ (l.filter p').length := by
  intro l
  induction l with
  | nil => intros; simp
  | cons x l ih =>
    intro p p' h
    have ih' := ih p p' (fun y hy => h y (List.mem_cons_of_mem _ hy))
    by_cases hx : p x = true
    · have hx' := h x (List.mem_cons_self) hx
      simp [List.filter_cons, hx, hx']; omega
    · by_cases hx' : p' x = true
      · simp [List.filter_cons, hx, hx']; omega
      · simp [List.filter_cons, hx, hx']; omega

theorem filter_len_lt {α : Type} : ∀ (l : List α) (p p' : α → Bool),
    (∀ x ∈ l, p x = true → p' x = true) → (∃ x ∈ l, p' x = true ∧ p x = false) →
    (l.filter p).length < (l.filter p').length := by
  intro l
  induction l with
  | nil => intro _ _ _ ⟨x, hx, _⟩; simp at hx
  | cons y l ih =>
    intro p p' h ⟨x, hx, hpx, hnx⟩
    have hmono := filter_len_mono l p p' (fun z hz => h z (List.mem_cons_of_mem _ hz))
    rcases List.mem_cons.mp hx with rfl | hx
    · simp [List.filter_cons, hpx, hnx]; omega
    · have ih' := ih p p' (fun z hz => h z (List.mem_cons_of_mem _ hz)) ⟨x, hx, hpx, hnx⟩
      by_cases hy : p y = true
      · have hy' := h y (List.mem_cons_self) hy
        simp [List.filter_cons, hy, hy']; omega
      · by_cases hy' : p' y = true
        · simp [List.filter_cons, hy, hy']; omega
        · simp [List.filter_cons, hy, hy']; omega

theorem pot_le (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool) (S : List Nat) :
    pot ch L r q S ≤ L.length := List.length_filter_le _ _

theorem stepS_sub (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool) (S : List Nat) :
    ∀ a ∈ S, a ∈ stepS ch L r q S := fun a h => (mem_stepS ch L r q S a).mpr (Or.inl h)

theorem pot_grow (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool) (S : List Nat)
    (hs : stable ch L r q S = false) : pot ch L r q S < pot ch L r q (stepS ch L r q S) := by
  unfold pot
  apply filter_len_lt
  · intro x _ hx
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hx ⊢
    exact ⟨hx.1, stepS_sub ch L r q S _ hx.2⟩
  · simp only [stable, List.all_eq_false, decide_eq_true_eq] at hs
    obtain ⟨a, ha, hn⟩ := hs
    obtain ⟨e, he, hr, rfl⟩ := (mem_fire ch L r q S _).mp ha
    refine ⟨e, he, ?_, ?_⟩
    · simp only [ready, Bool.and_eq_true, decide_eq_true_eq] at hr
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hr.1, (mem_stepS ch L r q S _).mpr (Or.inr ha)⟩
    · simp [hn]

theorem stepS_of_stable (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool) (S : List Nat)
    (hs : stable ch L r q S = true) : stepS ch L r q S = S := by
  unfold stepS
  simp only [stable, List.all_eq_true, decide_eq_true_eq] at hs
  generalize fire ch L r q S = l at hs
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldl_cons]
    have : ins S a = S := by unfold ins; simp [hs a List.mem_cons_self]
    rw [this]
    exact ih (fun x hx => hs x (List.mem_cons_of_mem _ hx))

theorem iter_of_stable (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool) (S : List Nat)
    (hs : stable ch L r q S = true) : ∀ n, iter ch L r q n S = S := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp only [iter, stepS_of_stable ch L r q S hs, ih]

/-- Early exit computes the same set. -/
theorem iterE_eq (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool) :
    ∀ n S, iterE ch L r q n S = iter ch L r q n S := by
  intro n
  induction n with
  | zero => intro S; rfl
  | succ n ih =>
    intro S
    simp only [iterE]
    split
    · rename_i hs; exact (iter_of_stable ch L r q S hs (n + 1)).symm
    · exact ih _

/-- The iteration is stable after `log.length` rounds from any start. -/
theorem iter_stable (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool) :
    ∀ n S, L.length ≤ n + pot ch L r q S → stable ch L r q (iter ch L r q n S) = true := by
  intro n
  induction n with
  | zero =>
    intro S h
    cases hs : stable ch L r q S
    · have := pot_grow ch L r q S hs
      have := pot_le ch L r q (stepS ch L r q S)
      omega
    · show stable ch L r q S = true; exact hs
  | succ n ih =>
    intro S h
    cases hs : stable ch L r q S
    · have := pot_grow ch L r q S hs
      exact ih _ (by omega)
    · rw [iter_of_stable ch L r q S hs]; exact hs

/-- Exactness from any sound start (the incremental form). -/
theorem mem_closFrom (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool) (S : List Nat)
    (hS : ∀ a ∈ S, derives (V ch L r q) a) (a : Nat) :
    a ∈ closFrom ch L r q S ↔ derives (V ch L r q) a := by
  unfold closFrom
  rw [iterE_eq]
  constructor
  · exact iter_sound ch L r q _ S hS a
  · exact complete_of_stable ch L r q _ (iter_stable ch L r q _ S (by omega)) a

/-- `clos` is exactly derivability. -/
theorem mem_clos (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool) (a : Nat) :
    a ∈ clos ch L r q ↔ derives (V ch L r q) a :=
  mem_closFrom ch L r q [] (fun _ h => by simp at h) a

theorem nodup_iter (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool) :
    ∀ n S, S.Nodup → (iter ch L r q n S).Nodup := by
  intro n
  induction n with
  | zero => intro S h; exact h
  | succ n ih => intro S h; exact ih _ (nodup_foldl_ins _ _ h)

theorem prefix_iter (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool) :
    ∀ n S, ∃ t, iter ch L r q n S = S ++ t := by
  intro n
  induction n with
  | zero => intro S; exact ⟨[], by simp [iter]⟩
  | succ n ih =>
    intro S
    obtain ⟨t₁, h₁⟩ := prefix_foldl_ins (fire ch L r q S) S
    obtain ⟨t₂, h₂⟩ := ih (stepS ch L r q S)
    refine ⟨t₁ ++ t₂, ?_⟩
    show iter ch L r q n (stepS ch L r q S) = S ++ (t₁ ++ t₂)
    rw [h₂]
    simp only [stepS, h₁, List.append_assoc]

theorem nodup_clos (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool) :
    (clos ch L r q).Nodup := by
  unfold clos closFrom; rw [iterE_eq]; exact nodup_iter ch L r q _ [] List.nodup_nil

theorem nodup_closFrom (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool) (S : List Nat)
    (h : S.Nodup) : (closFrom ch L r q S).Nodup := by
  unfold closFrom; rw [iterE_eq]; exact nodup_iter ch L r q _ S h

/-- Incremental equals scratch: closing the grown log from the
    old closure gives exactly the scratch closure's members. -/
theorem incremental_eq_scratch (ch : Chain) (L M : List Rec) (r : Nat) (q : List Nat → Bool) (a : Nat) :
    a ∈ closFrom ch (L ++ M) r q (clos ch L r q) ↔ a ∈ clos ch (L ++ M) r q := by
  rw [mem_closFrom, mem_clos]
  intro b hb
  exact View.derives_grow ch L M r q b ((mem_clos ch L r q b).mp hb)

end Closure

#print axioms Closure.mem_clos
#print axioms Closure.mem_closFrom
#print axioms Closure.iter_stable
#print axioms Closure.nodup_clos
#print axioms Closure.incremental_eq_scratch

end Canon
