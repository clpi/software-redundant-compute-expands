/-
  Proofs for the semantic-axes extension (examples/semantic-axes).

  1. Appending an axis (or a trace, which appends one coordinate per
     objective) never removes a point from the Pareto front
     (`front_ext`), and a point can only become dominated by one that
     was already weakly below it on the old coordinates (`dom_ext_le`).
     So the front over candidates updates exactly by re-checking only
     the previously dominated points against their old weak dominators,
     with no cold recompute.
  2. Fronts compose: the front of A ++ B is the front of the two
     archives' union (`front_union`). This is the merge the
     compositionality axis measures for the archive.
  3. Closures compose by seeding: starting from any set of terms that
     are already derivable (for example the union of the two halves'
     derived sets) and closing under all rules gives exactly the least
     closure (`seeded_eq`, `der_mono_rules`). This is the specification
     the propagate merge implements; the engine itself is checked by test.
-/
import AlgoSearch

namespace Axes
open AlgoSearch

theorem le_append : ∀ (a b a' b' : V), a.length = b.length →
    le (a ++ a') (b ++ b') = (le a b && le a' b')
  | [], [], a', b', _ => by simp [le]
  | x :: xs, y :: ys, a', b', h => by
    simp at h
    simp only [List.cons_append, le]
    rw [le_append xs ys a' b' h, Bool.and_assoc]
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h

theorem dom_ext_le (a b a' b' : V) (h : a.length = b.length)
    (hd : dom (a ++ a') (b ++ b') = true) : le a b = true := by
  simp only [dom, Bool.and_eq_true] at hd
  rw [le_append a b a' b' h] at hd
  simp only [Bool.and_eq_true] at hd
  exact hd.1.1

theorem front_ext (L : List V) (ext : V → V) (n : Nat) (hn : ∀ y, y ∈ L → y.length = n)
    (x : V) (hx : Front L x) : Front (L.map (fun y => y ++ ext y)) (x ++ ext x) := by
  refine ⟨List.mem_map.mpr ⟨x, hx.1, rfl⟩, ?_⟩
  intro z hz
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
  cases hd : dom (y ++ ext y) (x ++ ext x) with
  | false => rfl
  | true =>
    have hlen : y.length = x.length := by rw [hn y hy, hn x hx.1]
    have hle := dom_ext_le y x (ext y) (ext x) hlen hd
    by_cases hyx : y = x
    · subst hyx; simp [dom_irrefl] at hd
    · have : dom y x = true := by simp [dom, hle, hyx]
      rw [hx.2 y hy] at this; exact absurd this (by simp)

theorem front_union (A B : List V) (z : V) : Front (A ++ B) z ↔ Front (arch A ++ arch B) z := by
  constructor
  · intro ⟨hz, hn⟩
    refine ⟨?_, ?_⟩
    · rcases List.mem_append.mp hz with h | h
      · exact List.mem_append_left _ ((mem_arch A z).mpr ⟨h, fun y hy => hn y (List.mem_append_left _ hy)⟩)
      · exact List.mem_append_right _ ((mem_arch B z).mpr ⟨h, fun y hy => hn y (List.mem_append_right _ hy)⟩)
    · intro y hy
      rcases List.mem_append.mp hy with h | h
      · exact hn y (List.mem_append_left _ ((mem_arch A y).mp h).1)
      · exact hn y (List.mem_append_right _ ((mem_arch B y).mp h).1)
  · intro ⟨hz, hn⟩
    refine ⟨?_, ?_⟩
    · rcases List.mem_append.mp hz with h | h
      · exact List.mem_append_left _ ((mem_arch A z).mp h).1
      · exact List.mem_append_right _ ((mem_arch B z).mp h).1
    · intro y hy
      cases hd : dom y z with
      | false => rfl
      | true =>
        rcases List.mem_append.mp hy with h | h
        · obtain ⟨m, hm, hmz⟩ := front_dominator A z y.sum y rfl h hd
          rw [hn m (List.mem_append_left _ ((mem_arch A m).mpr hm))] at hmz; exact absurd hmz (by simp)
        · obtain ⟨m, hm, hmz⟩ := front_dominator B z y.sum y rfl h hd
          rw [hn m (List.mem_append_right _ ((mem_arch B m).mpr hm))] at hmz; exact absurd hmz (by simp)

/-! ## Exact undo of an archive insertion from the retained residual -/

/-- An accepted insertion keeps `x :: kept`; the residual is the list of
    members it removed. Dropping `x` and putting the residual back gives
    exactly the members held before (`ins` rejects without change). -/
theorem undo_residual (A : List V) (x : V) (z : V) :
    z ∈ A.filter (fun m => !dom x m) ++ A.filter (fun m => dom x m) ↔ z ∈ A := by
  simp only [List.mem_append, List.mem_filter]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · intro h
    cases hd : dom x z with
    | false => exact Or.inl ⟨h, by simp⟩
    | true => exact Or.inr ⟨h, rfl⟩

theorem ins_accept (A : List V) (x : V) (h : ¬ (A.any (fun m => dom m x) = true)) :
    ins A x = x :: A.filter (fun m => !dom x m) := by
  simp only [ins, if_neg h]

theorem ins_reject (A : List V) (x : V) (h : A.any (fun m => dom m x) = true) : ins A x = A := by
  simp only [ins, if_pos h]

/-! ## Closures compose by seeding -/

/-- Least closure of seeds `S` under finite-premise rules `R`. -/
inductive Der (S : Nat → Prop) (R : List (List Nat × Nat)) : Nat → Prop where
  | seed {a : Nat} : S a → Der S R a
  | step {ps : List Nat} {a : Nat} : (ps, a) ∈ R → (∀ p, p ∈ ps → Der S R p) → Der S R a

theorem der_mono_rules {S : Nat → Prop} {R R' : List (List Nat × Nat)} (h : ∀ r, r ∈ R → r ∈ R')
    {a : Nat} (d : Der S R a) : Der S R' a := by
  induction d with
  | seed hs => exact .seed hs
  | step hr _ ih => exact .step (h _ hr) ih

/-- Seeding with terms that are already derivable changes nothing. -/
theorem seeded_eq (S : Nat → Prop) (R : List (List Nat × Nat))
    (hS : ∀ a, S a → Der (fun _ => False) R a) (a : Nat) :
    Der S R a ↔ Der (fun _ => False) R a := by
  constructor
  · intro d
    induction d with
    | seed hs => exact hS _ hs
    | step hr _ ih => exact .step hr ih
  · intro d
    induction d with
    | seed hs => exact hs.elim
    | step hr _ ih => exact .step hr ih

/-- The propagate merge's specification: seed with the union of the two
    halves' derived terms and close under all rules; the result is the
    least closure of the whole log. -/
theorem merge_spec (RA RB : List (List Nat × Nat)) (a : Nat) :
    Der (fun t => Der (fun _ => False) RA t ∨ Der (fun _ => False) RB t) (RA ++ RB) a ↔
    Der (fun _ => False) (RA ++ RB) a := by
  apply seeded_eq
  intro t ht
  rcases ht with h | h
  · exact der_mono_rules (fun r hr => List.mem_append_left _ hr) h
  · exact der_mono_rules (fun r hr => List.mem_append_right _ hr) h

end Axes

#print axioms Axes.dom_ext_le
#print axioms Axes.front_ext
#print axioms Axes.front_union
#print axioms Axes.undo_residual
#print axioms Axes.ins_accept
#print axioms Axes.ins_reject
#print axioms Axes.seeded_eq
#print axioms Axes.merge_spec
