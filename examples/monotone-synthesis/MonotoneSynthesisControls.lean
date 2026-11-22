/-
  Controls for MonotoneSynthesis: each admission check is necessary.

  Every control is a kernel-checked pair: what the check refuses, and what
  goes wrong if the refused entry were on the log anyway. Reach is decided
  by `ExecutableClosure.close` through `reach_iff_close`, so the facts below
  are about the spec, not a separate model.
-/
import MonotoneSynthesis

namespace MonotoneSynthesis
namespace Controls
open Qualification

def x0 : Art Nat := ⟨0, [], 0⟩
def x1 : Art Nat := ⟨1, [0], 1⟩
def x2 : Art Nat := ⟨2, [], 5⟩
def x3 : Art Nat := ⟨3, [], 0⟩
def U : List Nat := [0, 1, 5]

/-- No host primitives: everything must come from artifacts. -/
abbrev P0 : Nat → Prop := fun a => a ∈ ([] : List Nat)
/-- A verifier that accepts everything (the controls isolate the other checks). -/
def V0 : Art Nat → Prop := fun _ => True

def L : List (Entry Nat) := [.add x0, .add x1, .add x2]

theorem base_run : Run P0 V0 L := by
  show Run P0 V0 ((([] ++ [.add x0]) ++ [.add x1]) ++ [.add x2])
  refine .snoc (.snoc (.snoc .nil ?_) ?_) ?_
  · exact admitAddB_sound V0 U [] [] x0 trivial (by decide)
  · exact admitAddB_sound V0 U [] _ x1 trivial (by decide)
  · exact admitAddB_sound V0 U [] _ x2 trivial (by decide)

/-- C1, coverage. Retiring `x0` for `x2` satisfies every other retire
    clause (both live, distinct ids), yet it would make capability 1
    unreachable. The coverage clause is what refuses it. -/
theorem retire_without_cover_refused :
    reach P0 L 1 ∧ ¬ reach P0 (L ++ [.retire 0 2]) 1 ∧
      (live L x0 ∧ live L x2 ∧ (2 : Nat) ≠ 0) ∧ ¬ Admit P0 V0 L (.retire 0 2) := by
  have before : reach P0 L 1 := (reach_iff_close U [] L (by decide) 1).mpr (by decide)
  have after : ¬ reach P0 (L ++ [.retire 0 2]) 1 := fun h =>
    absurd ((reach_iff_close U [] _ (by decide) 1).mp h) (by decide)
  refine ⟨before, after, ⟨(liveB_iff L x0).mp (by decide), (liveB_iff L x2).mp (by decide), by decide⟩, ?_⟩
  intro h
  cases h with
  | retire _ _ _ cover => exact after (cover 1 before)

/-- C2, the positive control: a replacement with the same head and grounded
    premises passes the executable check and keeps capability 1. -/
theorem covering_replacement_admitted :
    Admit P0 V0 (L ++ [.add x3]) (.retire 0 3) ∧ reach P0 (L ++ [.add x3] ++ [.retire 0 3]) 1 := by
  refine ⟨replaceB_sound V0 U [] (L ++ [.add x3]) x0 x3 3 (by decide), ?_⟩
  exact (reach_iff_close U [] _ (by decide) 1).mpr (by decide)

def bad : Art Nat := ⟨4, [], 1⟩
/-- A faithful verifier for truth `a = 0`: accepts only artifacts providing 0. -/
def V1 : Art Nat → Prop := fun x => x.head = 0

/-- C3, verification. Without a verifier, an artifact that provides a false
    capability is admitted and reached; the faithful verifier refuses it. -/
theorem unverified_unsound :
    Run P0 V0 [.add bad] ∧ reach P0 [.add bad] 1 ∧ ¬ (1 : Nat) = 0 ∧
      ¬ Admit P0 V1 [] (.add bad) := by
  refine ⟨?_, (reach_iff_close U [] _ (by decide) 1).mpr (by decide), by decide, ?_⟩
  · show Run P0 V0 ([] ++ [.add bad])
    exact .snoc .nil (admitAddB_sound V0 U [] [] bad trivial (by decide))
  · intro h
    cases h with
    | add hv _ _ _ => simp [V1, bad] at hv

def dead : Art Nat := ⟨5, [7], 1⟩

/-- C4, grounding. An artifact whose premise is unreachable is refused; on
    the log anyway it is live but its capability is not reachable, which is
    what `live_heads_reach` excludes. -/
theorem ungrounded_refused :
    ¬ Admit P0 V0 [] (.add dead) ∧ live [.add dead] dead ∧ ¬ reach P0 [.add dead] 1 := by
  have hno : ¬ reach P0 ([] : List (Entry Nat)) 7 := fun h =>
    absurd ((reach_iff_close U [] [] (by decide) 7).mp h) (by decide)
  refine ⟨fun h => ?_, (liveB_iff _ dead).mp (by decide), fun h => ?_⟩
  · cases h with
    | add _ _ _ hp => exact hno (hp 7 (by decide))
  · exact absurd ((reach_iff_close [0, 1, 5, 7] [] _ (by decide) 1).mp h) (by decide)

/-- The pool of C5. -/
def C : Art Nat → Prop := fun y => y = x0 ∨ y = x1

/-- C5, retry. One pass offering `x1` before `x0` admits only `x0`; that
    log is not saturated (x1 is ready but 1 is not reached). Offering again
    saturates. An unattended loop must keep retrying pending candidates. -/
theorem single_pass_not_saturated :
    ¬ Admit P0 V0 [] (.add x1) ∧ Admit P0 V0 [] (.add x0) ∧
      ¬ Saturated P0 V0 C [.add x0] ∧ Saturated P0 V0 C [.add x0, .add x1] := by
  have no0 : ¬ reach P0 ([] : List (Entry Nat)) 0 := fun h =>
    absurd ((reach_iff_close U [] [] (by decide) 0).mp h) (by decide)
  have no1 : ¬ reach P0 [.add x0] 1 := fun h =>
    absurd ((reach_iff_close U [] _ (by decide) 1).mp h) (by decide)
  refine ⟨fun h => ?_, admitAddB_sound V0 U [] [] x0 trivial (by decide), fun hs => ?_, ?_⟩
  · cases h with
    | add _ _ _ hp => exact no0 (hp 0 (by decide))
  · exact no1 (hs x1 (Or.inr rfl) trivial (fun p hp => by
      simp [x1] at hp; subst hp
      exact (reach_iff_close U [] _ (by decide) 0).mpr (by decide)))
  · intro y hy _ _
    rcases hy with rfl | rfl
    · exact (reach_iff_close U [] _ (by decide) 0).mpr (by decide)
    · exact (reach_iff_close U [] _ (by decide) 1).mpr (by decide)

def absBad : Art Nat := ⟨6, [0], 5⟩
def absOk : Art Nat := ⟨7, [0], 1⟩

/-- C6, abstraction. A composed rule whose head is not derivable from its
    premises changes what is reachable, so it is not an abstraction and
    must be admitted with evidence. One that is derivable changes nothing. -/
theorem abstraction_needs_derivation :
    reach P0 ([.add x0] ++ [.add absBad]) 5 ∧ ¬ reach P0 [.add x0] 5 ∧
      (∀ a, reach P0 ([.add x0, .add x1] ++ [.add absOk]) a ↔ reach P0 [.add x0, .add x1] a) := by
  refine ⟨(reach_iff_close U [] _ (by decide) 5).mpr (by decide),
    fun h => absurd ((reach_iff_close U [] _ (by decide) 5).mp h) (by decide), ?_⟩
  apply abstract_conservative
  have hx0 : live [.add x0, .add x1] x0 := (liveB_iff _ x0).mp (by decide)
  have hx1 : live [.add x0, .add x1] x1 := (liveB_iff _ x1).mp (by decide)
  exact .step ⟨x1, hx1, rfl, rfl⟩ (fun p hp => by
    simp [x1] at hp; subst hp; exact .root (Or.inr (by decide)))

def ya : Art Nat := ⟨0, [], 0⟩
def yb : Art Nat := ⟨1, [], 1⟩
def yc : Art Nat := ⟨2, [0, 1], 2⟩

/-- C7, composition. Neither library alone reaches 2; their union of
    results does not either; the composed rules do, after one reclosure.
    Joining libraries is superadditive, which `compose` accounts for. -/
theorem composition_needs_reclosure :
    ¬ reach P0 [.add ya] 2 ∧ ¬ reach P0 [.add yb, .add yc] 2 ∧
      Derives P0 (fun ps x => rules [.add ya] ps x ∨ rules [.add yb, .add yc] ps x) 2 := by
  refine ⟨fun h => absurd ((reach_iff_close [0, 1, 2] [] _ (by decide) 2).mp h) (by decide),
    fun h => absurd ((reach_iff_close [0, 1, 2] [] _ (by decide) 2).mp h) (by decide), ?_⟩
  have la : live [.add ya] ya := (liveB_iff _ ya).mp (by decide)
  have lb : live [.add yb, .add yc] yb := (liveB_iff _ yb).mp (by decide)
  have lc : live [.add yb, .add yc] yc := (liveB_iff _ yc).mp (by decide)
  refine .step (Or.inr ⟨yc, lc, rfl, rfl⟩) (fun p hp => ?_)
  simp [yc] at hp
  rcases hp with rfl | rfl
  · exact .step (Or.inl ⟨ya, la, rfl, rfl⟩) (fun _ h => by simp [ya] at h)
  · exact .step (Or.inr ⟨yb, lb, rfl, rfl⟩) (fun _ h => by simp [yb] at h)

/-- The same fact in software-optimality's own form, reused unchanged. -/
theorem composition_needs_reclosure_general :
    let B : Nat → Prop := fun x => x = 0
    let C : Nat → Prop := fun x => x = 1
    let R : List Nat → Nat → Prop := fun ps x => ps = [0, 1] ∧ x = 2
    let S : List Nat → Nat → Prop := fun _ _ => False
    Derives (fun x => B x ∨ C x) (fun ps x => R ps x ∨ S ps x) 2 ∧
      ¬ (Derives B R 2 ∨ Derives C S 2) :=
  ClosureStrength.union_without_reclosure_fails

/-- C8, compounding is strict: admitting `x0` makes `x1` ready, and it was
    not ready before. -/
theorem admission_enables :
    ¬ Ready P0 V0 [] x1 ∧ Ready P0 V0 [.add x0] x1 := by
  have no0 : ¬ reach P0 ([] : List (Entry Nat)) 0 := fun h =>
    absurd ((reach_iff_close U [] [] (by decide) 0).mp h) (by decide)
  refine enables_strict (admitAddB_sound V0 U [] [] x0 trivial (by decide)) no0 x1 trivial
    (by decide) (fun p hp => Or.inr (by simp [x1] at hp; exact hp))

/-- C9, order. Two saturated runs over pool {x0, x1, x3}, in different
    orders, one of them retiring x0 for x3, reach the same capabilities. -/
def C3 : Art Nat → Prop := fun y => y = x0 ∨ y = x1 ∨ y = x3

theorem two_orders_same_reach (a : Nat) :
    reach P0 [.add x0, .add x1, .add x3] a ↔ reach P0 [.add x3, .add x1, .add x0, .retire 0 3] a := by
  have r1 : Run P0 V0 [.add x0, .add x1, .add x3] := by
    show Run P0 V0 ((([] ++ [.add x0]) ++ [.add x1]) ++ [.add x3])
    refine .snoc (.snoc (.snoc .nil ?_) ?_) ?_
    · exact admitAddB_sound V0 U [] [] x0 trivial (by decide)
    · exact admitAddB_sound V0 U [] _ x1 trivial (by decide)
    · exact admitAddB_sound V0 U [] _ x3 trivial (by decide)
  have r2 : Run P0 V0 [.add x3, .add x1, .add x0, .retire 0 3] := by
    show Run P0 V0 (((([] ++ [.add x3]) ++ [.add x1]) ++ [.add x0]) ++ [.retire x0.id 3])
    refine .snoc (.snoc (.snoc (.snoc .nil ?_) ?_) ?_) ?_
    · exact admitAddB_sound V0 U [] [] x3 trivial (by decide)
    · exact admitAddB_sound V0 U [] _ x1 trivial (by decide)
    · exact admitAddB_sound V0 U [] _ x0 trivial (by decide)
    · exact replaceB_sound V0 U [] _ x0 x3 3 (by decide)
  have from1 : From C3 [.add x0, .add x1, .add x3] := by
    intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> simp [C3]
  have from2 : From C3 [.add x3, .add x1, .add x0, .retire 0 3] := by
    intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> simp [C3]
  have sat : ∀ M, (∀ b ∈ [0, 1], reach P0 M b) → Saturated P0 V0 C3 M := by
    intro M hM y hy _ _
    rcases hy with rfl | rfl | rfl
    · exact hM 0 (by decide)
    · exact hM 1 (by decide)
    · exact hM 0 (by decide)
  refine order_independent C3 r1 from1 (sat _ ?_) r2 from2 (sat _ ?_) a
  · intro b hb; simp at hb
    rcases hb with rfl | rfl
    · exact (reach_iff_close U [] _ (by decide) 0).mpr (by decide)
    · exact (reach_iff_close U [] _ (by decide) 1).mpr (by decide)
  · intro b hb; simp at hb
    rcases hb with rfl | rfl
    · exact (reach_iff_close U [] _ (by decide) 0).mpr (by decide)
    · exact (reach_iff_close U [] _ (by decide) 1).mpr (by decide)

#print axioms base_run
#print axioms retire_without_cover_refused
#print axioms covering_replacement_admitted
#print axioms unverified_unsound
#print axioms ungrounded_refused
#print axioms single_pass_not_saturated
#print axioms abstraction_needs_derivation
#print axioms composition_needs_reclosure
#print axioms composition_needs_reclosure_general
#print axioms admission_enables
#print axioms two_orders_same_reach

end Controls
end MonotoneSynthesis
