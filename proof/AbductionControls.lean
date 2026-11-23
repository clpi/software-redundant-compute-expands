/-
  Controls for `Abduction`: each check of the definitions is
  shown to matter on a concrete log, by the kernel.

  Log `L0` (one chain level, every color admitted): `2 -> bot`,
  `2 -> 1`, `3,4 -> 1`, `5 -> 1`. Observation `1`, abducibles
  `2,3,4,5`. The planted causes are `{5}` and `{3,4}`; `{2}`
  derives the observation and also `bot`.
-/
import Abduction

namespace Canon
namespace AbductionControls
open Abduction

def idc : Chain := ⟨fun _ c => c, 0, 0, Nat.le_refl 0⟩
def rc (i : Nat) (ps : List Nat) (h : Nat) : Rec := ⟨i, 0, [], ps, h⟩

def L0 : List Rec := [rc 0 [2] 9, rc 1 [2] 1, rc 2 [3, 4] 1, rc 3 [5] 1]
def P0 : Problem := ⟨idc, L0, 0, fun _ => true, 9, [2, 3, 4, 5], [1]⟩

/-- The checker with its consistency conjunct removed. -/
def explainsNoBot (P : Problem) (c : Nat) (H : List Nat) : Bool :=
  H.all (fun h => decide (h ∈ P.A)) && P.O.all (fun o => decide (o ∈ closWith P c H))

/-- C1: consistency matters. Without it `{2}` passes; it derives `bot`. -/
theorem c1_consistency : explainsNoBot P0 1 [2] = true ∧ explainsB P0 1 [2] = false := by decide

/-- C2: minimality matters. `{3,4,5}` explains and is not minimal. -/
theorem c2_minimality : explainsB P0 1 [3, 4, 5] = true ∧ minimalB P0 1 [3, 4, 5] = false := by decide

/-- C3: the enumerator recovers exactly the planted causes and
    rejects the planted false one. -/
theorem c3_recovery : abduce P0 1 3 = [[5], [3, 4]] := by decide

/-- C4: the size bound is real; at bound 1 `{3,4}` is not returned. -/
theorem c4_bound : abduce P0 1 1 = [[5]] := by decide

/-- C5: minimality does not persist when the log grows: after
    `3 -> 1` is appended, `{3,4}` explains but is no longer minimal. -/
theorem c5_minimal_not_persistent :
    minimalB P0 1 [3, 4] = true ∧
    explainsB { P0 with L := L0 ++ [rc 4 [3] 1] } 1 [3, 4] = true ∧
    minimalB { P0 with L := L0 ++ [rc 4 [3] 1] } 1 [3, 4] = false := by decide

/-- C6: refutations persist on every extension (an instance of
    `inconsistent_persists`), here with an extension that adds a
    competing explanation. -/
theorem c6_refutation_persists :
    decide (P0.bot ∈ closWith P0 1 [2]) = true ∧
    decide (P0.bot ∈ closWith { P0 with L := L0 ++ [rc 4 [3] 1] } 1 [2]) = true := by decide

/-- C7: the duplicate-free premise of `minimal_iff_erase` matters
    for the checker: `[5,5]` names a minimal set but is refused. -/
theorem c7_duplicates : minimalB P0 1 [5] = true ∧ minimalB P0 1 [5, 5] = false := by decide

/-- C8: the cone must be closed backwards. With `T = [1,9]` the
    middle term `6` is cut, the cone check fails, and on the cut log
    `{5}` no longer explains though it does on the whole log. -/
def L2 : List Rec := [rc 0 [6] 1, rc 1 [5] 6]
def P2 : Problem := ⟨idc, L2, 0, fun _ => true, 9, [5], [1]⟩

theorem c8_cone_closed :
    coneClosedB idc L2 0 (fun _ => true) [1, 9] = false ∧
    explainsB P2 1 [5] = true ∧
    explainsB { P2 with L := coneOf idc L2 0 [1, 9] } 1 [5] = false ∧
    coneClosedB idc L2 0 (fun _ => true) [1, 5, 6, 9] = true := by decide

/-- C9: admission refuses an unverified explanation and a
    non-minimal one, and admits a verified minimal one. -/
theorem c9_admission :
    admitLog P0 1 false [5] = L0 ∧ admitLog P0 1 true [3, 4, 5] = L0 ∧
    admitLog P0 1 true [5] = L0 ++ [hypRec 0 1 5] := by decide

/-- C10: ranking by coverage alone keeps a dominated candidate out
    only when cost is also compared: with equal coverage, the
    cheaper explanation dominates. -/
theorem c10_front :
    front [((0 : Nat), Score.mk 1 1), (1, Score.mk 1 2), (2, Score.mk 2 3)] =
      [(0, Score.mk 1 1), (2, Score.mk 2 3)] := by decide

/-- The certificate path end to end on `P0` with cone `[1,2,3,4,5,9]`. -/
theorem c11_certificate : [5].Nodup ∧ Minimal P0 [5] :=
  certificate P0 1 rfl [1, 2, 3, 4, 5, 9] [5] (by decide) (by decide) (by decide) (by decide)

end AbductionControls
end Canon

#print axioms Canon.AbductionControls.c1_consistency
#print axioms Canon.AbductionControls.c2_minimality
#print axioms Canon.AbductionControls.c3_recovery
#print axioms Canon.AbductionControls.c4_bound
#print axioms Canon.AbductionControls.c5_minimal_not_persistent
#print axioms Canon.AbductionControls.c6_refutation_persists
#print axioms Canon.AbductionControls.c7_duplicates
#print axioms Canon.AbductionControls.c8_cone_closed
#print axioms Canon.AbductionControls.c9_admission
#print axioms Canon.AbductionControls.c10_front
#print axioms Canon.AbductionControls.c11_certificate
