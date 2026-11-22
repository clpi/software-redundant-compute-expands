/-
  Incremental recomputation: the cone rules of the three engines, as
  theorems that the incremental form equals the from-scratch form.

  1. Frontier (system 1, and the meta-search): joining one item changes
     the frontier only through the ordered pairs that involve it; a
     withdrawal is the carried dominator sets minus the withdrawn item.
  2. Lookup cone (system 2): a program that reads a table only through
     lookups returns the same answer, and reads the same keys, on any
     table that agrees on every key it read, including keys that held
     no row. Dropping missing-row keys breaks this (control).
  3. Pair join (system 3, generic half): the pairs of a list with one
     item appended are the old pairs plus the pairs with the new item.
     The HMA-specific half (over Hma.live itself) is HmaJoin.lean.

  Lean core only, in the family's hand rolled style.
-/

namespace Cone

/-! ## 1. Frontier -/

section Frontier
variable {α : Type}

/-- The frontier: items no member dominates. -/
def front (d : α → α → Bool) (xs : List α) : List α :=
  xs.filter (fun a => !(xs.any (fun b => d b a)))

theorem any_append_single (p : α → Bool) (xs : List α) (y : α) :
    (xs ++ [y]).any p = (xs.any p || p y) := by
  simp [List.any_append]

theorem filter_congr' (p q : α → Bool) :
    ∀ (l : List α), (∀ e ∈ l, p e = q e) → l.filter p = l.filter q
  | [], _ => rfl
  | a :: l, h => by
    have ih := filter_congr' p q l (fun e he => h e (List.mem_cons_of_mem a he))
    have ha := h a (List.mem_cons.mpr (Or.inl rfl))
    simp [List.filter_cons, ha, ih]

theorem filter_and (p q : α → Bool) :
    ∀ (l : List α), l.filter (fun a => p a && q a) = (l.filter p).filter q
  | [] => rfl
  | a :: l => by
    have ih := filter_and p q l
    cases hp : p a <;> cases hq : q a <;> simp [List.filter_cons, hp, hq, ih]

/-- Join: the frontier after appending y, from the old frontier and
    the ordered pairs involving y only. -/
theorem front_join (d : α → α → Bool) (hirr : ∀ a, d a a = false)
    (xs : List α) (y : α) :
    front d (xs ++ [y]) =
      (front d xs).filter (fun a => !d y a) ++
        (if xs.any (fun b => d b y) then [] else [y]) := by
  unfold front
  rw [List.filter_append]
  have h1 : (xs.filter fun a => !((xs ++ [y]).any fun b => d b a)) =
      (xs.filter fun a => !(xs.any fun b => d b a)).filter (fun a => !d y a) := by
    rw [← filter_and]
    apply filter_congr'
    intro e _
    rw [any_append_single]
    cases (xs.any fun b => d b e) <;> cases d y e <;> rfl
  rw [h1]
  congr 1
  rw [List.filter_cons, List.filter_nil, any_append_single, hirr]
  cases (xs.any fun b => d b y) <;> rfl

/-- Withdrawal: the frontier of the list without y is the list without y
    filtered by the carried dominators minus y. No pair is re-evaluated:
    the right side reads d only on pairs already in the carried matrix. -/
theorem front_withdraw [DecidableEq α] (d : α → α → Bool) (xs : List α) (y : α) :
    front d (xs.filter (fun b => decide (b ≠ y))) =
      (xs.filter (fun b => decide (b ≠ y))).filter
        (fun a => !(xs.any (fun b => decide (b ≠ y) && d b a))) := by
  unfold front
  apply filter_congr'
  intro e _
  congr 1
  induction xs with
  | nil => rfl
  | cons x t ih =>
    by_cases hx : x = y
    · simp [List.filter_cons, hx, ih]
    · simp [List.filter_cons, hx, List.any_cons, ih]

/-- Carry: re-joining an item already present with the same vector is
    not a join; the frontier of a list is unchanged by deduplicating a
    repeated item that cannot dominate itself (stated for the frontier
    membership test of every other item). -/
theorem any_dup (d : α → α → Bool) (xs : List α) (y : α) (hy : y ∈ xs) (a : α) :
    (xs ++ [y]).any (fun b => d b a) = xs.any (fun b => d b a) := by
  rw [any_append_single]
  cases h : xs.any (fun b => d b a)
  · have : d y a = false := by
      cases hd : d y a
      · rfl
      · have : xs.any (fun b => d b a) = true := List.any_eq_true.mpr ⟨y, hy, hd⟩
        rw [h] at this; exact absurd this (by decide)
    simp [this]
  · rfl

end Frontier

/-! ## 2. Lookup cone -/

section Lookup

/-- A program that reads a table only by lookups. A lookup returns the
    row or none; none is an answer the program can branch on. -/
inductive Prog (K V R : Type) where
  | ret : R → Prog K V R
  | ask : K → (Option V → Prog K V R) → Prog K V R

variable {K V R : Type}

def run : Prog K V R → (K → Option V) → R
  | .ret r, _ => r
  | .ask k f, t => run (f (t k)) t

/-- The cone: every key read, in order, including keys that held no row. -/
def cone : Prog K V R → (K → Option V) → List K
  | .ret _, _ => []
  | .ask k f, t => k :: cone (f (t k)) t

/-- Cone rule: agreement on the cone gives the same answer and the same cone. -/
theorem run_cone (p : Prog K V R) (t t' : K → Option V)
    (h : ∀ k ∈ cone p t, t k = t' k) :
    run p t = run p t' ∧ cone p t = cone p t' := by
  induction p with
  | ret r => exact ⟨rfl, rfl⟩
  | ask k f ih =>
    have hk : t k = t' k := h k List.mem_cons_self
    have rest : ∀ k' ∈ cone (f (t k)) t, t k' = t' k' :=
      fun k' hk' => h k' (List.mem_cons_of_mem _ hk')
    have := ih (t k) rest
    simp only [run, cone]
    rw [← hk]
    exact ⟨this.1, by rw [this.2]⟩

/-- Edit rule: an edit at a key outside the cone changes nothing. -/
theorem edit_outside [DecidableEq K] (p : Prog K V R) (t : K → Option V)
    (k0 : K) (v : Option V) (hk : k0 ∉ cone p t) :
    run p (fun k => if k = k0 then v else t k) = run p t := by
  have h : ∀ k ∈ cone p t, t k = (fun k => if k = k0 then v else t k) k := by
    intro k hk'
    have : k ≠ k0 := fun e => hk (e ▸ hk')
    simp [this]
  exact ((run_cone p t _ h).1).symm

/-- Control: drop the missing-row keys from the cone and the rule fails.
    The program reads key 0 and branches on whether a row is there. -/
def probe : Prog Nat Nat Nat := .ask 0 (fun o => match o with | none => .ret 0 | some _ => .ret 1)

def presentCone (p : Prog Nat Nat Nat) (t : Nat → Option Nat) : List Nat :=
  (cone p t).filter (fun k => (t k).isSome)

theorem missing_is_a_premise :
    (∀ k ∈ presentCone probe (fun _ => none), (fun _ => (none : Option Nat)) k = (fun _ => some 5) k)
      ∧ run probe (fun _ => none) ≠ run probe (fun _ => some 5) := by
  refine ⟨?_, ?_⟩
  · intro k hk
    simp [presentCone, cone, probe] at hk
  · decide

end Lookup

/-! ## 3. Pair join (generic half) -/

section Pairs
variable {α : Type}

/-- Unordered pairs of a list, each once. -/
def pairsOf : List α → List (α × α)
  | [] => []
  | x :: xs => xs.map (fun y => (x, y)) ++ pairsOf xs

theorem pairs_join (q : α × α → Bool) :
    ∀ (xs : List α) (y : α),
      (pairsOf (xs ++ [y])).any q = ((pairsOf xs).any q || (xs.map (fun x => (x, y))).any q)
  | [], y => by simp [pairsOf]
  | x :: xs, y => by
    have ih := pairs_join q xs y
    simp only [List.cons_append, pairsOf, List.map_append, List.any_append, ih,
      List.map_cons, List.map_nil, List.any_cons, List.any_nil]
    cases (xs.map fun z => (x, z)).any q <;> cases q (x, y) <;>
      cases (pairsOf xs).any q <;> cases (xs.map fun z => (z, y)).any q <;> rfl

theorem pairs_count : ∀ (xs : List α) (y : α),
    (pairsOf (xs ++ [y])).length = (pairsOf xs).length + xs.length
  | [], _ => by simp [pairsOf]
  | x :: xs, y => by
    have ih := pairs_count xs y
    simp [pairsOf, List.length_append, ih]
    omega

end Pairs

end Cone
