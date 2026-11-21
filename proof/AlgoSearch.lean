/-
  Proofs for the algorithm-search survivors (examples/algorithm-search).

  1. The online Pareto archive (`ins`, one comparison pass against
     the current members) holds exactly the Pareto front of what has
     arrived, after every arrival and in any arrival order
     (`mem_arch`, `arch_perm`). This is the incremental re-scoring
     survivor: it never recomputes the front cold.
  2. Separable objectives decompose: for an additive score over
     independent factors, the plan of per-factor minima is a plan
     and no plan scores lower (`fmin_plan`, `fmin_le_plan`). This is
     why best-first enumeration examines one plan.
  3. Chebyshev weights aimed at a target f (weights 1/(f_i - z_i),
     scaled by K and computed in exact natural-number division) give
     f the score K, and every point that does not strictly dominate f
     in every coordinate scores at least K (`cheb_target`). So every
     point of the front is a minimizer of some Chebyshev scalarization,
     including unsupported points that no weighted sum reaches
     (prior work: Bowman 1976; Steuer and Choo 1983). Ties are not
     excluded by this statement; the measured runs break them with a
     small offset (`solved_weights`, eta).

  Vectors are `List Nat` of a common length; minimization throughout.
-/

namespace AlgoSearch

abbrev V := List Nat

/-- Pointwise `≤` on vectors of equal length. -/
def le : V → V → Bool
  | [], [] => true
  | a :: as, b :: bs => decide (a ≤ b) && le as bs
  | _, _ => false

/-- Pareto dominance (minimize): no worse everywhere, not equal. -/
def dom (a b : V) : Bool := le a b && a != b

theorem le_sum : ∀ a b : V, le a b = true → a.sum ≤ b.sum
  | [], [], _ => Nat.le_refl _
  | x :: xs, y :: ys, h => by
    simp [le] at h
    simp [List.sum_cons]
    exact Nat.add_le_add h.1 (le_sum xs ys h.2)
  | [], _ :: _, h => by simp [le] at h
  | _ :: _, [], h => by simp [le] at h

theorem le_eq_of_sum : ∀ a b : V, le a b = true → a.sum = b.sum → a = b
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, h, hs => by
    simp [le] at h
    simp [List.sum_cons] at hs
    have h1 := le_sum xs ys h.2
    have hx : x = y := by omega
    have hr : xs.sum = ys.sum := by omega
    rw [hx, le_eq_of_sum xs ys h.2 hr]
  | [], _ :: _, h, _ => by simp [le] at h
  | _ :: _, [], h, _ => by simp [le] at h

theorem dom_sum {a b : V} (h : dom a b = true) : a.sum < b.sum := by
  simp [dom] at h
  have h1 := le_sum a b h.1
  rcases Nat.lt_or_eq_of_le h1 with h2 | h2
  · exact h2
  · exact absurd (le_eq_of_sum a b h.1 h2) h.2

theorem le_trans' : ∀ a b c : V, le a b = true → le b c = true → le a c = true
  | [], [], [], _, _ => rfl
  | x :: xs, y :: ys, z :: zs, h1, h2 => by
    simp [le] at h1 h2 ⊢
    exact ⟨Nat.le_trans h1.1 h2.1, le_trans' xs ys zs h1.2 h2.2⟩
  | [], [], _ :: _, _, h2 => by simp [le] at h2
  | [], _ :: _, _, h1, _ => by simp [le] at h1
  | _ :: _, [], _, h1, _ => by simp [le] at h1
  | _ :: _, _ :: _, [], _, h2 => by simp [le] at h2

theorem dom_trans {a b c : V} (h1 : dom a b = true) (h2 : dom b c = true) : dom a c = true := by
  have s1 := dom_sum h1
  have s2 := dom_sum h2
  simp [dom] at h1 h2 ⊢
  refine ⟨le_trans' a b c h1.1 h2.1, ?_⟩
  intro e
  subst e
  omega

theorem dom_irrefl (a : V) : dom a a = false := by simp [dom]

/-- The Pareto front of a finite set, as a membership predicate. -/
def Front (L : List V) (x : V) : Prop := x ∈ L ∧ ∀ y, y ∈ L → dom y x = false

/-- Every dominated point of a finite set is dominated by a front point. -/
theorem front_dominator (L : List V) (x : V) :
    ∀ n y, y.sum = n → y ∈ L → dom y x = true → ∃ m, Front L m ∧ dom m x = true := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro y hn hy hd
    by_cases hf : ∀ z, z ∈ L → dom z y = false
    · exact ⟨y, ⟨hy, hf⟩, hd⟩
    · have : ∃ z, z ∈ L ∧ dom z y = true := by
        apply Classical.byContradiction
        intro hno
        apply hf
        intro z hz
        cases h : dom z y with
        | false => rfl
        | true => exact absurd ⟨z, hz, h⟩ hno
      obtain ⟨z, hz, hzy⟩ := this
      have hlt : z.sum < n := hn ▸ dom_sum hzy
      exact ih z.sum hlt z rfl hz (dom_trans hzy hd)

/-- One archive insertion: reject `x` if a member dominates it,
    otherwise add it and drop the members it dominates. -/
def ins (A : List V) (x : V) : List V :=
  if A.any (fun m => dom m x) then A else x :: A.filter (fun m => !dom x m)

/-- The archive after the arrivals `L`, newest first. -/
def arch : List V → List V
  | [] => []
  | x :: L => ins (arch L) x

theorem mem_arch : ∀ (L : List V) (z : V), z ∈ arch L ↔ Front L z
  | [], z => by simp [arch, Front]
  | x :: L, z => by
    have ih := mem_arch L
    simp only [arch, ins]
    by_cases hx : (arch L).any (fun m => dom m x) = true
    · rw [if_pos hx]
      obtain ⟨m, hmA, hmx⟩ := List.any_eq_true.mp hx
      have hmF := (ih m).mp hmA
      constructor
      · intro hz
        have hzF := (ih z).mp hz
        refine ⟨List.mem_cons_of_mem _ hzF.1, ?_⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · cases h : dom y z with
          | false => rfl
          | true => exact absurd (hzF.2 m hmF.1) (by rw [dom_trans hmx h]; simp)
        · exact hzF.2 y hy
      · intro hz
        rcases List.mem_cons.mp hz.1 with rfl | hzL
        · exact absurd (hz.2 m (List.mem_cons_of_mem _ hmF.1)) (by rw [hmx]; simp)
        · exact (ih z).mpr ⟨hzL, fun y hy => hz.2 y (List.mem_cons_of_mem _ hy)⟩
    · rw [if_neg hx]
      have hno : ∀ m, m ∈ arch L → dom m x = false := by
        intro m hm
        cases h : dom m x with
        | false => rfl
        | true => exact absurd (List.any_eq_true.mpr ⟨m, hm, h⟩) hx
      constructor
      · intro hz
        rcases List.mem_cons.mp hz with rfl | hz
        · refine ⟨List.mem_cons_self, ?_⟩
          intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact dom_irrefl _
          · cases h : dom y z with
            | false => rfl
            | true =>
              obtain ⟨m, hmF, hmz⟩ := front_dominator L z y.sum y rfl hy h
              exact absurd (hno m ((ih m).mpr hmF)) (by rw [hmz]; simp)
        · have hz' := List.mem_filter.mp hz
          have hzF := (ih z).mp hz'.1
          refine ⟨List.mem_cons_of_mem _ hzF.1, ?_⟩
          intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · simpa using hz'.2
          · exact hzF.2 y hy
      · intro hz
        rcases List.mem_cons.mp hz.1 with rfl | hzL
        · exact List.mem_cons_self
        · apply List.mem_cons_of_mem
          apply List.mem_filter.mpr
          refine ⟨(ih z).mpr ⟨hzL, fun y hy => hz.2 y (List.mem_cons_of_mem _ hy)⟩, ?_⟩
          simp [hz.2 x (List.mem_cons_self)]

/-- Arrival order does not change the archive's members. -/
theorem arch_perm {L M : List V} (h : L.Perm M) (z : V) : z ∈ arch L ↔ z ∈ arch M := by
  rw [mem_arch, mem_arch]
  simp only [Front]
  constructor
  · intro ⟨a, b⟩; exact ⟨h.mem_iff.mp a, fun y hy => b y (h.mem_iff.mpr hy)⟩
  · intro ⟨a, b⟩; exact ⟨h.mem_iff.mpr a, fun y hy => b y (h.mem_iff.mp hy)⟩

/-! ## Separable objectives -/

/-- Minimum of a nonempty factor (0 for an empty one). -/
def fmin : List Nat → Nat
  | [] => 0
  | [a] => a
  | a :: b :: l => min a (fmin (b :: l))

theorem fmin_le : ∀ (f : List Nat) (c : Nat), c ∈ f → fmin f ≤ c
  | [], _, h => by simp at h
  | [a], c, h => by simp at h; simp [fmin, h]
  | a :: b :: l, c, h => by
    simp only [fmin]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.min_le_left _ _
    · exact Nat.le_trans (Nat.min_le_right _ _) (fmin_le (b :: l) c h)

theorem fmin_mem : ∀ (f : List Nat), f ≠ [] → fmin f ∈ f
  | [], h => absurd rfl h
  | [a], _ => by simp [fmin]
  | a :: b :: l, _ => by
    simp only [fmin]
    rcases Nat.le_total a (fmin (b :: l)) with h | h
    · rw [Nat.min_eq_left h]; exact List.mem_cons_self
    · rw [Nat.min_eq_right h]; exact List.mem_cons_of_mem _ (fmin_mem (b :: l) (by simp))

/-- A plan picks one option score per factor. -/
def Plan : List Nat → List (List Nat) → Prop
  | [], [] => True
  | c :: cs, f :: fs => c ∈ f ∧ Plan cs fs
  | _, _ => False

/-- No plan scores below the sum of per-factor minima. -/
theorem fmin_le_plan : ∀ (cs : List Nat) (fs : List (List Nat)), Plan cs fs → (fs.map fmin).sum ≤ cs.sum
  | [], [], _ => Nat.le_refl _
  | c :: cs, f :: fs, h => by
    simp [Plan] at h
    simp [List.sum_cons]
    exact Nat.add_le_add (fmin_le f c h.1) (fmin_le_plan cs fs h.2)
  | [], _ :: _, h => by simp [Plan] at h
  | _ :: _, [], h => by simp [Plan] at h

/-- The per-factor minima are themselves a plan (factors nonempty). -/
theorem fmin_plan : ∀ (fs : List (List Nat)), (∀ f, f ∈ fs → f ≠ []) → Plan (fs.map fmin) fs
  | [], _ => trivial
  | f :: fs, h => ⟨fmin_mem f (h f (List.mem_cons_self)), fmin_plan fs (fun g hg => h g (List.mem_cons_of_mem _ hg))⟩

/-! ## Chebyshev weights aimed at a target -/

/-- Scaled Chebyshev score of `g` with weights `K / (f_i - z_i)`,
    in exact natural-number division. -/
def cheb (K : Nat) : V → V → V → Nat
  | f :: fs, z :: zs, g :: gs => max ((g - z) * K / (f - z)) (cheb K fs zs gs)
  | _, _, _ => 0

/-- `g` is below `f` in every coordinate (strict dominance everywhere). -/
def allLt : V → V → Prop
  | g :: gs, f :: fs => g < f ∧ allLt gs fs
  | _, _ => True

/-- `z` lies strictly below `f` in every coordinate. -/
def below : V → V → Prop
  | z :: zs, f :: fs => z < f ∧ below zs fs
  | [], [] => True
  | _, _ => False

theorem cheb_self_le : ∀ (K : Nat) (f z : V), below z f → cheb K f z f ≤ K
  | K, a :: as, b :: zs, h => by
    simp only [below] at h
    simp only [cheb]
    have : a - b > 0 := by omega
    rw [Nat.mul_div_cancel_left K this]
    exact Nat.max_le.mpr ⟨Nat.le_refl _, cheb_self_le K as zs h.2⟩
  | K, [], [], _ => by simp [cheb]
  | _, [], _ :: _, h => by simp [below] at h
  | _, _ :: _, [], h => by simp [below] at h

theorem cheb_self : ∀ (K : Nat) (f z : V), below z f → f ≠ [] → cheb K f z f = K
  | K, a :: as, b :: zs, h, _ => by
    simp only [below] at h
    simp only [cheb]
    have : a - b > 0 := by omega
    rw [Nat.mul_div_cancel_left K this]
    exact Nat.max_eq_left (cheb_self_le K as zs h.2)
  | _, [], _, _, h => absurd rfl h
  | _, _ :: _, [], h, _ => by simp [below] at h

theorem cheb_ge : ∀ (K : Nat) (f z g : V), 0 < K → below z f → g.length = f.length →
    ¬ allLt g f → K ≤ cheb K f z g
  | K, [], [], [], _, _, _, h => absurd trivial h
  | K, a :: as, b :: zs, c :: gs, hK, hb, hl, h => by
    simp only [below] at hb
    simp only [allLt] at h
    simp only [cheb]
    simp at hl
    by_cases hc : c < a
    · apply Nat.le_trans _ (Nat.le_max_right _ _)
      exact cheb_ge K as zs gs hK hb.2 hl (fun ha => h ⟨hc, ha⟩)
    · apply Nat.le_trans _ (Nat.le_max_left _ _)
      have hd : 0 < a - b := by omega
      apply (Nat.le_div_iff_mul_le hd).mpr
      have h3 : a - b ≤ c - b := by omega
      rw [Nat.mul_comm K]
      exact Nat.mul_le_mul_right K h3
  | _, [], _ :: _, _, _, hb, _, _ => by simp [below] at hb
  | _, _ :: _, [], _, _, hb, _, _ => by simp [below] at hb
  | _, [], [], _ :: _, _, _, hl, _ => by simp at hl
  | _, _ :: _, _ :: _, [], _, _, hl, _ => by simp at hl

/-- The aimed weights score the target `K`; every point that does not
    beat it in every coordinate scores at least `K`. So the target is a
    minimizer whenever nothing beats it everywhere, which every front
    point satisfies. -/
theorem cheb_target (K : Nat) (f z : V) (L : List V) (hK : 0 < K) (hb : below z f) (hf : f ≠ [])
    (hlen : ∀ g, g ∈ L → g.length = f.length) (hno : ∀ g, g ∈ L → ¬ allLt g f) :
    cheb K f z f = K ∧ ∀ g, g ∈ L → cheb K f z f ≤ cheb K f z g := by
  refine ⟨cheb_self K f z hb hf, fun g hg => ?_⟩
  rw [cheb_self K f z hb hf]
  exact cheb_ge K f z g hK hb (hlen g hg) (hno g hg)

/-- Chris's counterexample (0,4), (4,0), (3,3) with reference (-1,-1)
    shifted to (0,0) as (1,5), (5,1), (4,4): the unsupported point
    (4,4) is a Chebyshev minimizer with aimed weights. -/
theorem chris_unsupported_reached :
    cheb 12 [4, 4] [0, 0] [4, 4] ≤ cheb 12 [4, 4] [0, 0] [1, 5] ∧
    cheb 12 [4, 4] [0, 0] [4, 4] ≤ cheb 12 [4, 4] [0, 0] [5, 1] := by decide

/-- ... and no positive weighted sum picks it: for weights p, q > 0,
    one of the extremes is strictly cheaper (q > 0 is not even needed). -/
theorem chris_ws_miss (p q : Nat) (hp : 0 < p) :
    p * 1 + q * 5 < p * 4 + q * 4 ∨ p * 5 + q * 1 < p * 4 + q * 4 := by
  omega

end AlgoSearch

#print axioms AlgoSearch.mem_arch
#print axioms AlgoSearch.arch_perm
#print axioms AlgoSearch.fmin_le_plan
#print axioms AlgoSearch.fmin_plan
#print axioms AlgoSearch.cheb_target
#print axioms AlgoSearch.chris_unsupported_reached
#print axioms AlgoSearch.chris_ws_miss
