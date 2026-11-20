import Lean
import Canon

namespace Canon.ActionVector

/-- Dimensions are atomic keys on the same graph. Costs are normalized
    to lower-is-better, so the direction is fixed by the dimension schema. -/
structure Action where
  id : Nat
  scope : Nat
  prerequisites : List Nat
  inverseReceipt : Option Nat
  cost : Nat → Option Nat

structure Query where
  scope : Nat
  axes : List Nat
  reversibilityRequired : Bool

/-- Runtime roots are a checked projection of the current canonical view,
    not a declaration contributed by an action. -/
structure State where
  graph : Hypergraph Nat
  active : List Nat
  activeSound : ∀ p ∈ active, derives graph p
  inverseLaw : Nat → Nat → Nat → Prop
  checkInverse : Nat → Nat → Nat → Bool
  inverseSound : ∀ scope action p, checkInverse scope action p = true →
    inverseLaw scope action p
  metricKey : Nat → Nat → Nat → Nat → Nat
  checkMetric : Nat → Nat → Nat → Nat → Bool
  metricSound : ∀ scope action axis value, checkMetric scope action axis value = true →
    derives graph (metricKey scope action axis value)

def scored (s : State) (a : Action) (k : Nat) : Bool :=
  (a.cost k).any (fun v => s.checkMetric a.scope a.id k v)

def reversible (s : State) (a : Action) : Bool :=
  a.inverseReceipt.any (fun p => s.active.contains p && s.checkInverse a.scope a.id p)

def eligible (s : State) (q : Query) (a : Action) : Bool :=
  (a.scope == q.scope) &&
  a.prerequisites.all (fun p => s.active.contains p) &&
  (!q.reversibilityRequired || reversible s a) &&
  q.axes.all (scored s a)

theorem prerequisites_checked {s : State} {q : Query} {a : Action}
    (h : eligible s q a = true) :
    a.scope = q.scope ∧ (∀ p ∈ a.prerequisites, derives s.graph p) := by
  simp only [eligible, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact ⟨h.1.1.1, fun p hp => s.activeSound p (List.contains_iff_mem.mp (h.1.1.2 p hp))⟩

theorem inverse_checked {s : State} {q : Query} {a : Action}
    (h : eligible s q a = true) (hr : q.reversibilityRequired = true) :
    ∃ p, a.inverseReceipt = some p ∧ derives s.graph p ∧ s.inverseLaw q.scope a.id p := by
  simp only [eligible, hr, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h
  cases hx : a.inverseReceipt with
  | none => simp [reversible, hx] at h
  | some p =>
    have hp : p ∈ s.active ∧ s.checkInverse a.scope a.id p = true := by
      simpa [reversible, hx] using h.1.2
    have hs : a.scope = q.scope := (prerequisites_checked (by
      simpa only [eligible, hr, Bool.not_true, Bool.false_or, Bool.and_eq_true] using h :
      eligible s q a = true)).1
    exact ⟨p, rfl, s.activeSound p hp.1, hs ▸ s.inverseSound _ _ _ hp.2⟩

theorem metric_checked {s : State} {q : Query} {a : Action}
    (h : eligible s q a = true) :
    ∀ k ∈ q.axes, ∃ v, a.cost k = some v ∧ derives s.graph (s.metricKey q.scope a.id k v) := by
  have hs := (prerequisites_checked h).1
  simp only [eligible, Bool.and_eq_true, List.all_eq_true] at h
  intro k hk
  have hc := h.2 k hk
  cases hv : a.cost k with
  | none => simp [scored, hv] at hc
  | some v =>
    have hm : s.checkMetric a.scope a.id k v = true := by simpa [scored, hv] using hc
    exact ⟨v, rfl, hs ▸ s.metricSound _ _ _ _ hm⟩

def compare (strict : Bool) (a b : Action) (axis : Nat) : Bool :=
  match a.cost axis, b.cost axis with
  | some x, some y => if strict then decide (x < y) else decide (x ≤ y)
  | _, _ => false

def dominates (q : Query) (a b : Action) : Bool :=
  q.axes.all (compare false a b) && q.axes.any (compare true a b)

theorem dominance_exact {q : Query} {a b : Action} :
    dominates q a b = true ↔
    (∀ k ∈ q.axes, ∃ x y, a.cost k = some x ∧ b.cost k = some y ∧ x ≤ y) ∧
    (∃ k ∈ q.axes, ∃ x y, a.cost k = some x ∧ b.cost k = some y ∧ x < y) := by
  have step (t : Bool) (k : Nat) :
      compare t a b k = true ↔ ∃ x y, a.cost k = some x ∧ b.cost k = some y ∧
        (if t then x < y else x ≤ y) := by
    cases hx : a.cost k <;> cases hy : b.cost k <;> cases t <;>
      simp [compare, hx, hy]
  simp only [dominates, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, step,
    Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]

def frontier (s : State) (q : Query) (pool : List Action) : List Action :=
  let allowed := pool.filter (eligible s q)
  allowed.filter (fun a => !(allowed.any (fun b => dominates q b a)))

theorem frontier_exact {s : State} {q : Query} {pool : List Action} {a : Action} :
    a ∈ frontier s q pool ↔
    a ∈ pool ∧ eligible s q a = true ∧
    ¬ ∃ b ∈ pool, eligible s q b = true ∧ dominates q b a = true := by
  simp [frontier, and_assoc, and_left_comm, and_comm]

/-- The policy is a separate vector used only to order exact frontier members. -/
def rank (q : Query) (weight : Nat → Nat) (a : Action) : Nat :=
  (q.axes.map (fun k => weight k * (a.cost k).getD 0)).sum

def order (q : Query) (weight : Nat → Nat) (a b : Action) : Bool :=
  decide (rank q weight a < rank q weight b ∨
    rank q weight a = rank q weight b ∧ a.id ≤ b.id)

def dispatch (s : State) (q : Query) (pool : List Action) (weight : Nat → Nat) : Option Action :=
  ((frontier s q pool).mergeSort (order q weight)).head?

theorem selected_certified {s : State} {q : Query} {pool : List Action}
    {w : Nat → Nat} {a : Action} (h : dispatch s q pool w = some a) :
    a ∈ pool ∧ eligible s q a = true ∧
    ¬ ∃ b ∈ pool, eligible s q b = true ∧ dominates q b a = true := by
  apply frontier_exact.mp
  unfold dispatch at h
  have hh : a ∈ (frontier s q pool).mergeSort (order q w) := by
    generalize (frontier s q pool).mergeSort (order q w) = xs at *
    cases xs <;> simp_all
  exact List.mem_mergeSort.mp hh

theorem selected_best_rank {s : State} {q : Query} {pool : List Action}
    {w : Nat → Nat} {a : Action} (h : dispatch s q pool w = some a) :
    ∀ b ∈ frontier s q pool, order q w a b = true := by
  have ht : ∀ a b c, order q w a b = true → order q w b c = true →
      order q w a c = true := by
    intro a b c hab hbc
    simp only [order, decide_eq_true_eq] at *
    omega
  have hc : ∀ a b, (order q w a b || order q w b a) = true := by
    intro a b
    simp only [order, Bool.or_eq_true, decide_eq_true_eq]
    omega
  have hs := List.sorted_mergeSort ht hc (frontier s q pool)
  unfold dispatch at h
  obtain ⟨tail, htail⟩ := List.head?_eq_some_iff.mp h
  rw [htail] at hs
  intro b hb
  have hm : b ∈ (frontier s q pool).mergeSort (order q w) := List.mem_mergeSort.mpr hb
  rw [htail, List.mem_cons] at hm
  rcases hm with rfl | hm
  · simp [order]
  · exact (List.pairwise_cons.mp hs).1 b hm

theorem exact_stop {s : State} {q : Query} {pool : List Action} {w : Nat → Nat} :
    dispatch s q pool w = none ↔ frontier s q pool = [] := by
  simp [dispatch, ← List.length_eq_zero_iff]

private theorem sum_bounds (f g : Nat → Nat) (ks : List Nat)
    (h : ∀ k ∈ ks, f k ≤ g k) :
    (ks.map f).sum ≤ (ks.map g).sum ∧
    ((∃ k ∈ ks, f k < g k) → (ks.map f).sum < (ks.map g).sum) := by
  induction ks with
  | nil => simp
  | cons k ks ih =>
    have hk := h k (by simp)
    obtain ⟨hr, hs⟩ := ih (fun i hi => h i (by simp [hi]))
    simp only [List.map_cons, List.sum_cons]
    refine ⟨by omega, ?_⟩
    rintro ⟨i, hi, hlt⟩
    rcases List.mem_cons.mp hi with rfl | hi
    · omega
    · have := hs ⟨i, hi, hlt⟩
      omega

theorem dominance_lowers_unit_rank {q : Query} {a b : Action}
    (h : dominates q a b = true) :
    rank q (fun _ => 1) a < rank q (fun _ => 1) b := by
  obtain ⟨hw, k, hk, x, y, ha, hb, hs⟩ := dominance_exact.mp h
  have H := sum_bounds (fun i => (a.cost i).getD 0) (fun i => (b.cost i).getD 0)
    q.axes (by
      intro i hi
      obtain ⟨u, v, hu, hv, huv⟩ := hw i hi
      simpa [hu, hv] using huv)
  simpa [rank] using H.2 ⟨k, hk, by simpa [ha, hb] using hs⟩

theorem exact_stop_no_eligible {s : State} {q : Query} {pool : List Action} {w : Nat → Nat} :
    dispatch s q pool w = none ↔ ¬ ∃ a ∈ pool, eligible s q a = true := by
  rw [exact_stop]
  constructor
  · intro hf he
    let allowed := pool.filter (eligible s q)
    let r := rank q (fun _ => 1)
    have hn : allowed.map r ≠ [] := by
      obtain ⟨a, hp, ha⟩ := he
      have hm : r a ∈ allowed.map r := List.mem_map.mpr ⟨a, by simp [allowed, hp, ha], rfl⟩
      intro h
      rw [h] at hm
      simp at hm
    cases hm : (allowed.map r).min? with
    | none => exact hn (List.min?_eq_none_iff.mp hm)
    | some m =>
      have hs := (List.min?_eq_some_iff Nat.le_refl (fun x y => by omega) (fun _ _ _ => Nat.le_min)).mp hm
      obtain ⟨a, ha, har⟩ := List.mem_map.mp hs.1
      have hpa : a ∈ pool ∧ eligible s q a = true := List.mem_filter.mp ha
      have hmem : a ∈ frontier s q pool := frontier_exact.mpr ⟨hpa.1, hpa.2, by
        rintro ⟨b, hp, hb, hd⟩
        have hsmall := dominance_lowers_unit_rank hd
        have hbig := hs.2 (r b) (List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨hp, hb⟩, rfl⟩)
        change r b < r a at hsmall
        omega⟩
      simp [hf] at hmem
  · intro hn
    cases hf : frontier s q pool with
    | nil => rfl
    | cons a as =>
      have h : a ∈ frontier s q pool := by rw [hf]; simp
      exact False.elim (hn ⟨a, (frontier_exact.mp h).1, (frontier_exact.mp h).2.1⟩)

theorem stop_invariant_under_reweight
    (s : State) (q : Query) (pool : List Action) (w v : Nat → Nat) :
    dispatch s q pool w = none ↔ dispatch s q pool v = none := by
  rw [exact_stop, exact_stop]

/-- Input order cannot change the result if the action keys are unique. -/
theorem dispatch_permutation {s : State} {q : Query} {pool pool' : List Action}
    (hp : pool.Perm pool')
    (unique : ∀ a ∈ pool, ∀ b ∈ pool, a.id = b.id → a = b)
    (w : Nat → Nat) : dispatch s q pool w = dispatch s q pool' w := by
  have hf : ∀ a, a ∈ frontier s q pool ↔ a ∈ frontier s q pool' := by
    intro a
    simp only [frontier_exact, hp.mem_iff]
  cases h : dispatch s q pool w with
  | none =>
    apply Eq.symm
    exact exact_stop_no_eligible.mpr (by
      simpa only [hp.mem_iff] using (exact_stop_no_eligible.mp h))
  | some a =>
    have ha := frontier_exact.mpr (selected_certified h)
    cases h' : dispatch s q pool' w with
    | none =>
      have ha' := frontier_exact.mp ((hf a).mp ha)
      exact False.elim (exact_stop_no_eligible.mp h' ⟨a, ha'.1, ha'.2.1⟩)
    | some b =>
      have hb := (hf b).mpr (frontier_exact.mpr (selected_certified h'))
      have h₁ := selected_best_rank h b hb
      have h₂ := selected_best_rank h' a ((hf a).mp ha)
      simp only [order, decide_eq_true_eq] at h₁ h₂
      have hid : a.id = b.id := by omega
      exact congrArg some (unique a (frontier_exact.mp ha).1 b (frontier_exact.mp hb).1 hid)

#print axioms dispatch_permutation
#print axioms prerequisites_checked
#print axioms inverse_checked
#print axioms metric_checked
#print axioms dominance_exact
#print axioms frontier_exact
#print axioms selected_certified
#print axioms selected_best_rank
#print axioms dominance_lowers_unit_rank
#print axioms exact_stop_no_eligible
#print axioms exact_stop
#print axioms stop_invariant_under_reweight

end Canon.ActionVector
