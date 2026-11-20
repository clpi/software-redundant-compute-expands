import Lean
import Canon

namespace Canon.ClosureWorklist

abbrev Edge := List Nat × Nat

/-- Preserve the ordered premise list in the actual record projection. -/
def records (ch : Chain) (log : List Rec) (r : Nat) (color : List Nat → Bool) : List Edge :=
  (log.filter (fun e => decide (e.level ≤ r) && color e.colors)).map (proj ch r)

theorem records_exact (ch : Chain) (log : List Rec) (r : Nat) (color : List Nat → Bool)
    (ps : List Nat) (a : Nat) :
    (ps, a) ∈ records ch log r color ↔ (viewC ch log r color).edges ps a := by
  simp [records, viewC, and_assoc]

def distinct : List Nat → List Nat
  | [] => []
  | x :: xs => if xs.contains x then distinct xs else x :: distinct xs

theorem mem_distinct (x : Nat) (xs : List Nat) : x ∈ distinct xs ↔ x ∈ xs := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    by_cases h : a ∈ as
    · have hc := List.contains_iff_mem.mpr h
      simp only [distinct, hc, if_true, ih, List.mem_cons]
      exact ⟨Or.inr, fun he => he.elim (fun e => e ▸ h) id⟩
    · have hc : as.contains a = false := Bool.eq_false_iff.mpr
        (fun h' => h (List.contains_iff_mem.mp h'))
      simp [distinct, h, ih]

theorem distinct_nodup (xs : List Nat) : (distinct xs).Nodup := by
  induction xs with
  | nil => simp [distinct]
  | cons a as ih =>
    by_cases h : a ∈ as
    · simp [distinct, h, ih]
    · have hc : as.contains a = false := Bool.eq_false_iff.mpr
        (fun h' => h (List.contains_iff_mem.mp h'))
      simp [distinct, ih, mem_distinct, h]

def unseen (known carrier : List Nat) : List Nat :=
  carrier.filter (fun a => !(known.contains a))

def missing (known ps : List Nat) : Nat := (unseen known (distinct ps)).length

theorem missing_exact (known ps : List Nat) :
    missing known ps = 0 ↔ ∀ p ∈ ps, p ∈ known := by
  constructor
  · intro h p hp
    by_cases hk : p ∈ known
    · exact hk
    · have hm : p ∈ unseen known (distinct ps) := by
        simp [unseen, mem_distinct, hp, hk]
      have hz : unseen known (distinct ps) = [] := List.length_eq_zero_iff.mp h
      simp [hz] at hm
  · intro h
    cases hz : unseen known (distinct ps) with
    | nil => simp [missing, hz]
    | cons p ps' =>
      have hm : p ∈ unseen known (distinct ps) := by rw [hz]; simp
      simp only [unseen, List.mem_filter, mem_distinct, Bool.not_eq_true',
        Bool.eq_false_iff, List.contains_iff_mem] at hm
      exact False.elim (hm.2 (List.contains_iff_mem.mpr (h p hm.1)))

theorem unseen_cons (a : Nat) (known us : List Nat) :
    unseen (a :: known) us = (unseen known us).filter (fun x => !(decide (x = a))) := by
  simp [unseen, List.filter_filter, Bool.not_or]

theorem missing_update (known ps : List Nat) (a : Nat) :
    missing (a :: known) ps =
      if a ∈ ps ∧ a ∉ known then missing known ps - 1 else missing known ps := by
  unfold missing
  rw [unseen_cons]
  have hn : (unseen known (distinct ps)).Nodup :=
    List.filter_sublist.nodup (distinct_nodup ps)
  have ht : a ∈ unseen known (distinct ps) ↔ a ∈ ps ∧ a ∉ known := by
    simp [unseen, mem_distinct]
  split
  · rename_i h
    have hh : a ∈ unseen known (distinct ps) := ht.mpr h
    rw [← List.length_erase_of_mem hh, hn.erase_eq_filter]
    congr 1
  · rename_i h
    rw [List.filter_eq_self.mpr]
    intro x hx
    have hne : x ≠ a := fun hxa => h (ht.mp (hxa ▸ hx))
    simp [hne]

def ready (es : List Edge) (known : List Nat) : List Nat :=
  (es.filter (fun e => (missing known e.1 == 0) && !(known.contains e.2))).map Prod.snd

theorem ready_exact (es : List Edge) (known : List Nat) (a : Nat) :
    a ∈ ready es known ↔ (∃ ps, (ps, a) ∈ es ∧ (∀ p ∈ ps, p ∈ known)) ∧ a ∉ known := by
  constructor
  · intro h
    obtain ⟨⟨ps, b⟩, he, hab⟩ := List.mem_map.mp h
    change b = a at hab
    subst b
    simp [ready, List.mem_filter, missing_exact] at he
    exact ⟨⟨ps, he.1, he.2.1⟩, he.2.2⟩
  · rintro ⟨⟨ps, he, hp⟩, ha⟩
    apply List.mem_map.mpr
    exact ⟨(ps, a), by simp [ready, he, (missing_exact _ _).mpr hp, ha], rfl⟩

/-- Bounded reference worklist: every tick publishes one novel ready atom.
    It scans; an indexed implementation must separately refine its invariant. -/
def run (es : List Edge) : Nat → List Nat → List Nat
  | 0, known => known
  | fuel + 1, known =>
    match (ready es known).head? with
    | none => known
    | some a => run es fuel (a :: known)

def carrier (es : List Edge) : List Nat := distinct (es.map Prod.snd)

def graph (es : List Edge) : Hypergraph Nat := ⟨fun _ => False, fun ps a => (ps,a) ∈ es⟩

theorem run_sound (es : List Edge) (fuel : Nat) (known : List Nat)
    (hs : ∀ a ∈ known, derives (graph es) a) :
    ∀ a ∈ run es fuel known, derives (graph es) a := by
  induction fuel generalizing known with
  | zero => exact hs
  | succ fuel ih =>
    unfold run
    split
    · exact hs
    · rename_i a he
      have ha : a ∈ ready es known := by
        obtain ⟨tail, ht⟩ := List.head?_eq_some_iff.mp he
        rw [ht]; simp
      obtain ⟨⟨ps, hp, hk⟩, _⟩ := (ready_exact es known a).mp ha
      apply ih
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact .step hp (fun p h => hs p (hk p h))
      · exact hs b hb

def Closed (es : List Edge) (known : List Nat) : Prop :=
  ∀ ps a, (ps, a) ∈ es → (∀ p ∈ ps, p ∈ known) → a ∈ known

theorem ready_nil_iff_closed (es : List Edge) (known : List Nat) :
    ready es known = [] ↔ Closed es known := by
  constructor
  · intro h ps a he hp
    by_cases ha : a ∈ known
    · exact ha
    · have hm := (ready_exact es known a).mpr ⟨⟨ps, he, hp⟩, ha⟩
      simp [h] at hm
  · intro h
    cases hr : ready es known with
    | nil => rfl
    | cons a tail =>
      have hm : a ∈ ready es known := by rw [hr]; simp
      obtain ⟨⟨ps, he, hp⟩, ha⟩ := (ready_exact es known a).mp hm
      exact False.elim (ha (h ps a he hp))

theorem ready_spends_one (es : List Edge) (known : List Nat) (a : Nat)
    (ha : a ∈ ready es known) :
    (unseen (a :: known) (carrier es)).length <
      (unseen known (carrier es)).length := by
  obtain ⟨⟨ps, he, _⟩, hn⟩ := (ready_exact es known a).mp ha
  have hm : a ∈ unseen known (carrier es) := by
    have hu : a ∈ carrier es := (mem_distinct _ _).mpr (List.mem_map.mpr ⟨(ps,a), he, rfl⟩)
    simp [unseen, hu, hn]
  rw [unseen_cons]
  have hs : (List.filter (fun x => !(decide (x = a))) (unseen known (carrier es))).Sublist
      (unseen known (carrier es)) := List.filter_sublist
  have hle := hs.length_le
  by_cases hlt : (List.filter (fun x => !(decide (x = a))) (unseen known (carrier es))).length < (unseen known (carrier es)).length
  · exact hlt
  ·
    have heq := hs.eq_of_length (by omega)
    have hf : a ∈ List.filter (fun x => !(decide (x = a))) (unseen known (carrier es)) := by rw [heq]; exact hm
    simp at hf

theorem run_closed (es : List Edge) (fuel : Nat) (known : List Nat)
    (hf : (unseen known (carrier es)).length ≤ fuel) :
    Closed es (run es fuel known) := by
  induction fuel generalizing known with
  | zero =>
    have hz : unseen known (carrier es) = [] := List.length_eq_zero_iff.mp (by omega)
    apply (ready_nil_iff_closed es known).mp
    cases he : ready es known with
    | nil => rfl
    | cons a tail =>
      have hm : a ∈ ready es known := by rw [he]; simp
      have hs := ready_spends_one es known a hm
      simp [hz] at hs
  | succ fuel ih =>
    unfold run
    split
    · rename_i h
      exact (ready_nil_iff_closed es known).mp (List.head?_eq_none_iff.mp h)
    · rename_i a ha
      have hm : a ∈ ready es known := by
        obtain ⟨tail, ht⟩ := List.head?_eq_some_iff.mp ha
        rw [ht]; simp
      exact ih (a :: known) (by have := ready_spends_one es known a hm; omega)

def closure (es : List Edge) : List Nat := run es (carrier es).length []

theorem closure_exact (es : List Edge) (a : Nat) :
    a ∈ closure es ↔ derives (graph es) a := by
  constructor
  · exact run_sound _ _ [] (by simp) a
  · exact Derives.least (fun _ h => h.elim)
      (run_closed _ _ [] (List.length_filter_le _ _)) a

theorem canonical_exact (ch : Chain) (log : List Rec) (r : Nat) (color : List Nat → Bool) (a : Nat) :
    a ∈ closure (records ch log r color) ↔ derives (viewC ch log r color) a := by
  rw [closure_exact]
  have h : graph (records ch log r color) = viewC ch log r color := by
    unfold graph viewC
    congr 1
    funext ps x
    exact propext (records_exact ch log r color ps x)
  rw [h]

/-- Append prefixes may carry forward their exact closure at the
    same projection, while widening/narrowing applies a different view. -/
def resume (old delta : List Edge) : List Nat :=
  let es := old ++ delta
  let known := closure old
  run es (unseen known (carrier es)).length known

theorem resume_exact (old delta : List Edge) (a : Nat) :
    a ∈ resume old delta ↔ a ∈ closure (old ++ delta) := by
  rw [closure_exact]
  constructor
  · apply run_sound
    intro b hb
    exact Derives.mono (fun _ h => h.elim)
      (fun ps x h => List.mem_append_left _ (show (ps,x) ∈ old from h)) b
      ((closure_exact old b).mp hb)
  · exact Derives.least (B := (graph (old ++ delta)).roots) (fun _ h => h.elim)
      (run_closed _ _ _ (Nat.le_refl _)) a

theorem canonical_resume_exact (ch : Chain) (log extra : List Rec) (r : Nat)
    (color : List Nat → Bool) (a : Nat) :
    a ∈ resume (records ch log r color) (records ch extra r color) ↔
      derives (viewC ch (log ++ extra) r color) a := by
  rw [resume_exact, ← canonical_exact]
  simp [records]

#print axioms missing_update
#print axioms resume_exact
#print axioms canonical_resume_exact
#print axioms records_exact
#print axioms mem_distinct
#print axioms distinct_nodup
#print axioms missing_exact
#print axioms unseen_cons
#print axioms ready_exact
#print axioms run_sound
#print axioms ready_nil_iff_closed
#print axioms ready_spends_one
#print axioms run_closed
#print axioms closure_exact
#print axioms canonical_exact

end Canon.ClosureWorklist
