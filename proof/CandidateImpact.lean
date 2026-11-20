import Canon

namespace Canon.CandidateImpact

universe u

/-- A conservative dependency projection exposes candidate consequences, but the
    authoritative graph still requires every premise, not just a reachable path. -/
def Incidence {A : Type u} (edges : List A → A → Prop) (p a : A) : Prop :=
  ∃ ps, edges ps a ∧ p ∈ ps

def jointRule (ps : List Nat) (a : Nat) : Prop := ps = [0, 1] ∧ a = 2

def under (seeds : List Nat) (a : Nat) : Prop :=
  Derives (fun x => x ∈ seeds) jointRule a

theorem reachable_left : Incidence jointRule 0 2 :=
  ⟨[0, 1], ⟨rfl, rfl⟩, by decide⟩

theorem reachable_right : Incidence jointRule 1 2 :=
  ⟨[0, 1], ⟨rfl, rfl⟩, by decide⟩

theorem seed_necessary {seeds : List Nat} {a : Nat} (different : a ≠ 2) :
    under seeds a → a ∈ seeds := by
  intro h
  cases h with
  | root h => exact h
  | step he _ => exact False.elim (different he.2)

/-- Arbitrary input seeds: the result needs its full joint support, unless
    already a root. This is the exact intervention predicate. -/
theorem qualifies_iff (seeds : List Nat) :
    under seeds 2 ↔ 2 ∈ seeds ∨ (0 ∈ seeds ∧ 1 ∈ seeds) := by
  constructor
  · intro h
    cases h with
    | root h => exact Or.inl h
    | step he hs =>
      rcases he with ⟨rfl, _⟩
      exact Or.inr ⟨seed_necessary (by decide) (hs 0 (by decide)),
        seed_necessary (by decide) (hs 1 (by decide))⟩
  · intro h
    rcases h with h | ⟨h0, h1⟩
    · exact .root h
    · apply Derives.step (ps := [0, 1]) (show jointRule [0, 1] 2 from ⟨rfl, rfl⟩)
      intro p hp
      simp at hp
      rcases hp with rfl | rfl
      · exact .root h0
      · exact .root h1

theorem complementarity :
    ¬ under [0] 2 ∧ ¬ under [1] 2 ∧ under ([0] ++ [1]) 2 := by
  simp [qualifies_iff]

/-- Synthetic control: the three input states are views of one append-only
    canonical log at the same resolution and color filter. -/
def level : Chain := ⟨fun _ n => n, 0, 0, Nat.le_refl 0⟩
def ruleRecord : Rec := ⟨3, 0, [1], [0, 1], 2⟩
def rootRecord (n : Nat) : Rec := ⟨n, 0, [1], [], n⟩
def log (seeds : List Nat) : List Rec := [ruleRecord] ++ seeds.map rootRecord

theorem canonical_log_agrees (seeds : List Nat) (a : Nat) :
    derives (view level (log seeds) 0) a ↔ under seeds a := by
  have edges (ps : List Nat) (x : Nat) :
      (view level (log seeds) 0).edges ps x ↔
        jointRule ps x ∨ (ps = [] ∧ x ∈ seeds) := by
    simp only [view, viewC, log, Hypergraph.edges, List.mem_append, List.mem_singleton,
      List.mem_map, Nat.le_zero, and_true]
    constructor
    · rintro ⟨e, he, _, _, eq⟩
      rcases he with rfl | ⟨n, hn, rfl⟩
      · simp [ruleRecord, proj, lift] at eq
        exact Or.inl ⟨eq.1.symm, eq.2.symm⟩
      · simp [rootRecord, proj, lift] at eq
        exact Or.inr ⟨eq.1, eq.2 ▸ hn⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, hx⟩)
      · exact ⟨ruleRecord, Or.inl rfl, rfl, True.intro, rfl⟩
      · exact ⟨rootRecord x, Or.inr ⟨x, hx, rfl⟩, rfl, True.intro, rfl⟩
  rw [under, Derives.roots_as_edges]
  constructor
  · exact Derives.mono (fun _ h => h) (fun ps x h => (edges ps x).mp h) a
  · exact Derives.mono (fun _ h => h) (fun ps x h => (edges ps x).mpr h) a

theorem append_has_joint_consequence :
    ¬ derives (view level (log [0]) 0) 2 ∧
    ¬ derives (view level (log [1]) 0) 2 ∧
    derives (view level (log [0] ++ [rootRecord 1]) 0) 2 := by
  have h : log [0] ++ [rootRecord 1] = log [0, 1] := rfl
  rw [h]
  simpa only [canonical_log_agrees] using complementarity

end Canon.CandidateImpact

#print axioms Canon.CandidateImpact.qualifies_iff
#print axioms Canon.CandidateImpact.canonical_log_agrees
#print axioms Canon.CandidateImpact.append_has_joint_consequence
