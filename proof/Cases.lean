/-
  Case handling as an append-only hierarchy.

  A case is a named test on records with a parent case. The
  registry starts at the root case, whose test accepts every
  record, and grows only by appending a case whose identity is
  fresh, whose parent is already registered, and whose test
  implies its parent's test; the last condition is the proof
  obligation a new case must discharge when it is persisted.
  So no record is ever unhandled (the root covers it), no
  registered case is ever rewritten, a new case only refines
  the classification of the records it accepts, and every
  property proved for a case holds for every case beneath it.
-/

import Canon

namespace Canon

structure Case where
  id : Nat
  parent : Nat
  test : Rec → Bool

def rootCase : Case := ⟨0, 0, fun _ => true⟩

/-- Well-formed registries: the root, then appended cases with
    fresh identities, registered parents and implied tests. -/
inductive WF : List Case → Prop
  | root : WF [rootCase]
  | add {reg : List Case} {c : Case} : WF reg → c.id ∉ reg.map Case.id →
      (∃ p ∈ reg, p.id = c.parent ∧ ∀ e, c.test e = true → p.test e = true) →
      WF (reg ++ [c])

/-- The cases a record falls under. -/
def matched (reg : List Case) (e : Rec) : List Case := reg.filter (fun c => c.test e)

/-- Ancestry through registered parents. -/
inductive Anc (reg : List Case) : Case → Case → Prop
  | refl (c : Case) : Anc reg c c
  | step {c p a : Case} : p ∈ reg → p.id = c.parent → Anc reg p a → Anc reg c a

namespace Cases

theorem root_mem {reg : List Case} (h : WF reg) : rootCase ∈ reg := by
  induction h with
  | root => simp
  | add _ _ _ ih => exact List.mem_append.mpr (Or.inl ih)

/-- Caseless: every record is handled by some registered case. -/
theorem total {reg : List Case} (h : WF reg) (e : Rec) : ∃ c ∈ reg, c.test e = true :=
  ⟨rootCase, root_mem h, rfl⟩

theorem ids_unique {reg : List Case} (h : WF reg) :
    ∀ a ∈ reg, ∀ b ∈ reg, a.id = b.id → a = b := by
  induction h with
  | root => intro a ha b hb _; simp at ha hb; rw [ha, hb]
  | @add reg c _ hfresh _ ih =>
    intro a ha b hb hab
    rcases List.mem_append.mp ha with ha | ha <;> rcases List.mem_append.mp hb with hb | hb
    · exact ih a ha b hb hab
    · simp at hb; subst hb
      exact (hfresh (List.mem_map.mpr ⟨a, ‹a ∈ reg›, hab⟩)).elim
    · simp at ha; subst ha
      exact (hfresh (List.mem_map.mpr ⟨b, ‹b ∈ reg›, hab.symm⟩)).elim
    · simp at ha hb; rw [ha, hb]

/-- Every registered case has a registered parent whose test
    its own test implies. -/
theorem parent_exists {reg : List Case} (h : WF reg) :
    ∀ c ∈ reg, ∃ p ∈ reg, p.id = c.parent ∧ ∀ e, c.test e = true → p.test e = true := by
  induction h with
  | root =>
    intro c hc; simp at hc; subst hc
    exact ⟨rootCase, by simp, rfl, fun _ _ => rfl⟩
  | @add reg c _ _ hpar ih =>
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · obtain ⟨p, hp, h1, h2⟩ := ih d hd
      exact ⟨p, List.mem_append.mpr (Or.inl hp), h1, h2⟩
    · simp at hd; subst hd
      obtain ⟨p, hp, h1, h2⟩ := hpar
      exact ⟨p, List.mem_append.mpr (Or.inl hp), h1, h2⟩

/-- The registered parent of a case is unique, and the case's
    test implies it. -/
theorem parent_impl {reg : List Case} (h : WF reg) {c p : Case} (hc : c ∈ reg)
    (hp : p ∈ reg) (hid : p.id = c.parent) : ∀ e, c.test e = true → p.test e = true := by
  obtain ⟨p', hp', h1, h2⟩ := parent_exists h c hc
  have : p = p' := ids_unique h p hp p' hp' (hid.trans h1.symm)
  subst this
  exact h2

/-- Inheritance: a property proved for a case holds for every
    registered case beneath it. -/
theorem inherit {reg : List Case} (h : WF reg) {c a : Case} (hc : c ∈ reg) (hanc : Anc reg c a)
    (Q : Rec → Prop) (hq : ∀ e, a.test e = true → Q e) : ∀ e, c.test e = true → Q e := by
  induction hanc with
  | refl => exact hq
  | @step c p a hp hid _ ih =>
    intro e he
    exact ih hp hq e (parent_impl h hc hp hid e he)

/-- Appending a case never rewrites the classification of a
    record: the old matches stay, the new case is added only
    for the records it accepts. -/
theorem refine (reg : List Case) (c : Case) (e : Rec) :
    matched (reg ++ [c]) e = matched reg e ++ (if c.test e then [c] else []) := by
  simp only [matched, List.filter_append, List.filter_cons, List.filter_nil]

/-- A record accepted by a case is accepted by all its
    ancestors. -/
theorem up_closed {reg : List Case} (h : WF reg) {c a : Case} (hc : c ∈ reg) (hanc : Anc reg c a)
    (e : Rec) (he : c.test e = true) : a.test e = true :=
  inherit h hc hanc (fun e => a.test e = true) (fun _ h => h) e he

end Cases

namespace Control

/-- Control fresh: a second case reusing a registered identity
    is refused by the well-formedness rule. -/
theorem fresh : ¬ WF ([rootCase] ++ [⟨0, 0, fun _ => false⟩]) := by
  intro h
  have he := Cases.ids_unique h rootCase (by simp) ⟨0, 0, fun _ => false⟩ (by simp) rfl
  have := congrArg (fun c => c.test ⟨0, 0, [], [], 0⟩) he
  simp [rootCase] at this

end Control

#print axioms Cases.root_mem
#print axioms Cases.total
#print axioms Cases.ids_unique
#print axioms Cases.parent_exists
#print axioms Cases.parent_impl
#print axioms Cases.inherit
#print axioms Cases.refine
#print axioms Cases.up_closed
#print axioms Control.fresh

end Canon
