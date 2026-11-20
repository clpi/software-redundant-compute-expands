/-
  Intent composition on the one hypergraph.

  Intent derived from symbolic expressions enters as records
  appended to the same log, colored as intent. Two situations
  are proved to compose into one derived instantiation: intent
  that brings an implication the graph does not yet carry
  extends every view by exactly that edge and keeps every old
  edge; intent that overlaps implications already carried
  leaves every edge relation unchanged and only adds its color
  to the edges it overlaps. Composition is a function of the
  set of records alone: re-ordering, regrouping or repeating
  the composed parts yields the same hypergraph, so two
  derivations of the same records cannot fork. The closure of
  a composition is the closure of the union of the edges, so
  it carries every derivation of either part and the
  mixed-premise derivations neither part has (control).
-/

import Canon

namespace Canon

/-- Compose a log with intent records: append. -/
def compose (L I : List Rec) : List Rec := L ++ I

namespace Intent

/-- New information extends: an intent record's implication is
    an edge of the composed view, and every old edge stays. -/
theorem extends_ (ch : Chain) (L : List Rec) (i : Rec) (r : Nat) (q : List Nat → Bool)
    (hl : i.level ≤ r) (hq : q i.colors = true) :
    (viewC ch (compose L [i]) r q).edges (proj ch r i).1 (proj ch r i).2
      ∧ ∀ ps a, (viewC ch L r q).edges ps a → (viewC ch (compose L [i]) r q).edges ps a :=
  View.refine_append ch L i r hl q hq

/-- Overlap changes no edge: when every intent record's
    implication is already carried, the composed edge relation
    is the old one. -/
theorem overlap (ch : Chain) (L I : List Rec) (r : Nat) (q : List Nat → Bool)
    (hov : ∀ i ∈ I, i.level ≤ r → q i.colors = true →
      ∃ e ∈ L, e.level ≤ r ∧ q e.colors = true ∧ proj ch r e = proj ch r i) (ps : List Nat) (a : Nat) :
    (viewC ch (compose L I) r q).edges ps a ↔ (viewC ch L r q).edges ps a := by
  constructor
  · intro h
    rcases (View.join ch L I r q ps a).mp h with h | ⟨i, hi, hl, hq, hp⟩
    · exact h
    · obtain ⟨e, he, hel, heq, hep⟩ := hov i hi hl hq
      exact ⟨e, he, hel, heq, hep.trans hp⟩
  · exact View.grow ch L I r q ps a

/-- Overlap adds its color to the edges it overlaps. -/
theorem overlap_color (ch : Chain) (L : List Rec) (i : Rec) (r : Nat) (hl : i.level ≤ r) (c : Nat)
    (hc : c ∈ i.colors) : colorsOf ch (compose L [i]) r (proj ch r i).1 (proj ch r i).2 c :=
  ⟨i, by simp [compose], hl, rfl, hc⟩

/-- No forks: composition depends only on the records, not on
    their order or grouping. -/
theorem no_fork (ch : Chain) {L I L' I' : List Rec} (p : (compose L I).Perm (compose L' I'))
    (r : Nat) (q : List Nat → Bool) :
    viewC ch (compose L I) r q = viewC ch (compose L' I') r q := View.perm ch p r q

theorem comm (ch : Chain) (L I : List Rec) (r : Nat) (q : List Nat → Bool) :
    viewC ch (compose L I) r q = viewC ch (compose I L) r q :=
  View.perm ch List.perm_append_comm r q

theorem assoc (L I J : List Rec) : compose (compose L I) J = compose L (compose I J) :=
  List.append_assoc L I J

theorem idem (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool) :
    viewC ch (compose L L) r q = viewC ch L r q :=
  View.absorb ch L L (fun _ h => h) r q

/-- Composition carries every derivation of either part. -/
theorem carries (ch : Chain) (L I : List Rec) (r : Nat) (q : List Nat → Bool) (a : Nat)
    (h : derives (viewC ch L r q) a ∨ derives (viewC ch I r q) a) :
    derives (viewC ch (compose L I) r q) a := by
  rcases h with h | h
  · exact View.derives_grow ch L I r q a h
  · have := View.derives_grow ch I L r q a h
    rw [comm ch L I r q]
    exact this

end Intent

namespace Control

def idch : Chain := ⟨fun _ c => c, 0, 0, Nat.le_refl 0⟩

/-- Control mixed premise: the log admits 1, the intent admits
    2 and records the rule from 1 and 2 to 3; only the
    composition derives 3 when the rule sits with 2 and 1 sits
    apart. The closure of a composition is not the union of the
    closures. -/
theorem mixed :
    derives (view idch (compose [⟨0, 0, [], [], 1⟩] [⟨1, 0, [], [], 2⟩, ⟨2, 0, [], [1, 2], 3⟩]) 0) 3 := by
  refine Derives.step (ps := [1, 2]) ⟨⟨2, 0, [], [1, 2], 3⟩, by simp [compose], by decide, rfl, rfl⟩ ?_
  intro p hp
  simp at hp
  rcases hp with rfl | rfl
  · exact Derives.step (ps := []) ⟨⟨0, 0, [], [], 1⟩, by simp [compose], by decide, rfl, rfl⟩
      (fun _ h => by simp at h)
  · exact Derives.step (ps := []) ⟨⟨1, 0, [], [], 2⟩, by simp [compose], by decide, rfl, rfl⟩
      (fun _ h => by simp at h)

theorem mixed_apart : ¬ derives (view idch [⟨1, 0, [], [], 2⟩, ⟨2, 0, [], [1, 2], 3⟩] 0) 3 := by
  intro h
  have key : ∀ a, derives (view idch [⟨1, 0, [], [], 2⟩, ⟨2, 0, [], [1, 2], 3⟩] 0) a → a = 2 ∨ a = 3 := by
    intro a h
    induction h with
    | root h => exact h.elim
    | @step ps a he hp ih =>
      obtain ⟨e, he, _, _, hpe⟩ := he
      simp at he
      rcases he with rfl | rfl
      · simp [proj, lift] at hpe; exact Or.inl hpe.2.symm
      · simp [proj, lift] at hpe; exact Or.inr hpe.2.symm
  have h1 : derives (view idch [⟨1, 0, [], [], 2⟩, ⟨2, 0, [], [1, 2], 3⟩] 0) 1 := by
    cases h with
    | root h => exact h.elim
    | step he hp =>
      obtain ⟨e, he, _, _, hpe⟩ := he
      simp at he
      rcases he with rfl | rfl
      · simp [proj, lift] at hpe
      · simp [proj, lift] at hpe
        exact hp 1 (by rw [← hpe]; simp)
  rcases key 1 h1 with h | h <;> simp at h

end Control

#print axioms Intent.extends_
#print axioms Intent.overlap
#print axioms Intent.overlap_color
#print axioms Intent.no_fork
#print axioms Intent.comm
#print axioms Intent.assoc
#print axioms Intent.idem
#print axioms Intent.carries
#print axioms Control.mixed
#print axioms Control.mixed_apart

end Canon
