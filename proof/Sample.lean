/-
  Premise-closed samples reconstruct exactly (gap G3, kernel).

  A set of atoms is premise-closed at a level when every edge
  concluding in it has all its premises in it. Restricting the
  view to the edges concluding in such a set loses no
  derivation of any of its atoms: derivability inside the
  sample equals derivability in the whole graph, for every atom
  of the sample. A sample that is not premise-closed can lose a
  derivation (control). This is the fold form the campaign's
  premise-closed protocol rests on; the protocol's measured run
  is in the program's results, not here.
-/

import Canon

namespace Canon

/-- Premise-closure of an atom set in a hypergraph. -/
def PremClosed (g : Hypergraph Nat) (C : Nat → Prop) : Prop :=
  ∀ ps a, g.edges ps a → C a → ∀ p ∈ ps, C p

/-- The restriction of a hypergraph to edges concluding in a
    set. -/
def restrict (g : Hypergraph Nat) (C : Nat → Prop) : Hypergraph Nat :=
  ⟨fun a => g.roots a ∧ C a, fun ps a => g.edges ps a ∧ C a⟩

namespace Sample

/-- Exact reconstruction: inside a premise-closed set,
    derivability in the restriction equals derivability in the
    whole graph. -/
theorem exact (g : Hypergraph Nat) (C : Nat → Prop) (hc : PremClosed g C) (a : Nat) (ha : C a) :
    derives (restrict g C) a ↔ derives g a := by
  constructor
  · intro h
    exact Derives.mono (fun _ h => h.1) (fun _ _ h => h.1) a h
  · intro h
    have key : ∀ x, derives g x → C x → derives (restrict g C) x := by
      intro x hx
      induction hx with
      | root hb => intro hx; exact Derives.root ⟨hb, hx⟩
      | @step ps x he _ ih =>
        intro hx
        exact Derives.step ⟨he, hx⟩ (fun p hp => ih p hp (hc ps x he hx p hp))
    exact key a h ha

/-- Premise-closure is preserved by unions. -/
theorem union (g : Hypergraph Nat) (C D : Nat → Prop) (hc : PremClosed g C) (hd : PremClosed g D) :
    PremClosed g (fun a => C a ∨ D a) := by
  intro ps a he ha p hp
  rcases ha with ha | ha
  · exact Or.inl (hc ps a he ha p hp)
  · exact Or.inr (hd ps a he ha p hp)

/-- Premise-closure of a view survives appending records only
    when the new edges respect it: closure is a property of the
    current log. -/
theorem shrink_log (ch : Chain) (L M : List Rec) (r : Nat) (q : List Nat → Bool) (C : Nat → Prop)
    (hc : PremClosed (viewC ch (L ++ M) r q) C) : PremClosed (viewC ch L r q) C :=
  fun ps a he ha p hp => hc ps a (View.grow ch L M r q ps a he) ha p hp

end Sample

namespace Control

/-- Control open sample: the sample {3} is not premise-closed
    under the rule from 1 to 3, and the restriction loses the
    derivation of 3. -/
def openG : Hypergraph Nat := ⟨fun a => a = 1, fun ps a => ps = [1] ∧ a = 3⟩

theorem open_sample : derives openG 3 ∧ ¬ derives (restrict openG (fun a => a = 3)) 3 := by
  constructor
  · exact Derives.step (ps := [1]) ⟨rfl, rfl⟩ (fun p hp => by
      simp at hp; subst hp; exact Derives.root rfl)
  · intro h
    have : ∀ x, derives (restrict openG (fun a => a = 3)) x → False := by
      intro x hx
      induction hx with
      | root hb => exact absurd (hb.1.symm.trans hb.2) (by decide)
      | @step ps x he _ ih =>
        obtain ⟨⟨hps, _⟩, _⟩ := he
        subst hps
        exact ih 1 (by simp)
    exact this 3 h

end Control

#print axioms Sample.exact
#print axioms Sample.union
#print axioms Sample.shrink_log
#print axioms Control.open_sample

end Canon
