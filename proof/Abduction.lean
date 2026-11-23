import Lean
import Canon

namespace Canon.Abduction

abbrev Choice := Nat → Prop
def Sub (a b : Choice) : Prop := ∀ x, a x → b x

def assume (g : Hypergraph Nat) (offers : Nat → Nat → Prop) (s : Choice) :
    Hypergraph Nat :=
  ⟨fun t => g.roots t ∨ ∃ a, s a ∧ offers a t, g.edges⟩

theorem assume_mono (g : Hypergraph Nat) (offers : Nat → Nat → Prop)
    {a b : Choice} (h : Sub a b) {t : Nat} :
    derives (assume g offers a) t → derives (assume g offers b) t :=
  Derives.mono (B := (assume g offers a).roots) (C := (assume g offers b).roots)
    (R := g.edges) (S := g.edges)
    (fun _ r => r.elim Or.inl (fun ⟨x,hx,hxt⟩ => Or.inr ⟨x,h x hx,hxt⟩))
    (fun _ _ r => r) t

theorem no_assumptions_restore (g : Hypergraph Nat) (offers : Nat → Nat → Prop) (t : Nat) :
    derives (assume g offers (fun _ => False)) t ↔ derives g t :=
  ⟨Derives.mono (B := (assume g offers (fun _ => False)).roots) (C := g.roots)
      (R := g.edges) (S := g.edges)
      (fun _ r => r.elim id (fun ⟨_,h,_⟩ => False.elim h)) (fun _ _ r => r) t,
   Derives.mono (B := g.roots) (C := (assume g offers (fun _ => False)).roots)
      (R := g.edges) (S := g.edges) (fun _ h => Or.inl h) (fun _ _ r => r) t⟩

structure Query where
  graph : Hypergraph Nat
  offers : Nat → Nat → Prop
  goals : List Nat
  forbidden : List Nat

def Solves (q : Query) (s : Choice) : Prop :=
  (∀ t ∈ q.goals, derives (assume q.graph q.offers s) t) ∧
  (∀ t ∈ q.forbidden, ¬ derives (assume q.graph q.offers s) t)

def Minimal (q : Query) (s : Choice) : Prop :=
  Solves q s ∧ ∀ k, Sub k s → Solves q k → Sub s k

namespace Cover
def Add (lo : Choice) (a : Nat) : Choice := fun x => lo x ∨ x = a
def Drop (hi : Choice) (a : Nat) : Choice := fun x => hi x ∧ x ≠ a

inductive Cert (q : Query) (plans : List Choice) : Choice → Choice → Prop where
  | covered {lo hi p} : p ∈ plans → Sub p lo → Cert q plans lo hi
  | forbidden {lo hi t} : t ∈ q.forbidden →
      derives (assume q.graph q.offers lo) t → Cert q plans lo hi
  | unreachable {lo hi t} : t ∈ q.goals →
      (¬ derives (assume q.graph q.offers hi) t) → Cert q plans lo hi
  | split {lo hi} (a : Nat) :
      Cert q plans lo (Drop hi a) → Cert q plans (Add lo a) hi → Cert q plans lo hi

theorem sound {q plans lo hi} (c : Cert q plans lo hi) :
    ∀ s, Sub lo s → Sub s hi → Solves q s → ∃ p ∈ plans, Sub p s := by
  induction c with
  | covered hm hsub =>
    intro s hl _ _
    exact ⟨_,hm,fun x hx => hl x (hsub x hx)⟩
  | forbidden ht hd =>
    intro s hl _ hs
    exact False.elim (hs.2 _ ht (assume_mono _ _ hl hd))
  | unreachable ht hn =>
    intro s _ hh hs
    exact False.elim (hn (assume_mono _ _ hh (hs.1 _ ht)))
  | split a _ _ left right =>
    intro s hl hh hs
    classical
    by_cases h : s a
    · exact right s (fun x hx => hx.elim (hl x) (fun e => e ▸ h)) hh hs
    · exact left s hl (fun x hx => ⟨hh x hx, fun e => h (e ▸ hx)⟩) hs

theorem exact_minimal {q plans lo hi s}
    (c : Cert q plans lo hi) (hl : Sub lo s) (hh : Sub s hi) (m : Minimal q s)
    (good : ∀ p ∈ plans, Solves q p) :
    ∃ p ∈ plans, Sub p s ∧ Sub s p := by
  obtain ⟨p,hp,sub⟩ := sound c s hl hh m.1
  exact ⟨p,hp,sub,m.2 p sub (good p hp)⟩

theorem every_solution_has_minimal_subset {q plans lo hi s}
    (c : Cert q plans lo hi) (hl : Sub lo s) (hh : Sub s hi) (h : Solves q s)
    (allMinimal : ∀ p ∈ plans, Minimal q p) :
    ∃ p, Minimal q p ∧ Sub p s := by
  obtain ⟨p,hp,hps⟩ := sound c s hl hh h
  exact ⟨p,allMinimal p hp,hps⟩
end Cover

/-- A premise-closed backward slice preserves both positive derivations and
    negative closure tests at every retained target. -/
def restrict (g : Hypergraph Nat) (keep : Nat → Prop) : Hypergraph Nat :=
  ⟨fun t => keep t ∧ g.roots t, fun ps t => keep t ∧ g.edges ps t⟩

theorem restriction_exact (g : Hypergraph Nat) (keep : Nat → Prop)
    (closed : ∀ ps t, g.edges ps t → keep t → ∀ p ∈ ps, keep p)
    (t : Nat) (ht : keep t) :
    derives (restrict g keep) t ↔ derives g t := by
  constructor
  · exact Derives.mono (B := (restrict g keep).roots) (C := g.roots)
      (R := (restrict g keep).edges) (S := g.edges)
      (fun _ r => r.2) (fun _ _ r => r.2) t
  · intro d
    exact Derives.least (B := g.roots) (R := g.edges)
      (X := fun a => keep a → derives (restrict g keep) a)
      (fun a root ha => Derives.root ⟨ha,root⟩)
      (fun ps a edge hk ha => Derives.step ⟨ha,edge⟩
        (fun p hp => hk p hp (closed ps a edge ha p hp))) t d ht

theorem single_omissions_certify_minimal (q : Query) (x : Choice)
    (good : Solves q x)
    (essential : ∀ a, x a → ∃ t ∈ q.goals,
      ¬ derives (assume q.graph q.offers (Cover.Drop x a)) t) : Minimal q x := by
  refine ⟨good,?_⟩
  intro y sub ok a ha
  classical
  by_cases h : y a
  · exact h
  · obtain ⟨t,hm,none⟩ := essential a ha
    exact False.elim (none (assume_mono _ _
      (fun p hp => ⟨sub p hp, fun e => h (e ▸ hp)⟩) (ok.1 t hm)))

theorem no_authority_from_offer (g : Hypergraph Nat) (offers : Nat → Nat → Prop)
    (t : Nat) (failed : ¬ derives g t) :
    ¬ derives (assume g offers (fun _ => False)) t :=
  fun p => failed ((no_assumptions_restore g offers t).mp p)

#print axioms assume_mono
#print axioms no_assumptions_restore
#print axioms Cover.sound
#print axioms Cover.exact_minimal
#print axioms Cover.every_solution_has_minimal_subset
#print axioms no_authority_from_offer
#print axioms restriction_exact
#print axioms single_omissions_certify_minimal
end Canon.Abduction
