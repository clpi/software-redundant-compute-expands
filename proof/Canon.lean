/-
  The canonical hypergraph: one record log, every resolution
  level appended to it, every view derived from it.

  Mirror. `Derives` and `Hypergraph` are the authoritative
  definitions of software-optimality at 95df5fb
  (Qualification.lean, HypergraphIncremental.lean): atoms,
  roots, finite-premise edges, derivability as the least
  closure. They are restated verbatim here and their
  properties are proved again from the definitions.

  Settled intent this file states for the first time (no
  earlier Lean home): terms are identified by a total
  equivalence at each resolution level; levels form a finite
  chain from the finest observed terms (level 0) to the
  coarsest view, each level's equivalence the kernel of a key,
  each coarser key a function of the finer one (`up`); the
  symbol level is a named index and analysis is admitted only
  at that level or finer. Observations at every level are
  records appended to one log; a record carries its receipt,
  its level, its colors (qualifications, possibly
  overlapping), its premises and its head, as classes at its
  own level. The hypergraph at level `r` is the projection of
  every record at level `r` or finer. Roots are records with
  no premises, so the log is the only source of truth.

  Proved: total equivalences nest along the chain and are
  equality at level 0; projections compose; every view is
  invariant under re-ordering the log; appending only adds
  edges, colors and derivations, at every level; the view of
  a join is the union of the views and appending what is
  already present changes nothing; every edge and every
  derivation at a level projects to an edge and a derivation
  at every coarser level, so a refinement appended later never
  contradicts a coarse result already read.
-/

namespace Canon

universe u

/-- Mirror of `Qualification.Derives` (software-optimality at
    95df5fb): derivability as the least closure of roots under
    finite-premise edges. -/
inductive Derives {A : Type u} (B : A → Prop) (R : List A → A → Prop) : A → Prop where
  | root {a : A} : B a → Derives B R a
  | step {ps : List A} {a : A} : R ps a → (∀ p, p ∈ ps → Derives B R p) → Derives B R a

/-- Mirror of `HypergraphIncremental.Hypergraph`. -/
structure Hypergraph (A : Type u) where
  roots : A → Prop
  edges : List A → A → Prop

def derives {A : Type u} (g : Hypergraph A) : A → Prop := Derives g.roots g.edges

namespace Derives

theorem least {A : Type u} {B : A → Prop} {R : List A → A → Prop} {X : A → Prop}
    (hb : ∀ a, B a → X a) (hr : ∀ ps a, R ps a → (∀ p, p ∈ ps → X p) → X a) :
    ∀ a, Derives B R a → X a := by
  intro a h
  induction h with
  | root h => exact hb _ h
  | step he _ ih => exact hr _ _ he ih

theorem mono {A : Type u} {B C : A → Prop} {R S : List A → A → Prop}
    (hb : ∀ a, B a → C a) (hr : ∀ ps a, R ps a → S ps a) :
    ∀ a, Derives B R a → Derives C S a :=
  least (fun a h => .root (hb a h)) (fun ps a h hp => .step (hr ps a h) hp)

/-- Roots are edges with no premises: the single-log form
    loses and adds nothing. -/
theorem roots_as_edges {A : Type u} (B : A → Prop) (R : List A → A → Prop) (a : A) :
    Derives B R a ↔ Derives (fun _ => False) (fun ps x => R ps x ∨ (ps = [] ∧ B x)) a := by
  constructor
  · intro h
    induction h with
    | root hb => exact .step (Or.inr ⟨rfl, hb⟩) (fun p hp => by simp at hp)
    | step he _ ih => exact .step (Or.inl he) ih
  · intro h
    induction h with
    | root hb => exact hb.elim
    | step he hp ih =>
      rcases he with he | ⟨rfl, hb⟩
      · exact .step he ih
      · exact .root hb

end Derives

/-- A finite resolution chain. Level 0 holds the finest
    observed terms; `up r` sends a class at level `r` to its
    class at level `r + 1`; `sym` is the symbol level, the
    coarsest level at which analysis is admitted; `top` is the
    coarsest level of the chain. -/
structure Chain where
  up : Nat → Nat → Nat
  sym : Nat
  top : Nat
  sym_le_top : sym ≤ top

/-- Projection from level `r` up `k` steps. -/
def lift (ch : Chain) (r : Nat) : Nat → Nat → Nat
  | 0, c => c
  | k + 1, c => ch.up (r + k) (lift ch r k c)

/-- The key of a level-0 term at level `r`: its class under
    the level's total equivalence. -/
def key (ch : Chain) (r : Nat) (t : Nat) : Nat := lift ch 0 r t

/-- Total equivalence at a level: equal keys. -/
def Eqv (ch : Chain) (r : Nat) (t u : Nat) : Prop := key ch r t = key ch r u

/-- A record of the one log. -/
structure Rec where
  id : Nat
  level : Nat
  colors : List Nat
  premises : List Nat
  head : Nat
  deriving DecidableEq

/-- A record projected to level `r` (meaningful when its own
    level is at most `r`). -/
def proj (ch : Chain) (r : Nat) (e : Rec) : List Nat × Nat :=
  (e.premises.map (lift ch e.level (r - e.level)), lift ch e.level (r - e.level) e.head)

/-- The hypergraph at level `r`: every record at level `r` or
    finer, projected to `r`, filtered by a color test. -/
def viewC (ch : Chain) (log : List Rec) (r : Nat) (q : List Nat → Bool) : Hypergraph Nat :=
  ⟨fun _ => False, fun ps a => ∃ e, e ∈ log ∧ e.level ≤ r ∧ q e.colors = true ∧ proj ch r e = (ps, a)⟩

/-- The uncolored (possible) view. -/
def view (ch : Chain) (log : List Rec) (r : Nat) : Hypergraph Nat := viewC ch log r (fun _ => true)

/-- The colors an edge carries at level `r`: every color of
    every record supporting it. -/
def colorsOf (ch : Chain) (log : List Rec) (r : Nat) (ps : List Nat) (a c : Nat) : Prop :=
  ∃ e, e ∈ log ∧ e.level ≤ r ∧ proj ch r e = (ps, a) ∧ c ∈ e.colors

namespace Lift

theorem zero (ch : Chain) (r c : Nat) : lift ch r 0 c = c := rfl

/-- Projections compose. -/
theorem add (ch : Chain) (r j : Nat) : ∀ k c,
    lift ch r (j + k) c = lift ch (r + j) k (lift ch r j c) := by
  intro k
  induction k with
  | zero => intro c; rfl
  | succ k ih =>
    intro c
    show ch.up (r + (j + k)) (lift ch r (j + k) c) = ch.up (r + j + k) (lift ch (r + j) k (lift ch r j c))
    rw [ih, Nat.add_assoc]

/-- The key at a coarser level is the projection of the key
    at the finer level. -/
theorem key_lift (ch : Chain) (r k t : Nat) : key ch (r + k) t = lift ch r k (key ch r t) := by
  simp only [key]
  have := add ch 0 r k t
  simpa using this

/-- Level 0 is the floor: its equivalence is equality. -/
theorem floor (ch : Chain) (t u : Nat) : Eqv ch 0 t u ↔ t = u := Iff.rfl

/-- Total equivalences nest: equal at a level, equal at every
    coarser level. -/
theorem nest (ch : Chain) (r k t u : Nat) (h : Eqv ch r t u) : Eqv ch (r + k) t u := by
  simp only [Eqv, key_lift] at *
  rw [h]

theorem eqv_refl (ch : Chain) (r t : Nat) : Eqv ch r t t := rfl
theorem eqv_symm (ch : Chain) (r t u : Nat) (h : Eqv ch r t u) : Eqv ch r u t := h.symm
theorem eqv_trans (ch : Chain) (r t u v : Nat) (h₁ : Eqv ch r t u) (h₂ : Eqv ch r u v) :
    Eqv ch r t v := h₁.trans h₂

end Lift

namespace View

/-- Projecting a projected record is projecting the record. -/
theorem proj_lift (ch : Chain) (e : Rec) (r k : Nat) (hl : e.level ≤ r) :
    proj ch (r + k) e
      = ((proj ch r e).1.map (lift ch r k), lift ch r k (proj ch r e).2) := by
  simp only [proj, List.map_map]
  have hk : r + k - e.level = (r - e.level) + k := by omega
  have hr : e.level + (r - e.level) = r := by omega
  have hf : ∀ c, lift ch e.level (r + k - e.level) c
      = lift ch r k (lift ch e.level (r - e.level) c) := by
    intro c
    rw [hk, Lift.add, hr]
  refine Prod.ext ?_ ?_
  · simp only
    apply List.map_congr_left
    intro c _
    simp [hf]
  · simp [hf]

/-- Re-ordering the log changes no view. -/
theorem perm (ch : Chain) {L L' : List Rec} (p : L.Perm L') (r : Nat) (q : List Nat → Bool) :
    viewC ch L r q = viewC ch L' r q := by
  simp only [viewC]
  congr
  funext ps a
  apply propext
  constructor
  · rintro ⟨e, he, h⟩; exact ⟨e, p.mem_iff.mp he, h⟩
  · rintro ⟨e, he, h⟩; exact ⟨e, p.mem_iff.mpr he, h⟩

/-- Appending only adds edges. -/
theorem grow (ch : Chain) (L M : List Rec) (r : Nat) (q : List Nat → Bool) (ps : List Nat) (a : Nat)
    (h : (viewC ch L r q).edges ps a) : (viewC ch (L ++ M) r q).edges ps a := by
  obtain ⟨e, he, h⟩ := h
  exact ⟨e, List.mem_append.mpr (Or.inl he), h⟩

/-- Appending only adds derivations. -/
theorem derives_grow (ch : Chain) (L M : List Rec) (r : Nat) (q : List Nat → Bool) (a : Nat)
    (h : derives (viewC ch L r q) a) : derives (viewC ch (L ++ M) r q) a :=
  Derives.mono (fun _ h => h) (fun ps a h => grow ch L M r q ps a h) a h

/-- The view of a join is the union of the views. -/
theorem join (ch : Chain) (L M : List Rec) (r : Nat) (q : List Nat → Bool) (ps : List Nat) (a : Nat) :
    (viewC ch (L ++ M) r q).edges ps a ↔ (viewC ch L r q).edges ps a ∨ (viewC ch M r q).edges ps a := by
  constructor
  · rintro ⟨e, he, h⟩
    rcases List.mem_append.mp he with he | he
    · exact Or.inl ⟨e, he, h⟩
    · exact Or.inr ⟨e, he, h⟩
  · rintro (⟨e, he, h⟩ | ⟨e, he, h⟩)
    · exact ⟨e, List.mem_append.mpr (Or.inl he), h⟩
    · exact ⟨e, List.mem_append.mpr (Or.inr he), h⟩

/-- Appending records already present changes nothing. -/
theorem absorb (ch : Chain) (L M : List Rec) (hm : ∀ e ∈ M, e ∈ L) (r : Nat) (q : List Nat → Bool) :
    viewC ch (L ++ M) r q = viewC ch L r q := by
  simp only [viewC]
  congr
  funext ps a
  apply propext
  constructor
  · rintro ⟨e, he, h⟩
    rcases List.mem_append.mp he with he | he
    · exact ⟨e, he, h⟩
    · exact ⟨e, hm e he, h⟩
  · rintro ⟨e, he, h⟩; exact ⟨e, List.mem_append.mpr (Or.inl he), h⟩

/-- Colors are append-only: appending never removes a color
    from an edge. -/
theorem colors_grow (ch : Chain) (L M : List Rec) (r : Nat) (ps : List Nat) (a c : Nat)
    (h : colorsOf ch L r ps a c) : colorsOf ch (L ++ M) r ps a c := by
  obtain ⟨e, he, h⟩ := h
  exact ⟨e, List.mem_append.mpr (Or.inl he), h⟩

/-- Color filters nest: a stronger test sees fewer edges. -/
theorem filter_nest (ch : Chain) (L : List Rec) (r : Nat) (q q' : List Nat → Bool)
    (hq : ∀ cs, q cs = true → q' cs = true) (ps : List Nat) (a : Nat)
    (h : (viewC ch L r q).edges ps a) : (viewC ch L r q').edges ps a := by
  obtain ⟨e, he, hl, hc, hp⟩ := h
  exact ⟨e, he, hl, hq _ hc, hp⟩

/-- Every edge at a level projects to an edge at every
    coarser level. -/
theorem edge_proj (ch : Chain) (L : List Rec) (r k : Nat) (q : List Nat → Bool) (ps : List Nat) (a : Nat)
    (h : (viewC ch L r q).edges ps a) :
    (viewC ch L (r + k) q).edges (ps.map (lift ch r k)) (lift ch r k a) := by
  obtain ⟨e, he, hl, hc, hp⟩ := h
  refine ⟨e, he, by omega, hc, ?_⟩
  rw [proj_lift ch e r k hl, hp]

/-- Every derivation at a level projects to a derivation at
    every coarser level: a coarse result is a projection of the
    fine one, and refinement never contradicts it. -/
theorem derives_proj (ch : Chain) (L : List Rec) (r k : Nat) (q : List Nat → Bool) (a : Nat)
    (h : derives (viewC ch L r q) a) : derives (viewC ch L (r + k) q) (lift ch r k a) := by
  induction h with
  | root h => exact h.elim
  | @step ps a he _ ih =>
    refine Derives.step (edge_proj ch L r k q ps a he) ?_
    intro p hp
    obtain ⟨p0, hp0, rfl⟩ := List.mem_map.mp hp
    exact ih p0 hp0

/-- Appending a finer record adds its projection to every
    coarser view, and removes nothing anywhere. -/
theorem refine_append (ch : Chain) (L : List Rec) (e : Rec) (r : Nat) (hl : e.level ≤ r)
    (q : List Nat → Bool) (hq : q e.colors = true) :
    (viewC ch (L ++ [e]) r q).edges (proj ch r e).1 (proj ch r e).2
      ∧ ∀ ps a, (viewC ch L r q).edges ps a → (viewC ch (L ++ [e]) r q).edges ps a :=
  ⟨⟨e, by simp, hl, hq, rfl⟩, fun ps a h => grow ch L [e] r q ps a h⟩

end View

namespace Control

/-- Control floor: at a coarser level two distinct terms can be
    one class, so identification is a property of the level. -/
def chain2 : Chain := ⟨fun _ c => c / 10, 1, 1, Nat.le_refl 1⟩

theorem merge : ¬ Eqv chain2 0 10 11 ∧ Eqv chain2 1 10 11 := by
  constructor
  · intro h
    have h' : key chain2 0 10 = key chain2 0 11 := h
    simp [key, lift] at h'
  · show key chain2 1 10 = key chain2 1 11
    decide

/-- Control coarse-only: a record observed only at a coarse
    level is absent from every finer view; information never
    flows from coarse to fine. -/
theorem coarse_only :
    ¬ (view chain2 [⟨0, 1, [], [], 5⟩] 0).edges [] 5 := by
  rintro ⟨e, he, hl, _, _⟩
  simp at he
  subst he
  exact absurd hl (by decide)

end Control

#print axioms Derives.least
#print axioms Derives.mono
#print axioms Derives.roots_as_edges
#print axioms Lift.add
#print axioms Lift.key_lift
#print axioms Lift.floor
#print axioms Lift.nest
#print axioms View.proj_lift
#print axioms View.perm
#print axioms View.grow
#print axioms View.derives_grow
#print axioms View.join
#print axioms View.absorb
#print axioms View.colors_grow
#print axioms View.filter_nest
#print axioms View.edge_proj
#print axioms View.derives_proj
#print axioms View.refine_append
#print axioms Control.merge
#print axioms Control.coarse_only

end Canon
