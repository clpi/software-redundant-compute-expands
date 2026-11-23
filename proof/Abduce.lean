/-
  Abduction on the canonical hypergraph.

  A hypothesis is a set of terms appended to the one log as
  root records (level `r`, one color `c`, no premises). An
  explanation of observations `O` is a set `H` of abducible
  terms such that, once `H` is appended, every observation is
  derivable in the view and the reserved term `bot` is not.
  Negative observations enter the log as ordinary records whose
  head is `bot`, so consistency is derivability, nothing else.

  Proved here:
  * appending hypothesis records is the same as adding roots
    (`derivesWith_iff`), so the computable `closWith` is exact
    (`mem_closWith`) and `explainsB` decides `Explains`;
  * explanations depend only on the set of hypotheses
    (`explains_congr`), consistency is inherited by subsets
    (`consistent_sub`), so for a duplicate-free `H` minimality is
    decided by removing one hypothesis at a time
    (`minimal_iff_erase`, `minimalB_iff`);
  * the enumerator `abduce` returns exactly the minimal
    explanations within the size bound (`mem_abduce`), and every
    minimal explanation of that size has a member with the same
    terms (`abduce_complete`);
  * the cone of the observations decides everything about them
    (`cone_derivesWith`, `explains_cone`), which is what lets a
    certificate carry only the records that can reach them;
  * refutations never need retracting when the log grows
    (`inconsistent_persists`); an explanation stays one unless a
    new record derives `bot` (`explains_persists`); minimality
    does not persist (see the controls), so a minimality claim is
    tied to the log it was checked on;
  * admission appends only the records of a verified minimal
    explanation, only ever extends the log, never loses a
    derivation, and leaves the observations derivable and `bot`
    underivable (`admit_prefix`, `admit_monotone`,
    `admit_explains`, `admit_consistent`, `admit_refuses`);
  * ranking: the Pareto front over (coverage up, cost down) is
    exactly the undominated candidates (`mem_front`) and is never
    empty for a nonempty candidate list (`front_nonempty`).
-/
import Canon
import Closure

namespace Canon
namespace Abduce
open Closure

/-- A hypothesis record: a root at level `r` with color `c`. -/
def hypRec (r c : Nat) (h : Nat) : Rec := ⟨0, r, [c], [], h⟩

def hyps (r c : Nat) (H : List Nat) : List Rec := H.map (hypRec r c)

/-- An abduction problem over one log. -/
structure Problem where
  ch : Chain
  L : List Rec
  r : Nat
  q : List Nat → Bool
  bot : Nat
  A : List Nat
  O : List Nat

/-- Derivability once the terms of `H` are assumed. -/
def DerivesWith (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool) (H : List Nat) (a : Nat) : Prop :=
  Derives (fun x => x ∈ H) (V ch L r q).edges a

def Explains (P : Problem) (H : List Nat) : Prop :=
  (∀ h ∈ H, h ∈ P.A) ∧ (∀ o ∈ P.O, DerivesWith P.ch P.L P.r P.q H o) ∧
    ¬ DerivesWith P.ch P.L P.r P.q H P.bot

/-- No proper subset (as a set of terms) explains. -/
def Minimal (P : Problem) (H : List Nat) : Prop :=
  Explains P H ∧ ∀ H', (∀ x ∈ H', x ∈ H) → (∃ x ∈ H, x ∉ H') → ¬ Explains P H'

theorem proj_hyp (ch : Chain) (r c h : Nat) : proj ch r (hypRec r c h) = ([], h) := by
  simp [proj, hypRec, Nat.sub_self, lift]

/-- Appending hypothesis records is adding roots. -/
theorem derivesWith_iff (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool) (c : Nat)
    (hq : q [c] = true) (H : List Nat) (a : Nat) :
    derives (V ch (L ++ hyps r c H) r q) a ↔ DerivesWith ch L r q H a := by
  constructor
  · intro h
    induction h with
    | root hb => exact hb.elim
    | step he _ ih =>
      obtain ⟨e, hm, hl, hc, hp⟩ := he
      rcases List.mem_append.mp hm with hL | hH
      · exact Derives.step ⟨e, hL, hl, hc, hp⟩ ih
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hH
        rw [proj_hyp] at hp
        cases hp
        exact Derives.root hx
  · intro h
    induction h with
    | root hb =>
      rename_i x
      refine Derives.step (ps := []) ⟨hypRec r c x, ?_, Nat.le_refl r, hq, proj_hyp ch r c x⟩ ?_
      · exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨x, hb, rfl⟩))
      · intro p hp; simp at hp
    | step he _ ih =>
      obtain ⟨e, hm, hl, hc, hp⟩ := he
      exact Derives.step ⟨e, List.mem_append.mpr (Or.inl hm), hl, hc, hp⟩ ih

/-- The computable closure with `H` assumed. -/
def closWith (P : Problem) (c : Nat) (H : List Nat) : List Nat :=
  clos P.ch (P.L ++ hyps P.r c H) P.r P.q

theorem mem_closWith (P : Problem) (c : Nat) (hq : P.q [c] = true) (H : List Nat) (a : Nat) :
    a ∈ closWith P c H ↔ DerivesWith P.ch P.L P.r P.q H a :=
  (mem_clos _ _ _ _ a).trans (derivesWith_iff _ _ _ _ c hq H a)

def explainsB (P : Problem) (c : Nat) (H : List Nat) : Bool :=
  H.all (fun h => decide (h ∈ P.A)) &&
    (P.O.all (fun o => decide (o ∈ closWith P c H)) && !decide (P.bot ∈ closWith P c H))

theorem explainsB_iff (P : Problem) (c : Nat) (hq : P.q [c] = true) (H : List Nat) :
    explainsB P c H = true ↔ Explains P H := by
  simp only [explainsB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not, mem_closWith P c hq, Explains]

/-! Set invariance and inheritance. -/

theorem derivesWith_roots (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool) (H H' : List Nat)
    (h : ∀ x ∈ H, x ∈ H') (a : Nat) : DerivesWith ch L r q H a → DerivesWith ch L r q H' a :=
  Derives.mono (fun x hx => h x hx) (fun _ _ he => he) a

theorem derivesWith_congr (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool) (H H' : List Nat)
    (h : ∀ x, x ∈ H ↔ x ∈ H') (a : Nat) : DerivesWith ch L r q H a ↔ DerivesWith ch L r q H' a :=
  ⟨derivesWith_roots ch L r q H H' (fun x hx => (h x).mp hx) a,
   derivesWith_roots ch L r q H' H (fun x hx => (h x).mpr hx) a⟩

theorem explains_congr (P : Problem) (H H' : List Nat) (h : ∀ x, x ∈ H ↔ x ∈ H') :
    Explains P H ↔ Explains P H' := by
  unfold Explains
  constructor
  · rintro ⟨hA, hO, hb⟩
    refine ⟨fun x hx => hA x ((h x).mpr hx), fun o ho => (derivesWith_congr _ _ _ _ H H' h o).mp (hO o ho), ?_⟩
    intro hb'; exact hb ((derivesWith_congr _ _ _ _ H H' h _).mpr hb')
  · rintro ⟨hA, hO, hb⟩
    refine ⟨fun x hx => hA x ((h x).mp hx), fun o ho => (derivesWith_congr _ _ _ _ H H' h o).mpr (hO o ho), ?_⟩
    intro hb'; exact hb ((derivesWith_congr _ _ _ _ H H' h _).mp hb')

/-- Every subset of a consistent hypothesis set is consistent. -/
theorem consistent_sub (P : Problem) (H H' : List Nat) (hs : ∀ x ∈ H', x ∈ H)
    (hc : ¬ DerivesWith P.ch P.L P.r P.q H P.bot) : ¬ DerivesWith P.ch P.L P.r P.q H' P.bot :=
  fun h => hc (derivesWith_roots _ _ _ _ H' H hs _ h)

/-- For a duplicate-free `H`, minimality is decided by removing
    one hypothesis at a time. -/
theorem minimal_iff_erase (P : Problem) (H : List Nat) (hn : H.Nodup) :
    Minimal P H ↔ Explains P H ∧ ∀ x ∈ H, ¬ Explains P (H.erase x) := by
  constructor
  · rintro ⟨he, hm⟩
    refine ⟨he, fun x hx => hm (H.erase x) (fun y hy => List.mem_of_mem_erase hy) ⟨x, hx, ?_⟩⟩
    exact fun h => ((List.Nodup.mem_erase_iff hn).mp h).1 rfl
  · rintro ⟨he, hm⟩
    refine ⟨he, ?_⟩
    rintro H' hsub ⟨x, hx, hnx⟩ ⟨hA', hO', hb'⟩
    apply hm x hx
    have hsub' : ∀ y ∈ H', y ∈ H.erase x := by
      intro y hy
      have hne : y ≠ x := fun h => hnx (h ▸ hy)
      exact (List.Nodup.mem_erase_iff hn).mpr ⟨hne, hsub y hy⟩
    refine ⟨fun y hy => he.1 y (List.mem_of_mem_erase hy), ?_, ?_⟩
    · intro o ho; exact derivesWith_roots _ _ _ _ H' (H.erase x) hsub' o (hO' o ho)
    · exact consistent_sub P H (H.erase x) (fun y hy => List.mem_of_mem_erase hy) he.2.2

def minimalB (P : Problem) (c : Nat) (H : List Nat) : Bool :=
  decide H.Nodup && explainsB P c H && H.all (fun x => !explainsB P c (H.erase x))

theorem minimalB_iff (P : Problem) (c : Nat) (hq : P.q [c] = true) (H : List Nat) :
    minimalB P c H = true ↔ H.Nodup ∧ Minimal P H := by
  unfold minimalB
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true',
    explainsB_iff P c hq]
  constructor
  · rintro ⟨⟨hn, he⟩, hm⟩
    refine ⟨hn, (minimal_iff_erase P H hn).mpr ⟨he, fun x hx h => ?_⟩⟩
    have := hm x hx
    rw [← Bool.not_eq_true, explainsB_iff P c hq] at this
    exact this h
  · rintro ⟨hn, hmin⟩
    obtain ⟨he, hm⟩ := (minimal_iff_erase P H hn).mp hmin
    refine ⟨⟨hn, he⟩, fun x hx => ?_⟩
    rw [← Bool.not_eq_true, explainsB_iff P c hq]
    exact hm x hx

/-! The enumerator. -/

/-- Every sublist, as a list of lists. -/
def subs : List Nat → List (List Nat)
  | [] => [[]]
  | a :: t => subs t ++ (subs t).map (a :: ·)

theorem mem_subs : ∀ (l H : List Nat), H ∈ subs l ↔ List.Sublist H l := by
  intro l
  induction l with
  | nil => intro H; simp [subs]
  | cons a t ih =>
    intro H
    simp only [subs, List.mem_append, List.mem_map, ih]
    constructor
    · rintro (h | ⟨H0, h0, rfl⟩)
      · exact h.cons a
      · exact h0.cons₂ a
    · intro h
      cases h with
      | cons _ h => exact Or.inl h
      | cons₂ _ h => exact Or.inr ⟨_, h, rfl⟩

def abduce (P : Problem) (c k : Nat) : List (List Nat) :=
  (subs P.A).filter (fun H => decide (H.length ≤ k) && minimalB P c H)

theorem mem_abduce (P : Problem) (c k : Nat) (hq : P.q [c] = true) (H : List Nat) :
    H ∈ abduce P c k ↔ List.Sublist H P.A ∧ H.length ≤ k ∧ H.Nodup ∧ Minimal P H := by
  unfold abduce
  rw [List.mem_filter, mem_subs]
  simp only [Bool.and_eq_true, decide_eq_true_eq, minimalB_iff P c hq]

theorem nodup_length_le : ∀ (l m : List Nat), l.Nodup → (∀ x ∈ l, x ∈ m) → l.length ≤ m.length := by
  intro l
  induction l with
  | nil => intro m _ _; simp
  | cons a l ih =>
    intro m hn hs
    have ha : a ∈ m := hs a (List.mem_cons_self)
    have hn' := List.nodup_cons.mp hn
    have h1 : l.length ≤ (m.erase a).length := by
      apply ih (m.erase a) hn'.2
      intro x hx
      have hne : x ≠ a := fun h => hn'.1 (h ▸ hx)
      exact (List.mem_erase_of_ne hne).mpr (hs x (List.mem_cons_of_mem a hx))
    rw [List.length_erase_of_mem ha] at h1
    have : 0 < m.length := List.length_pos_of_mem ha
    simp only [List.length_cons]
    omega

/-- Completeness: every minimal explanation within
    the bound has a member of `abduce` with exactly its terms. -/
theorem abduce_complete (P : Problem) (c k : Nat) (hq : P.q [c] = true) (hA : P.A.Nodup)
    (S : List Nat) (hk : S.length ≤ k) (hm : Minimal P S) :
    ∃ H ∈ abduce P c k, ∀ x, x ∈ H ↔ x ∈ S := by
  refine ⟨P.A.filter (fun x => decide (x ∈ S)), ?_, ?_⟩
  · have hsame : ∀ x, x ∈ P.A.filter (fun x => decide (x ∈ S)) ↔ x ∈ S := by
      intro x
      rw [List.mem_filter, decide_eq_true_eq]
      exact ⟨fun h => h.2, fun h => ⟨hm.1.1 x h, h⟩⟩
    have hsub : List.Sublist (P.A.filter (fun x => decide (x ∈ S))) P.A := List.filter_sublist
    have hn : (P.A.filter (fun x => decide (x ∈ S))).Nodup := hA.sublist hsub
    refine (mem_abduce P c k hq _).mpr ⟨hsub, ?_, hn, ?_⟩
    · exact Nat.le_trans (nodup_length_le _ S hn (fun x hx => (hsame x).mp hx)) hk
    · refine ⟨(explains_congr P _ S hsame).mpr hm.1, ?_⟩
      intro H' hs hx
      apply hm.2 H' (fun y hy => (hsame y).mp (hs y hy))
      obtain ⟨x, hx, hnx⟩ := hx
      exact ⟨x, (hsame x).mp hx, hnx⟩
  · intro x
    rw [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hm.1.1 x h, h⟩⟩

/-! The cone: only records that can reach the observations matter. -/

/-- `T` is closed backwards: every record of the view whose head is
    in `T` has all its premises in `T`. -/
def coneClosedB (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool) (T : List Nat) : Bool :=
  L.all (fun e => !(decide (e.level ≤ r) && q e.colors && decide ((proj ch r e).2 ∈ T)) ||
    (proj ch r e).1.all (fun p => decide (p ∈ T)))

def coneOf (ch : Chain) (L : List Rec) (r : Nat) (T : List Nat) : List Rec :=
  L.filter (fun e => decide ((proj ch r e).2 ∈ T))

theorem cone_derivesWith (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool) (T H : List Nat)
    (hc : coneClosedB ch L r q T = true) (a : Nat) (ha : a ∈ T) :
    DerivesWith ch L r q H a ↔ DerivesWith ch (coneOf ch L r T) r q H a := by
  constructor
  · intro h
    revert ha
    induction h with
    | root hb => intro _; exact Derives.root hb
    | @step ps x he _ ih =>
      intro hx
      obtain ⟨e, hm, hl, hcol, hp⟩ := he
      simp only [coneClosedB, List.all_eq_true] at hc
      have hce := hc e hm
      simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
        List.all_eq_true, decide_eq_true_eq] at hce
      have hhead : (proj ch r e).2 ∈ T := by rw [hp]; exact hx
      have hprem : ∀ p ∈ ps, p ∈ T := by
        rcases hce with ((h1 | h1) | h1) | h1
        · exact absurd hl h1
        · rw [hcol] at h1; exact absurd h1 (by simp)
        · exact absurd hhead h1
        · rw [hp] at h1; exact h1
      refine Derives.step ⟨e, ?_, hl, hcol, hp⟩ (fun p hpm => ih p hpm (hprem p hpm))
      exact List.mem_filter.mpr ⟨hm, decide_eq_true hhead⟩
  · intro h
    exact Derives.mono (fun _ hx => hx)
      (fun ps x ⟨e, hm, hl, hcol, hp⟩ => ⟨e, (List.mem_filter.mp hm).1, hl, hcol, hp⟩) a h

/-- A problem on the cone explains exactly what the problem on the
    whole log explains, when the observations and `bot` lie in a
    backward-closed `T`. -/
theorem explains_cone (P : Problem) (T : List Nat) (hc : coneClosedB P.ch P.L P.r P.q T = true)
    (hO : ∀ o ∈ P.O, o ∈ T) (hb : P.bot ∈ T) (H : List Nat) :
    Explains P H ↔ Explains { P with L := coneOf P.ch P.L P.r T } H := by
  unfold Explains
  constructor
  · rintro ⟨hA, hO', hb'⟩
    refine ⟨hA, fun o ho => (cone_derivesWith _ _ _ _ T H hc o (hO o ho)).mp (hO' o ho), ?_⟩
    intro h; exact hb' ((cone_derivesWith _ _ _ _ T H hc _ hb).mpr h)
  · rintro ⟨hA, hO', hb'⟩
    refine ⟨hA, fun o ho => (cone_derivesWith _ _ _ _ T H hc o (hO o ho)).mpr (hO' o ho), ?_⟩
    intro h; exact hb' ((cone_derivesWith _ _ _ _ T H hc _ hb).mp h)

theorem minimal_cone (P : Problem) (T : List Nat) (hc : coneClosedB P.ch P.L P.r P.q T = true)
    (hO : ∀ o ∈ P.O, o ∈ T) (hb : P.bot ∈ T) (H : List Nat) :
    Minimal P H ↔ Minimal { P with L := coneOf P.ch P.L P.r T } H := by
  unfold Minimal
  constructor
  · rintro ⟨he, hm⟩
    exact ⟨(explains_cone P T hc hO hb H).mp he,
      fun H' hs hx h => hm H' hs hx ((explains_cone P T hc hO hb H').mpr h)⟩
  · rintro ⟨he, hm⟩
    exact ⟨(explains_cone P T hc hO hb H).mpr he,
      fun H' hs hx h => hm H' hs hx ((explains_cone P T hc hO hb H').mp h)⟩

/-- A certificate: the cone check runs over the whole log, the
    minimality check only over the cone. -/
theorem certificate (P : Problem) (c : Nat) (hq : P.q [c] = true) (T H : List Nat)
    (hc : coneClosedB P.ch P.L P.r P.q T = true)
    (hO : P.O.all (fun o => decide (o ∈ T)) = true) (hb : decide (P.bot ∈ T) = true)
    (hm : minimalB { P with L := coneOf P.ch P.L P.r T } c H = true) : H.Nodup ∧ Minimal P H := by
  simp only [List.all_eq_true, decide_eq_true_eq] at hO hb
  have h := (minimalB_iff { P with L := coneOf P.ch P.L P.r T } c hq H).mp hm
  exact ⟨h.1, (minimal_cone P T hc hO hb H).mpr h.2⟩

/-- The same, with the cone given as a literal list and its equation
    to `coneOf` checked once. -/
theorem certificate_lit (P : Problem) (c : Nat) (hq : P.q [c] = true) (T H : List Nat) (Lc : List Rec)
    (hc : coneClosedB P.ch P.L P.r P.q T = true) (hL : coneOf P.ch P.L P.r T = Lc)
    (hO : P.O.all (fun o => decide (o ∈ T)) = true) (hb : decide (P.bot ∈ T) = true)
    (hm : minimalB { P with L := Lc } c H = true) : H.Nodup ∧ Minimal P H :=
  certificate P c hq T H hc hO hb (hL ▸ hm)

/-! One-pass certificates. A derivation trace proves derivability;
    a closed set proves non-derivability. Both are checked in one
    pass over the records, so the kernel never runs the closure. -/

/-- `S` contains `H` and is closed under every record of the view. -/
def closedB (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool) (H S : List Nat) : Bool :=
  H.all (fun h => decide (h ∈ S)) &&
    L.all (fun e => !(decide (e.level ≤ r) && q e.colors && (proj ch r e).1.all (fun p => decide (p ∈ S))) ||
      decide ((proj ch r e).2 ∈ S))

theorem closedB_sound (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool) (H S : List Nat)
    (hc : closedB ch L r q H S = true) (a : Nat) (ha : DerivesWith ch L r q H a) : a ∈ S := by
  simp only [closedB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hH, hL⟩ := hc
  revert ha
  apply Derives.least (X := fun a => a ∈ S)
  · intro x hx; exact hH x hx
  · rintro ps x ⟨e, hm, hl, hcol, hp⟩ hps
    have he := hL e hm
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
      List.all_eq_false, decide_eq_true_eq] at he
    rcases he with ((h1 | h1) | ⟨p, hp1, hp2⟩) | h1
    · exact absurd hl h1
    · rw [hcol] at h1; exact absurd h1 (by simp)
    · rw [hp] at hp1; exact absurd (hps p hp1) hp2
    · rw [hp] at h1; exact h1

/-- A derivation trace: each term is assumed or the head of a record
    whose premises appear earlier. -/
def traceOk (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool) (H : List Nat) :
    List Nat → List Nat → Bool
  | _, [] => true
  | D, a :: t =>
    (decide (a ∈ H) || L.any (fun e => decide (e.level ≤ r) && q e.colors && decide ((proj ch r e).2 = a) &&
      (proj ch r e).1.all (fun p => decide (p ∈ D)))) && traceOk ch L r q H (a :: D) t

theorem traceOk_sound (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool) (H : List Nat) :
    ∀ (t D : List Nat), (∀ d ∈ D, DerivesWith ch L r q H d) → traceOk ch L r q H D t = true →
      ∀ a ∈ t, DerivesWith ch L r q H a := by
  intro t
  induction t with
  | nil => intro D _ _ a ha; simp at ha
  | cons x t ih =>
    intro D hD ht
    simp only [traceOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true,
      List.all_eq_true] at ht
    obtain ⟨hx, ht⟩ := ht
    have hdx : DerivesWith ch L r q H x := by
      rcases hx with hx | ⟨e, hm, ⟨⟨hl, hcol⟩, hh⟩, hps⟩
      · exact Derives.root hx
      · refine Derives.step (ps := (proj ch r e).1) ⟨e, hm, hl, hcol, by rw [← hh]⟩ ?_
        intro p hp; exact hD p (hps p hp)
    have hD' : ∀ d ∈ x :: D, DerivesWith ch L r q H d := by
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact hdx
      · exact hD d hd
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hdx
    · exact ih (x :: D) hD' ht a ha

/-- The whole certificate: `H` duplicate free and abducible, a
    trace deriving every observation, a closed set without `bot`,
    and for each hypothesis a closed set over the rest that misses
    an observation. -/
def certB (P : Problem) (H tr Sbot : List Nat) (Sx : List (Nat × List Nat)) : Bool :=
  decide H.Nodup && H.all (fun h => decide (h ∈ P.A)) &&
  traceOk P.ch P.L P.r P.q H [] tr && P.O.all (fun o => decide (o ∈ tr)) &&
  closedB P.ch P.L P.r P.q H Sbot && !decide (P.bot ∈ Sbot) &&
  H.all (fun x => Sx.any (fun p => decide (p.1 = x) && closedB P.ch P.L P.r P.q (H.erase x) p.2 &&
    P.O.any (fun o => !decide (o ∈ p.2))))

theorem certB_sound (P : Problem) (H tr Sbot : List Nat) (Sx : List (Nat × List Nat))
    (hc : certB P H tr Sbot Sx = true) : H.Nodup ∧ Minimal P H := by
  simp only [certB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, List.any_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨hn, hA⟩, htr⟩, hOtr⟩, hSb⟩, hbot⟩, hx⟩ := hc
  have hder := traceOk_sound P.ch P.L P.r P.q H tr [] (fun d hd => by simp at hd) htr
  have he : Explains P H :=
    ⟨hA, fun o ho => hder o (hOtr o ho), fun hb => hbot (closedB_sound _ _ _ _ H Sbot hSb _ hb)⟩
  refine ⟨hn, (minimal_iff_erase P H hn).mpr ⟨he, fun x hxm hex => ?_⟩⟩
  obtain ⟨p, _, ⟨hpx, hpc⟩, o, ho, hno⟩ := hx x hxm
  exact hno (closedB_sound _ _ _ _ (H.erase x) p.2 hpc o (hex.2.1 o ho))

/-- One-pass certificate on the cone, transferred to the whole log. -/
theorem certificate_fast (P : Problem) (T H : List Nat) (Lc : List Rec) (tr Sbot : List Nat)
    (Sx : List (Nat × List Nat))
    (hc : coneClosedB P.ch P.L P.r P.q T = true) (hL : coneOf P.ch P.L P.r T = Lc)
    (hO : P.O.all (fun o => decide (o ∈ T)) = true) (hb : decide (P.bot ∈ T) = true)
    (hm : certB { P with L := Lc } H tr Sbot Sx = true) : H.Nodup ∧ Minimal P H := by
  simp only [List.all_eq_true, decide_eq_true_eq] at hO hb
  have h := certB_sound { P with L := Lc } H tr Sbot Sx hm
  subst hL
  exact ⟨h.1, (minimal_cone P T hc hO hb H).mpr h.2⟩

/-! Growth of the log. -/

theorem derivesWith_grow (ch : Chain) (L M : List Rec) (r : Nat) (q : List Nat → Bool) (H : List Nat)
    (a : Nat) (h : DerivesWith ch L r q H a) : DerivesWith ch (L ++ M) r q H a :=
  Derives.mono (fun _ hx => hx) (fun ps x he => View.grow ch L M r q ps x he) a h

/-- A refutation never needs retracting: once `H` derives `bot`,
    it does so on every extension of the log. -/
theorem inconsistent_persists (ch : Chain) (L M : List Rec) (r : Nat) (q : List Nat → Bool)
    (H : List Nat) (bot : Nat) (h : DerivesWith ch L r q H bot) : DerivesWith ch (L ++ M) r q H bot :=
  derivesWith_grow ch L M r q H bot h

/-- An explanation stays one on an extension unless the extension
    derives `bot` from it. -/
theorem explains_persists (P : Problem) (M : List Rec) (H : List Nat) (he : Explains P H)
    (hc : ¬ DerivesWith P.ch (P.L ++ M) P.r P.q H P.bot) : Explains { P with L := P.L ++ M } H :=
  ⟨he.1, fun o ho => derivesWith_grow _ _ M _ _ H o (he.2.1 o ho), hc⟩

/-! Admission. -/

/-- Append the hypothesis records of `H` when it is verified and a
    minimal explanation; otherwise append nothing. -/
def admitLog (P : Problem) (c : Nat) (verified : Bool) (H : List Nat) : List Rec :=
  if verified && minimalB P c H then P.L ++ hyps P.r c H else P.L

theorem admit_prefix (P : Problem) (c : Nat) (v : Bool) (H : List Nat) :
    ∃ t, admitLog P c v H = P.L ++ t := by
  unfold admitLog
  split
  · exact ⟨_, rfl⟩
  · exact ⟨[], by simp⟩

theorem admit_monotone (P : Problem) (c : Nat) (v : Bool) (H : List Nat) (a : Nat)
    (h : derives (V P.ch P.L P.r P.q) a) : derives (V P.ch (admitLog P c v H) P.r P.q) a := by
  obtain ⟨t, ht⟩ := admit_prefix P c v H
  rw [ht]
  exact View.derives_grow P.ch P.L t P.r P.q a h

theorem admit_refuses (P : Problem) (c : Nat) (v : Bool) (H : List Nat)
    (h : v = false ∨ minimalB P c H = false) : admitLog P c v H = P.L := by
  unfold admitLog
  rcases h with h | h <;> simp [h]

theorem admit_explains (P : Problem) (c : Nat) (hq : P.q [c] = true) (H : List Nat)
    (hm : minimalB P c H = true) : ∀ o ∈ P.O, derives (V P.ch (admitLog P c true H) P.r P.q) o := by
  intro o ho
  have hmin := ((minimalB_iff P c hq H).mp hm).2
  unfold admitLog
  simp only [Bool.true_and, hm, if_true]
  exact (derivesWith_iff _ _ _ _ c hq H o).mpr (hmin.1.2.1 o ho)

theorem admit_consistent (P : Problem) (c : Nat) (hq : P.q [c] = true) (H : List Nat)
    (hm : minimalB P c H = true) : ¬ derives (V P.ch (admitLog P c true H) P.r P.q) P.bot := by
  have hmin := ((minimalB_iff P c hq H).mp hm).2
  unfold admitLog
  simp only [Bool.true_and, hm, if_true]
  rw [derivesWith_iff _ _ _ _ c hq H]
  exact hmin.1.2.2

/-! Ranking: Pareto front over (coverage up, cost down). -/

structure Score where
  cover : Nat
  cost : Nat
  deriving DecidableEq

def dom (a b : Score) : Bool :=
  decide (b.cover ≤ a.cover) && decide (a.cost ≤ b.cost) && (decide (b.cover < a.cover) || decide (a.cost < b.cost))

def front {α : Type} (xs : List (α × Score)) : List (α × Score) :=
  xs.filter (fun x => !(xs.any (fun y => dom y.2 x.2)))

theorem mem_front {α : Type} (xs : List (α × Score)) (x : α × Score) :
    x ∈ front xs ↔ x ∈ xs ∧ ∀ y ∈ xs, dom y.2 x.2 = false := by
  unfold front
  simp [List.mem_filter, List.any_eq_true]

/-- Lexicographic order: more coverage first, then less cost. -/
def lexLe (a b : Score) : Prop := a.cover < b.cover ∨ (a.cover = b.cover ∧ b.cost ≤ a.cost)

theorem dom_lex (a b : Score) (h : dom a b = true) : ¬ lexLe a b := by
  simp only [dom, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  unfold lexLe
  omega

theorem exists_lex_max {α : Type} : ∀ (xs : List (α × Score)), xs ≠ [] →
    ∃ x ∈ xs, ∀ y ∈ xs, lexLe y.2 x.2 := by
  intro xs
  induction xs with
  | nil => intro h; exact absurd rfl h
  | cons a t ih =>
    intro _
    by_cases ht : t = []
    · subst ht
      refine ⟨a, List.mem_cons_self, ?_⟩
      intro y hy
      simp at hy; subst hy
      unfold lexLe; omega
    · obtain ⟨m, hm, hmax⟩ := ih ht
      by_cases hla : lexLe a.2 m.2
      · refine ⟨m, List.mem_cons_of_mem a hm, ?_⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hla
        · exact hmax y hy
      · refine ⟨a, List.mem_cons_self, ?_⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · unfold lexLe; omega
        · have := hmax y hy
          unfold lexLe at hla this ⊢
          omega

theorem front_nonempty {α : Type} (xs : List (α × Score)) (h : xs ≠ []) : front xs ≠ [] := by
  obtain ⟨x, hx, hmax⟩ := exists_lex_max xs h
  have hxf : x ∈ front xs := by
    refine (mem_front xs x).mpr ⟨hx, fun y hy => ?_⟩
    cases hd : dom y.2 x.2
    · rfl
    · have hlex := hmax y hy
      have := dom_lex y.2 x.2 hd
      unfold lexLe at hlex this
      omega
  intro hn; rw [hn] at hxf; simp at hxf

end Abduce
end Canon

#print axioms Canon.Abduce.derivesWith_iff
#print axioms Canon.Abduce.mem_closWith
#print axioms Canon.Abduce.explainsB_iff
#print axioms Canon.Abduce.explains_congr
#print axioms Canon.Abduce.consistent_sub
#print axioms Canon.Abduce.minimal_iff_erase
#print axioms Canon.Abduce.minimalB_iff
#print axioms Canon.Abduce.mem_abduce
#print axioms Canon.Abduce.abduce_complete
#print axioms Canon.Abduce.cone_derivesWith
#print axioms Canon.Abduce.explains_cone
#print axioms Canon.Abduce.minimal_cone
#print axioms Canon.Abduce.certificate
#print axioms Canon.Abduce.certificate_lit
#print axioms Canon.Abduce.closedB_sound
#print axioms Canon.Abduce.traceOk_sound
#print axioms Canon.Abduce.certB_sound
#print axioms Canon.Abduce.certificate_fast
#print axioms Canon.Abduce.inconsistent_persists
#print axioms Canon.Abduce.explains_persists
#print axioms Canon.Abduce.admit_prefix
#print axioms Canon.Abduce.admit_monotone
#print axioms Canon.Abduce.admit_refuses
#print axioms Canon.Abduce.admit_explains
#print axioms Canon.Abduce.admit_consistent
#print axioms Canon.Abduce.mem_front
#print axioms Canon.Abduce.front_nonempty
