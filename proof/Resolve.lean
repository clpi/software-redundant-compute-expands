/-
  The resolution algorithm, and its Pareto optimality over a
  stated objective set.

  Input: the one record log, a resolution chain, a color test,
  a compute budget and a cost per level. Output: the finest
  admitted level the budget affords, with the hypergraph view
  at that level, or the explicit outcome UNMEASURED at symbol
  resolution. Admitted levels are level 0 (finest) through the
  symbol level; nothing coarser than the symbol level is ever
  returned as an analysis, so a budget that cannot afford the
  symbol level gets no silent coarse answer.

  Proved: the algorithm is total and structurally recursive
  (the gate rejects every non-terminating escape), a function
  of its inputs, invariant under re-ordering the log; its
  level is admitted and affordable; no strictly finer admitted
  level is affordable; it returns UNMEASURED exactly when the
  symbol level is unaffordable, under the premise that coarser
  levels cost no more; more budget never yields a coarser
  level; the chosen level is Pareto optimal over the objective
  pair (fineness, cost) within the affordable admitted levels;
  every derivation at the chosen level projects to every
  coarser affordable level.

  Premise-labeled: `Antitone cost` (coarser analysis costs no
  more), the fidelity of the cost model to real compute, and
  the fidelity of the chain's `up` maps to the containment of
  terms (the adapter obligation). Not claimed: cost
  minimality (cheaper coarser levels stay Pareto points of
  their own), and optimality over any objective outside the
  pair stated.
-/

import Canon

namespace Canon

/-- Scan levels `i, i+1, ..., i+n-1` for the first one whose
    cost the budget affords. -/
def scan (cost : Nat → Nat) (avail : Nat) : Nat → Nat → Option Nat
  | _, 0 => none
  | i, n + 1 => if cost i ≤ avail then some i else scan cost avail (i + 1) n

/-- The resolved level: the finest admitted level the budget
    affords. -/
def resolveLevel (ch : Chain) (cost : Nat → Nat) (avail : Nat) : Option Nat :=
  scan cost avail 0 (ch.sym + 1)

/-- The resolution algorithm: the level and the hypergraph
    view there, or `none`, read as UNMEASURED at symbol
    resolution. -/
def resolve (ch : Chain) (cost : Nat → Nat) (avail : Nat) (log : List Rec)
    (q : List Nat → Bool) : Option (Nat × Hypergraph Nat) :=
  (resolveLevel ch cost avail).map (fun r => (r, viewC ch log r q))

/-- Coarser analysis costs no more. -/
def Antitone (cost : Nat → Nat) : Prop := ∀ r s, r ≤ s → cost s ≤ cost r

namespace Resolve

theorem scan_some (cost : Nat → Nat) (avail : Nat) : ∀ n i r, scan cost avail i n = some r →
    i ≤ r ∧ r < i + n ∧ cost r ≤ avail ∧ ∀ s, i ≤ s → s < r → avail < cost s := by
  intro n
  induction n with
  | zero => intro i r h; simp [scan] at h
  | succ n ih =>
    intro i r h
    simp only [scan] at h
    by_cases hc : cost i ≤ avail
    · rw [if_pos hc] at h
      cases h
      exact ⟨Nat.le_refl _, by omega, hc, fun s h1 h2 => by omega⟩
    · rw [if_neg hc] at h
      obtain ⟨h1, h2, h3, h4⟩ := ih (i + 1) r h
      refine ⟨by omega, by omega, h3, ?_⟩
      intro s hs hsr
      by_cases hsi : s = i
      · subst hsi; omega
      · exact h4 s (by omega) hsr

theorem scan_none (cost : Nat → Nat) (avail : Nat) : ∀ n i, scan cost avail i n = none →
    ∀ s, i ≤ s → s < i + n → avail < cost s := by
  intro n
  induction n with
  | zero => intro i _ s h1 h2; omega
  | succ n ih =>
    intro i h s h1 h2
    simp only [scan] at h
    by_cases hc : cost i ≤ avail
    · rw [if_pos hc] at h; cases h
    · rw [if_neg hc] at h
      by_cases hsi : s = i
      · subst hsi; omega
      · exact ih (i + 1) h s (by omega) (by omega)

/-- The resolved level is admitted (at least symbolic) and
    affordable. -/
theorem feasible (ch : Chain) (cost : Nat → Nat) (avail r : Nat)
    (h : resolveLevel ch cost avail = some r) : r ≤ ch.sym ∧ cost r ≤ avail := by
  obtain ⟨_, h2, h3, _⟩ := scan_some cost avail _ 0 r h
  exact ⟨by omega, h3⟩

/-- No strictly finer level is affordable. -/
theorem finest (ch : Chain) (cost : Nat → Nat) (avail r : Nat)
    (h : resolveLevel ch cost avail = some r) : ∀ s, s < r → avail < cost s := by
  obtain ⟨_, _, _, h4⟩ := scan_some cost avail _ 0 r h
  exact fun s hs => h4 s (Nat.zero_le _) hs

/-- UNMEASURED exactly when the symbol level is unaffordable,
    under the antitone cost premise. -/
theorem unmeasured_iff (ch : Chain) (cost : Nat → Nat) (avail : Nat) (ha : Antitone cost) :
    resolveLevel ch cost avail = none ↔ avail < cost ch.sym := by
  constructor
  · intro h
    exact scan_none cost avail _ 0 h ch.sym (Nat.zero_le _) (by omega)
  · intro h
    cases hr : resolveLevel ch cost avail with
    | none => rfl
    | some r =>
      obtain ⟨hle, hc⟩ := feasible ch cost avail r hr
      have := ha r ch.sym hle
      omega

/-- More budget never yields a coarser level. -/
theorem budget_mono (ch : Chain) (cost : Nat → Nat) (a a' r : Nat) (hle : a ≤ a')
    (h : resolveLevel ch cost a = some r) :
    ∃ r', resolveLevel ch cost a' = some r' ∧ r' ≤ r := by
  obtain ⟨hr, hc⟩ := feasible ch cost a r h
  cases h' : resolveLevel ch cost a' with
  | none =>
    have := scan_none cost a' _ 0 h' r (Nat.zero_le _) (by omega)
    omega
  | some r' =>
    refine ⟨r', rfl, ?_⟩
    by_cases hlt : r < r'
    · have := finest ch cost a' r' h' r hlt; omega
    · omega

/-- Pareto optimality over (fineness, cost) within the
    affordable admitted levels: no affordable admitted level is
    at least as fine and at least as cheap with one of the two
    strict. -/
theorem pareto (ch : Chain) (cost : Nat → Nat) (avail r : Nat)
    (h : resolveLevel ch cost avail = some r) :
    ∀ s, s ≤ ch.sym → cost s ≤ avail →
      ¬ (s ≤ r ∧ cost s ≤ cost r ∧ (s < r ∨ cost s < cost r)) := by
  intro s _ hs ⟨h1, h2, h3⟩
  rcases h3 with h3 | h3
  · have := finest ch cost avail r h s h3; omega
  · have : s = r := by
      by_cases hlt : s < r
      · have := finest ch cost avail r h s hlt; omega
      · omega
    subst this; omega

/-- The algorithm is invariant under re-ordering the log. -/
theorem order (ch : Chain) (cost : Nat → Nat) (avail : Nat) {L L' : List Rec} (p : L.Perm L')
    (q : List Nat → Bool) : resolve ch cost avail L q = resolve ch cost avail L' q := by
  simp only [resolve]
  cases resolveLevel ch cost avail with
  | none => rfl
  | some r => simp [View.perm ch p r q]

/-- Every derivation at the resolved level projects to every
    coarser level: the coarse results are projections of the
    resolved one. -/
theorem retains (ch : Chain) (cost : Nat → Nat) (avail r : Nat) (log : List Rec)
    (q : List Nat → Bool) (_ : resolveLevel ch cost avail = some r) (k a : Nat)
    (hd : derives (viewC ch log r q) a) : derives (viewC ch log (r + k) q) (lift ch r k a) :=
  View.derives_proj ch log r k q a hd

/-- Appending observations never changes the resolved level,
    and only adds to its view. -/
theorem append (ch : Chain) (cost : Nat → Nat) (avail : Nat) (L M : List Rec) (q : List Nat → Bool)
    (r : Nat) (h : resolveLevel ch cost avail = some r) (a : Nat)
    (hd : derives (viewC ch L r q) a) : derives (viewC ch (L ++ M) r q) a ∧
      (resolve ch cost avail (L ++ M) q).map Prod.fst = some r := by
  refine ⟨View.derives_grow ch L M r q a hd, ?_⟩
  simp [resolve, h]

end Resolve

namespace Control

/-- Control budget: with the symbol level unaffordable the
    algorithm answers UNMEASURED, never a coarser view. -/
theorem budget :
    resolveLevel ⟨fun _ c => c, 2, 3, by decide⟩ (fun r => 10 - r) 7 = none
      ∧ resolveLevel ⟨fun _ c => c, 2, 3, by decide⟩ (fun r => 10 - r) 8 = some 2
      ∧ resolveLevel ⟨fun _ c => c, 2, 3, by decide⟩ (fun r => 10 - r) 100 = some 0 := by
  refine ⟨by decide, by decide, by decide⟩

/-- Control antitone: without the antitone premise a finer
    level can be affordable while the symbol level is not, so
    the UNMEASURED characterization needs it. -/
theorem antitone :
    resolveLevel ⟨fun _ c => c, 1, 1, by decide⟩ (fun r => if r = 0 then 1 else 9) 5 = some 0 := by
  decide

end Control

#print axioms Resolve.scan_some
#print axioms Resolve.scan_none
#print axioms Resolve.feasible
#print axioms Resolve.finest
#print axioms Resolve.unmeasured_iff
#print axioms Resolve.budget_mono
#print axioms Resolve.pareto
#print axioms Resolve.order
#print axioms Resolve.retains
#print axioms Resolve.append
#print axioms Control.budget
#print axioms Control.antitone

end Canon
