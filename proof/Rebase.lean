/-
  Redundant compute re-based onto the canonical hypergraph.

  On the one record log, terms are identified at each level,
  so an atom used by many hyperedges is shared, never
  redundant. Redundant compute at level `r` is redundant
  support: a record whose projected implication (premises and
  head at level `r`) another record already supports. Its
  count is the list measure of the projected implications
  under an injective encoding (the encoding is an adapter
  obligation, like receipt identities; the count does not
  depend on which injective encoding is used).

  Proved: the count is monotone under appending to the log,
  invariant under re-ordering it, exact over joins (the parts
  plus the implications they share), positive exactly when a
  parallel support witness exists, independent of the
  injective encoding, and on records observed at a level it
  never decreases when read at a coarser level (merging
  identities only adds parallel support), so the resolved
  level gives the least inflated count among the affordable
  levels. Weighted by reweightable color parameters, the same
  holds for every weighting.

  The bridge to the landed list form: reading a list-form
  graph as a log (nodes as admissions, hyperedges as records)
  makes its node half the canonical count of parallel
  admissions exactly, while its incidence half bounds the
  canonical count of parallel hyperedges from above and can be
  positive where the canonical count is zero (control): the
  incidence half measures sharing, not redundant compute.
-/

import Units
import Resolve

namespace Canon

open Redundant

/-- The implications projected to level `r`, in log order. -/
def impls (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool) : List (List Nat × Nat) :=
  (L.filter (fun e => decide (e.level ≤ r) && q e.colors)).map (proj ch r)

/-- Redundant support at level `r`: parallel records. -/
def parallel (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool)
    (enc : List Nat × Nat → Nat) : Nat :=
  red ((impls ch L r q).map enc)

/-- Weighted redundant support, under reweightable
    parameters on encoded implications. -/
def parallelW (w : Nat → Nat) (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool)
    (enc : List Nat × Nat → Nat) : Nat :=
  wred w ((impls ch L r q).map enc)

/-- An implication projected up `k` levels. -/
def liftPair (ch : Chain) (r k : Nat) (x : List Nat × Nat) : List Nat × Nat :=
  (x.1.map (lift ch r k), lift ch r k x.2)

namespace Rebase

theorem impls_append (ch : Chain) (L M : List Rec) (r : Nat) (q : List Nat → Bool) :
    impls ch (L ++ M) r q = impls ch L r q ++ impls ch M r q := by
  simp [impls, List.filter_append]

theorem grow (ch : Chain) (L M : List Rec) (r : Nat) (q : List Nat → Bool) (enc : List Nat × Nat → Nat) :
    parallel ch L r q enc ≤ parallel ch (L ++ M) r q enc := by
  simp only [parallel, impls_append, List.map_append]
  exact Red.left _ _

theorem order (ch : Chain) {L L' : List Rec} (p : L.Perm L') (r : Nat) (q : List Nat → Bool)
    (enc : List Nat × Nat → Nat) : parallel ch L r q enc = parallel ch L' r q enc := by
  simp only [parallel, impls]
  exact Red.perm (((p.filter _).map _).map _)

theorem join (ch : Chain) (L M : List Rec) (r : Nat) (q : List Nat → Bool) (enc : List Nat × Nat → Nat) :
    parallel ch (L ++ M) r q enc
      = parallel ch L r q enc + parallel ch M r q enc
        + shared ((impls ch L r q).map enc) ((impls ch M r q).map enc) := by
  simp only [parallel, impls_append, List.map_append]
  exact Exact.join _ _

theorem witness (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool) (enc : List Nat × Nat → Nat) :
    1 ≤ parallel ch L r q enc ↔ Repeat ((impls ch L r q).map enc) := Red.witness _

/-- The count does not depend on the injective encoding. -/
theorem enc_indep (ch : Chain) (L : List Rec) (r : Nat) (q : List Nat → Bool)
    (enc enc' : List Nat × Nat → Nat)
    (h : ∀ x ∈ impls ch L r q, ∀ y ∈ impls ch L r q, enc x = enc y → x = y)
    (h' : ∀ x ∈ impls ch L r q, ∀ y ∈ impls ch L r q, enc' x = enc' y → x = y) :
    parallel ch L r q enc = parallel ch L r q enc' := by
  simp only [parallel]
  exact Nat.le_antisymm
    (Red.key_le enc enc' _ (fun a ha b hb hab => by rw [h a ha b hb hab]))
    (Red.key_le enc' enc _ (fun a ha b hb hab => by rw [h' a ha b hb hab]))

/-- On records observed at level `r` or finer, the coarser
    implications are the projections of the finer ones. -/
theorem impls_lift (ch : Chain) (L : List Rec) (r k : Nat) (q : List Nat → Bool)
    (hall : ∀ e ∈ L, e.level ≤ r) :
    impls ch L (r + k) q = (impls ch L r q).map (liftPair ch r k) := by
  simp only [impls, List.map_map]
  have hf : L.filter (fun e => decide (e.level ≤ r + k) && q e.colors)
      = L.filter (fun e => decide (e.level ≤ r) && q e.colors) :=
    List.filter_congr (fun e he => by
      have h1 := hall e he
      simp [show e.level ≤ r + k by omega, h1])
  rw [hf]
  apply List.map_congr_left
  intro e he
  have hl := hall e (List.mem_filter.mp he).1
  simp only [Function.comp, liftPair]
  rw [View.proj_lift ch e r k hl]

/-- Reading at a coarser level never lowers redundant support
    on records observed at the finer level. -/
theorem coarser (ch : Chain) (L : List Rec) (r k : Nat) (q : List Nat → Bool)
    (enc : List Nat × Nat → Nat) (hall : ∀ e ∈ L, e.level ≤ r)
    (hinj : ∀ x ∈ impls ch L r q, ∀ y ∈ impls ch L r q, enc x = enc y → x = y) :
    parallel ch L r q enc ≤ parallel ch L (r + k) q enc := by
  simp only [parallel]
  rw [impls_lift ch L r k q hall, List.map_map]
  exact Red.key_le enc (enc ∘ liftPair ch r k) _
    (fun a ha b hb hab => by simp [hinj a ha b hb hab])

/-- The resolved level gives the least inflated count among
    the affordable admitted levels, on records observed at it. -/
theorem resolved_least (ch : Chain) (cost : Nat → Nat) (avail r : Nat)
    (hr : resolveLevel ch cost avail = some r) (L : List Rec) (q : List Nat → Bool)
    (enc : List Nat × Nat → Nat) (hall : ∀ e ∈ L, e.level ≤ r)
    (hinj : ∀ x ∈ impls ch L r q, ∀ y ∈ impls ch L r q, enc x = enc y → x = y)
    (s : Nat) (hs : cost s ≤ avail) : parallel ch L r q enc ≤ parallel ch L s q enc := by
  have hrs : r ≤ s := by
    by_cases h : s < r
    · have := Resolve.finest ch cost avail r hr s h; omega
    · omega
  obtain ⟨k, rfl⟩ : ∃ k, s = r + k := ⟨s - r, by omega⟩
  exact coarser ch L r k q enc hall hinj

/-- Weighted, for every weighting: monotone and order
    invariant, additive in the weights. -/
theorem weighted (w v : Nat → Nat) (ch : Chain) (L M : List Rec) (r : Nat) (q : List Nat → Bool)
    (enc : List Nat × Nat → Nat) :
    parallelW w ch L r q enc ≤ parallelW w ch (L ++ M) r q enc
      ∧ parallelW (fun x => w x + v x) ch L r q enc
          = parallelW w ch L r q enc + parallelW v ch L r q enc := by
  constructor
  · simp only [parallelW, impls_append, List.map_append]
    exact Color.left w _ _
  · exact Color.add w v [] _

theorem weighted_order (w : Nat → Nat) (ch : Chain) {L L' : List Rec} (p : L.Perm L') (r : Nat)
    (q : List Nat → Bool) (enc : List Nat × Nat → Nat) :
    parallelW w ch L r q enc = parallelW w ch L' r q enc := by
  simp only [parallelW, impls, wred]
  exact Color.perm w (((p.filter _).map _).map _) []

end Rebase

/-- The identity chain: one level, terms are themselves. -/
def idChain : Chain := ⟨fun _ c => c, 0, 0, Nat.le_refl 0⟩

/-- A list-form graph read as a log: nodes as admissions,
    hyperedges as records. -/
def toLog (g : Graph) : List Rec :=
  g.nodes.map (fun n => ⟨0, 0, [], [], n⟩) ++ g.edges.map (fun e => ⟨0, 0, [], e.1, e.2⟩)

namespace Bridge

theorem lift0 (ch : Chain) (r c : Nat) : lift ch r 0 c = c := rfl

theorem impls_toLog (g : Graph) :
    impls idChain (toLog g) 0 (fun _ => true) = g.nodes.map (fun n => ([], n)) ++ g.edges := by
  simp only [impls, toLog, List.filter_append, List.map_append]
  congr 1
  · induction g.nodes with
    | nil => rfl
    | cons n ns ih => simp [List.filter_cons, proj, lift] at ih ⊢; exact ih
  · induction g.edges with
    | nil => rfl
    | cons e es ih =>
      simp [List.filter_cons, proj, lift] at ih ⊢
      first | exact ih | exact ⟨rfl, ih⟩

/-- The node half is the canonical count of parallel
    admissions. -/
theorem nodes (g : Graph) (enc : List Nat × Nat → Nat)
    (hinj : ∀ x y, enc x = enc y → x = y) :
    red ((g.nodes.map (fun n => (([] : List Nat), n))).map enc) = red g.nodes := by
  rw [List.map_map]
  apply Red.relabel_inj
  intro a _ b _ hab
  have := hinj _ _ hab
  simpa using this

/-- The canonical count of parallel hyperedges never exceeds
    the incidence half. -/
theorem edges_le (g : Graph) (enc : List Nat × Nat → Nat)
    (hinj : ∀ x y, enc x = enc y → x = y) :
    red (g.edges.map enc) ≤ red (incidence g) :=
  Sig.le_incidence enc g (fun e _ f _ h => by rw [hinj e f h])

/-- The canonical count over the whole log is at least the two
    halves. -/
theorem whole (g : Graph) (enc : List Nat × Nat → Nat) :
    red ((g.nodes.map (fun n => (([] : List Nat), n))).map enc) + red (g.edges.map enc)
      ≤ parallel idChain (toLog g) 0 (fun _ => true) enc := by
  simp only [parallel, impls_toLog, List.map_append]
  exact Red.sum _ _

end Bridge

namespace Control

/-- Control sharing: two hyperedges sharing a conclusion carry
    incidence redundancy one in the list form, while no record
    supports a parallel implication; on the canonical graph the
    shared atom is sharing, not redundant compute. -/
theorem sharing :
    red (incidence ⟨[], [([1], 3), ([2], 3)]⟩) = 1
      ∧ parallel idChain (toLog ⟨[], [([1], 3), ([2], 3)]⟩) 0 (fun _ => true)
          (fun x => x.1.sum * 1000 + x.2) = 0 := by
  constructor <;> decide

/-- Control parallel: two receipts for the same implication
    are redundant support. -/
theorem parallel_pos :
    parallel idChain [⟨10, 0, [], [0, 1], 2⟩, ⟨11, 0, [], [0, 1], 2⟩] 0 (fun _ => true)
      (fun x => x.1.sum * 1000 + x.2) = 1 := by
  decide

end Control

#print axioms Rebase.impls_append
#print axioms Rebase.grow
#print axioms Rebase.order
#print axioms Rebase.join
#print axioms Rebase.witness
#print axioms Rebase.enc_indep
#print axioms Rebase.impls_lift
#print axioms Rebase.coarser
#print axioms Rebase.resolved_least
#print axioms Rebase.weighted
#print axioms Rebase.weighted_order
#print axioms Bridge.impls_toLog
#print axioms Bridge.nodes
#print axioms Bridge.edges_le
#print axioms Bridge.whole
#print axioms Control.sharing
#print axioms Control.parallel_pos

end Canon
