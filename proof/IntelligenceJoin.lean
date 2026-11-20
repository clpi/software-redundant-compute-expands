import Lean
import Canon
import ClosureWorklist

namespace Canon.IntelligenceJoin

/-- Identity includes the originating source and version. Conflicting payloads
    are retained as distinct events, not overwritten by arrival order. -/
structure Event where
  source : Nat
  seq : Nat
  payload : Rec
  deriving DecidableEq

abbrev Events := Event → Prop

def join (a b : Events) : Events := fun e => a e ∨ b e

def Includes (a b : Events) : Prop := ∀ e, a e → b e

theorem join_assoc (a b c : Events) : join (join a b) c = join a (join b c) := by
  funext e
  exact propext or_assoc

theorem join_comm (a b : Events) : join a b = join b a := by
  funext e
  exact propext or_comm

theorem join_idem (a : Events) : join a a = a := by
  funext e
  exact or_self _

/-- Once every committed event belonging to a finite named cutoff has been
    delivered and no foreign event is included, either replica has that set.
    This is a convergence statement, not a liveness proof for the transport. -/
theorem convergence_at_delivered_cut (committed a b : Events)
    (ac : Includes a committed) (bc : Includes b committed)
    (ca : Includes committed a) (cb : Includes committed b) : a = b := by
  funext e
  exact propext ⟨fun h => cb e (ac e h), fun h => ca e (bc e h)⟩

def sequenceSeen (received : List Event) (source seq : Nat) : Bool :=
  received.any (fun e => (e.source == source) && (e.seq == seq))

/-- The prefix length must be received from a trusted checkpoint. This
    checks missing coordinates, not the authenticity of the payload at one. -/
def missingPrefix (received : List Event) (source checkpoint : Nat) : List Nat :=
  (List.range checkpoint).filter (fun seq => !(sequenceSeen received source seq))

theorem missing_prefix_exact (received : List Event) (source checkpoint seq : Nat) :
    seq ∈ missingPrefix received source checkpoint ↔
    seq < checkpoint ∧ ¬ ∃ e ∈ received, e.source = source ∧ e.seq = seq := by
  simp [missingPrefix, sequenceSeen, Bool.eq_false_iff]

theorem no_missing_prefix_iff (received : List Event) (source checkpoint : Nat) :
    missingPrefix received source checkpoint = [] ↔
    ∀ seq < checkpoint, ∃ e ∈ received, e.source = source ∧ e.seq = seq := by
  constructor
  · intro h seq hs
    by_cases he : ∃ e ∈ received, e.source = source ∧ e.seq = seq
    · exact he
    · have hh := (missing_prefix_exact received source checkpoint seq).mpr ⟨hs, he⟩
      rw [h] at hh
      contradiction
  · intro h
    cases he : missingPrefix received source checkpoint with
    | nil => rfl
    | cons seq tail =>
      have hm : seq ∈ missingPrefix received source checkpoint := by rw [he]; simp
      obtain ⟨hs, hn⟩ := (missing_prefix_exact received source checkpoint seq).mp hm
      exact False.elim (hn (h seq hs))

/-- Two cutoff hypotheses with the same input to a detector disagree on omission.
    A detector inspecting only the received observations cannot always tell them apart. -/
theorem no_uncheckpointed_detector (detect : List Event → Bool) :
    ¬ (∀ received checkpoint, detect received = true ↔ missingPrefix received 0 checkpoint ≠ []) := by
  intro h
  have h0 := h [] 0
  have h1 := h [] 1
  have h00 : missingPrefix [] 0 0 = [] := by decide
  have h11 : missingPrefix [] 0 1 ≠ [] := by decide
  exact (h0.mp (h1.mpr h11)) h00

def Represents (rs : List Event) (events : Events) : Prop :=
  ∀ e, e ∈ rs ↔ events e

theorem append_represents_union {xs ys : List Event} {a b : Events}
    (hx : Represents xs a) (hy : Represents ys b) : Represents (xs ++ ys) (join a b) := by
  intro e
  simp [join, hx e, hy e]

/-- All views here use the one canonical record projection, at a precision
    and color filter selected before comparison. -/
def projected (ch : Chain) (rs : List Event) (r : Nat) (q : List Nat → Bool) : Hypergraph Nat :=
  viewC ch (rs.map Event.payload) r q

theorem projection_same_delivered_set (ch : Chain) (r : Nat) (q : List Nat → Bool)
    {xs ys : List Event} {a : Events} (hx : Represents xs a) (hy : Represents ys a) :
    projected ch xs r q = projected ch ys r q := by
  unfold projected viewC
  congr 1
  funext ps w
  apply propext
  simp only [List.mem_map]
  constructor <;> rintro ⟨e, ⟨z, hz, hze⟩, hlev, hc, hp⟩
  · exact ⟨e, ⟨z, (hy z).mpr ((hx z).mp hz), hze⟩, hlev, hc, hp⟩
  · exact ⟨e, ⟨z, (hx z).mpr ((hy z).mp hz), hze⟩, hlev, hc, hp⟩

def reconstruct (ch : Chain) (rs : List Event) (r : Nat) (q : List Nat → Bool) : List Nat :=
  ClosureWorklist.closure (ClosureWorklist.records ch (rs.map Event.payload) r q)

theorem reconstruct_exact (ch : Chain) (rs : List Event) (r : Nat) (q : List Nat → Bool) (w : Nat) :
    w ∈ reconstruct ch rs r q ↔ derives (projected ch rs r q) w :=
  ClosureWorklist.canonical_exact ch (rs.map Event.payload) r q w

theorem reconstruction_at_join (ch : Chain) (r : Nat) (q : List Nat → Bool)
    {xs ys zs : List Event} {a b : Events} (hx : Represents xs a) (hy : Represents ys b)
    (hz : Represents zs (join a b)) (w : Nat) :
    w ∈ reconstruct ch zs r q ↔ derives (projected ch (xs ++ ys) r q) w := by
  rw [reconstruct_exact, projection_same_delivered_set ch r q hz (append_represents_union hx hy)]

#print axioms join_assoc
#print axioms join_comm
#print axioms join_idem
#print axioms convergence_at_delivered_cut
#print axioms missing_prefix_exact
#print axioms no_missing_prefix_iff
#print axioms no_uncheckpointed_detector
#print axioms append_represents_union
#print axioms projection_same_delivered_set
#print axioms reconstruct_exact
#print axioms reconstruction_at_join

end Canon.IntelligenceJoin
