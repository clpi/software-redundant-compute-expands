/-
  Exact undo of a closure append by replaying its journal backwards
  (examples/semantic-axes, engines.py: Counter.undo_last and
  Watch.undo_last).

  1. `undo_run`: for any journal whose every entry's recorded inverse
     holds at the state the entry was applied to (`Valid`), undoing the
     journal last-entry-first restores the state before the append.
  2. One lemma per entry kind the engines log, over a model of their
     state, giving exactly the condition `Valid` needs:
       r    push a rule slot              (pop; the slot's counter was 0)
       w    push onto a waiter list       (pop)
       wp   empty a waiter list           (restore the recorded list)
       c    decrement a counter           (increment)
       pos  move a watch position         (restore the recorded position)
       d    derive a fresh term           (un-derive; term was underived)
       wit  set a fresh witness           (clear; no witness was set)
  What is proved is the journal discipline and the inverse of each entry.
  That the engines log exactly these entries, with recorded values read
  before the change and freshness for `d` and `wit`, is checked by test
  (reversibility axis: undo exact at every tested append), not proved.
-/
namespace Journal

/-- One journal entry: the change and its recorded inverse. -/
structure Step (S : Type) where
  fwd : S → S
  bwd : S → S

def run {S : Type} : List (Step S) → S → S
  | [], s => s
  | e :: es, s => run es (e.fwd s)

/-- Undo applies the inverses last entry first. -/
def undo {S : Type} : List (Step S) → S → S
  | [], s => s
  | e :: es, s => e.bwd (undo es s)

/-- Every entry's inverse holds at the state the entry was applied to. -/
def Valid {S : Type} : List (Step S) → S → Prop
  | [], _ => True
  | e :: es, s => e.bwd (e.fwd s) = s ∧ Valid es (e.fwd s)

theorem undo_run {S : Type} : ∀ (es : List (Step S)) (s : S), Valid es s → undo es (run es s) = s
  | [], _, _ => rfl
  | e :: es, s, ⟨h1, h2⟩ => by
    simp only [run, undo]
    rw [undo_run es (e.fwd s) h2, h1]

/-! ## The engines' state and entries -/

def upd {α β : Type} [DecidableEq α] (f : α → β) (x : α) (v : β) : α → β :=
  fun y => if y = x then v else f y

theorem upd_same {α β : Type} [DecidableEq α] (f : α → β) (x : α) (v : β) : upd f x v x = v := by
  simp [upd]

theorem upd_upd_self {α β : Type} [DecidableEq α] (f : α → β) (x : α) (v : β) :
    upd (upd f x v) x (f x) = f := by
  funext y; by_cases h : y = x <;> simp [upd, h]

/-- Model of a Counter/Watch state: derived terms, rule heads and record
    indexes, per-rule counters, waiter (or watch) lists, watch positions
    and witnesses. -/
structure St where
  D : Nat → Bool
  heads : List Nat
  ridx : List Nat
  count : Nat → Int
  waiters : Nat → List Nat
  pos : Nat → Nat
  wit : Nat → Option Nat

/-- r: push a rule slot with head `h`, record `k`, counter `m`. -/
def pushRule (h k : Nat) (m : Int) : Step St where
  fwd s := { s with heads := s.heads ++ [h], ridx := s.ridx ++ [k], count := upd s.count s.heads.length m }
  bwd s := { s with heads := s.heads.dropLast, ridx := s.ridx.dropLast, count := upd s.count (s.heads.length - 1) 0 }

theorem pushRule_inv (h k : Nat) (m : Int) (s : St) (hc : s.count s.heads.length = 0) :
    (pushRule h k m).bwd ((pushRule h k m).fwd s) = s := by
  cases s with
  | mk D heads ridx count waiters pos wit =>
    simp only [pushRule, List.dropLast_concat, List.length_append, List.length_cons, List.length_nil,
      Nat.add_sub_cancel]
    simp only at hc
    rw [← hc, upd_upd_self]

/-- w: push rule `i` onto the waiter list of term `p`. -/
def pushWaiter (p i : Nat) : Step St where
  fwd s := { s with waiters := upd s.waiters p (s.waiters p ++ [i]) }
  bwd s := { s with waiters := upd s.waiters p (s.waiters p).dropLast }

theorem pushWaiter_inv (p i : Nat) (s : St) : (pushWaiter p i).bwd ((pushWaiter p i).fwd s) = s := by
  cases s with
  | mk D heads ridx count waiters pos wit =>
    simp only [pushWaiter, upd_same, List.dropLast_concat]
    rw [upd_upd_self]

/-- wp: empty the waiter list of `t`, logging the list `ws` it held. -/
def popWaiters (t : Nat) (ws : List Nat) : Step St where
  fwd s := { s with waiters := upd s.waiters t [] }
  bwd s := { s with waiters := upd s.waiters t ws }

theorem popWaiters_inv (t : Nat) (s : St) (ws : List Nat) (hw : ws = s.waiters t) :
    (popWaiters t ws).bwd ((popWaiters t ws).fwd s) = s := by
  cases s with
  | mk D heads ridx count waiters pos wit =>
    simp only at hw
    simp only [popWaiters]
    rw [hw, upd_upd_self]

/-- c: decrement rule `j`'s counter. -/
def dec (j : Nat) : Step St where
  fwd s := { s with count := upd s.count j (s.count j - 1) }
  bwd s := { s with count := upd s.count j (s.count j + 1) }

theorem dec_inv (j : Nat) (s : St) : (dec j).bwd ((dec j).fwd s) = s := by
  cases s with
  | mk D heads ridx count waiters pos wit =>
    simp only [dec, upd_same, Int.sub_add_cancel]
    rw [upd_upd_self]

/-- pos: move rule `j`'s watch position to `v`, logging the old one `old`. -/
def movePos (j v old : Nat) : Step St where
  fwd s := { s with pos := upd s.pos j v }
  bwd s := { s with pos := upd s.pos j old }

theorem movePos_inv (j v old : Nat) (s : St) (ho : old = s.pos j) :
    (movePos j v old).bwd ((movePos j v old).fwd s) = s := by
  cases s with
  | mk D heads ridx count waiters pos wit =>
    simp only at ho
    simp only [movePos]
    rw [ho, upd_upd_self]

/-- d: derive term `g`. -/
def derive (g : Nat) : Step St where
  fwd s := { s with D := upd s.D g true }
  bwd s := { s with D := upd s.D g false }

theorem derive_inv (g : Nat) (s : St) (hf : s.D g = false) : (derive g).bwd ((derive g).fwd s) = s := by
  cases s with
  | mk D heads ridx count waiters pos wit =>
    simp only at hf
    simp only [derive]
    have : upd (upd D g true) g false = D := by rw [← hf]; exact upd_upd_self D g true
    rw [this]

/-- wit: record witness `k` for term `g`. -/
def setWit (g k : Nat) : Step St where
  fwd s := { s with wit := upd s.wit g (some k) }
  bwd s := { s with wit := upd s.wit g none }

theorem setWit_inv (g k : Nat) (s : St) (hf : s.wit g = none) : (setWit g k).bwd ((setWit g k).fwd s) = s := by
  cases s with
  | mk D heads ridx count waiters pos wit =>
    simp only at hf
    simp only [setWit]
    have : upd (upd wit g (some k)) g none = wit := by rw [← hf]; exact upd_upd_self wit g (some k)
    rw [this]

/-- An append that skips an unadmitted record logs a no-op. -/
def noop : Step St where
  fwd s := s
  bwd s := s

theorem noop_inv (s : St) : noop.bwd (noop.fwd s) = s := rfl

/-- A concrete journal shape: register a rule with one missing premise,
    later derive that premise, wake the rule and fire it. Undo restores
    the state exactly, from the entry lemmas alone. -/
theorem example_append (s : St) (p h k i : Nat) (ws : List Nat)
    (hc : s.count s.heads.length = 0)
    (hw : ws = ((pushRule h k 1).fwd ((pushWaiter p i).fwd s)).waiters p)
    (hp : s.D p = false) (hh : h ≠ p) (hhD : s.D h = false) (hwit : s.wit p = none) :
    let es := [pushWaiter p i, pushRule h k 1, popWaiters p ws, dec i, derive p, setWit p k, derive h]
    undo es (run es s) = s := by
  intro es
  apply undo_run
  refine ⟨pushWaiter_inv p i s, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · apply pushRule_inv; cases s; simpa [pushWaiter] using hc
  · exact popWaiters_inv p _ ws hw
  · exact dec_inv i _
  · apply derive_inv; cases s; simpa [pushWaiter, pushRule, popWaiters, dec] using hp
  · apply setWit_inv; cases s; simpa [pushWaiter, pushRule, popWaiters, dec, derive] using hwit
  · apply derive_inv; cases s; simp only at hhD; simp [pushWaiter, pushRule, popWaiters, dec, derive, setWit, upd]; exact ⟨hh, hhD⟩

end Journal

#print axioms Journal.undo_run
#print axioms Journal.pushRule_inv
#print axioms Journal.pushWaiter_inv
#print axioms Journal.popWaiters_inv
#print axioms Journal.dec_inv
#print axioms Journal.movePos_inv
#print axioms Journal.derive_inv
#print axioms Journal.setWit_inv
#print axioms Journal.example_append
