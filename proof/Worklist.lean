/-
  Counter-based worklist closure on the canonical hypergraph.

  Scope. This is a derived-closure optimization: it computes
  the same derivable set as `Closure.clos` for the view
  `viewC ch L r q`, with less work. It is not the canonical
  behavioral hypergraph itself, and not the action Pareto
  search. The algorithm is the classic counter-and-watch-list
  forward chaining of Dowling and Gallier (1984, linear-time
  Horn satisfiability), also the core of semi-naive Datalog
  evaluation. What is new here is only that it is proved
  against the exact `viewC` semantics, incrementally, at every
  append prefix of the one record log.

  Algorithm. Records are appended one at a time. A record is
  admitted exactly when `viewC` would keep it: level at most
  `r` and the color test `q` passes (`admits`). Records that
  fail either test (finer views, disqualified or demanded
  colors, whatever `q` rejects) never enter the rule table,
  the counts or the waiter index. For an admitted record the
  premises are the projections to level `r`, deduplicated
  (`prem`): two raw premises that are the same class at level
  `r`, or the same term written twice, count once. The state
  keeps, per admitted rule, the number of distinct premises not
  yet processed (`cnt`), and per term the rules waiting on it
  (`wait`). Admission seeds: a rule with no missing premise
  pushes its head at once; otherwise it is registered under
  each missing premise. Draining pops a term, visits only its
  waiters, decrements their counts, and pushes the head of
  every rule whose count reaches zero. A term is pushed only if
  it is not already derived, so each term enters the queue
  once.

  Semantics made explicit (not assumed):
  * premise identity is equality of level-`r` classes, the
    same identity `viewC` uses (`proj`);
  * duplicate premises count once (`prem_nodup`, `mem_prem`),
    and firing on "count reaches zero" is the same condition
    as `viewC`'s "every premise derived" (`fire`, `complete`);
  * filtered records are exactly the records `viewC` drops
    (`admits`, `rules`), so they never fire even when their
    premises are derived (`Control.filtered_color`,
    `Control.filtered_level`).

  Proved, with every premise listed explicitly:
  * `mem_run`: after any log `L` the derived set is exactly
    derivability in `viewC ch L r q` (sound and complete);
  * `run_eq_clos`: it has the same members as the naive
    closure `Closure.clos`;
  * `mem_prefix`: at every append prefix of a log;
  * `mem_continue`: continuing from the stored state of `L`
    over appended records `M` (no recomputation, rules
    incomplete before the append fire through their stored
    counts) gives exactly derivability in `L ++ M`;
  * `drain_empty`: the queue empties within the fuel bound
    `nu`, which is at most twice the number of admitted rules
    (finite term bound: every derived term is the head of an
    admitted rule);
  * `pops_eq`, `nodup_run`: every derived term is dequeued
    exactly once and derived once;
  * `visits_le`: total waiter visits never exceed the total
    number of distinct premises of admitted records, whatever
    the append order.
-/
import Closure

namespace Canon
namespace Worklist
open Closure

section Defs
variable (ch : Chain) (r : Nat) (q : List Nat → Bool)

/-- Admission: exactly the record filter of `viewC`. -/
def admits (e : Rec) : Bool := decide (e.level ≤ r) && q e.colors

/-- Distinct premises of a record at level `r`. -/
def prem (e : Rec) : List Nat := (proj ch r e).1.foldl ins []

/-- Head of a record at level `r`. -/
def hd (e : Rec) : Nat := (proj ch r e).2

end Defs

/-- Worklist state. `rules` are the admitted records in
    admission order; a rule is named by its index. The three
    last fields are work counters, not used by the algorithm. -/
structure St where
  rules : List Rec
  cnt : Nat → Nat
  wait : Nat → List Nat
  D : List Nat
  Q : List Nat
  scans : Nat
  visits : Nat
  pops : Nat

def St.init : St := ⟨[], fun _ => 0, fun _ => [], [], [], 0, 0, 0⟩

/-- Not yet processed: not derived, or derived and still queued. -/
def nd (s : St) (x : Nat) : Bool := !decide (x ∈ s.D) || decide (x ∈ s.Q)

section Alg
variable (ch : Chain) (r : Nat) (q : List Nat → Bool)

/-- Derive a term: enqueue it once, only if new. -/
def push (s : St) (a : Nat) : St :=
  if a ∈ s.D then s else { s with D := a :: s.D, Q := a :: s.Q }

/-- Visit one waiter: decrement its count, fire at zero. -/
def visit (s : St) (i : Nat) : St :=
  let s' : St := { s with
                          cnt := fun j => if j = i then s.cnt i - 1 else s.cnt j,
                          visits := s.visits + 1 }
  match s.rules[i]? with
  | some e => if s.cnt i - 1 = 0 then push s' (hd ch r e) else s'
  | none => s'

/-- Pop one term and visit only its waiters. -/
def pop (s : St) : St :=
  match s.Q with
  | [] => s
  | t :: rest => (s.wait t).foldl (visit ch r) { s with Q := rest, pops := s.pops + 1 }

def drain : Nat → St → St
  | 0, s => s
  | n + 1, s => if s.Q = [] then s else drain n (pop ch r s)

/-- Admit one record: count its missing distinct premises,
    register it under each, and fire it at once if none is
    missing. Filtered records change nothing. -/
def enter (s : St) (e : Rec) : St :=
  if admits r q e then
    let i := s.rules.length
    let miss := (prem ch r e).filter (nd s)
    let s' : St := { s with
                           rules := s.rules ++ [e],
                           cnt := fun j => if j = i then miss.length else s.cnt j,
                           wait := fun t => if t ∈ miss then s.wait t ++ [i] else s.wait t,
                           scans := s.scans + (prem ch r e).length }
    if miss = [] then push s' (hd ch r e) else s'
  else s

/-- Fuel bound: twice the admitted rules, less what has been
    derived and dequeued. -/
def nu (s : St) : Nat := 2 * s.rules.length - (s.pops + s.D.length)

/-- Append one record and drain. -/
def appendRec (s : St) (e : Rec) : St :=
  let s' := enter ch r q s e
  drain ch r (nu s') s'

/-- The state after appending a whole log, record by record. -/
def run (L : List Rec) : St := L.foldl (appendRec ch r q) St.init

end Alg

/-! ## Small list facts -/

theorem mem_prem (ch : Chain) (r : Nat) (e : Rec) (x : Nat) :
    x ∈ prem ch r e ↔ x ∈ (proj ch r e).1 := by
  unfold prem; rw [mem_foldl_ins]; simp

theorem prem_nodup (ch : Chain) (r : Nat) (e : Rec) : (prem ch r e).Nodup :=
  nodup_foldl_ins _ _ List.nodup_nil

/-- Toggling one member of a duplicate-free list from kept to
    dropped shortens the filter by exactly one. -/
theorem filter_toggle (t : Nat) (f g : Nat → Bool) (hf : f t = true) (hg : g t = false)
    (he : ∀ x, x ≠ t → g x = f x) :
    ∀ l : List Nat, l.Nodup →
      (l.filter g).length + (if t ∈ l then 1 else 0) = (l.filter f).length := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons y l ih =>
    intro hn
    rw [List.nodup_cons] at hn
    have ih' := ih hn.2
    by_cases hy : y = t
    · subst hy
      have : (if y ∈ l then 1 else 0) = 0 := by simp [hn.1]
      rw [this] at ih'
      simp [List.filter_cons, hf, hg]
      omega
    · have hgy := he y hy
      have hiff : (t ∈ y :: l) ↔ t ∈ l := by
        simp only [List.mem_cons]
        constructor
        · rintro (h | h)
          · exact absurd h.symm hy
          · exact h
        · exact Or.inr
      by_cases hfy : f y = true
      · simp [List.filter_cons, hfy, hgy, hiff]
        by_cases ht : t ∈ l <;> simp [ht] at ih' ⊢ <;> omega
      · simp [List.filter_cons, hfy, hgy, hiff]
        by_cases ht : t ∈ l <;> simp [ht] at ih' ⊢ <;> omega

theorem nodup_len_le : ∀ (l m : List Nat), l.Nodup → (∀ x ∈ l, x ∈ m) → l.length ≤ m.length := by
  intro l
  induction l with
  | nil => intros; simp
  | cons a l ih =>
    intro m hn hs
    rw [List.nodup_cons] at hn
    have ham : a ∈ m := hs a List.mem_cons_self
    have h := ih (m.erase a) hn.2 (fun x hx => by
      have hxa : x ≠ a := fun h => hn.1 (h ▸ hx)
      exact (List.mem_erase_of_ne hxa).mpr (hs x (List.mem_cons_of_mem _ hx)))
    rw [List.length_erase_of_mem ham] at h
    have : 0 < m.length := List.length_pos_of_mem ham
    simp; omega

theorem get_app (l : List Rec) (e x : Rec) (i : Nat) :
    (l ++ [e])[i]? = some x ↔ l[i]? = some x ∨ (i = l.length ∧ x = e) := by
  by_cases h : i < l.length
  · rw [List.getElem?_append_left h]
    constructor
    · exact Or.inl
    · rintro (h' | ⟨rfl, _⟩)
      · exact h'
      · exact absurd h (Nat.lt_irrefl _)
  · rw [List.getElem?_append_right (by omega), List.getElem?_singleton,
      List.getElem?_eq_none (by omega)]
    by_cases hi : i - l.length = 0
    · have : i = l.length := by omega
      simp [hi, this, eq_comm]
    · have : i ≠ l.length := by omega
      simp [hi, this]

theorem lt_of_get (l : List Rec) (i : Nat) (x : Rec) (h : l[i]? = some x) : i < l.length := by
  by_cases hi : i < l.length
  · exact hi
  · rw [List.getElem?_eq_none (by omega)] at h; cases h

/-- Sum of a count function over the first `n` indices. -/
def csum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => csum f n + f n

theorem csum_congr (f g : Nat → Nat) : ∀ n, (∀ j, j < n → f j = g j) → csum f n = csum g n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    simp only [csum]
    rw [ih (fun j hj => h j (by omega)), h n (by omega)]

theorem csum_dec (f : Nat → Nat) (i : Nat) (hf : 1 ≤ f i) :
    ∀ n, i < n → csum (fun j => if j = i then f i - 1 else f j) n + 1 = csum f n := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro h
    simp only [csum]
    by_cases hin : i = n
    · subst hin
      rw [csum_congr (fun j => if j = i then f i - 1 else f j) f i (fun j hj => by
        have : j ≠ i := by omega
        simp [this])]
      simp; omega
    · have := ih (by omega)
      have hni : n ≠ i := fun h => hin h.symm
      simp only [hni, if_false]
      omega

/-- Total distinct premises of a rule list. -/
def premTotal (ch : Chain) (r : Nat) (rs : List Rec) : Nat :=
  (rs.map (fun e => (prem ch r e).length)).foldl (· + ·) 0

theorem premTotal_snoc (ch : Chain) (r : Nat) (rs : List Rec) (e : Rec) :
    premTotal ch r (rs ++ [e]) = premTotal ch r rs + (prem ch r e).length := by
  simp [premTotal, List.foldl_append]

theorem nodup_snoc (l : List Nat) (n : Nat) (hl : l.Nodup) (hn : n ∉ l) : (l ++ [n]).Nodup := by
  have h : ins l n = l ++ [n] := by simp [ins, hn]
  rw [← h]; exact nodup_ins l n hl

/-! ## The invariant -/

section Proof
variable (ch : Chain) (r : Nat) (q : List Nat → Bool)

/-- `W`: waiters of the term being popped not yet visited (their
    stored count is one above the unprocessed premises). `X`:
    rules whose firing is still pending in the current step. -/
structure Inv (L : List Rec) (W X : List Nat) (s : St) : Prop where
  rules : s.rules = L.filter (admits r q)
  dnd : s.D.Nodup
  qnd : s.Q.Nodup
  qd : ∀ x ∈ s.Q, x ∈ s.D
  sound : ∀ a ∈ s.D, derives (viewC ch L r q) a
  heads : ∀ a ∈ s.D, a ∈ s.rules.map (hd ch r)
  cnt : ∀ i e, s.rules[i]? = some e →
    s.cnt i = ((prem ch r e).filter (nd s)).length + (if i ∈ W then 1 else 0)
  wait : ∀ t, nd s t = true →
    (s.wait t).Nodup ∧ ∀ i, i ∈ s.wait t ↔ ∃ e, s.rules[i]? = some e ∧ t ∈ prem ch r e
  fire : ∀ i e, s.rules[i]? = some e → i ∉ X →
    (∀ p ∈ prem ch r e, nd s p = false) → hd ch r e ∈ s.D
  wnd : W.Nodup
  wrules : ∀ i ∈ W, ∃ e, s.rules[i]? = some e
  pq : s.pops + s.Q.length = s.D.length
  scans : s.scans = premTotal ch r s.rules
  work : s.visits + csum s.cnt s.rules.length ≤ s.scans

theorem init_inv : Inv ch r q [] [] [] St.init := by
  refine ⟨rfl, List.nodup_nil, List.nodup_nil, ?_, ?_, ?_, ?_, ?_, ?_, List.nodup_nil, ?_, rfl, rfl, ?_⟩ <;>
    simp [St.init, csum, premTotal]

theorem nd_false (s : St) (x : Nat) (h : nd s x = false) : x ∈ s.D ∧ x ∉ s.Q := by
  simp [nd] at h; exact h

theorem derives_of_rule (L : List Rec) (s : St) (hr : s.rules = L.filter (admits r q))
    (hs : ∀ a ∈ s.D, derives (viewC ch L r q) a) (i : Nat) (e : Rec) (he : s.rules[i]? = some e)
    (hp : ∀ p ∈ prem ch r e, nd s p = false) : derives (viewC ch L r q) (hd ch r e) := by
  have hm : e ∈ L.filter (admits r q) := hr ▸ List.mem_of_getElem? he
  rw [List.mem_filter] at hm
  simp only [admits, Bool.and_eq_true, decide_eq_true_eq] at hm
  refine Derives.step (ps := (proj ch r e).1) ⟨e, hm.1, hm.2.1, hm.2.2, rfl⟩ ?_
  intro p hpm
  exact hs p (nd_false s p (hp p ((mem_prem ch r e p).mpr hpm))).1

theorem nd_push (s : St) (a x : Nat) : nd (push s a) x = nd s x := by
  unfold push
  split
  · rfl
  · rename_i ha
    by_cases hx : x = a
    · subst hx; simp [nd, ha]
    · simp [nd, hx]

theorem mem_push (s : St) (a : Nat) : a ∈ (push s a).D := by
  unfold push; split
  · assumption
  · exact List.mem_cons_self

theorem push_D (s : St) (a : Nat) : ∀ x ∈ s.D, x ∈ (push s a).D := by
  intro x hx; unfold push; split
  · exact hx
  · exact List.mem_cons_of_mem _ hx

@[simp] theorem push_rules (s : St) (a : Nat) : (push s a).rules = s.rules := by
  unfold push; split <;> rfl
@[simp] theorem push_pops (s : St) (a : Nat) : (push s a).pops = s.pops := by
  unfold push; split <;> rfl
@[simp] theorem push_cnt (s : St) (a : Nat) : (push s a).cnt = s.cnt := by
  unfold push; split <;> rfl
@[simp] theorem push_wait (s : St) (a : Nat) : (push s a).wait = s.wait := by
  unfold push; split <;> rfl
@[simp] theorem push_visits (s : St) (a : Nat) : (push s a).visits = s.visits := by
  unfold push; split <;> rfl
@[simp] theorem push_scans (s : St) (a : Nat) : (push s a).scans = s.scans := by
  unfold push; split <;> rfl

theorem push_len (s : St) (a : Nat) : s.D.length ≤ (push s a).D.length := by
  unfold push; split
  · exact Nat.le_refl _
  · simp

/-- Pushing a derivable head of an admitted rule keeps the invariant. -/
theorem inv_push (L : List Rec) (W X : List Nat) (s : St) (hi : Inv ch r q L W X s) (a : Nat)
    (hda : derives (viewC ch L r q) a) (hha : a ∈ s.rules.map (hd ch r)) :
    Inv ch r q L W X (push s a) := by
  have hnp : ∀ x, nd (push s a) x = nd s x := nd_push s a
  have hfp : ∀ l : List Nat, l.filter (nd (push s a)) = l.filter (nd s) := fun l =>
    List.filter_congr (fun x _ => hnp x)
  refine ⟨by simp [hi.rules], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hi.wnd, ?_, ?_, by simp [hi.scans],
    by simpa using hi.work⟩
  · unfold push; split
    · exact hi.dnd
    · rename_i ha; exact List.nodup_cons.mpr ⟨ha, hi.dnd⟩
  · unfold push; split
    · exact hi.qnd
    · rename_i ha; exact List.nodup_cons.mpr ⟨fun h => ha (hi.qd a h), hi.qnd⟩
  · unfold push; split
    · exact hi.qd
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hi.qd x hx)
  · unfold push; split
    · exact hi.sound
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hda
      · exact hi.sound x hx
  · simp only [push_rules]
    unfold push; split
    · exact hi.heads
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hha
      · exact hi.heads x hx
  · intro i e he; simp only [push_rules] at he; rw [hfp, push_cnt]; exact hi.cnt i e he
  · intro t ht; rw [hnp] at ht; simp only [push_wait, push_rules]; exact hi.wait t ht
  · intro i e he hx hp; simp only [push_rules] at he
    exact push_D s a _ (hi.fire i e he hx (fun p hp' => by rw [← hnp]; exact hp p hp'))
  · intro i hi'; simp only [push_rules]; exact hi.wrules i hi'
  · have := hi.pq
    unfold push; split
    · exact this
    · simp; omega

/-- Dropping a pending-fire exception once that rule has fired. -/
theorem inv_shrink (L : List Rec) (W X : List Nat) (i : Nat) (s : St) (hi : Inv ch r q L W (i :: X) s)
    (hf : ∀ e, s.rules[i]? = some e → (∀ p ∈ prem ch r e, nd s p = false) → hd ch r e ∈ s.D) :
    Inv ch r q L W X s := by
  refine ⟨hi.rules, hi.dnd, hi.qnd, hi.qd, hi.sound, hi.heads, hi.cnt, hi.wait, ?_, hi.wnd, hi.wrules,
    hi.pq, hi.scans, hi.work⟩
  intro j e he hj hp
  by_cases hji : j = i
  · subst hji; exact hf e he hp
  · exact hi.fire j e he (by simp only [List.mem_cons, not_or]; exact ⟨hji, hj⟩) hp

theorem filter_nil_iff (s : St) (l : List Nat) :
    l.filter (nd s) = [] ↔ ∀ p ∈ l, nd s p = false := by
  rw [List.filter_eq_nil_iff]; simp

/-- Visiting the next waiter keeps the invariant, one waiter fewer. -/
theorem inv_visit (L : List Rec) (i : Nat) (W : List Nat) (s : St) (hi : Inv ch r q L (i :: W) (i :: W) s) :
    Inv ch r q L W W (visit ch r s i) := by
  obtain ⟨e, he⟩ := hi.wrules i List.mem_cons_self
  have hwn := List.nodup_cons.mp hi.wnd
  have hc := hi.cnt i e he
  simp only [List.mem_cons_self, if_true] at hc
  let s' : St := { s with
                          cnt := fun j => if j = i then s.cnt i - 1 else s.cnt j,
                          visits := s.visits + 1 }
  have hi' : Inv ch r q L W (i :: W) s' := by
    refine ⟨hi.rules, hi.dnd, hi.qnd, hi.qd, hi.sound, hi.heads, ?_, hi.wait, ?_, hwn.2, ?_, hi.pq,
      hi.scans, ?_⟩
    · intro j e' he'
      show (if j = i then s.cnt i - 1 else s.cnt j) = _
      by_cases hj : j = i
      · subst hj
        rw [he] at he'; cases he'
        simp only [if_true, hwn.1, if_false]
        show s.cnt j - 1 = ((prem ch r e).filter (nd s)).length + 0
        omega
      · have := hi.cnt j e' he'
        simp only [hj, if_false]
        rw [this]
        have hiff : (j ∈ i :: W) ↔ j ∈ W := by
          simp only [List.mem_cons]
          constructor
          · rintro (h | h)
            · exact absurd h hj
            · exact h
          · exact Or.inr
        simp only [hiff]
        rfl
    · intro j e' he' hjW hp; exact hi.fire j e' he' hjW hp
    · intro j hj; exact hi.wrules j (List.mem_cons_of_mem _ hj)
    · have hw := hi.work
      have hlt := lt_of_get s.rules i e he
      have hd := csum_dec s.cnt i (by omega) s.rules.length hlt
      show s.visits + 1 + csum (fun j => if j = i then s.cnt i - 1 else s.cnt j) s.rules.length ≤ s.scans
      omega
  have hv : visit ch r s i = if s.cnt i - 1 = 0 then push s' (hd ch r e) else s' := by
    simp only [visit, he]; rfl
  rw [hv]
  split
  · rename_i h0
    have hall : ∀ p ∈ prem ch r e, nd s p = false := by
      rw [← filter_nil_iff, ← List.length_eq_zero_iff]; omega
    have hp := inv_push ch r q L W (i :: W) s' hi' (hd ch r e)
      (derives_of_rule ch r q L s' hi.rules hi.sound i e he hall)
      (List.mem_map.mpr ⟨e, List.mem_of_getElem? he, rfl⟩)
    refine inv_shrink ch r q L W W i _ hp ?_
    intro e' he' _
    simp only [push_rules] at he'
    have : e' = e := by
      have : s'.rules[i]? = some e := he
      rw [this] at he'; cases he'; rfl
    subst this; exact mem_push _ _
  · rename_i h0
    refine inv_shrink ch r q L W W i _ hi' ?_
    intro e' he' hp
    have : e' = e := by
      have : s'.rules[i]? = some e := he
      rw [this] at he'; cases he'; rfl
    subst this
    have : ((prem ch r e').filter (nd s)).length = 0 := by
      rw [List.length_eq_zero_iff, filter_nil_iff]; exact hp
    omega

theorem inv_fold (L : List Rec) : ∀ (W : List Nat) (s : St), Inv ch r q L W W s →
    Inv ch r q L [] [] (W.foldl (visit ch r) s) := by
  intro W
  induction W with
  | nil => intro s h; exact h
  | cons i W ih => intro s h; exact ih _ (inv_visit ch r q L i W s h)

/-- Popping a term and visiting its waiters keeps the invariant. -/
theorem inv_pop (L : List Rec) (s : St) (hi : Inv ch r q L [] [] s) : Inv ch r q L [] [] (pop ch r s) := by
  unfold pop
  split
  · exact hi
  · rename_i t rest hq
    let s0 : St := { s with Q := rest, pops := s.pops + 1 }
    have htQ : t ∈ s.Q := by rw [hq]; exact List.mem_cons_self
    have htD := hi.qd t htQ
    have hqn : (t :: rest).Nodup := hq ▸ hi.qnd
    have hnt : nd s t = true := by simp [nd, htQ]
    have hn0t : nd s0 t = false := by
      simp [nd, s0, htD, (List.nodup_cons.mp hqn).1]
    have hn0 : ∀ x, x ≠ t → nd s0 x = nd s x := by
      intro x hx; simp [nd, s0, hq, hx]
    have hw := hi.wait t hnt
    apply inv_fold ch r q L (s.wait t) s0
    refine ⟨hi.rules, hi.dnd, (List.nodup_cons.mp hqn).2, ?_, hi.sound, hi.heads, ?_, ?_, ?_, hw.1, ?_,
      ?_, hi.scans, hi.work⟩
    · intro x hx; exact hi.qd x (by rw [hq]; exact List.mem_cons_of_mem _ hx)
    · intro i e he
      have hc := hi.cnt i e he
      simp only [List.not_mem_nil, if_false, Nat.add_zero] at hc
      show s.cnt i = _
      rw [hc]
      have ht := filter_toggle t (nd s) (nd s0) hnt hn0t hn0 (prem ch r e) (prem_nodup ch r e)
      have hiff : (i ∈ s.wait t) ↔ t ∈ prem ch r e := by
        rw [hw.2 i]
        constructor
        · rintro ⟨e', he', ht'⟩; rw [he] at he'; cases he'; exact ht'
        · intro h; exact ⟨e, he, h⟩
      have : (if i ∈ s0.wait t then 1 else 0) = (if t ∈ prem ch r e then 1 else 0) := by
        show (if i ∈ s.wait t then 1 else 0) = _
        by_cases h : t ∈ prem ch r e
        · simp [h, hiff.mpr h]
        · simp [h, (not_congr hiff).mpr h]
      rw [this]; exact ht.symm
    · intro x hx
      have hxt : x ≠ t := fun h => by rw [h, hn0t] at hx; cases hx
      rw [hn0 x hxt] at hx
      exact hi.wait x hx
    · intro i e he hiw hp
      have htn : t ∉ prem ch r e := fun h => hiw ((hw.2 i).mpr ⟨e, he, h⟩)
      apply hi.fire i e he (fun h => nomatch h)
      intro p hpm
      have hpt : p ≠ t := fun h => htn (h ▸ hpm)
      rw [← hn0 p hpt]; exact hp p hpm
    · intro i hiw
      obtain ⟨e, he, _⟩ := (hw.2 i).mp hiw
      exact ⟨e, he⟩
    · have := hi.pq; rw [hq] at this; simp [s0] at this ⊢; omega

theorem inv_drain (L : List Rec) : ∀ n s, Inv ch r q L [] [] s → Inv ch r q L [] [] (drain ch r n s) := by
  intro n
  induction n with
  | zero => intro s h; exact h
  | succ n ih =>
    intro s h
    simp only [drain]
    split
    · exact h
    · exact ih _ (inv_pop ch r q L s h)

/-- Admitting a record keeps the invariant for the grown log,
    whatever the queue holds. -/
theorem inv_enter (L : List Rec) (s : St) (hi : Inv ch r q L [] [] s) (e : Rec) :
    Inv ch r q (L ++ [e]) [] [] (enter ch r q s e) := by
  unfold enter
  split
  · rename_i hadm
    let n := s.rules.length
    let miss := (prem ch r e).filter (nd s)
    let s' : St := { s with
                           rules := s.rules ++ [e],
                           cnt := fun j => if j = n then miss.length else s.cnt j,
                           wait := fun t => if t ∈ miss then s.wait t ++ [n] else s.wait t,
                           scans := s.scans + (prem ch r e).length }
    have hnd : ∀ x, nd s' x = nd s x := fun x => rfl
    have hfl : ∀ l : List Nat, l.filter (nd s') = l.filter (nd s) := fun l => rfl
    have hrules : s'.rules = (L ++ [e]).filter (admits r q) := by
      show s.rules ++ [e] = _
      rw [hi.rules, List.filter_append]; simp [hadm]
    have hsound : ∀ a ∈ s'.D, derives (viewC ch (L ++ [e]) r q) a := fun a ha =>
      View.derives_grow ch L [e] r q a (hi.sound a ha)
    have hget : ∀ j e', s'.rules[j]? = some e' ↔ s.rules[j]? = some e' ∨ (j = n ∧ e' = e) :=
      fun j e' => get_app s.rules e e' j
    have hold : ∀ j e', s.rules[j]? = some e' → j ≠ n := fun j e' h hj =>
      Nat.lt_irrefl _ (hj ▸ lt_of_get s.rules j e' h)
    have hbase : Inv ch r q (L ++ [e]) [] [n] s' := by
      refine ⟨hrules, hi.dnd, hi.qnd, hi.qd, hsound, ?_, ?_, ?_, ?_, List.nodup_nil, ?_, hi.pq, ?_, ?_⟩
      · intro a ha
        obtain ⟨x, hx, hxa⟩ := List.mem_map.mp (hi.heads a ha)
        exact List.mem_map.mpr ⟨x, List.mem_append.mpr (Or.inl hx), hxa⟩
      · intro j e' he'
        rcases (hget j e').mp he' with h | ⟨rfl, rfl⟩
        · have hjn := hold j e' h
          show (if j = n then miss.length else s.cnt j) = _
          rw [if_neg hjn, hi.cnt j e' h, hfl]
        · show (if n = n then miss.length else s.cnt n) = _
          simp only [if_true, List.not_mem_nil, if_false, Nat.add_zero]
          rfl
      · intro t ht
        rw [hnd] at ht
        have hw := hi.wait t ht
        have hmiss : t ∈ miss ↔ t ∈ prem ch r e := by
          simp only [miss, List.mem_filter, ht, and_true]
        have hnw : n ∉ s.wait t := fun h => by
          obtain ⟨e', he', _⟩ := (hw.2 n).mp h
          exact hold n e' he' rfl
        show (if t ∈ miss then s.wait t ++ [n] else s.wait t).Nodup ∧
          ∀ i, i ∈ (if t ∈ miss then s.wait t ++ [n] else s.wait t) ↔
            ∃ e', s'.rules[i]? = some e' ∧ t ∈ prem ch r e'
        by_cases htm : t ∈ miss
        · rw [if_pos htm]
          refine ⟨nodup_snoc _ _ hw.1 hnw, ?_⟩
          intro i
          rw [List.mem_append, hw.2 i, List.mem_singleton]
          constructor
          · rintro (⟨e', he', ht'⟩ | rfl)
            · exact ⟨e', (hget i e').mpr (Or.inl he'), ht'⟩
            · exact ⟨e, (hget n e).mpr (Or.inr ⟨rfl, rfl⟩), hmiss.mp htm⟩
          · rintro ⟨e', he', ht'⟩
            rcases (hget i e').mp he' with h | ⟨rfl, rfl⟩
            · exact Or.inl ⟨e', h, ht'⟩
            · exact Or.inr rfl
        · rw [if_neg htm]
          refine ⟨hw.1, ?_⟩
          intro i
          rw [hw.2 i]
          constructor
          · rintro ⟨e', he', ht'⟩; exact ⟨e', (hget i e').mpr (Or.inl he'), ht'⟩
          · rintro ⟨e', he', ht'⟩
            rcases (hget i e').mp he' with h | ⟨rfl, rfl⟩
            · exact ⟨e', h, ht'⟩
            · exact absurd (hmiss.mpr ht') htm
      · intro j e' he' hj hp
        rcases (hget j e').mp he' with h | ⟨rfl, rfl⟩
        · exact hi.fire j e' h (fun h => nomatch h) (fun p hp' => by rw [← hnd]; exact hp p hp')
        · exact absurd (List.mem_singleton.mpr rfl) hj
      · intro j hj; cases hj
      · show s.scans + (prem ch r e).length = premTotal ch r (s.rules ++ [e])
        rw [premTotal_snoc, hi.scans]
      · show s.visits + csum (fun j => if j = n then miss.length else s.cnt j) (s.rules ++ [e]).length
            ≤ s.scans + (prem ch r e).length
        have hl : (s.rules ++ [e]).length = n + 1 := by simp [n]
        rw [hl]
        simp only [csum, if_true]
        rw [csum_congr (fun j => if j = n then miss.length else s.cnt j) s.cnt n (fun j hj => by
          simp [Nat.ne_of_lt hj])]
        have := hi.work
        have := List.length_filter_le (nd s) (prem ch r e)
        have h1 : csum s.cnt n = csum s.cnt s.rules.length := rfl
        have h2 : miss.length = ((prem ch r e).filter (nd s)).length := rfl
        omega
    show Inv ch r q (L ++ [e]) [] [] (if miss = [] then push s' (hd ch r e) else s')
    split
    · rename_i hm
      have hall : ∀ p ∈ prem ch r e, nd s' p = false := (filter_nil_iff s' _).mp hm
      have hen : s'.rules[n]? = some e := (hget n e).mpr (Or.inr ⟨rfl, rfl⟩)
      have hp := inv_push ch r q (L ++ [e]) [] [n] s' hbase (hd ch r e)
        (derives_of_rule ch r q (L ++ [e]) s' hrules hsound n e hen hall)
        (List.mem_map.mpr ⟨e, List.mem_of_getElem? hen, rfl⟩)
      refine inv_shrink ch r q (L ++ [e]) [] [] n _ hp ?_
      intro e' he' _
      simp only [push_rules] at he'
      rw [hen] at he'; cases he'
      exact mem_push _ _
    · rename_i hm
      refine inv_shrink ch r q (L ++ [e]) [] [] n _ hbase ?_
      intro e' he' hp
      have hen : s'.rules[n]? = some e := (hget n e).mpr (Or.inr ⟨rfl, rfl⟩)
      rw [hen] at he'; cases he'
      exact absurd ((filter_nil_iff s' _).mpr hp) hm
  · rename_i hadm
    refine ⟨?_, hi.dnd, hi.qnd, hi.qd, fun a ha => View.derives_grow ch L [e] r q a (hi.sound a ha),
      hi.heads, hi.cnt, hi.wait, hi.fire, hi.wnd, hi.wrules, hi.pq, hi.scans, hi.work⟩
    rw [hi.rules, List.filter_append]; simp [hadm]

/-! ## Termination from the finite term bound -/

theorem visit_rules (s : St) (i : Nat) : (visit ch r s i).rules = s.rules ∧
    (visit ch r s i).pops = s.pops ∧ s.D.length ≤ (visit ch r s i).D.length := by
  unfold visit
  split
  · split
    · refine ⟨by simp, by simp, ?_⟩
      rename_i e _ _
      have h := push_len { s with cnt := fun j => if j = i then s.cnt i - 1 else s.cnt j, visits := s.visits + 1 } (hd ch r e)
      exact h
    · exact ⟨rfl, rfl, Nat.le_refl _⟩
  · exact ⟨rfl, rfl, Nat.le_refl _⟩

theorem fold_rules : ∀ (W : List Nat) (s : St), (W.foldl (visit ch r) s).rules = s.rules ∧
    (W.foldl (visit ch r) s).pops = s.pops ∧ s.D.length ≤ (W.foldl (visit ch r) s).D.length := by
  intro W
  induction W with
  | nil => intro s; exact ⟨rfl, rfl, Nat.le_refl _⟩
  | cons i W ih =>
    intro s
    obtain ⟨h1, h2, h3⟩ := visit_rules ch r s i
    obtain ⟨g1, g2, g3⟩ := ih (visit ch r s i)
    exact ⟨g1.trans h1, g2.trans h2, Nat.le_trans h3 g3⟩

/-- Every derived term is the head of an admitted rule, so the
    derived set is bounded by the admitted rules. -/
theorem D_le (L : List Rec) (W X : List Nat) (s : St) (hi : Inv ch r q L W X s) :
    s.D.length ≤ s.rules.length := by
  have := nodup_len_le s.D (s.rules.map (hd ch r)) hi.dnd hi.heads
  simpa using this

theorem nu_pop (L : List Rec) (s : St) (hi : Inv ch r q L [] [] s) (hq : s.Q ≠ []) :
    nu (pop ch r s) < nu s := by
  have hi' := inv_pop ch r q L s hi
  have hb := D_le ch r q L [] [] _ hi'
  have hpq := hi'.pq
  have hb0 := D_le ch r q L [] [] _ hi
  have hpq0 := hi.pq
  unfold pop at hb hpq ⊢
  split
  · rename_i h; exact absurd h hq
  · rename_i t rest hqe
    simp only [hqe] at hb hpq
    obtain ⟨h1, h2, h3⟩ := fold_rules ch r (s.wait t) { s with Q := rest, pops := s.pops + 1 }
    simp only [nu, h1, h2]
    simp only at h3
    rw [h1] at hb
    rw [h2] at hpq
    rw [hqe] at hpq0
    simp at hpq0
    omega

/-- The queue empties within `nu` pops. -/
theorem drain_empty (L : List Rec) : ∀ n s, Inv ch r q L [] [] s → nu s ≤ n → (drain ch r n s).Q = [] := by
  intro n
  induction n with
  | zero =>
    intro s hi hn
    simp only [drain]
    have hb := D_le ch r q L [] [] s hi
    have hpq := hi.pq
    simp only [nu] at hn
    cases hq : s.Q with
    | nil => rfl
    | cons x xs => rw [hq] at hpq; simp at hpq; omega
  | succ n ih =>
    intro s hi hn
    simp only [drain]
    split
    · assumption
    · rename_i hq
      exact ih _ (inv_pop ch r q L s hi) (by have := nu_pop ch r q L s hi hq; omega)

/-- `nu` is at most twice the number of admitted rules. -/
theorem nu_le (s : St) : nu s ≤ 2 * s.rules.length := by unfold nu; omega

/-! ## Correctness at every append prefix -/

/-- With an empty queue the derived set is closed: it holds
    every term derivable in the view. -/
theorem complete (L : List Rec) (s : St) (hi : Inv ch r q L [] [] s) (hq : s.Q = []) :
    ∀ a, derives (viewC ch L r q) a → a ∈ s.D := by
  apply Derives.least (X := fun a => a ∈ s.D)
  · intro a h; exact h.elim
  · rintro ps a ⟨e, he, hl, hc, hp⟩ hps
    have hm : e ∈ s.rules := by
      rw [hi.rules, List.mem_filter]
      exact ⟨he, by simp [admits, hl, hc]⟩
    obtain ⟨i, hi'⟩ := List.getElem?_of_mem hm
    have := hi.fire i e hi' (fun h => nomatch h) (by
      intro p hpm
      have hpD := hps p (by have := (mem_prem ch r e p).mp hpm; rw [hp] at this; exact this)
      simp [nd, hpD, hq])
    unfold hd at this; rw [hp] at this; exact this

theorem inv_append (L : List Rec) (s : St) (hi : Inv ch r q L [] [] s) (e : Rec) :
    Inv ch r q (L ++ [e]) [] [] (appendRec ch r q s e) ∧ (appendRec ch r q s e).Q = [] := by
  have ha := inv_enter ch r q L s hi e
  exact ⟨inv_drain ch r q _ _ _ ha, drain_empty ch r q _ _ _ ha (Nat.le_refl _)⟩

/-- Continuing from any invariant state over appended records. -/
theorem inv_continue : ∀ (M L : List Rec) (s : St), Inv ch r q L [] [] s → s.Q = [] →
    Inv ch r q (L ++ M) [] [] (M.foldl (appendRec ch r q) s) ∧ (M.foldl (appendRec ch r q) s).Q = [] := by
  intro M
  induction M with
  | nil => intro L s hi hq; simpa using ⟨hi, hq⟩
  | cons e M ih =>
    intro L s hi _
    obtain ⟨h1, h2⟩ := inv_append ch r q L s hi e
    have := ih (L ++ [e]) _ h1 h2
    simpa using this

theorem inv_run (L : List Rec) : Inv ch r q L [] [] (run ch r q L) ∧ (run ch r q L).Q = [] := by
  have := inv_continue ch r q L [] St.init (init_inv ch r q) rfl
  simpa [run] using this

/-- Exactness: the derived set after any log is derivability in
    the view of that log. -/
theorem mem_run (L : List Rec) (a : Nat) : a ∈ (run ch r q L).D ↔ derives (viewC ch L r q) a :=
  ⟨(inv_run ch r q L).1.sound a, complete ch r q L _ (inv_run ch r q L).1 (inv_run ch r q L).2 a⟩

/-- Same members as the naive closure. -/
theorem run_eq_clos (L : List Rec) (a : Nat) : a ∈ (run ch r q L).D ↔ a ∈ clos ch L r q := by
  rw [mem_run, mem_clos]

/-- At every append prefix of a log. -/
theorem mem_prefix (L : List Rec) (k a : Nat) :
    a ∈ (run ch r q (L.take k)).D ↔ derives (viewC ch (L.take k) r q) a := mem_run ch r q _ a

/-- The run is incremental: the state of `L ++ M` is the state
    of `L` continued over `M`, with nothing recomputed. -/
theorem run_append (L M : List Rec) :
    run ch r q (L ++ M) = M.foldl (appendRec ch r q) (run ch r q L) := by
  simp [run, List.foldl_append]

/-- Continuing the stored state of `L` over `M` gives exactly
    derivability in `L ++ M`, including rules admitted before
    the append whose premises only the appended records supply. -/
theorem mem_continue (L M : List Rec) (a : Nat) :
    a ∈ (M.foldl (appendRec ch r q) (run ch r q L)).D ↔ derives (viewC ch (L ++ M) r q) a := by
  rw [← run_append]; exact mem_run ch r q _ a

theorem nodup_run (L : List Rec) : (run ch r q L).D.Nodup := (inv_run ch r q L).1.dnd

/-- Every derived term is dequeued exactly once. -/
theorem pops_eq (L : List Rec) : (run ch r q L).pops = (run ch r q L).D.length := by
  have h := (inv_run ch r q L).1.pq
  rw [(inv_run ch r q L).2] at h
  simpa using h

/-- The admitted rules are exactly the records `viewC` keeps. -/
theorem rules_run (L : List Rec) : (run ch r q L).rules = L.filter (admits r q) :=
  (inv_run ch r q L).1.rules

/-- Total waiter visits are bounded by the distinct premises of
    the admitted records, whatever the append order. -/
theorem visits_le (L : List Rec) :
    (run ch r q L).visits ≤ premTotal ch r (L.filter (admits r q)) := by
  have hi := (inv_run ch r q L).1
  have := hi.work
  rw [hi.scans, hi.rules] at this
  omega

/-- Admission scans are exactly the distinct premises of the
    admitted records. -/
theorem scans_run (L : List Rec) :
    (run ch r q L).scans = premTotal ch r (L.filter (admits r q)) := by
  have hi := (inv_run ch r q L).1
  rw [hi.scans, hi.rules]

end Proof

/-! ## Controls (kernel-checked on concrete logs) -/

namespace Control

def ch0 : Chain := ⟨fun _ c => c, 0, 0, Nat.le_refl 0⟩
def any : List Nat → Bool := fun _ => true
/-- Rejects color 4 (disqualified in the estate numbering). -/
def noDisq : List Nat → Bool := fun cs => !cs.contains 4

/-- A rule admitted before its premise exists stays pending with
    count one; appending the premise's producer fires it through
    the stored count. -/
theorem pending_then_fire :
    let s := run ch0 0 any [⟨0, 0, [], [7], 8⟩]
    s.D = [] ∧ s.cnt 0 = 1 ∧
    (([⟨1, 0, [], [], 7⟩] : List Rec).foldl (appendRec ch0 0 any) s).D = [8, 7] := by
  decide

/-- Duplicate premises count once: `[5, 5]` has one distinct
    premise; the rule fires after one visit. -/
theorem duplicate_once :
    (proj ch0 0 ⟨0, 0, [], [5, 5], 6⟩).1.length = 2 ∧ (prem ch0 0 ⟨0, 0, [], [5, 5], 6⟩).length = 1 ∧
    (run ch0 0 any [⟨0, 0, [], [5, 5], 6⟩, ⟨1, 0, [], [], 5⟩]).D = [6, 5] ∧
    (run ch0 0 any [⟨0, 0, [], [5, 5], 6⟩, ⟨1, 0, [], [], 5⟩]).visits = 1 := by
  decide

/-- Premise identity is the level-`r` class: `10` and `11` are
    one class at level 1, so the rule has one distinct premise. -/
theorem merged_premises :
    (prem Control.chain2 1 ⟨0, 0, [], [10, 11], 20⟩).length = 1 ∧
    (run Control.chain2 1 any [⟨0, 0, [], [10, 11], 20⟩, ⟨1, 0, [], [], 12⟩]).D = [2, 1] := by
  decide

/-- A record failing the color test never fires, even with every
    premise derived, and is not derivable in the view. -/
theorem filtered_color :
    (run ch0 0 noDisq [⟨0, 0, [], [], 5⟩, ⟨1, 0, [4], [5], 6⟩]).D = [5] ∧
    (run ch0 0 noDisq [⟨0, 0, [], [], 5⟩, ⟨1, 0, [4], [5], 6⟩]).rules.length = 1 ∧
    ¬ derives (viewC ch0 [⟨0, 0, [], [], 5⟩, ⟨1, 0, [4], [5], 6⟩] 0 noDisq) 6 := by
  refine ⟨by decide, by decide, fun h => ?_⟩
  have := (mem_run ch0 0 noDisq _ 6).mpr h
  revert this; decide

/-- A record finer than the view level is not admitted. -/
theorem filtered_level :
    (run Control.chain2 0 any [⟨0, 1, [], [], 5⟩]).D = [] ∧
    ¬ derives (viewC Control.chain2 [⟨0, 1, [], [], 5⟩] 0 any) 5 := by
  refine ⟨by decide, fun h => ?_⟩
  have := (mem_run Control.chain2 0 any _ 5).mpr h
  revert this; decide

end Control

end Worklist

#print axioms Worklist.filter_toggle
#print axioms Worklist.inv_enter
#print axioms Worklist.inv_pop
#print axioms Worklist.drain_empty
#print axioms Worklist.complete
#print axioms Worklist.mem_run
#print axioms Worklist.run_eq_clos
#print axioms Worklist.mem_prefix
#print axioms Worklist.run_append
#print axioms Worklist.mem_continue
#print axioms Worklist.nodup_run
#print axioms Worklist.pops_eq
#print axioms Worklist.rules_run
#print axioms Worklist.visits_le
#print axioms Worklist.scans_run
#print axioms Worklist.nu_le
#print axioms Worklist.Control.pending_then_fire
#print axioms Worklist.Control.duplicate_once
#print axioms Worklist.Control.merged_premises
#print axioms Worklist.Control.filtered_color
#print axioms Worklist.Control.filtered_level

end Canon
