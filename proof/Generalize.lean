/-
  How far the one equivalence graph generalizes across software.

  Target model: the canonical hypergraph of clpi/software,
  theses/redundancy-is-equivalence/spec.md (ruling of
  2026-11-19). Its edges are total equivalence classes of
  terms; a join is admitted only on a witness; edges merge and
  never split; there is one partition, with no private
  equivalence per level or per qualification.

  This file proves, in plain Lean with no library beyond core:

  1. Limit. No procedure decides behavioral equivalence for a
     language with the recursion property, and so no computable
     key is both sound and complete for it (`noDecider`,
     `noExactKey`). The recursion property is a named premise
     (`Diag`): Kleene's second recursion theorem gives it for
     every Turing-complete language and every computable
     candidate, and that theorem is not proved here.
  2. What bounded resolution recovers. For any deterministic
     step machine, outputs found at a fuel bound persist at
     every larger bound (`run_mono`); a decisive separation
     (both sides halted, outputs differ) persists under every
     refinement of inputs and fuel (`decisive_persists`) and
     refutes equivalence (`decisive_sound`); every difference
     between two halted outputs is found at some finite
     resolution (`decisive_complete`).
  3. What it cannot recover. Halting against running forever is
     never decisively separated at any resolution
     (`diverge_never_decisive`), and for every bound K there is
     a pair that agrees at every fuel up to K and differs later
     (`no_uniform_bound`). So a join witnessed by bounded
     agreement can be false, and the model has no split.
  4. One partition and several observers. If two observers'
     equivalences are joined into one partition, transitivity
     relates terms that neither observer relates
     (`leak_example`). Joining observer-applied terms instead
     (the form term `o(p)` of the grammar) never leaks: every
     derived equivalence is a fact of exactly one observer
     (`qualified_sound`). This keeps the spec's single
     partition and its grammar unchanged.
  5. Tolerance is not an equivalence. Any transitive, symmetric
     relation that relates each grid point to its neighbour
     relates every pair (`tolerance_collapse`), so closeness
     can be painted only as a relation term, never as a join.
  6. Contexts. An equivalence used as a rewrite is sound inside
     a context only when the observer is compositional for that
     context. Sequential final-state equivalence is not
     compositional for parallel composition (`par_breaks`).
  7. Exhaustive domains. Agreement on a list that holds every
     input is equality of behavior (`exhaustive_iff`), so a bare
     join on such a measurement is sound.
-/

namespace Generalize

/- ## 1. The limit -/

/-- A language at its most abstract: programs and a behavior
    for each. -/
structure Lang where
  P : Type
  B : Type
  sem : P → B

/-- The recursion premise for a candidate decider `d`: for any
    two programs `a` and `b` the language builds a program that
    asks `d` whether it is equivalent to `a`, then behaves as `b`
    when told yes and as `a` when told no. -/
def Diag (L : Lang) (d : L.P → L.P → Bool) : Prop :=
  ∀ a b : L.P, ∃ p : L.P, L.sem p = (if d p a = true then L.sem b else L.sem a)

/-- `d` decides behavioral equivalence exactly. -/
def Decides (L : Lang) (d : L.P → L.P → Bool) : Prop :=
  ∀ x y, d x y = true ↔ L.sem x = L.sem y

/-- No exact decider exists once the language has two programs
    with different behavior and the recursion premise holds for
    the candidate. -/
theorem noDecider (L : Lang) (d : L.P → L.P → Bool) (hdiag : Diag L d)
    (a b : L.P) (hab : L.sem a ≠ L.sem b) : ¬ Decides L d := by
  intro hdec
  obtain ⟨p, hp⟩ := hdiag a b
  cases h : d p a with
  | true =>
    rw [h] at hp
    simp at hp
    have hpa : L.sem p = L.sem a := (hdec p a).1 h
    exact hab (hpa.symm.trans hp)
  | false =>
    rw [h] at hp
    simp at hp
    have := (hdec p a).2 hp
    rw [h] at this
    exact Bool.false_ne_true this

/-- A key is exact when equal keys are exactly equal behavior:
    sound (equal key, equal behavior) and complete (equal
    behavior, equal key). This is what a total equivalence
    level would need to be for behavioral equivalence. -/
def ExactKey (L : Lang) {K : Type} (k : L.P → K) : Prop :=
  ∀ x y, k x = k y ↔ L.sem x = L.sem y

/-- The decider a key with decidable equality induces. -/
def keyDecider (L : Lang) {K : Type} [DecidableEq K] (k : L.P → K) : L.P → L.P → Bool :=
  fun x y => decide (k x = k y)

/-- No exact key with decidable equality exists for a language
    whose recursion premise holds for that key's decider. -/
theorem noExactKey (L : Lang) {K : Type} [DecidableEq K] (k : L.P → K)
    (hdiag : Diag L (keyDecider L k)) (a b : L.P) (hab : L.sem a ≠ L.sem b) :
    ¬ ExactKey L k := by
  intro hk
  apply noDecider L (keyDecider L k) hdiag a b hab
  intro x y
  simp only [keyDecider, decide_eq_true_eq]
  exact hk x y

/-- Soundness alone is free: spelling is a sound key. -/
theorem spelling_sound (L : Lang) (x y : L.P) (h : x = y) : L.sem x = L.sem y := by
  rw [h]

/- ## 2. Bounded resolution: a deterministic step machine -/

/-- Run a machine for at most `n` steps: `some o` when it halts
    with `o` within the bound, `none` otherwise. -/
def run {S O : Type} (step : S → S ⊕ O) : Nat → S → Option O
  | 0, _ => none
  | n + 1, s =>
    match step s with
    | .inl s' => run step n s'
    | .inr o => some o

/-- An output found at a bound stays found at every larger
    bound. -/
theorem run_mono {S O : Type} (step : S → S ⊕ O) :
    ∀ (n m : Nat) (s : S) (o : O), run step n s = some o → run step (n + m) s = some o := by
  intro n
  induction n with
  | zero => intro m s o h; simp [run] at h
  | succ n ih =>
    intro m s o h
    rw [Nat.succ_add]
    simp only [run] at h ⊢
    cases hs : step s with
    | inl s' => rw [hs] at h; exact ih m s' o h
    | inr o' => rw [hs] at h; exact h

theorem run_mono_le {S O : Type} (step : S → S ⊕ O) (n m : Nat) (s : S) (o : O)
    (hle : n ≤ m) (h : run step n s = some o) : run step m s = some o := by
  have := run_mono step n (m - n) s o h
  rwa [Nat.add_sub_cancel' hle] at this

/-- A program over inputs `I`: its own state type, a machine on
    it, and an initial state for each input. -/
structure Prog (I O : Type) : Type 1 where
  S : Type
  step : S → S ⊕ O
  init : I → S

/-- The program's observation at fuel `k` on input `x`. -/
def obs {I O : Type} (p : Prog I O) (k : Nat) (x : I) : Option O :=
  run p.step k (p.init x)

/-- The eventual output of a program on an input. -/
def Outcome {I O : Type} (p : Prog I O) (x : I) (o : O) : Prop :=
  ∃ k, obs p k x = some o

/-- The eventual output is unique. -/
theorem outcome_unique {I O : Type} (p : Prog I O) (x : I) (o o' : O)
    (h : Outcome p x o) (h' : Outcome p x o') : o = o' := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨k', hk'⟩ := h'
  have a : run p.step (k + k') (p.init x) = some o := run_mono p.step k k' (p.init x) o hk
  have b : run p.step (k' + k) (p.init x) = some o' := run_mono p.step k' k (p.init x) o' hk'
  rw [Nat.add_comm] at b
  rw [a] at b
  exact Option.some.inj b

/-- Behavioral equivalence of programs: the same eventual
    outputs on every input. -/
def Equiv {I O : Type} (p q : Prog I O) : Prop :=
  ∀ x o, Outcome p x o ↔ Outcome q x o

/-- A decisive separation at the resolution of inputs `xs` and
    fuel `k`: on some listed input both sides halted within the
    fuel and their outputs differ. -/
def Decisive {I O : Type} (p q : Prog I O) (xs : List I) (k : Nat) : Prop :=
  ∃ x, x ∈ xs ∧ ∃ o o', obs p k x = some o ∧ obs q k x = some o' ∧ o ≠ o'

/-- A decisive separation persists under every refinement:
    more inputs and more fuel. This is the append-only half of
    bounded resolution: a separation, once witnessed, is final. -/
theorem decisive_persists {I O : Type} (p q : Prog I O) (xs ys : List I) (k m : Nat)
    (hsub : ∀ x, x ∈ xs → x ∈ ys) (hle : k ≤ m) (h : Decisive p q xs k) :
    Decisive p q ys m := by
  obtain ⟨x, hx, o, o', ho, ho', hne⟩ := h
  exact ⟨x, hsub x hx, o, o', run_mono_le p.step k m _ o hle ho,
    run_mono_le q.step k m _ o' hle ho', hne⟩

/-- A decisive separation refutes equivalence. -/
theorem decisive_sound {I O : Type} (p q : Prog I O) (xs : List I) (k : Nat)
    (h : Decisive p q xs k) : ¬ Equiv p q := by
  intro he
  obtain ⟨x, _, o, o', ho, ho', hne⟩ := h
  have hq : Outcome q x o := (he x o).1 ⟨k, ho⟩
  exact hne (outcome_unique q x o o' hq ⟨k, ho'⟩)

/-- Every difference between two halted outputs is decisively
    witnessed at some finite resolution. -/
theorem decisive_complete {I O : Type} (p q : Prog I O) (x : I) (o o' : O)
    (hp : Outcome p x o) (hq : Outcome q x o') (hne : o ≠ o') :
    ∃ k, Decisive p q [x] k := by
  obtain ⟨k, hk⟩ := hp
  obtain ⟨k', hk'⟩ := hq
  refine ⟨k + k', x, by simp, o, o', run_mono p.step k k' _ o hk, ?_, hne⟩
  have := run_mono q.step k' k _ o' hk'
  rwa [Nat.add_comm] at this

/- ## 3. What bounded resolution cannot recover -/

/-- A program that never halts. -/
def loopP (I O : Type) : Prog I O := ⟨Unit, fun _ => .inl (), fun _ => ()⟩

theorem loop_obs (I O : Type) : ∀ (k : Nat) (x : I), obs (loopP I O) k x = none := by
  intro k
  induction k with
  | zero => intro x; rfl
  | succ k ih => intro x; simp only [obs, run, loopP] at ih ⊢; exact ih x

/-- Running forever is never decisively separated from anything,
    at any resolution. -/
theorem diverge_never_decisive {I O : Type} (q : Prog I O) (xs : List I) (k : Nat) :
    ¬ Decisive (loopP I O) q xs k := by
  intro h
  obtain ⟨x, _, o, _, ho, _, _⟩ := h
  rw [loop_obs] at ho
  exact Option.noConfusion ho

/-- A program that halts with `0` after exactly `K + 1` steps. -/
def lateP (I : Type) (K : Nat) : Prog I Nat :=
  ⟨Nat, fun s => if s = K then .inr 0 else .inl (s + 1), fun _ => 0⟩

theorem late_none (K : Nat) : ∀ (k s : Nat), s ≤ K → k + s ≤ K →
    run (lateP Unit K).step k s = none := by
  intro k
  induction k with
  | zero => intro s _ _; rfl
  | succ k ih =>
    intro s hs hk
    simp only [run, lateP]
    have hne : s ≠ K := by omega
    simp [hne]
    exact ih (s + 1) (by omega) (by omega)

theorem late_halts (K : Nat) : ∀ s, s ≤ K → run (lateP Unit K).step (K - s + 1) s = some 0 := by
  intro s hs
  induction h : K - s generalizing s with
  | zero =>
    have : s = K := by omega
    subst this
    simp [run, lateP]
  | succ j ih =>
    simp only [run, lateP]
    have hne : s ≠ K := by omega
    simp only [hne, if_false]
    exact ih (s + 1) (by omega) (by omega)

/-- For every bound `K` there is an inequivalent pair that agrees
    at every fuel up to `K`: no single fuel bound makes bounded
    agreement a sound witness of equivalence. -/
theorem no_uniform_bound (K : Nat) :
    (∀ k, k ≤ K → obs (lateP Unit K) k () = none ∧ obs (loopP Unit Nat) k () = none) ∧
    ¬ Equiv (lateP Unit K) (loopP Unit Nat) := by
  refine ⟨fun k hk => ⟨late_none K k 0 (Nat.zero_le K) (by omega), loop_obs Unit Nat k ()⟩, ?_⟩
  intro he
  have h0 : Outcome (lateP Unit K) () 0 := ⟨K + 1, by
    have := late_halts K 0 (Nat.zero_le K)
    simpa [obs] using this⟩
  obtain ⟨k, hk⟩ := (he () 0).1 h0
  rw [loop_obs] at hk
  exact Option.noConfusion hk

/- ## 4. One partition, several observers -/

/-- The equivalence closure of a relation. -/
inductive Closure {α : Type} (r : α → α → Prop) : α → α → Prop where
  | base {a b : α} : r a b → Closure r a b
  | refl (a : α) : Closure r a a
  | symm {a b : α} : Closure r a b → Closure r b a
  | trans {a b c : α} : Closure r a b → Closure r b c → Closure r a c

/-- Facts of several observers poured into one partition: the
    bare join of `p` and `q` whenever some observer sees them
    equal. -/
def Bare {Ob P K : Type} (key : Ob → P → K) (p q : P) : Prop :=
  ∃ o, key o p = key o q

/-- The same facts as joins of observer-applied terms: `o(p)`
    joined with `o(q)`. A pair stands for the form term whose
    head is the observer symbol and whose one argument is the
    program term. -/
def Qual {Ob P K : Type} (key : Ob → P → K) (a b : Ob × P) : Prop :=
  a.1 = b.1 ∧ key a.1 a.2 = key b.1 b.2

/-- Observer-applied joins never leak: every equivalence derived
    in the one partition is a fact of exactly one observer. -/
theorem qualified_sound {Ob P K : Type} (key : Ob → P → K) (a b : Ob × P)
    (h : Closure (Qual key) a b) : a.1 = b.1 ∧ key a.1 a.2 = key b.1 b.2 := by
  induction h with
  | base h => exact h
  | refl a => exact ⟨rfl, rfl⟩
  | symm _ ih => exact ⟨ih.1.symm, ih.2.symm⟩
  | trans _ _ ih1 ih2 =>
    exact ⟨ih1.1.trans ih2.1, ih1.2.trans ih2.2⟩

/-- The leak, on a concrete pair of observers of file writes:
    `content` reads the final file bytes, `calls` counts write
    calls. `t1` writes "ab" in one call, `t2` writes "a" then
    "b", `t3` writes "x" then "y". -/
inductive Obs2 | content | calls deriving DecidableEq
inductive W3 | t1 | t2 | t3 deriving DecidableEq

def key3 : Obs2 → W3 → Nat
  | .content, .t1 => 0   -- "ab"
  | .content, .t2 => 0   -- "ab"
  | .content, .t3 => 1   -- "xy"
  | .calls, .t1 => 1
  | .calls, .t2 => 2
  | .calls, .t3 => 2

/-- The bare partition joins `t1` and `t3`, though no observer
    sees them equal. -/
theorem leak_example :
    Closure (Bare key3) W3.t1 W3.t3 ∧ ¬ Bare key3 W3.t1 W3.t3 := by
  refine ⟨Closure.trans (b := W3.t2) (.base ⟨.content, rfl⟩) (.base ⟨.calls, rfl⟩), ?_⟩
  intro ⟨o, h⟩
  cases o <;> simp [key3] at h

/-- The qualified partition, fed the same facts, does not. -/
theorem qualified_example (o o' : Obs2) :
    ¬ Closure (Qual key3) (o, W3.t1) (o', W3.t3) := by
  intro h
  have := qualified_sound key3 _ _ h
  obtain ⟨ho, hk⟩ := this
  simp only at ho hk
  subst ho
  cases o <;> simp [key3] at hk

/-- A coarser observer's join is derived from a finer one's, so
    observers that refine each other need no extra witness. -/
theorem refine_join {Ob P K : Type} (key : Ob → P → K) (fine coarse : Ob) (g : K → K)
    (hg : ∀ p, key coarse p = g (key fine p)) (p q : P)
    (h : key fine p = key fine q) : key coarse p = key coarse q := by
  rw [hg, hg, h]

/-- Grammar bridge: the observer-applied term is a form term,
    and two of them are equal exactly when observer and program
    are equal, so pairs above lose nothing. -/
inductive Term (Sym : Type) where
  | atom : Sym → Term Sym
  | form : Term Sym → List (Term Sym) → Term Sym

def applied {Sym : Type} (o : Sym) (p : Term Sym) : Term Sym := .form (.atom o) [p]

theorem applied_inj {Sym : Type} (o o' : Sym) (p p' : Term Sym)
    (h : applied o p = applied o' p') : o = o' ∧ p = p' := by
  simp only [applied, Term.form.injEq, Term.atom.injEq, List.cons.injEq] at h
  exact ⟨h.1, h.2.1⟩

/- ## 5. Tolerance is not an equivalence -/

/-- A symmetric, transitive relation on a grid that relates each
    point to the next relates every pair. -/
theorem tolerance_collapse (R : Nat → Nat → Prop)
    (symm : ∀ a b, R a b → R b a) (trans : ∀ a b c, R a b → R b c → R a c)
    (near : ∀ a, R a (a + 1)) : ∀ a b, R a b := by
  have h0 : ∀ n, R 0 n ∨ n = 0 := by
    intro n
    induction n with
    | zero => exact Or.inr rfl
    | succ n ih =>
      rcases ih with h | h
      · exact Or.inl (trans 0 n (n + 1) h (near n))
      · subst h; exact Or.inl (near 0)
  have hself : R 0 0 := trans 0 1 0 (near 0) (symm 0 1 (near 0))
  have hz : ∀ n, R 0 n := by
    intro n
    rcases h0 n with h | h
    · exact h
    · subst h; exact hself
  intro a b
  exact trans a 0 b (symm 0 a (hz a)) (hz b)

/- ## 6. Contexts: sequential equivalence is not a congruence for
   parallel composition -/

/-- One thread's atomic operations on a shared cell `x` and a
    thread-local register `r`. -/
inductive Op | inc | load | storeInc deriving DecidableEq

/-- Execute one operation: new shared value and new register. -/
def exec : Op → Nat → Nat → Nat × Nat
  | .inc, x, r => (x + 1, r)
  | .load, x, _ => (x, x)
  | .storeInc, _, r => (r + 1, r)

/-- Solo run of one thread. -/
def solo : List Op → Nat → Nat → Nat
  | [], x, _ => x
  | op :: ops, x, r => let (x', r') := exec op x r; solo ops x' r'

/-- Every final shared value over every interleaving of two
    threads, by structural recursion on a step budget. -/
def finals : Nat → Nat → Nat → Nat → List Op → List Op → List Nat
  | _, x, _, _, [], [] => [x]
  | 0, _, _, _, _, _ => []
  | n + 1, x, r1, r2, a :: as, [] =>
    let (x', r1') := exec a x r1; finals n x' r1' r2 as []
  | n + 1, x, r1, r2, [], b :: bs =>
    let (x', r2') := exec b x r2; finals n x' r1 r2' [] bs
  | n + 1, x, r1, r2, a :: as, b :: bs =>
    (let (x', r1') := exec a x r1; finals n x' r1' r2 as (b :: bs)) ++
    (let (x', r2') := exec b x r2; finals n x' r1 r2' (a :: as) bs)

def atomicInc : List Op := [.inc]
def splitInc : List Op := [.load, .storeInc]

/-- Run alone, the two increments are equal on every input. -/
theorem solo_equal (x r : Nat) : solo atomicInc x r = solo splitInc x r := by
  simp [solo, atomicInc, splitInc, exec]

/-- Composed in parallel with a copy of itself, the atomic one
    always ends at 2 and the split one can end at 1: the
    sequential equivalence does not survive the context. -/
theorem par_breaks :
    finals 4 0 0 0 atomicInc atomicInc = [2, 2] ∧
    (1 ∈ finals 4 0 0 0 splitInc splitInc) := by
  decide

/- ## 7. Exhaustive domains -/

/-- Agreement on a list that holds every input is equality of
    total behavior. -/
theorem exhaustive_iff {I O : Type} (xs : List I) (hall : ∀ x, x ∈ xs) (f g : I → O) :
    (∀ x, x ∈ xs → f x = g x) ↔ f = g := by
  constructor
  · intro h; funext x; exact h x (hall x)
  · intro h x _; rw [h]

/-- Agreement on a list that misses an input says nothing about
    that input. -/
theorem nonexhaustive_gap :
    (∀ x, x ∈ [0, 1, 2] → (fun n : Nat => n) x = (fun n : Nat => if n = 3 then 0 else n) x) ∧
    (fun n : Nat => n) ≠ (fun n : Nat => if n = 3 then 0 else n) := by
  refine ⟨by decide, ?_⟩
  intro h
  have := congrFun h 3
  simp at this


/- ## 8. Proof witnesses: a compiler and its passes -/

/-- Expressions over a value type with one variable and binary
    operations named by number. -/
inductive Expr (V : Type) where
  | c : V → Expr V
  | x : Expr V
  | bin : Nat → Expr V → Expr V → Expr V
  deriving DecidableEq

/-- The binary operations of a value type. -/
structure Ops (V : Type) where
  ap : Nat → V → V → V

/-- Source semantics. -/
def Expr.ev {V : Type} (O : Ops V) (v : V) : Expr V → V
  | .c a => a
  | .x => v
  | .bin k a b => O.ap k (a.ev O v) (b.ev O v)

/-- Stack machine instructions. -/
inductive Ins (V : Type) where
  | push : V → Ins V
  | load : Ins V
  | op : Nat → Ins V

/-- The compiler: postfix code. -/
def compile {V : Type} : Expr V → List (Ins V)
  | .c a => [.push a]
  | .x => [.load]
  | .bin k a b => compile a ++ compile b ++ [.op k]

/-- The stack machine. An operation on a short stack is skipped;
    compiled code never reaches that case. -/
def vm {V : Type} (O : Ops V) (v : V) : List (Ins V) → List V → List V
  | [], st => st
  | .push a :: is, st => vm O v is (a :: st)
  | .load :: is, st => vm O v is (v :: st)
  | .op k :: is, b :: a :: st => vm O v is (O.ap k a b :: st)
  | .op _ :: is, [] => vm O v is []
  | .op _ :: is, [a] => vm O v is [a]

/-- Compiled code pushes the source value. -/
theorem compile_correct {V : Type} (O : Ops V) (v : V) :
    ∀ (e : Expr V) (is : List (Ins V)) (st : List V),
      vm O v (compile e ++ is) st = vm O v is (e.ev O v :: st) := by
  intro e
  induction e with
  | c a => intro is st; rfl
  | x => intro is st; rfl
  | bin k a b iha ihb =>
    intro is st
    simp only [compile, List.append_assoc]
    rw [iha, ihb]
    rfl

theorem compile_run {V : Type} (O : Ops V) (v : V) (e : Expr V) :
    vm O v (compile e) [] = [e.ev O v] := by
  have := compile_correct O v e [] []
  simpa using this

/-- Constant folding of one operation. -/
def foldBin {V : Type} (O : Ops V) (k : Nat) : Expr V → Expr V → Expr V
  | .c u, .c w => .c (O.ap k u w)
  | a, b => .bin k a b

theorem foldBin_ev {V : Type} (O : Ops V) (v : V) (k : Nat) (a b : Expr V) :
    (foldBin O k a b).ev O v = O.ap k (a.ev O v) (b.ev O v) := by
  cases a <;> cases b <;> rfl

/-- The folding pass. -/
def fold {V : Type} (O : Ops V) : Expr V → Expr V
  | .bin k a b => foldBin O k (fold O a) (fold O b)
  | e => e

/-- Folding preserves the source value, for every value type: no
    premise. -/
theorem fold_sound {V : Type} (O : Ops V) (v : V) : ∀ e, (fold O e).ev O v = e.ev O v := by
  intro e
  induction e with
  | c a => rfl
  | x => rfl
  | bin k a b iha ihb => simp only [fold, foldBin_ev, iha, ihb, Expr.ev]

/-- A rewrite of `e * k0` (operation `mulK` with a constant right
    argument `k0`) into `rhs e`, applied bottom up. -/
def rewrite {V : Type} [DecidableEq V] (mulK : Nat) (k0 : V) (rhs : Expr V → Expr V) :
    Expr V → Expr V
  | .bin k a b =>
    let a' := rewrite mulK k0 rhs a
    let b' := rewrite mulK k0 rhs b
    if k = mulK ∧ b' = .c k0 then rhs a' else .bin k a' b'
  | e => e

/-- The rewrite is sound when its law holds of the value type. -/
theorem rewrite_sound {V : Type} [DecidableEq V] (O : Ops V) (v : V) (mulK : Nat) (k0 : V)
    (rhs : Expr V → Expr V)
    (law : ∀ e, (rhs e).ev O v = O.ap mulK (e.ev O v) k0) :
    ∀ e, (rewrite mulK k0 rhs e).ev O v = e.ev O v := by
  intro e
  induction e with
  | c a => rfl
  | x => rfl
  | bin k a b iha ihb =>
    simp only [rewrite]
    split
    · rename_i h
      obtain ⟨hk, hb⟩ := h
      rw [law, iha, Expr.ev, hk, ← ihb, hb]
      rfl
    · simp only [Expr.ev, iha, ihb]

/-- And unsound wherever its law fails: one failing value gives a
    program whose result the rewrite changes. -/
theorem rewrite_needs_law {V : Type} [DecidableEq V] (O : Ops V) (mulK : Nat) (k0 : V)
    (rhs : Expr V → Expr V) (u : V)
    (hfail : (rhs (Expr.x)).ev O u ≠ O.ap mulK u k0) :
    (rewrite mulK k0 rhs (.bin mulK .x (.c k0))).ev O u ≠ (Expr.bin mulK Expr.x (Expr.c k0)).ev O u := by
  simp only [rewrite, and_self, if_true]
  exact hfail

end Generalize

#print axioms Generalize.noDecider
#print axioms Generalize.noExactKey
#print axioms Generalize.spelling_sound
#print axioms Generalize.run_mono
#print axioms Generalize.run_mono_le
#print axioms Generalize.outcome_unique
#print axioms Generalize.decisive_persists
#print axioms Generalize.decisive_sound
#print axioms Generalize.decisive_complete
#print axioms Generalize.loop_obs
#print axioms Generalize.diverge_never_decisive
#print axioms Generalize.late_none
#print axioms Generalize.late_halts
#print axioms Generalize.no_uniform_bound
#print axioms Generalize.qualified_sound
#print axioms Generalize.leak_example
#print axioms Generalize.qualified_example
#print axioms Generalize.refine_join
#print axioms Generalize.applied_inj
#print axioms Generalize.tolerance_collapse
#print axioms Generalize.solo_equal
#print axioms Generalize.par_breaks
#print axioms Generalize.exhaustive_iff
#print axioms Generalize.nonexhaustive_gap
#print axioms Generalize.compile_correct
#print axioms Generalize.compile_run
#print axioms Generalize.foldBin_ev
#print axioms Generalize.fold_sound
#print axioms Generalize.rewrite_sound
#print axioms Generalize.rewrite_needs_law
