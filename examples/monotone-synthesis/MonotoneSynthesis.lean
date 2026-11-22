/-
  Monotone synthesis: the admission core of an unattended loop that only
  ever grows a library of composable software artifacts.

  The library is one append-only log. An entry either adds an artifact
  (premises it composes, the capability it provides) or retires an earlier
  artifact in favour of a live replacement. Nothing is deleted: a retired
  artifact stays in the log; it only stops being live.

  What the log can reach is the least closure of the host primitives `P`
  under the live artifacts, `Qualification.Derives` from
  clpi/software-optimality (imported at a pin, not mirrored).

  Admission (the only way an entry gets onto a run):
    add x        the verifier accepts x (`V x`, read from a receipt), its id
                 is fresh, and every premise of x is already reachable.
    retire i n   i and n are live, n is not i, and everything reachable
                 before the retirement is reachable after it.

  Proved here, every hypothesis explicit:
    monotone      reach never shrinks along a run (`run_monotone`), and a
                  live artifact's capability is never lost, retired or not
                  (`capability_never_lost`).
    compounding   readiness persists (`ready_persists`); an admission makes
                  ready every candidate whose missing premises it supplies
                  (`enables`), strictly when the head was new
                  (`enables_strict`); two libraries compose with nothing lost
                  after one reclosure (`compose`, from
                  `ClosureStrength.compounding_sources`), and so does any
                  indexed family (`compose_family`, from
                  `ClosureStrength.compounding_family`).
    generalizing  an abstraction (a composed rule whose head is already
                  derivable from its premises) changes nothing reachable
                  (`abstract_conservative`).
    autonomy      every saturated run reaches exactly the closure of the
                  verified pool, whatever the order of offers and
                  retirements (`saturated_exact`, `order_independent`).
    soundness     if the verifier is faithful, everything reached is true
                  (`reach_sound`); faithfulness is a premise, not a theorem.

  The controls in MonotoneSynthesisControls.lean show each admission check
  is necessary.
-/
import Qualification
import ExecutableClosure
import ClosureStrength

namespace MonotoneSynthesis
open Qualification

universe u v w
variable {A : Type u}

/-- A candidate artifact: an id, the capabilities it composes, and the one
    capability it provides. -/
structure Art (A : Type u) where
  id : Nat
  prem : List A
  head : A
  deriving DecidableEq

/-- An entry of the one append-only log. -/
inductive Entry (A : Type u) where
  | add (x : Art A)
  | retire (i n : Nat)
  deriving DecidableEq

/-- An artifact is live when it was added and never retired. -/
def live (L : List (Entry A)) (x : Art A) : Prop :=
  Entry.add x ∈ L ∧ ∀ n, Entry.retire x.id n ∉ L

/-- The live artifacts as finite-premise rules. -/
def rules (L : List (Entry A)) : List A → A → Prop :=
  fun ps a => ∃ x, live L x ∧ x.prem = ps ∧ x.head = a

/-- What the log can reach from the host primitives `P`. -/
def reach (P : A → Prop) (L : List (Entry A)) : A → Prop :=
  Derives P (rules L)

/-- A candidate the verifier accepts whose premises are all reachable. -/
def Ready (P : A → Prop) (V : Art A → Prop) (L : List (Entry A)) (x : Art A) : Prop :=
  V x ∧ ∀ p, p ∈ x.prem → reach P L p

/-- The admission rule. -/
inductive Admit (P : A → Prop) (V : Art A → Prop) (L : List (Entry A)) : Entry A → Prop where
  | add {x : Art A} :
      V x →
      (∀ y, Entry.add y ∈ L → y.id ≠ x.id) →
      (∀ n, Entry.retire x.id n ∉ L) →
      (∀ p, p ∈ x.prem → reach P L p) →
      Admit P V L (.add x)
  | retire {i n : Nat} :
      (∃ y, live L y ∧ y.id = i) →
      (∃ z, live L z ∧ z.id = n) →
      n ≠ i →
      (∀ a, reach P L a → reach P (L ++ [.retire i n]) a) →
      Admit P V L (.retire i n)

/-- A run: entries appended one at a time, each admitted against the log
    before it. -/
inductive Run (P : A → Prop) (V : Art A → Prop) : List (Entry A) → Prop where
  | nil : Run P V []
  | snoc {L : List (Entry A)} {e : Entry A} : Run P V L → Admit P V L e → Run P V (L ++ [e])

section Basics
variable {P : A → Prop} {V : Art A → Prop}

/-- Induction from the right, over appended singletons. -/
theorem snoc_induction {α : Type w} {motive : List α → Prop} (nil : motive [])
    (snoc : ∀ l a, motive l → motive (l ++ [a])) : ∀ l, motive l := by
  intro l
  have : ∀ r : List α, motive r.reverse := by
    intro r
    induction r with
    | nil => exact nil
    | cons a r ih => simpa using snoc _ a ih
  simpa using this l.reverse

theorem run_snoc_inv' : ∀ {L' : List (Entry A)}, Run P V L' →
    ∀ (L : List (Entry A)) (e : Entry A), L' = L ++ [e] → Run P V L ∧ Admit P V L e := by
  intro L' h
  cases h with
  | nil => intro L e heq; exact absurd heq.symm (by simp)
  | snoc hr ha =>
    intro L e heq
    obtain ⟨rfl, h2⟩ := List.append_inj' heq rfl
    cases h2
    exact ⟨hr, ha⟩

theorem run_snoc_inv {L : List (Entry A)} {e : Entry A} (h : Run P V (L ++ [e])) :
    Run P V L ∧ Admit P V L e := run_snoc_inv' h L e rfl

theorem run_prefix (L : List (Entry A)) : ∀ (M : List (Entry A)), Run P V (L ++ M) → Run P V L := by
  refine snoc_induction (fun h => by simpa using h) ?_
  intro M e ih h
  rw [← List.append_assoc] at h
  exact ih (run_snoc_inv h).1

/-- Appending an add keeps every live artifact live. -/
theorem live_add {L : List (Entry A)} {x y : Art A} (h : live L y) : live (L ++ [.add x]) y := by
  refine ⟨List.mem_append_left _ h.1, fun n hn => ?_⟩
  rcases List.mem_append.mp hn with hn | hn
  · exact h.2 n hn
  · simp at hn

/-- Live after a step: live before, or the artifact the step added. -/
theorem live_snoc {L : List (Entry A)} {e : Entry A} {x : Art A} (h : live (L ++ [e]) x) :
    live L x ∨ e = .add x := by
  rcases List.mem_append.mp h.1 with hm | hm
  · exact Or.inl ⟨hm, fun n hn => h.2 n (List.mem_append_left _ hn)⟩
  · simp at hm
    exact Or.inr hm.symm

theorem rules_add (L : List (Entry A)) (x : Art A) (ps : List A) (a : A) (h : rules L ps a) :
    rules (L ++ [.add x]) ps a := by
  obtain ⟨y, hy, h1, h2⟩ := h
  exact ⟨y, live_add hy, h1, h2⟩

end Basics

/-! ## Monotone -/

section Monotone
variable {P : A → Prop} {V : Art A → Prop}

/-- One admitted step never shrinks what is reachable. The add case is
    `Qualification.monotone`; the retire case is its admission clause. -/
theorem step_monotone {L : List (Entry A)} {e : Entry A} (h : Admit P V L e) :
    ∀ a, reach P L a → reach P (L ++ [e]) a := by
  cases h with
  | add _ _ _ _ =>
    exact monotone (fun _ h => h) (fun ps a h => rules_add L _ ps a h)
  | retire _ _ _ cover => exact cover

/-- Along any run, what a prefix reaches the whole run reaches. -/
theorem run_monotone (L : List (Entry A)) : ∀ (M : List (Entry A)), Run P V (L ++ M) →
    ∀ a, reach P L a → reach P (L ++ M) a := by
  refine snoc_induction (fun _ a h => by simpa using h) ?_
  intro M e ih h a ha
  rw [← List.append_assoc] at h ⊢
  have k := run_snoc_inv h
  exact step_monotone k.2 a (ih k.1 a ha)

/-- Every artifact on a run passed the verifier. -/
theorem run_verified : ∀ {L : List (Entry A)}, Run P V L → ∀ x, Entry.add x ∈ L → V x := by
  intro L h
  induction h with
  | nil => intro x hx; simp at hx
  | snoc _ ha ih =>
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact ih x hx
    · simp at hx
      subst hx
      cases ha with
      | add hv _ _ _ => exact hv

/-- Every live artifact's capability is reachable: no admitted artifact is
    dead. -/
theorem live_heads_reach : ∀ {L : List (Entry A)}, Run P V L →
    ∀ x, live L x → reach P L x.head := by
  intro L h
  induction h with
  | nil => intro x hx; simp [live] at hx
  | @snoc L e hr ha ih =>
    intro x hx
    rcases live_snoc hx with hl | he
    · exact step_monotone ha _ (ih x hl)
    · subst he
      cases ha with
      | add h1 h2 h3 hp =>
        exact .step ⟨x, hx, rfl, rfl⟩
          (fun p hpm => step_monotone (Admit.add h1 h2 h3 hp) p (hp p hpm))

/-- No capability an artifact ever provided is lost: once live at some
    prefix, its head stays reachable for the rest of the run, whether or
    not the artifact is later retired. -/
theorem capability_never_lost (L M : List (Entry A)) (h : Run P V (L ++ M))
    (x : Art A) (hx : live L x) : reach P (L ++ M) x.head :=
  run_monotone L M h _ (live_heads_reach (run_prefix L M h) x hx)

/-- A retirement is only ever admitted with a replacement that is live and
    distinct, and with everything reachable preserved. -/
theorem retire_has_replacement {L : List (Entry A)} {i n : Nat}
    (h : Admit P V L (.retire i n)) :
    (∃ z, live L z ∧ z.id = n) ∧ n ≠ i ∧ ∀ a, reach P L a → reach P (L ++ [.retire i n]) a := by
  cases h with
  | retire _ hz hne cover => exact ⟨hz, hne, cover⟩

end Monotone

/-! ## A decidable sufficient condition for a covering replacement -/

section Replace
variable {P : A → Prop}

/-- Retiring artifact `y` in favour of a live `z` with the same head, all of
    whose premises stay reachable without `y`, preserves everything
    reachable. This is what an executable checker tests in place of the
    semantic coverage clause. -/
theorem replace_covers (L : List (Entry A)) (y z : Art A) (n : Nat)
    (hz : live L z) (hzn : z.id = n) (hne : n ≠ y.id) (hhead : z.head = y.head)
    (hprem : ∀ p, p ∈ z.prem → reach P (L ++ [.retire y.id n]) p)
    (uniq : ∀ w, Entry.add w ∈ L → w.id = y.id → w = y) :
    ∀ a, reach P L a → reach P (L ++ [.retire y.id n]) a := by
  refine least (X := reach P (L ++ [.retire y.id n])) (fun a h => .root h) ?_
  intro ps a ⟨w, hw, hps, ha⟩ hp
  subst hps; subst ha
  by_cases hid : w.id = y.id
  · have hwy : w = y := uniq w hw.1 hid
    subst hwy
    have zl : live (L ++ [.retire w.id n]) z := by
      refine ⟨List.mem_append_left _ hz.1, fun m hm => ?_⟩
      rcases List.mem_append.mp hm with hm | hm
      · exact hz.2 m hm
      · simp at hm
        exact hne (hzn ▸ hm.1)
    rw [← hhead]
    exact .step ⟨z, zl, rfl, rfl⟩ hprem
  · have wl : live (L ++ [.retire y.id n]) w := by
      refine ⟨List.mem_append_left _ hw.1, fun m hm => ?_⟩
      rcases List.mem_append.mp hm with hm | hm
      · exact hw.2 m hm
      · simp at hm
        exact hid hm.1
    exact .step ⟨w, wl, rfl, rfl⟩ hp

end Replace

/-! ## An executable checker, proved against the spec

`ExecutableClosure.close` (software-optimality) decides reach exactly on a
bounded universe (`close_exact`); the checks below are Boolean, and each is
proved to imply the corresponding admission clause. The closure here
enumerates subsets of the universe, so it is for small controls; the loop on
real data uses the worklist and is checked against a from-scratch spec. -/

section Executable
variable {A : Type} [DecidableEq A]

def notRetired (L : List (Entry A)) (i : Nat) : Bool :=
  L.all (fun e => match e with | .retire j _ => j != i | .add _ => true)

def liveB (L : List (Entry A)) (x : Art A) : Bool :=
  decide (Entry.add x ∈ L) && notRetired L x.id

omit [DecidableEq A] in
theorem notRetired_iff (L : List (Entry A)) (i : Nat) :
    notRetired L i = true ↔ ∀ n, Entry.retire i n ∉ L := by
  unfold notRetired
  rw [List.all_eq_true]
  constructor
  · intro h n hn
    have := h _ hn
    simp at this
  · intro h e he
    cases e with
    | add _ => rfl
    | retire j m =>
      simp only [bne_iff_ne, ne_eq]
      intro hj
      subst hj
      exact h m he

theorem liveB_iff (L : List (Entry A)) (x : Art A) : liveB L x = true ↔ live L x := by
  simp only [liveB, Bool.and_eq_true, decide_eq_true_eq, notRetired_iff, live]

def ruleList (L : List (Entry A)) : List (List A × A) :=
  L.filterMap (fun e => match e with
    | .add x => if liveB L x then some (x.prem, x.head) else none
    | .retire _ _ => none)

theorem rules_iff (L : List (Entry A)) (ps : List A) (a : A) :
    rules L ps a ↔ (ps, a) ∈ ruleList L := by
  unfold ruleList rules
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨x, hx, rfl, rfl⟩
    exact ⟨.add x, hx.1, by simp [(liveB_iff L x).mpr hx]⟩
  · rintro ⟨e, he, hm⟩
    cases e with
    | retire _ _ => simp at hm
    | add x =>
      by_cases hl : liveB L x = true
      · simp [hl] at hm
        obtain ⟨rfl, rfl⟩ := hm
        exact ⟨x, (liveB_iff L x).mp hl, rfl, rfl⟩
      · simp [hl] at hm

/-- The universe bound `close_exact` needs: every root and live head is in
    `U`. -/
def boundedB (U B : List A) (L : List (Entry A)) : Bool :=
  B.all (fun a => U.contains a) && (ruleList L).all (fun r => U.contains r.2)

theorem reach_iff_close (U B : List A) (L : List (Entry A)) (hb : boundedB U B L = true) (a : A) :
    reach (fun a => a ∈ B) L a ↔ a ∈ ExecutableClosure.close U B (ruleList L) := by
  simp only [boundedB, Bool.and_eq_true, List.all_eq_true, List.contains_iff] at hb
  rw [ExecutableClosure.close_exact U B (ruleList L) hb.1 (fun ps a h => hb.2 (ps, a) h)]
  exact ClosureStrength.derives_congr (fun _ => Iff.rfl) (fun ps a => rules_iff L ps a) a

def freshB (L : List (Entry A)) (i : Nat) : Bool :=
  L.all (fun e => match e with | .add y => y.id != i | .retire j _ => j != i)

/-- Executable add check: fresh id, never retired, premises reachable. The
    verdict `V x` is a separate input read from a receipt. -/
def admitAddB (U B : List A) (L : List (Entry A)) (x : Art A) : Bool :=
  boundedB U B L && freshB L x.id &&
    x.prem.all (fun p => (ExecutableClosure.close U B (ruleList L)).contains p)

theorem admitAddB_sound (V : Art A → Prop) (U B : List A) (L : List (Entry A)) (x : Art A)
    (hv : V x) (h : admitAddB U B L x = true) : Admit (fun a => a ∈ B) V L (.add x) := by
  simp only [admitAddB, Bool.and_eq_true] at h
  obtain ⟨⟨hb, hf⟩, hp⟩ := h
  unfold freshB at hf
  rw [List.all_eq_true] at hf hp
  refine .add hv (fun y hy => ?_) (fun n hn => ?_) (fun p hpm => ?_)
  · have := hf _ hy; simpa using this
  · have := hf _ hn; simp at this
  · exact (reach_iff_close U B L hb p).mpr (List.contains_iff.mp (hp p hpm))

/-- Executable replacement check: retire the unique artifact `y` with id `i`
    for a live `z` with id `n ≠ i`, same head, premises reachable after the
    retirement. -/
def replaceB (U B : List A) (L : List (Entry A)) (y z : Art A) (n : Nat) : Bool :=
  liveB L y && liveB L z && decide (z.id = n) && decide (n ≠ y.id) && decide (z.head = y.head) &&
    L.all (fun e => match e with | .add w => (w.id != y.id) || decide (w = y) | .retire _ _ => true) &&
    boundedB U B (L ++ [.retire y.id n]) &&
    z.prem.all (fun p => (ExecutableClosure.close U B (ruleList (L ++ [.retire y.id n]))).contains p)

theorem replaceB_sound (V : Art A → Prop) (U B : List A) (L : List (Entry A)) (y z : Art A) (n : Nat)
    (h : replaceB U B L y z n = true) : Admit (fun a => a ∈ B) V L (.retire y.id n) := by
  simp only [replaceB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hy, hz⟩, hzn⟩, hne⟩, hhead⟩, huniq⟩, hb⟩, hp⟩ := h
  have yl := (liveB_iff L y).mp hy
  have zl := (liveB_iff L z).mp hz
  rw [List.all_eq_true] at huniq hp
  have uniq : ∀ w, Entry.add w ∈ L → w.id = y.id → w = y := by
    intro w hw hid
    have := huniq _ hw
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at this
    exact this.resolve_left (fun h => h hid)
  refine .retire ⟨y, yl, rfl⟩ ⟨z, zl, hzn⟩ hne ?_
  exact replace_covers L y z n zl hzn hne hhead
    (fun p hpm => (reach_iff_close U B _ hb p).mpr (List.contains_iff.mp (hp p hpm))) uniq

end Executable

/-! ## Compounding -/

section Compounding
variable {P : A → Prop} {V : Art A → Prop}

/-- Readiness persists: a candidate ready now is ready at every later point
    of the run. A refused candidate can only become ready; an admissible
    one never stops being admissible (fresh id aside). -/
theorem ready_persists (L M : List (Entry A)) (h : Run P V (L ++ M)) (x : Art A)
    (hx : Ready P V L x) : Ready P V (L ++ M) x :=
  ⟨hx.1, fun p hp => run_monotone L M h p (hx.2 p hp)⟩

/-- An admission supplies its head: every verified candidate whose premises
    are reachable or equal to the new head is ready afterwards. -/
theorem enables {L : List (Entry A)} {x : Art A} (ha : Admit P V L (.add x))
    (y : Art A) (hv : V y) (hp : ∀ p, p ∈ y.prem → reach P L p ∨ p = x.head) :
    Ready P V (L ++ [.add x]) y := by
  have hx : reach P (L ++ [.add x]) x.head := by
    cases ha with
    | add h1 h2 h3 hq =>
      have xl : live (L ++ [.add x]) x :=
        ⟨List.mem_append_right _ (by simp), fun n hn => by
          rcases List.mem_append.mp hn with hn | hn
          · exact h3 n hn
          · simp at hn⟩
      exact .step ⟨x, xl, rfl, rfl⟩
        (fun q hq' => step_monotone (Admit.add h1 h2 h3 hq) q (hq q hq'))
  refine ⟨hv, fun p hpm => ?_⟩
  rcases hp p hpm with hr | rfl
  · exact step_monotone ha p hr
  · exact hx

/-- Strictly: if the head was not reachable before and the candidate needs
    it, the candidate was not ready before and is ready after. -/
theorem enables_strict {L : List (Entry A)} {x : Art A} (ha : Admit P V L (.add x))
    (hnew : ¬ reach P L x.head)
    (y : Art A) (hv : V y) (hneed : x.head ∈ y.prem)
    (hp : ∀ p, p ∈ y.prem → reach P L p ∨ p = x.head) :
    ¬ Ready P V L y ∧ Ready P V (L ++ [.add x]) y :=
  ⟨fun hr => hnew (hr.2 _ hneed), enables ha y hv hp⟩

/-- Composition of two libraries loses nothing: reaching under the joint
    rules from the primitives equals reaching under the joint rules from
    what each library reaches on its own. An instance of
    `ClosureStrength.compounding_sources`. -/
theorem compose (L M : List (Entry A)) (a : A) :
    Derives P (fun ps x => rules L ps x ∨ rules M ps x) a ↔
      Derives (fun x => reach P L x ∨ reach P M x) (fun ps x => rules L ps x ∨ rules M ps x) a := by
  have k := ClosureStrength.compounding_sources P P (rules L) (rules M) a
  have e : ∀ x, (P x ∨ P x) ↔ P x := fun _ => ⟨fun h => h.elim id id, Or.inl⟩
  exact (ClosureStrength.derives_congr (fun x => (e x).symm) (fun _ _ => Iff.rfl) a).trans k

/-- Any indexed family of libraries (one per parameter value) composes the
    same way. An instance of `ClosureStrength.compounding_family`. -/
theorem compose_family {I : Sort v} (Ls : I → List (Entry A)) (hI : Nonempty I) (a : A) :
    Derives P (fun ps x => ∃ i, rules (Ls i) ps x) a ↔
      Derives (fun x => ∃ i, reach P (Ls i) x) (fun ps x => ∃ i, rules (Ls i) ps x) a := by
  have k := ClosureStrength.compounding_family (fun _ : I => P) (fun i => rules (Ls i)) a
  have e : ∀ x, (∃ _ : I, P x) ↔ P x := fun _ =>
    ⟨fun ⟨_, h⟩ => h, fun h => hI.elim (fun i => ⟨i, h⟩)⟩
  exact (ClosureStrength.derives_congr (fun x => (e x).symm) (fun _ _ => Iff.rfl) a).trans k

/-- Readiness under composition: anything ready in either library is ready
    in the composed one. -/
theorem compose_reach_left (L M : List (Entry A)) (a : A) (h : reach P L a) :
    Derives P (fun ps x => rules L ps x ∨ rules M ps x) a :=
  monotone (fun _ h => h) (fun _ _ h => Or.inl h) a h

end Compounding

/-! ## Generalizing: abstractions are conservative -/

section Abstraction
variable {P : A → Prop}

/-- An abstraction is a composed rule `x` whose head is already derivable
    from its premises under the live rules. Appending it (fresh, never
    retired) changes nothing reachable: it can only shorten derivations. -/
theorem abstract_conservative (L : List (Entry A)) (x : Art A)
    (hderiv : Derives (fun b => P b ∨ b ∈ x.prem) (rules L) x.head) (a : A) :
    reach P (L ++ [.add x]) a ↔ reach P L a := by
  constructor
  · refine least (X := reach P L) (fun a h => .root h) ?_ a
    intro ps b ⟨w, hw, hps, hb⟩ hp
    subst hps; subst hb
    rcases live_snoc hw with hl | he
    · exact .step ⟨w, hl, rfl, rfl⟩ hp
    · have hxw : x = w := by injection he
      subst hxw
      have k : Derives (reach P L) (rules L) x.head :=
        monotone (B := fun b => P b ∨ b ∈ x.prem)
          (fun b hb => hb.elim (fun h => .root h) (fun h => hp b h)) (fun _ _ h => h) _ hderiv
      exact (idempotent P (rules L) _).mp k
  · exact monotone (fun _ h => h) (fun ps b h => rules_add L x ps b h) a

end Abstraction

/-! ## Autonomy: saturated runs are order independent -/

section Saturation
variable {P : A → Prop} {V : Art A → Prop}

/-- Every added artifact came from the candidate pool `C`. -/
def From (C : Art A → Prop) (L : List (Entry A)) : Prop := ∀ x, Entry.add x ∈ L → C x

/-- No verified candidate is left whose premises are reachable but whose
    head is not: the loop has nothing ready left to take in. -/
def Saturated (P : A → Prop) (V : Art A → Prop) (C : Art A → Prop) (L : List (Entry A)) : Prop :=
  ∀ y, C y → V y → (∀ p, p ∈ y.prem → reach P L p) → reach P L y.head

/-- The closure of the verified pool, independent of any run. -/
def target (P : A → Prop) (V : Art A → Prop) (C : Art A → Prop) : A → Prop :=
  Derives P (fun ps a => ∃ y, C y ∧ V y ∧ y.prem = ps ∧ y.head = a)

/-- A saturated run reaches exactly the closure of the verified pool, for
    any order of offers, any interleaving of retirements, any retries. -/
theorem saturated_exact {L : List (Entry A)} (C : Art A → Prop) (hrun : Run P V L)
    (hfrom : From C L) (hsat : Saturated P V C L) (a : A) :
    reach P L a ↔ target P V C a := by
  constructor
  · exact monotone (fun _ h => h)
      (fun ps b ⟨x, hx, h1, h2⟩ => ⟨x, hfrom x hx.1, run_verified hrun x hx.1, h1, h2⟩) a
  · refine least (X := reach P L) (fun a h => .root h) ?_ a
    intro ps b ⟨y, hc, hv, h1, h2⟩ hp
    subst h1; subst h2
    exact hsat y hc hv hp

/-- Two saturated runs over the same pool reach the same capabilities,
    however differently they were ordered. -/
theorem order_independent {L M : List (Entry A)} (C : Art A → Prop)
    (hL : Run P V L) (fL : From C L) (sL : Saturated P V C L)
    (hM : Run P V M) (fM : From C M) (sM : Saturated P V C M) (a : A) :
    reach P L a ↔ reach P M a :=
  (saturated_exact C hL fL sL a).trans (saturated_exact C hM fM sM a).symm

/-- Saturation is monotone in the run once reached? No: a later retirement
    keeps reach, so saturation is kept along any further run from the pool. -/
theorem saturated_persists (C : Art A → Prop) (L M : List (Entry A))
    (h : Run P V (L ++ M)) (hs : Saturated P V C L) (hfrom : From C (L ++ M)) :
    Saturated P V C (L ++ M) := by
  intro y hc hv hp
  have hL := run_prefix L M h
  have fL : From C L := fun x hx => hfrom x (List.mem_append_left _ hx)
  have k1 : ∀ b, reach P (L ++ M) b ↔ target P V C b := by
    intro b
    constructor
    · exact monotone (fun _ h => h)
        (fun ps c ⟨x, hx, h1, h2⟩ => ⟨x, hfrom x hx.1, run_verified h x hx.1, h1, h2⟩) b
    · intro hb
      exact run_monotone L M h b ((saturated_exact C hL fL hs b).mpr hb)
  exact (k1 _).mpr (.step ⟨y, hc, hv, rfl, rfl⟩ (fun p hpm => (k1 p).mp (hp p hpm)))

end Saturation

/-! ## Soundness, conditional on a faithful verifier -/

section Soundness
variable {P : A → Prop} {V : Art A → Prop}

/-- If the host primitives are true and the verifier only accepts artifacts
    that preserve truth, everything a run reaches is true. Faithfulness of
    `V` is the premise; nothing here proves it. -/
theorem reach_sound (T : A → Prop) (hp : ∀ a, P a → T a)
    (faithful : ∀ x, V x → (∀ p, p ∈ x.prem → T p) → T x.head)
    {L : List (Entry A)} (h : Run P V L) : ∀ a, reach P L a → T a :=
  soundness hp (fun ps a ⟨x, hx, h1, h2⟩ hps => by
    subst h1; subst h2; exact faithful x (run_verified h x hx.1) hps)

end Soundness

#print axioms run_monotone
#print axioms capability_never_lost
#print axioms live_heads_reach
#print axioms retire_has_replacement
#print axioms replace_covers
#print axioms ready_persists
#print axioms enables
#print axioms enables_strict
#print axioms compose
#print axioms compose_family
#print axioms compose_reach_left
#print axioms abstract_conservative
#print axioms saturated_exact
#print axioms order_independent
#print axioms saturated_persists
#print axioms reach_sound
#print axioms reach_iff_close
#print axioms admitAddB_sound
#print axioms replaceB_sound

end MonotoneSynthesis
