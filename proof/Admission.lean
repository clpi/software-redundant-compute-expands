/-
Admission: claims on the one append-only log can only be appended with
premises bound to recorded behavior. A gamed claim is refused at append
time by the log's own admission rule, not detected afterwards.

Shape of the log (positions are append order; every reference points
backward, to a smaller position):

  dim dom d            dimension d is part of domain dom (anyone may add one;
                       never removed). Claims quantify over all of them.
  work dom w bytes     development workload w of dom.
  config dom c         a comparator configuration. The merged peak of a
                       domain is the best correct sample of every config.
  null dom n           the do-nothing subject of dom.
  contract dom h s f r measurement contract: harness hash h, sealed
                       held-out hash s, absolute floor f, repeats r.
                       One per domain, fixed before any build of it.
  build dom s inputs   subject s, built from earlier records.
  run k s w d h t      a measurement under contract k. It has NO value
                       field: the kernel reads correctness and samples
                       from the trace t. A self-reported number cannot be
                       written down at all.
  reveal k w bytes     held-out workload, accepted only if its bytes hash
                       to the contract's seal.
  derive g inputs      derived data. The output is not stored; it is the
                       generator applied to the inputs.
  fact evidence        a statement about behavior. Its evidence must be
                       runs, or data derived only from runs.
  claim dom s          s beats the merged peak of dom on every registered
                       dimension and every workload, held-out included.

Named premises (not theorems here):
  P1  H is collision resistant on the blobs that occur (the concrete H
      below is not; the Idol kernel uses idol-lib's sha256).
  P2  okT and the samples in a trace are what the harness observed: the
      harness bytes are bound by hash, their faithfulness is not proved.
  P3  the sealer of the held-out bytes did not show them to the builder
      before the reveal (commit then reveal; the seal binds bytes, not
      secrecy).
  P4  every dimension that matters for dom has been registered by
      someone. A claim says nothing about unregistered dimensions, and a
      claimant can still open a new domain with fewer dimensions; its
      claims then only speak about that domain.
-/

namespace Admission

abbrev Blob := List Nat

/-- Content hash used by this model. Concrete so that every check
computes; collision resistance is premise P1. -/
def H (b : Blob) : Nat :=
  b.foldl (fun h x => (h * 1000003 + x + 1) % 4294967311) 7

/-- Trace layout: first cell 1 iff the output matched the expected output,
then the samples, lower is better. -/
def okT (t : Blob) : Bool := t.head? == some 1
def worstT (t : Blob) : Nat := (t.drop 1).foldl max 0
def bestT (t : Blob) : Nat := (t.drop 1).foldl min (worstT t)

inductive Rec where
  | dim (dom d : Nat)
  | work (dom w : Nat) (input : Blob)
  | config (dom c : Nat)
  | null (dom n : Nat)
  | contract (dom harness sealed floor reps : Nat)
  | build (dom s : Nat) (inputs : List Nat)
  | run (k s w d : Nat) (harness trace : Blob)
  | reveal (k w : Nat) (input : Blob)
  | derive (gen : Nat) (inputs : List Nat)
  | fact (evidence : List Nat)
  | claim (dom s : Nat)
  deriving DecidableEq, Repr

/-- Each admission check, by name. `none` switches nothing off; any other
value switches exactly that check off (used only to show each check is
necessary). -/
inductive Check where
  | none | contractOnce | buildAfterContract | buildLeak | runRegistered
  | runHarness | runSubject | revealSeal | factGrounded
  | heldout | cover | correct | peak | margin | merged | nullBase
  deriving DecidableEq, Repr

section views
variable (g : List Rec)

def dimsOf (dom : Nat) : List Nat :=
  g.filterMap fun r => match r with
    | .dim d' x => if d' == dom then some x else none
    | _ => none

def devWorks (dom : Nat) : List Nat :=
  g.filterMap fun r => match r with
    | .work d' w _ => if d' == dom then some w else none
    | _ => none

def revealedWorks (k : Nat) : List Nat :=
  g.filterMap fun r => match r with
    | .reveal k' w _ => if k' == k then some w else none
    | _ => none

def worksOf (dom k : Nat) : List Nat := devWorks g dom ++ revealedWorks g k

def configsOf (dom : Nat) : List Nat :=
  g.filterMap fun r => match r with
    | .config d' c => if d' == dom then some c else none
    | _ => none

def nullOf (dom : Nat) : Option Nat :=
  (g.filterMap fun r => match r with
    | .null d' n => if d' == dom then some n else none
    | _ => none).head?

def isContractOf (dom i : Nat) : Bool :=
  match g[i]? with
  | some (.contract d' _ _ _ _) => d' == dom
  | _ => false

def contractIdx (dom : Nat) : Option Nat :=
  (List.range g.length).find? (isContractOf g dom)

def isBuildOf (dom s i : Nat) : Bool :=
  match g[i]? with
  | some (.build d' s' _) => d' == dom && s' == s
  | _ => false

def buildIdx (dom s : Nat) : Option Nat :=
  (List.range g.length).find? (isBuildOf g dom s)

def subjectIn (dom s : Nat) : Bool :=
  (buildIdx g dom s).isSome || (configsOf g dom).contains s || nullOf g dom == some s

def isRevealOf (k i : Nat) : Bool :=
  match g[i]? with
  | some (.reveal k' _ _) => k' == k
  | _ => false

def runsOf (k s w d : Nat) : List Blob :=
  g.filterMap fun r => match r with
    | .run k' s' w' d' _ t =>
        if k' == k && s' == s && w' == w && d' == d then some t else none
    | _ => none

def nullRuns (k n w : Nat) : List Blob :=
  g.filterMap fun r => match r with
    | .run k' s' w' _ _ t => if k' == k && s' == n && w' == w then some t else none
    | _ => none

/-- The contract index a record belongs to, if it is a run or a reveal. -/
def contractOfRec : Rec → Option Nat
  | .run k _ _ _ _ _ => some k
  | .reveal k _ _ => some k
  | _ => none

/-- Does record i, or anything it was derived or built from, carry a run
trace or held-out bytes of contract k? (answer leakage into a subject) -/
def leaks (k : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | fuel + 1, i =>
    match g[i]? with
    | some (.run k' _ _ _ _ _) => k' == k
    | some (.reveal k' _ _) => k' == k
    | some (.derive _ ins) => ins.any (leaks k fuel)
    | some (.build _ _ ins) => ins.any (leaks k fuel)
    | some _ => false
    | none => true

/-- Evidence grounded in behavior: a run, or data derived only from
grounded records. A workload's bytes or any other literal is not. -/
def grounded : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, i =>
    match g[i]? with
    | some (.run _ _ _ _ _ _) => true
    | some (.derive _ ins) => ins != [] && ins.all (fun j => decide (j < i) && grounded fuel j)
    | _ => false

end views

def on (off c : Check) (b : Bool) : Bool := off == c || b

/-- The pairs a claim must win: subject worst sample plus floor below every
correct sample of every comparator config (the merged peak). With `merged`
switched off only the first config is compared. -/
def cfgSet (off : Check) (cs : List Nat) : List Nat :=
  if off == .merged then cs.take 1 else cs

def claimChecks (off : Check) (g : List Rec) (dom s : Nat) : Bool :=
  match contractIdx g dom with
  | none => false
  | some k =>
    match g[k]? with
    | some (.contract _ _ _ fl rp) =>
      match buildIdx g dom s with
      | none => false
      | some b =>
        let ws := worksOf g dom k
        let ds := dimsOf g dom
        let cs := cfgSet off (configsOf g dom)
        on off .heldout ((List.range g.length).any fun i => decide (b < i) && isRevealOf g k i) &&
        on off .cover (ws != [] && ds != [] &&
          ws.all fun w => ds.all fun d => decide (rp ≤ (runsOf g k s w d).length)) &&
        on off .correct (ws.all fun w => ds.all fun d => (runsOf g k s w d).all okT) &&
        on off .peak (ws.all fun w => ds.all fun d =>
          cs.any fun c => (runsOf g k c w d).any okT) &&
        on off .margin (ws.all fun w => ds.all fun d =>
          (runsOf g k s w d).all fun t => cs.all fun c =>
            (runsOf g k c w d).all fun t' => !okT t' || decide (worstT t + fl < bestT t')) &&
        on off .nullBase (match nullOf g dom with
          | none => false
          | some n => ws.all fun w =>
              nullRuns g k n w != [] && (nullRuns g k n w).all fun t => !okT t)
    | _ => false

def acceptW (off : Check) (g : List Rec) : Rec → Bool
  | .dim _ _ => true
  | .work dom w _ => !(devWorks g dom).contains w
  | .config _ _ => true
  | .null dom _ => (nullOf g dom).isNone
  | .contract dom _ _ _ rp =>
      on off .contractOnce (contractIdx g dom).isNone && decide (1 ≤ rp)
  | .build dom s ins =>
      ins.all (fun j => decide (j < g.length)) && !subjectIn g dom s &&
      on off .buildAfterContract (contractIdx g dom).isSome &&
      on off .buildLeak (match contractIdx g dom with
        | none => true
        | some k => !(ins.any (leaks g k g.length)))
  | .run k s w d h t =>
      match g[k]? with
      | some (.contract dom hh _ _ _) =>
          on off .runRegistered ((dimsOf g dom).contains d &&
            ((devWorks g dom).contains w || (revealedWorks g k).contains w)) &&
          on off .runHarness (H h == hh) &&
          on off .runSubject (subjectIn g dom s) &&
          decide (2 ≤ t.length)
      | _ => false
  | .reveal k w inp =>
      match g[k]? with
      | some (.contract dom _ se _ _) =>
          on off .revealSeal (H inp == se) && !(revealedWorks g k).contains w &&
          !(devWorks g dom).contains w
      | _ => false
  | .derive _ ins => ins.all (fun j => decide (j < g.length))
  | .fact ev => ev != [] && on off .factGrounded (ev.all (grounded g g.length))
  | .claim dom s => claimChecks off g dom s

abbrev accepts := acceptW .none

/-! ## Append-only growth -/

def append (g : List Rec) (r : Rec) : Option (List Rec) :=
  if accepts g r then some (g ++ [r]) else none

inductive Reach : List Rec → Prop where
  | nil : Reach []
  | step {g : List Rec} {r : Rec} : Reach g → accepts g r = true → Reach (g ++ [r])

/-- Replay a whole log through the admission rule. -/
def replay : List Rec → List Rec → Option (List Rec)
  | g, [] => some g
  | g, r :: rs => match append g r with
    | some g' => replay g' rs
    | none => none

theorem replay_reach : ∀ (rs g g' : List Rec), Reach g → replay g rs = some g' → Reach g'
  | [], g, g', h, e => by simp [replay] at e; exact e ▸ h
  | r :: rs, g, g', h, e => by
      unfold replay at e
      unfold append at e
      by_cases hr : accepts g r = true
      · rw [if_pos hr] at e
        exact replay_reach rs (g ++ [r]) g' (Reach.step h hr) e
      · rw [if_neg hr] at e
        exact absurd e (by simp)

/-- By construction: every record of a reachable log was accepted against
exactly the prefix in front of it. Nothing enters any other way. -/
theorem reach_accepted : ∀ {g : List Rec}, Reach g →
    ∀ (i : Nat) (r : Rec), g[i]? = some r → accepts (g.take i) r = true := by
  intro g h
  induction h with
  | nil => intro i r e; simp at e
  | @step g r' _ hr ih =>
    intro i r e
    by_cases hi : i < g.length
    · rw [List.getElem?_append_left hi] at e
      rw [List.take_append_of_le_length (Nat.le_of_lt hi)]
      exact ih i r e
    · have hge : g.length ≤ i := Nat.le_of_not_lt hi
      rw [List.getElem?_append_right hge] at e
      have hz : i - g.length = 0 := by
        cases Nat.lt_or_ge (i - g.length) 1 with
        | inl h1 => omega
        | inr h1 =>
          rw [List.getElem?_eq_none (by simpa using h1)] at e
          exact absurd e (by simp)
      rw [hz] at e
      simp at e
      have hieq : i = g.length := by omega
      subst hieq
      rw [List.take_left]
      exact e ▸ hr

/-! ## What an accepted claim means, stated without the checker -/

/-- Declarative meaning of a claim on prefix g: contract and build exist,
held-out was revealed after the build, every registered workload and
dimension has the required repeats, every subject run is correct, some
comparator ran correctly on every cell, every subject sample plus floor
beats every correct comparator sample, and the do-nothing subject ran on
every workload and failed every time. -/
def ClaimSpec (g : List Rec) (dom s : Nat) : Prop :=
  ∃ k hh se fl rp b,
    contractIdx g dom = some k ∧ g[k]? = some (.contract dom hh se fl rp) ∧
    buildIdx g dom s = some b ∧
    (∃ i, i < g.length ∧ b < i ∧ isRevealOf g k i = true) ∧
    worksOf g dom k ≠ [] ∧ dimsOf g dom ≠ [] ∧
    (∀ w ∈ worksOf g dom k, ∀ d ∈ dimsOf g dom,
      rp ≤ (runsOf g k s w d).length ∧
      (∀ t ∈ runsOf g k s w d, okT t = true) ∧
      (∃ c ∈ configsOf g dom, ∃ t ∈ runsOf g k c w d, okT t = true) ∧
      (∀ t ∈ runsOf g k s w d, ∀ c ∈ configsOf g dom, ∀ t' ∈ runsOf g k c w d,
        okT t' = true → worstT t + fl < bestT t')) ∧
    (∃ n, nullOf g dom = some n ∧ ∀ w ∈ worksOf g dom k,
      nullRuns g k n w ≠ [] ∧ ∀ t ∈ nullRuns g k n w, okT t = false)

theorem contract_dom {g : List Rec} {dom k : Nat} (h : contractIdx g dom = some k) :
    isContractOf g dom k = true := by
  unfold contractIdx at h
  exact List.find?_some h

theorem claim_spec {g : List Rec} {dom s : Nat} :
    claimChecks .none g dom s = true → ClaimSpec g dom s := by
  intro h
  unfold claimChecks at h
  split at h
  · exact absurd h (by simp)
  · rename_i k hk
    have hc := contract_dom hk
    unfold isContractOf at hc
    split at h
    · rename_i d' hh se fl rp hg
      rw [hg] at hc
      simp at hc
      subst hc
      split at h
      · exact absurd h (by simp)
      · rename_i b hb
        simp [on, cfgSet, List.all_eq_true, List.any_eq_true] at h
        obtain ⟨⟨⟨⟨⟨⟨i, hi1, hi2, hi3⟩, ⟨hw, hd⟩, hrep⟩, hcor⟩, hpk⟩, hmar⟩, hnull⟩ := h
        refine ⟨k, hh, se, fl, rp, b, hk, hg, hb, ⟨i, hi1, hi2, hi3⟩, hw, hd, ?_, ?_⟩
        · intro w hwm d hdm
          refine ⟨hrep w hwm d hdm, hcor w hwm d hdm, hpk w hwm d hdm, ?_⟩
          intro t ht c hcm t' ht' hok
          exact (hmar w hwm d hdm t ht c hcm t' ht').resolve_left (by simp [hok])
        · split at hnull
          · exact absurd hnull (by simp)
          · rename_i n hn
            refine ⟨n, hn, ?_⟩
            simp [List.all_eq_true] at hnull
            intro w hwm
            obtain ⟨hne, hall⟩ := hnull w hwm
            exact ⟨hne, fun t ht => by simpa using hall t ht⟩
    · exact absurd h (by simp)

/-- Main theorem: every claim in any reachable log satisfies ClaimSpec
over the log as it stood when the claim was appended. -/
theorem claims_sound {g : List Rec} (h : Reach g) {i dom s : Nat}
    (e : g[i]? = some (.claim dom s)) : ClaimSpec (g.take i) dom s :=
  claim_spec (reach_accepted h i _ e)

/-- Grounded evidence, declaratively. -/
inductive Grounded (g : List Rec) : Nat → Prop where
  | run {i k s w d h t} : g[i]? = some (.run k s w d h t) → Grounded g i
  | derive {i gen ins} : g[i]? = some (.derive gen ins) → ins ≠ [] →
      (∀ j ∈ ins, j < i) → (∀ j ∈ ins, Grounded g j) → Grounded g i

theorem grounded_spec (g : List Rec) : ∀ (fuel i : Nat), grounded g fuel i = true → Grounded g i
  | 0, i, h => by simp [grounded] at h
  | fuel + 1, i, h => by
    unfold grounded at h
    split at h
    · rename_i k s w d hh t he; exact Grounded.run he
    · rename_i gen ins he
      simp [List.all_eq_true] at h
      obtain ⟨hne, hall⟩ := h
      exact Grounded.derive he hne (fun j hj => (hall j hj).1)
        (fun j hj => grounded_spec g fuel j (hall j hj).2)
    · exact absurd h (by simp)

/-- Every fact in a reachable log cites only evidence grounded in runs. -/
theorem facts_grounded {g : List Rec} (h : Reach g) {i : Nat} {ev : List Nat}
    (e : g[i]? = some (.fact ev)) : ∀ j ∈ ev, Grounded (g.take i) j := by
  have ha := reach_accepted h i _ e
  simp [accepts, acceptW, on, List.all_eq_true] at ha
  intro j hj
  exact grounded_spec _ _ j (ha.2 j hj)

end Admission

#print axioms Admission.replay_reach
#print axioms Admission.reach_accepted
#print axioms Admission.claim_spec
#print axioms Admission.claims_sound
#print axioms Admission.grounded_spec
#print axioms Admission.facts_grounded
