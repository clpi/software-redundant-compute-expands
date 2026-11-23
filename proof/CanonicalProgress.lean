import Canon
import AlgoSearch
import Lean

namespace CanonicalProgress

structure Coordinate where
  configuration : Nat
  ordering : Nat
  observation : Nat
  deriving DecidableEq, Repr

abbrev Row := Coordinate × Nat

structure State where
  pin : Nat
  observations : List Row
  cost : List Nat
  deriving DecidableEq, Repr

structure Contract where
  edition : Nat
  possible : List Row
  required : List Coordinate
  deriving DecidableEq, Repr

def find (s : State) (c : Coordinate) := s.observations.find? (fun r => r.1 == c)

def wellformed (k : Contract) (s : State) : Bool :=
  decide ((s.observations.map Prod.fst).Nodup) &&
  s.observations.all k.possible.contains &&
  k.required.all (fun c => (find s c).isSome)

def carries (k : Contract) (old new : State) : Bool :=
  k.required.all (fun c => find new c == find old c)

def compatible (k : Contract) (old new : State) : Bool :=
  wellformed k old && wellformed k new && carries k old new && AlgoSearch.le new.cost old.cost

-- Graph witness colors carry checked and counterexample statuses separately.
-- Tag spaces make contracts, subjects, and observation-check identities distinct.
def checked (e : Canon.Rec) (k : Contract) (old new : State) (check : Nat) : Bool :=
  e.level == 0 && e.colors.contains 1 && !e.colors.contains 2 &&
    e.premises == [4*old.pin, 4*k.edition+1, 4*check+2] && e.head == 4*new.pin

def witnessed (log : List Canon.Rec) (k : Contract) (old new : State) (check : Nat) :=
  log.any (fun e => checked e k old new check)

inductive Progress (log : List Canon.Rec) (k : Contract) (check : Nat) : State → State → Type where
  | constructed {old new : State} :
      compatible k old new = true → witnessed log k old new check = true →
      Progress log k check old new

def construct (log : List Canon.Rec) (k : Contract) (check : Nat) (old new : State) :
    Option (Progress log k check old new) :=
  if h : compatible k old new = true then
    if w : witnessed log k old new check = true then some (.constructed h w)
    else none
  else none

theorem construct_exact (log) (k) (check) (old new) :
    (construct log k check old new).isSome = true ↔
    compatible k old new = true ∧ witnessed log k old new check = true := by
  unfold construct
  split <;> rename_i h
  · split <;> rename_i w <;> simp [h,w]
  · simp [h]

theorem checked_edge (log) (k) (check) (old new)
    (h : witnessed log k old new check = true) (ch : Canon.Chain) :
    (Canon.viewC ch log 0 (fun colors => colors.contains 1 && !colors.contains 2)).edges
      [4*old.pin, 4*k.edition+1, 4*check+2] (4*new.pin) := by
  obtain ⟨e, he, hw⟩ := List.any_eq_true.mp h
  have hw' : (e.level = 0 ∧ 1 ∈ e.colors ∧ 2 ∉ e.colors) ∧
      e.premises = [4*old.pin,4*k.edition+1,4*check+2] ∧ e.head = 4*new.pin := by
    simp [checked, Bool.and_eq_true, and_assoc] at hw
    exact ⟨⟨hw.1,hw.2.1,hw.2.2.1⟩,hw.2.2.2⟩
  exact ⟨e, he, by omega, by simp [hw'.1.2.1,hw'.1.2.2],
    by simp [Canon.proj, Canon.lift, hw'.2.1, hw'.2.2]⟩

theorem supported_successor_derives {log k check old new}
    (p : Progress log k check old new) (ch : Canon.Chain)
    (supports : ∀ n, n ∈ [4*old.pin,4*k.edition+1,4*check+2] →
      Canon.derives (Canon.viewC ch log 0 (fun cs => cs.contains 1 && !cs.contains 2)) n) :
    Canon.derives (Canon.viewC ch log 0 (fun cs => cs.contains 1 && !cs.contains 2)) (4*new.pin) := by
  cases p with
  | constructed _ w => exact Canon.Derives.step (checked_edge _ _ _ _ _ w ch) supports

theorem cost_monotone {log k check old new} (p : Progress log k check old new) :
    AlgoSearch.le new.cost old.cost = true := by
  cases p with
  | constructed h _ => simp [compatible] at h; exact h.2

theorem behavior_preserved {log k check old new} (p : Progress log k check old new)
    (c) (hc : c ∈ k.required) : find new c = find old c := by
  cases p with
  | constructed h _ =>
      have f : carries k old new = true := by
        simp [compatible] at h
        exact h.1.2
      exact beq_iff_eq.mp ((List.all_eq_true.mp f) _ hc)

theorem impossible_if_cost_regresses {log k check old new}
    (worse : AlgoSearch.le new.cost old.cost = false) : ¬ Nonempty (Progress log k check old new) := by
  rintro ⟨p⟩
  have good := cost_monotone p
  rw [worse] at good
  contradiction

def append_keeps_witness {log suffix k check old new} (p : Progress log k check old new) :
    Progress (log ++ suffix) k check old new := by
  cases p with
  | constructed h w =>
      unfold witnessed at w
      exact .constructed h (by simp [witnessed, List.any_append, w])

inductive History (log : List Canon.Rec) (k : Contract) (origin : State) : State → Prop where
  | start : History log k origin origin
  | extend {a b : State} {check : Nat} : History log k origin a →
      Progress log k check a b → History log k origin b

theorem le_refl_vec : ∀ v : List Nat, AlgoSearch.le v v = true
  | [] => rfl
  | x :: xs => by simp [AlgoSearch.le, le_refl_vec xs]

theorem history_no_worse {log k origin dest} (h : History log k origin dest) :
    AlgoSearch.le dest.cost origin.cost = true := by
  induction h with
  | start => exact le_refl_vec _
  | extend _ step ih => exact AlgoSearch.le_trans' _ _ _ (cost_monotone step) ih

theorem history_carries {log k origin dest} (h : History log k origin dest)
    (c) (hc : c ∈ k.required) : find dest c = find origin c := by
  induction h with
  | start => rfl
  | extend _ step ih => exact (behavior_preserved step c hc).trans ih

theorem history_append {log suffix k origin dest} (h : History log k origin dest) :
    History (log ++ suffix) k origin dest := by
  induction h with
  | start => exact .start
  | extend _ step ih => exact .extend ih (append_keeps_witness step)

theorem no_new_disallowed_behavior {log k check old new}
    (p : Progress log k check old new) (r : Row) (h : r ∈ new.observations) :
    r ∈ k.possible := by
  cases p with
  | constructed ok _ =>
    have valid : wellformed k new = true := by
      simp [compatible] at ok
      exact ok.1.1.2
    simp [wellformed] at valid
    exact valid.1.2 r.1 r.2 h

def validCosts (log : List Canon.Rec) (k : Contract) (old : State)
    (candidates : List (Nat × State)) : List (List Nat) :=
  candidates.filterMap fun (check,new) =>
    if (construct log k check old new).isSome then some new.cost else none

def front (log : List Canon.Rec) (k : Contract) (old : State)
    (candidates : List (Nat × State)) := AlgoSearch.arch (validCosts log k old candidates)

theorem valid_cost_exact (log) (k) (old) (candidates) (v) :
    v ∈ validCosts log k old candidates ↔
      ∃ pair ∈ candidates, (construct log k pair.1 old pair.2).isSome = true ∧ pair.2.cost = v := by
  simp only [validCosts, List.mem_filterMap]
  constructor
  · rintro ⟨⟨check,new⟩, hmem, hp⟩
    by_cases h : (construct log k check old new).isSome = true
    · exact ⟨(check,new), hmem, h, by simpa [h] using hp⟩
    · simp [h] at hp
  · rintro ⟨⟨check,new⟩, hmem, h, eq⟩
    exact ⟨(check,new), hmem, by simpa [h] using eq⟩

theorem front_exact (log) (k) (old) (candidates) (v) :
    v ∈ front log k old candidates ↔
    AlgoSearch.Front (validCosts log k old candidates) v :=
  AlgoSearch.mem_arch _ _

theorem candidate_has_front_cover (log) (k) (old) (candidates) (v)
    (h : v ∈ validCosts log k old candidates) :
    ∃ w ∈ front log k old candidates, w = v ∨ AlgoSearch.dom w v = true := by
  classical
  by_cases hf : AlgoSearch.Front (validCosts log k old candidates) v
  · exact ⟨v,(front_exact _ _ _ _ _).mpr hf,Or.inl rfl⟩
  · have d : ∃ y ∈ validCosts log k old candidates, AlgoSearch.dom y v = true := by
      apply Classical.byContradiction
      intro hn
      apply hf
      refine ⟨h,?_⟩
      intro y hy
      cases eq : AlgoSearch.dom y v
      · rfl
      · exact False.elim (hn ⟨y,hy,eq⟩)
    obtain ⟨y,hy,hd⟩ := d
    obtain ⟨w,hw,wd⟩ := AlgoSearch.front_dominator _ _ y.sum y rfl hy hd
    exact ⟨w,(front_exact _ _ _ _ _).mpr hw,Or.inr wd⟩

def coordinate (order : Nat) := Coordinate.mk 0 order 0

def scope : Contract := ⟨11, [(coordinate 0,0),(coordinate 0,1),(coordinate 1,0),(coordinate 1,1)],
                         [coordinate 0, coordinate 1]⟩

def boot : State := ⟨1,[(coordinate 0,0),(coordinate 1,1)],[10,10]⟩
def left : State := ⟨2,boot.observations,[9,10]⟩
def right : State := ⟨3,boot.observations,[10,9]⟩
def unsoundJoin : State := ⟨4,[(coordinate 0,0),(coordinate 1,0)],[8,8]⟩
def goodJoin : State := ⟨5,boot.observations,[8,8]⟩

def receipt (old new : State) (check : Nat) (colors : List Nat) : Canon.Rec :=
  ⟨check,0,colors,[4*old.pin,4*scope.edition+1,4*check+2],4*new.pin⟩

def trail := [receipt boot left 1 [1],receipt boot right 2 [1],
              receipt boot unsoundJoin 3 [1],receipt boot goodJoin 4 [2]]

theorem separate_progress_does_not_compose :
    (construct trail scope 1 boot left).isSome = true ∧
    (construct trail scope 2 boot right).isSome = true ∧
    (construct trail scope 3 boot unsoundJoin).isSome = false := by decide

theorem observations_do_not_grant_progress :
    (construct trail scope 4 boot goodJoin).isSome = false ∧
    (construct (trail ++ [receipt boot goodJoin 5 [1]]) scope 5 boot goodJoin).isSome = true := by decide

theorem qualified_orders_are_retained :
    find boot (coordinate 0) = some (coordinate 0,0) ∧
    find boot (coordinate 1) = some (coordinate 1,1) := by decide

section Incremental
variable {A : Type} [DecidableEq A]
structure Task (A : Type) where
  name : Nat
  premises : List Nat
  evaluate : List A → A

def result (t : Task A) (s : Nat → A) := t.evaluate (t.premises.map s)

def put (s : Nat → A) (key : Nat) (value : A) : Nat → A :=
  fun i => if i = key then value else s i

def execute (t : Task A) (s : Nat → A) := put s t.name (result t s)

def cut (t : Task A) (old new : Nat → A) (cached : A) :=
  if t.premises.map old = t.premises.map new then put new t.name cached else execute t new

theorem cut_exact (t : Task A) (old new : Nat → A) (cached : A)
    (held : cached = result t old) : cut t old new cached = execute t new := by
  unfold cut
  split
  · rename_i same
    simp [held, execute, result, same]
  · rfl

def full : List (Task A) → (Nat → A) → (Nat → A)
  | [], s => s
  | t :: ts, s => full ts (execute t s)

def replay : List (Task A) → (Nat → A) → (Nat → A) → (Nat → A)
  | [], _, s => s
  | t :: ts, old, new =>
      replay ts (execute t old) (cut t old new (result t old))

theorem replay_exact : ∀ (tasks : List (Task A)) (old new : Nat → A),
    replay tasks old new = full tasks new
  | [], _, _ => rfl
  | t :: ts, old, new => by
      simp only [replay, full, cut_exact t old new (result t old) rfl]
      exact replay_exact ts (execute t old) (execute t new)
end Incremental

#print axioms supported_successor_derives
#print axioms cut_exact
#print axioms replay_exact
#print axioms construct_exact
#print axioms checked_edge
#print axioms cost_monotone
#print axioms behavior_preserved
#print axioms impossible_if_cost_regresses
#print axioms append_keeps_witness
#print axioms history_no_worse
#print axioms history_carries
#print axioms history_append
#print axioms no_new_disallowed_behavior
#print axioms valid_cost_exact
#print axioms front_exact
#print axioms candidate_has_front_cover
#print axioms separate_progress_does_not_compose
#print axioms observations_do_not_grant_progress
#print axioms qualified_orders_are_retained
end CanonicalProgress
