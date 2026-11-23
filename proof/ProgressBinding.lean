import CanonicalProgress

namespace CanonicalProgress.Exact

def pack (a b : List Nat) : List Nat := a.length :: (a ++ b)

theorem pack_injective {a b c d : List Nat} (h : pack a b = pack c d) :
    a = c ∧ b = d := by
  have e := List.cons.inj h
  have htake := congrArg (List.take a.length) e.2
  rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length] at htake
  rw [e.1, List.take_append_of_le_length (Nat.le_refl _), List.take_length] at htake
  exact ⟨htake, List.append_cancel_left (htake ▸ e.2)⟩

def coordinates : List Coordinate → List Nat
  | [] => []
  | x :: xs => x.configuration :: x.ordering :: x.observation :: coordinates xs

def rows : List Row → List Nat
  | [] => []
  | (x,n) :: xs => x.configuration :: x.ordering :: x.observation :: n :: rows xs

theorem coordinates_injective : ∀ {a b}, coordinates a = coordinates b → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [coordinates] at h
  | _ :: _, [], h => by simp [coordinates] at h
  | ⟨a,b,c⟩ :: xs, ⟨d,e,f⟩ :: ys, h => by
      simp only [coordinates,List.cons.injEq] at h
      obtain ⟨rfl,rfl,rfl,ht⟩ := h
      rw [coordinates_injective ht]

theorem rows_injective : ∀ {a b}, rows a = rows b → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [rows] at h
  | _ :: _, [], h => by simp [rows] at h
  | (⟨a,b,c⟩,n) :: xs, (⟨d,e,f⟩,m) :: ys, h => by
      simp only [rows,List.cons.injEq] at h
      obtain ⟨rfl,rfl,rfl,rfl,ht⟩ := h
      rw [rows_injective ht]

def state (s : State) : List Nat := s.pin :: pack (rows s.observations) s.cost
def contract (k : Contract) : List Nat := k.edition :: pack (rows k.possible) (coordinates k.required)

theorem state_injective {a b} (h : state a = state b) : a = b := by
  cases a; cases b
  obtain ⟨p,q⟩ := List.cons.inj h
  obtain ⟨x,y⟩ := pack_injective q
  have z := rows_injective x
  congr

theorem contract_injective {a b} (h : contract a = contract b) : a = b := by
  cases a; cases b
  obtain ⟨p,q⟩ := List.cons.inj h
  obtain ⟨x,y⟩ := pack_injective q
  have z := rows_injective x
  have w := coordinates_injective y
  congr

def body (k : Contract) (check : Nat) (old new : State) : List Nat :=
  check :: pack (contract k) (pack (state old) (state new))

theorem body_injective {k k' check check' old old' new new'}
    (h : body k check old new = body k' check' old' new') :
    k = k' ∧ check = check' ∧ old = old' ∧ new = new' := by
  obtain ⟨c,p⟩ := List.cons.inj h
  obtain ⟨k,p⟩ := pack_injective p
  obtain ⟨a,b⟩ := pack_injective p
  exact ⟨contract_injective k,c,state_injective a,state_injective b⟩

-- Reserve a disjoint residue for payload terms. This is a second receipt
-- format on the very same Canon.Rec and ledger, not a second graph.
def payload (k : Contract) (check : Nat) (old new : State) : List Nat :=
  (body k check old new).map (fun n => 4*n+3)

def premises (k : Contract) (check : Nat) (old new : State) : List Nat :=
  [4*old.pin,4*k.edition+1,4*check+2] ++ payload k check old new

theorem tagged_injective : ∀ {xs ys : List Nat},
    xs.map (fun n => 4*n+3) = ys.map (fun n => 4*n+3) → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
    obtain ⟨a,b⟩ := List.cons.inj h
    change 4*x+3 = 4*y+3 at a
    have same : x = y := by omega
    rw [same, tagged_injective b]

theorem premises_injective {k k' check check' old old' new new'}
    (h : premises k check old new = premises k' check' old' new') :
    k = k' ∧ check = check' ∧ old = old' ∧ new = new' := by
  have p := congrArg (List.drop 3) h
  simp [premises, payload, List.drop] at p
  exact body_injective (tagged_injective p)

def checked (e : Canon.Rec) (k : Contract) (check : Nat) (old new : State) : Bool :=
  e.level == 0 && e.colors.contains 1 && !e.colors.contains 2 &&
    e.premises == premises k check old new && e.head == 4*new.pin

def witnessed (log : List Canon.Rec) (k : Contract) (check : Nat) (old new : State) : Bool :=
  log.any (fun e => checked e k check old new)

theorem one_receipt_one_transition {e k k' check check' old old' new new'}
    (h : checked e k check old new = true) (h' : checked e k' check' old' new' = true) :
    k = k' ∧ check = check' ∧ old = old' ∧ new = new' := by
  simp [checked, Bool.and_eq_true, and_assoc] at h h'
  exact premises_injective (h.2.2.2.1.symm.trans h'.2.2.2.1)

inductive BoundProgress (log : List Canon.Rec) (k : Contract) (check : Nat) :
    State → State → Type where
  | constructed {old new} :
      compatible k old new = true → witnessed log k check old new = true →
        BoundProgress log k check old new

def construct (log : List Canon.Rec) (k : Contract) (check : Nat) (old new : State) :
    Option (BoundProgress log k check old new) :=
  if h : compatible k old new = true then
    if w : witnessed log k check old new = true then some (.constructed h w)
    else none
  else none

def keep {log suffix k check old new} (p : BoundProgress log k check old new) :
    BoundProgress (log ++ suffix) k check old new := by
  cases p with
  | constructed h w =>
      unfold witnessed at w
      exact .constructed h (by simp [witnessed, List.any_append, w])

theorem checked_projects_to_full_edge {log k check old new}
    (p : BoundProgress log k check old new) (ch : Canon.Chain) :
    (Canon.viewC ch log 0 (fun cs => cs.contains 1 && !cs.contains 2)).edges
      (premises k check old new) (4*new.pin) := by
  cases p with
  | constructed _ w =>
    obtain ⟨e,mem,valid⟩ := List.any_eq_true.mp w
    simp [checked, Bool.and_eq_true, and_assoc] at valid
    exact ⟨e,mem,by omega,by simp [valid.2.1,valid.2.2.1],
      by simp [Canon.proj,Canon.lift,valid.2.2.2.1,valid.2.2.2.2]⟩

theorem checked_cost_monotone {log k check old new}
    (p : BoundProgress log k check old new) :
    AlgoSearch.le new.cost old.cost = true := by
  cases p with
  | constructed ok _ => simp [compatible] at ok; exact ok.2

theorem checked_behavior_preserved {log k check old new}
    (p : BoundProgress log k check old new) (c) (hc : c ∈ k.required) :
    find new c = find old c := by
  cases p with
  | constructed ok _ =>
    simp [compatible] at ok
    exact beq_iff_eq.mp (List.all_eq_true.mp ok.1.2 c hc)

def exactReceipt (k : Contract) (old new : State) (check : Nat) : Canon.Rec :=
  ⟨check,0,[1],premises k check old new,4*new.pin⟩

def aliasCost : State := {left with cost := [7,8]}
def aliasOrder : State := {left with observations := left.observations.reverse}
def aliasContract : Contract := {scope with required := scope.required.reverse}

theorem bare_ids_accept_different_costs_and_order :
    (CanonicalProgress.construct trail scope 1 boot aliasCost).isSome = true ∧
    (CanonicalProgress.construct trail scope 1 boot aliasOrder).isSome = true ∧
    (CanonicalProgress.construct trail aliasContract 1 boot left).isSome = true := by decide

theorem exact_receipt_controls :
    (construct [exactReceipt scope boot left 1] scope 1 boot left).isSome = true ∧
    (construct [exactReceipt scope boot left 1] scope 1 boot aliasCost).isSome = false ∧
    (construct [exactReceipt scope boot left 1] scope 1 boot aliasOrder).isSome = false ∧
    (construct [exactReceipt scope boot left 1] aliasContract 1 boot left).isSome = false ∧
    (construct trail scope 1 boot left).isSome = false := by decide

#print axioms body_injective
#print axioms one_receipt_one_transition
#print axioms keep
#print axioms checked_projects_to_full_edge
#print axioms checked_cost_monotone
#print axioms checked_behavior_preserved
#print axioms bare_ids_accept_different_costs_and_order
#print axioms exact_receipt_controls
end CanonicalProgress.Exact
