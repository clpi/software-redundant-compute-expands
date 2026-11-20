/-
  Same-contract measurement: the proved worklist (`Worklist.run`,
  `Worklist.appendRec`) against naive round-based closure on real
  append traces. Contract: same log, same level `r`, same color
  test `q`, same output set at every append prefix (checked here
  on every prefix; proved in `Worklist.mem_prefix`).

  Counted units (not machine time):
  * naive: `exam` = admitted record examined in a round,
    `check` = premise membership test (short-circuit, as
    `Closure.ready` does with `List.all`). One `fire` pass per
    round: the fairer form, not `Closure.iterE`, which evaluates
    `fire` twice per round.
  * worklist: `raw` = raw premises read when deduplicating at
    admission, `scans` = distinct premises tested at admission,
    `visits` = waiter visits (one count decrement each),
    `pops` = dequeues.
  Membership tests are list scans in `Worklist` and hash lookups
  in this naive harness; their cost is not counted on either
  side. Wall time is not reported.
-/
import Worklist
import EstateData
import V2Data
import Std.Data.HashSet
open Canon Canon.Worklist

namespace Measure

def chId : Chain := ⟨fun _ c => c, 0, 0, Nat.le_refl 0⟩

/-- `live` from candidate-space `Space.lean`: drop records colored
    disqualified (4), demanded (5) or proposal (7). -/
def live (cs : List Nat) : Bool := !(cs.contains 4) && !(cs.contains 5) && !(cs.contains 7)

structure NC where
  exam : Nat := 0
  check : Nat := 0
  rounds : Nat := 0

/-- One naive round: every admitted record, premises checked in
    order until the first missing one. -/
def naiveRound (r : Nat) (q : List Nat → Bool) (L : List Rec) (S : Std.HashSet Nat) (c : NC) :
    List Nat × NC := Id.run do
  let mut fired : List Nat := []
  let mut c := { c with rounds := c.rounds + 1 }
  for e in L do
    if admits r q e then
      c := { c with exam := c.exam + 1 }
      let ps := (proj chId r e).1
      let mut ok := true
      for p in ps do
        if ok then
          c := { c with check := c.check + 1 }
          if !S.contains p then ok := false
      if ok then fired := (proj chId r e).2 :: fired
  return (fired, c)

/-- Naive closure from a start set: rounds until nothing new. -/
def naiveClose (r : Nat) (q : List Nat → Bool) (L : List Rec) (S : Std.HashSet Nat) (c : NC) (fuel : Nat) :
    Std.HashSet Nat × NC :=
  match fuel with
  | 0 => (S, c)
  | n + 1 =>
    let (f, c) := naiveRound r q L S c
    let new := f.filter (fun a => !S.contains a)
    if new.isEmpty then (S, c) else naiveClose r q L (new.foldl (·.insert ·) S) c n

def setEq (D : List Nat) (S : Std.HashSet Nat) : Bool :=
  D.length == S.size && D.all S.contains

/-- Deterministic shuffle (fixed-seed linear congruential keys). -/
def shuffle (L : List Rec) : List Rec :=
  let keyed := (L.zipIdx).map (fun (e, i) => ((i * 1103515245 + 12345) % 2147483648, e))
  (keyed.mergeSort (fun a b => a.1 ≤ b.1)).map Prod.snd

def runTrace (name : String) (r : Nat) (q : List Nat → Bool) (L : List Rec) : IO Unit := do
  -- worklist, record by record, checking every prefix against naive incremental
  let mut s := St.init
  let mut S : Std.HashSet Nat := {}
  let mut c : NC := {}
  let mut pre : List Rec := []
  let mut agree := true
  let mut raw := 0
  let mut k := 0
  for e in L do
    s := appendRec chId r q s e
    if admits r q e then raw := raw + (proj chId r e).1.length
    pre := pre ++ [e]
    let (S', c') := naiveClose r q pre S c (pre.length + 1)
    S := S'; c := c'
    k := k + 1
    if !setEq s.D S then agree := false
  -- naive from scratch on the whole log, and the proved `Closure.clos`
  let (Sscratch, cs) := naiveClose r q L {} {} (L.length + 1)
  let closL := Closure.clos chId L r q
  let wlTotal := raw + s.scans + s.visits
  IO.println s!"{name}: records {L.length}, admitted {s.rules.length}, derived {s.D.length}, prefixes {k}"
  IO.println s!"  agree with naive at every prefix: {agree}; final = naive scratch: {setEq s.D Sscratch}; final = Closure.clos: {setEq s.D (closL.foldl (·.insert ·) {})}"
  IO.println s!"  worklist: raw {raw}, scans {s.scans}, visits {s.visits}, pops {s.pops}, total premise ops {wlTotal}"
  IO.println s!"  naive incremental over all prefixes: rounds {c.rounds}, exams {c.exam}, checks {c.check}"
  IO.println s!"  naive scratch on final log only: rounds {cs.rounds}, exams {cs.exam}, checks {cs.check}"
  IO.println s!"  bounds: visits ≤ distinct premises {decide (s.visits ≤ s.scans)}; pops = derived {s.pops == s.D.length}"
  let kv : List (String × String) := [("trace", "\"" ++ name ++ "\""), ("records", toString L.length),
    ("admitted", toString s.rules.length), ("derived", toString s.D.length), ("agree_every_prefix", toString agree),
    ("wl_raw", toString raw), ("wl_scans", toString s.scans), ("wl_visits", toString s.visits),
    ("wl_pops", toString s.pops), ("wl_total", toString wlTotal), ("naive_inc_rounds", toString c.rounds),
    ("naive_inc_exams", toString c.exam), ("naive_inc_checks", toString c.check),
    ("naive_scratch_rounds", toString cs.rounds), ("naive_scratch_exams", toString cs.exam),
    ("naive_scratch_checks", toString cs.check)]
  IO.println ("JSON {" ++ ", ".intercalate (kv.map (fun (k, v) => "\"" ++ k ++ "\": " ++ v)) ++ "}")
  (← IO.getStdout).flush

end Measure

open Measure in
def main : IO Unit := do
  runTrace "estate-forward" 0 live Estate.log
  runTrace "estate-reverse" 0 live Estate.log.reverse
  runTrace "estate-shuffled" 0 live (shuffle Estate.log)
  runTrace "idol-lib-v2-forward" 0 live V2.log
  runTrace "idol-lib-v2-reverse" 0 live V2.log.reverse
  runTrace "idol-lib-v2-shuffled" 0 live (shuffle V2.log)
