import Admission

/-!
Controls for Admission: one honest log that admits, and one control per
gaming route. For each control we show, by evaluation:

  1. the log in front of the gamed record is itself admissible
     (it replays from empty), so the refusal is not an artefact;
  2. the gamed record is refused;
  3. with exactly one named check switched off, the same record is
     accepted. So every check is necessary for its control.

Routes that the record shapes make unrepresentable (no control can even be
written down): a self-reported number (runs carry no value field), a
decision rule chosen after the results (the rule is the kernel, not a
field), a run under a contract that does not exist yet (references only
point backward), and rewriting history (Reach only appends; the Idol kernel
also chains a head over the log).
-/

namespace Admission.Controls
open Admission

def hb : Blob := [9, 9]          -- harness bytes
def ho : Blob := [7, 7, 7]       -- held-out bytes, sealed in the contract
def ctr : Rec := .contract 0 (H hb) (H ho) 2 1

/-- runs of one subject on one workload, both dimensions -/
def cell (s w : Nat) (t1 t2 : Blob) : List Rec :=
  [.run 6 s w 1 hb t1, .run 6 s w 2 hb t2]

/-- Positions 0 to 22. Subject 40 beats comparator configs 20 and 21 on
both dimensions and both workloads; the do-nothing subject 30 fails. -/
def pre : List Rec :=
  [.dim 0 1, .dim 0 2, .work 0 10 [5, 5], .config 0 20, .config 0 21, .null 0 30,
   ctr, .build 0 40 [2]] ++
  cell 40 10 [1, 3] [1, 4] ++ cell 20 10 [1, 50] [1, 60] ++ cell 21 10 [1, 10] [1, 12] ++
  [.run 6 30 10 1 hb [0, 0], .reveal 6 11 ho] ++
  cell 40 11 [1, 3] [1, 4] ++ cell 20 11 [1, 50] [1, 60] ++ cell 21 11 [1, 10] [1, 12] ++
  [.run 6 30 11 1 hb [0, 0]]

def honest : List Rec := pre ++ [.claim 0 40, .derive 0 [8, 9], .fact [24]]

theorem pre_len : pre.length = 23 := by decide

theorem honest_replays : replay [] honest = some honest := by decide

theorem honest_reach : Reach honest :=
  replay_reach honest [] honest Reach.nil honest_replays

/-- The control predicate: prefix admissible, record refused, record accepted
with only check `x` off. -/
def onlyBy (x : Check) (p : List Rec) (r : Rec) : Bool :=
  replay [] p == some p && !accepts p r && acceptW x p r

-- 01 Goodhart: a dimension the comparator is measured on (say rendering)
-- is left out of the subject's runs.
def c01 : List Rec := pre ++ [.dim 0 3, .run 6 20 10 3 hb [1, 5], .run 6 20 11 3 hb [1, 5]]
theorem goodhart : onlyBy .cover c01 (.claim 0 40) = true := by decide

-- 02 Benchmark selection after results: a second contract for the domain.
theorem reselect : onlyBy .contractOnce pre (.contract 0 (H hb) (H [8]) 2 1) = true := by decide

-- 03 Held-out leakage: a subject built after the reveal is claimed.
def c03 : List Rec := pre ++ [.build 0 41 [2]] ++
  cell 41 10 [1, 3] [1, 4] ++ cell 41 11 [1, 3] [1, 4]
theorem tuned_after_reveal : onlyBy .heldout c03 (.claim 0 41) = true := by decide

-- 04 Held-out swapped: revealed bytes are not the sealed ones.
theorem seal_swap : onlyBy .revealSeal (pre.take 15) (.reveal 6 11 [6, 6, 6]) = true := by decide

-- 05 Measurement contract mismatch: a comparator measured under another
-- harness (for example with browser start-up inside the timed scope).
theorem harness_mismatch : onlyBy .runHarness pre (.run 6 21 10 1 [8, 8] [1, 100]) = true := by
  decide

-- 06 Proof over transcribed data: a fact whose evidence is derived from a
-- workload's bytes, not from any run.
theorem transcribed : onlyBy .factGrounded (pre ++ [.derive 0 [2]]) (.fact [23]) = true := by
  decide

-- 07 Name-matched identity: a run for a subject id never built in this
-- domain (same spelling as something elsewhere).
theorem name_match : onlyBy .runSubject pre (.run 6 99 10 1 hb [1, 1]) = true := by decide

-- 08 Timing-only win, and a pass reported by the claimant: the subject is
-- fast but its own trace says the output was wrong.
theorem fast_but_wrong :
    onlyBy .correct (pre.set 8 (.run 6 40 10 1 hb [0, 3])) (.claim 0 40) = true := by decide

-- 09 Do-nothing baseline: doing nothing passes a workload, so the workload
-- tests nothing.
theorem do_nothing_passes :
    onlyBy .nullBase (pre.set 14 (.run 6 30 10 1 hb [1, 0])) (.claim 0 40) = true := by decide

-- 10 Win inside the noise floor: subject worst 3, floor 2, comparator best 4.
theorem inside_floor :
    onlyBy .margin (pre.set 12 (.run 6 21 10 1 hb [1, 4])) (.claim 0 40) = true := by decide

-- 11 Unmeasured comparator: a dimension where no comparator has a correct
-- run is claimed as beaten.
def c11 : List Rec := pre ++ [.dim 0 4, .run 6 40 10 4 hb [1, 1], .run 6 40 11 4 hb [1, 1]]
theorem unmeasured_peak : onlyBy .peak c11 (.claim 0 40) = true := by decide

-- 12 Answer replay: a subject built from a recorded comparator trace.
theorem answer_replay : onlyBy .buildLeak pre (.build 0 42 [10]) = true := by decide

-- 13 Weak comparator chosen: the subject beats config 20 but not config 21;
-- switching the merged peak off compares against the first config only.
theorem weak_comparator :
    onlyBy .merged (pre.set 8 (.run 6 40 10 1 hb [1, 20])) (.claim 0 40) = true := by decide

-- 14 No held-out at all (fixtures co-designed with the subject).
theorem no_heldout : onlyBy .heldout (pre.take 15) (.claim 0 40) = true := by decide

-- 15 One lucky run where the contract fixed three.
theorem lucky_run :
    onlyBy .cover (pre.set 6 (.contract 0 (H hb) (H ho) 2 3)) (.claim 0 40) = true := by decide

-- 16 Seal chosen after seeing the subject: a build before any contract.
theorem build_before_contract :
    onlyBy .buildAfterContract (pre.take 6) (.build 0 40 [2]) = true := by decide

-- 17 Unregistered workload or dimension measured into the claim.
theorem unregistered_run : onlyBy .runRegistered pre (.run 6 40 12 1 hb [1, 1]) = true := by decide

end Admission.Controls

#print axioms Admission.Controls.honest_reach
#print axioms Admission.Controls.goodhart
#print axioms Admission.Controls.reselect
#print axioms Admission.Controls.tuned_after_reveal
#print axioms Admission.Controls.seal_swap
#print axioms Admission.Controls.harness_mismatch
#print axioms Admission.Controls.transcribed
#print axioms Admission.Controls.name_match
#print axioms Admission.Controls.fast_but_wrong
#print axioms Admission.Controls.do_nothing_passes
#print axioms Admission.Controls.inside_floor
#print axioms Admission.Controls.unmeasured_peak
#print axioms Admission.Controls.answer_replay
#print axioms Admission.Controls.weak_comparator
#print axioms Admission.Controls.no_heldout
#print axioms Admission.Controls.lucky_run
#print axioms Admission.Controls.build_before_contract
#print axioms Admission.Controls.unregistered_run
