/-
Copyright (c) 2026 PNP Labs.

Exact first-failure semantics and a closed initialized search. The reader
contract is erased proof data; the source integration discharges it from
the actual input-derived candidate and cache.
-/
import PNP.Concrete.NormalizerFirstFailureLoop

namespace PNP.Concrete.NormalizerBlocks.FirstFailure
open BitRegister Occurrence
attribute [local irreducible] CandidateTruth.clauseResult

def find (test : Nat → Bool) (first : Nat) : Nat → Option Nat
  | 0 => none
  | count+1 => if test first then find test (first+1) count else some first
def ReaderCorrect (literals assignment : BitString) (limit : Nat) (test : Nat → Bool) : Prop :=
  ∀ (r : CandidateTruth.State) (i : Nat), i < limit →
    r.core.formula = literals → r.matching = assignment →
    r.core.index = List.replicate i true →
    (CandidateTruth.clauseResult r).registers.output = [test i]
theorem query_truth (r : State) (literals assignment : BitString) (limit first : Nat)
    (test : Nat → Bool) (correct : ReaderCorrect literals assignment limit test)
    (within : first < limit) (counter : r.counter = List.replicate first true)
    (literalRead : r.core.core.formula = literals) (assignmentRead : r.core.matching = assignment) :
    truth r = test first := by
  have computed := correct (loaded r).core first within literalRead assignmentRead counter
  change ForwardEdge.present (CandidateTruth.clauseResult (loaded r).core).registers.output = _
  rw [computed]
  rfl
theorem scan_buffer (word : BitString) (r : State) (literals assignment : BitString)
    (limit first : Nat) (test : Nat → Bool) (correct : ReaderCorrect literals assignment limit test)
    (within : first + word.length ≤ limit) (counter : r.counter = List.replicate first true)
    (empty : r.buffer = [false]) (literalRead : r.core.core.formula = literals)
    (assignmentRead : r.core.matching = assignment) :
    (scan word r).state.buffer = TableOwner.answer (find test first word.length) := by
  induction word generalizing r first with
  | nil => exact empty
  | cons bit rest ih =>
      let before := {r with remaining := bit::rest}
      have index : first < limit := by simp only [List.length_cons] at within; omega
      have computed := query_truth before literals assignment limit first test correct index
        counter literalRead assignmentRead
      dsimp only [before] at computed
      cases h : test first
      · have bad : truth before = false := computed.trans h
        simp only [scan,computed,h,Bool.false_eq_true,ite_false,List.length_cons,find]
        rw [body_buffer,bad]
        change true::r.counter = true::List.replicate first true
        rw [counter]
      · have ok : truth before = true := computed.trans h
        have counterNext : (bodyResult before).counter = List.replicate (first+1) true := by
          rw [body_counter,ok]
          change true::r.counter = _
          rw [counter,List.replicate_succ]
        have bufferNext : (bodyResult before).buffer = [false] := by
          rw [body_buffer,ok]
          exact empty
        have fields := body_fields before
        have tail := ih (bodyResult before) (first+1)
          (by simp only [List.length_cons] at within; omega) counterNext bufferNext
          (fields.1.trans literalRead) (fields.2.trans assignmentRead)
        simpa only [scan,computed,h,ite_true,List.length_cons,find,before] using tail

theorem find_ofFn (test : Nat → Bool) (first count : Nat) :
    find test first count =
      (List.ofFn (fun i : Fin count => first + i.val)).find? (fun i => !test i) := by
  induction count generalizing first with
  | zero => rfl
  | succ count ih =>
      rw [find,List.ofFn_succ]
      simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ]
      have shifted : List.ofFn (fun i : Fin count => first + (i.val+1)) =
          List.ofFn (fun i : Fin count => (first+1) + i.val) := by
        apply congrArg List.ofFn
        funext i
        omega
      rw [shifted,ih (first+1)]
      cases h : test first <;>
        simp only [List.find?,h,Bool.not_false,Bool.not_true,Bool.false_eq_true,ite_false,ite_true]

def start : Block 22 :=
  .seq (.action (.clear 20)) (.seq (.action (.clear 21)) (.action (.push 21 false)))
def started (r : State) : State := {r with counter := [],buffer := [false]}
theorem start_exec (r : State) : Exec start r.store 3 (started r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
def front : Block 22 := .seq start loop
def frontResult (r : State) : State := (whole (started r)).state
def frontSteps (r : State) : Nat := 3 + (whole (started r)).fuel
theorem front_exec (r : State) : Exec front r.store (frontSteps r) (frontResult r).store :=
  Exec.seq (start_exec r) (whole_exec (started r))
def finish : Block 22 := .action (.copy 8 21)
def finished (r : State) : State :=
  r.withCore (r.core.withRegisters {r.registers with output := r.buffer})
theorem finish_exec (r : State) : Exec finish r.store 1 (finished r).store := .action _ _
def call : Block 22 := .seq front finish
def called (r : State) : State := finished (frontResult r)
def callSteps (r : State) : Nat := frontSteps r + 1
theorem call_exec (r : State) : Exec call r.store (callSteps r) (called r).store :=
  Exec.seq (front_exec r) (finish_exec (frontResult r))
theorem called_fields (r : State) :
    (called r).core.core.formula = r.core.core.formula ∧
    (called r).core.matching = r.core.matching :=
  ⟨(scan_fields r.remaining (started r)).1,(scan_fields r.remaining (started r)).2.1⟩
theorem called_canonical (r : State) (literals assignment : BitString) (count : Nat)
    (test : Nat → Bool) (correct : ReaderCorrect literals assignment count test)
    (remaining : r.remaining.length = count) (literalRead : r.core.core.formula = literals)
    (assignmentRead : r.core.matching = assignment) :
    (called r).registers.output = TableOwner.answer (find test 0 count) := by
  have checked := scan_buffer r.remaining (started r) literals assignment count 0 test correct
    (by omega) rfl rfl literalRead assignmentRead
  change (frontResult r).buffer = _ at checked
  rw [remaining] at checked
  exact checked
def callBound : NatPolynomial := .add loopBound (.constant 4)
theorem callSteps_bound (r : State) (n : Nat) (bounded : r.store.Bounded n) :
    callSteps r ≤ callBound.eval n := by
  have cursor := Store.get_length_le r.store (19 : Fin 22) bounded
  have formula := Store.get_length_le r.store (13 : Fin 22) bounded
  change r.remaining.length ≤ n at cursor
  change r.core.core.formula.length ≤ n at formula
  have budget : (started r).counter.length + (started r).remaining.length ≤ n := by
    change 0 + r.remaining.length ≤ n
    omega
  have cost := whole_fuel_bound (started r) n budget formula
  change callSteps r ≤ loopBound.eval n + 4
  unfold callSteps frontSteps
  omega

end PNP.Concrete.NormalizerBlocks.FirstFailure
