/-
Copyright (c) 2026 PNP Labs.

Complete width-bounded recovery in original source order. The output theorem
uses the closed reader's semantics, not a caller-supplied correctness oracle.
The requested width may differ from the frontend's full auxiliary width.
-/
import PNP.Concrete.NormalizerRecoveryLoop
import PNP.Concrete.NormalizerCandidateBitsCall

namespace PNP.Concrete.NormalizerBlocks.Recovery
open BitRegister Occurrence
open CandidateBits (values values_ofFn)

theorem scan_buffer (word : BitString) (r : State) (formula : List (List CNFLiteral))
    (matching : MatchingTable.Entries) (variables : List CNFLiteral) (assignment : BitString)
    (first : Nat) (counter : r.counter = List.replicate first true)
    (formulaRead : r.formula = GraphQuery.clauseData formula)
    (matchingRead : r.matching = MatchingTable.encode matching)
    (variablesRead : r.variables = SearchVertices.encodeVertices variables)
    (assignmentRead : r.assignment = assignment) :
    (scan word r).state.buffer =
      (values (bitValue formula matching variables assignment) first word.length).reverse++r.buffer := by
  induction word generalizing r first with
  | nil => rfl
  | cons head rest ih =>
      let before := {r with remaining := head::rest}
      have computed := bit_canonical before formula matching variables first formulaRead matchingRead variablesRead counter
      change (bitResult before).core.output = [bitValue formula matching variables r.assignment first] at computed
      rw [assignmentRead] at computed
      have step := body_fields before
      have counterNext : (bodyResult before).counter = List.replicate (first+1) true := by
        rw [step.2.2]
        change true::r.counter = _
        rw [counter,List.replicate_succ]
      have ff : (bodyResult before).formula = GraphQuery.clauseData formula :=
        (congrArg Data.formula step.1).trans formulaRead
      have fm : (bodyResult before).matching = MatchingTable.encode matching :=
        (congrArg Data.matching step.1).trans matchingRead
      have fv : (bodyResult before).variables = SearchVertices.encodeVertices variables :=
        (congrArg Data.variables step.1).trans variablesRead
      have fa : (bodyResult before).assignment = assignment :=
        (congrArg Data.assignment step.1).trans assignmentRead
      have tail := ih (bodyResult before) (first+1) counterNext ff fm fv fa
      change (scan rest (bodyResult before)).state.buffer = _
      rw [tail,body_buffer,computed]
      simp only [List.length_cons,values,List.reverse_cons,List.append_assoc,List.cons_append,
        List.nil_append,List.headD_cons]
      rfl

def start : Block 16 := .seq (.action (.clear 14)) (.action (.clear 15))
def started (r : State) : State := {r with counter := [],buffer := []}
theorem start_exec (r : State) : Exec start r.store 2 (started r).store :=
  Exec.seq (.action _ _) (.action _ _)
def front : Block 16 := .seq start loop
def frontResult (r : State) : State := (whole (started r)).state
def frontSteps (r : State) : Nat := 2+(whole (started r)).fuel
theorem front_exec (r : State) : Exec front r.store (frontSteps r) (frontResult r).store :=
  Exec.seq (start_exec r) (whole_exec (started r))
def prepareFinish : Block 16 := .seq (.action (.copy 3 15)) (.action (.clear 8))
def finishPrepared (r : State) : State := r.withCore {r.core with excess := r.buffer,output := []}
theorem prepareFinish_exec (r : State) : Exec prepareFinish r.store 2 (finishPrepared r).store :=
  Exec.seq (.action _ _) (.action _ _)
def finish : Block 16 := .seq prepareFinish (lift ClauseQuery.reverseLoop)
def finished (r : State) : State := r.withCore {r.core with excess := [],output := r.buffer.reverse}
def finishFuel (r : State) : Nat := 4*r.buffer.length+3
theorem finish_exec (r : State) : Exec finish r.store (finishFuel r) (finished r).store := by
  have reverse := ClauseQuery.reverse_exec (finishPrepared r).core r.buffer
  change Exec ClauseQuery.reverseLoop (finishPrepared r).core.store (4*r.buffer.length+1)
    ({r.core with excess := [],output := r.buffer.reverse++[]}).store at reverse
  rw [List.append_nil] at reverse
  have checked := Exec.seq (prepareFinish_exec r) (lift_exec _ (finishPrepared r) _ _ reverse)
  change Exec finish r.store (2+(4*r.buffer.length+1)) (finished r).store at checked
  have cost : 2+(4*r.buffer.length+1) = finishFuel r := by unfold finishFuel; omega
  rw [cost] at checked
  exact checked
def call : Block 16 := .seq front finish
def called (r : State) : State := finished (frontResult r)
def callSteps (r : State) : Nat := frontSteps r+finishFuel (frontResult r)
theorem call_exec (r : State) : Exec call r.store (callSteps r) (called r).store :=
  Exec.seq (front_exec r) (finish_exec (frontResult r))
theorem called_data (r : State) : (called r).data = r.data :=
  (scan_fields r.remaining (started r)).1
theorem called_output_length (r : State) : (called r).core.output.length = r.remaining.length := by
  change (frontResult r).buffer.reverse.length = _
  rw [List.length_reverse]
  have length := scan_buffer_length r.remaining (started r)
  change (frontResult r).buffer.length = r.remaining.length+0 at length
  simpa only [Nat.add_zero] using length
theorem called_canonical (r : State) (formula : List (List CNFLiteral))
    (matching : MatchingTable.Entries) (variables : List CNFLiteral) (count : Nat)
    (remaining : r.remaining.length = count)
    (formulaRead : r.formula = GraphQuery.clauseData formula)
    (matchingRead : r.matching = MatchingTable.encode matching)
    (variablesRead : r.variables = SearchVertices.encodeVertices variables) :
    (called r).core.output =
      List.ofFn (fun i : Fin count => bitValue formula matching variables r.assignment i.val) := by
  have checked := scan_buffer r.remaining (started r) formula matching variables r.assignment
    0 rfl formulaRead matchingRead variablesRead rfl
  change (frontResult r).buffer = _++[] at checked
  rw [List.append_nil,remaining] at checked
  change (frontResult r).buffer.reverse = _
  rw [checked,List.reverse_reverse,values_ofFn]
  simp only [Nat.zero_add]
def callBound : NatPolynomial := .add loopBound (.linear 4 5)
theorem callSteps_bound (r : State) (n : Nat) (bounded : r.store.Bounded n) :
    callSteps r ≤ callBound.eval n := by
  have cursor := Store.get_length_le r.store (13 : Fin 16) bounded
  have formula := Store.get_length_le r.store (9 : Fin 16) bounded
  have matching := Store.get_length_le r.store (10 : Fin 16) bounded
  have variables := Store.get_length_le r.store (11 : Fin 16) bounded
  change r.remaining.length ≤ n at cursor
  change r.formula.length ≤ n at formula
  change r.matching.length ≤ n at matching
  change r.variables.length ≤ n at variables
  have budget : (started r).counter.length+(started r).remaining.length ≤ n := by
    change 0+r.remaining.length ≤ n
    omega
  have cost := whole_fuel_bound (started r) n budget formula matching variables
  have length := scan_buffer_length r.remaining (started r)
  change (frontResult r).buffer.length = r.remaining.length+0 at length
  change callSteps r ≤ loopBound.eval n+(4*n+5)
  unfold callSteps frontSteps finishFuel
  omega

end PNP.Concrete.NormalizerBlocks.Recovery
