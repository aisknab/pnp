/-
Copyright (c) 2026 PNP Labs.

A literal, tape-preserving unary-register tag test. The expected tag determines
a finite control table; the actual tag is read from tape. Failed comparisons
also restore the entire tape. Only a bounded prefix is read for oversized tags.
This is runtime branch control, not a complete formula builder.
-/

import PNP.Concrete.CookLevinBuilderDividerOperands
import PNP.Concrete.WorkMachineProgramPath

namespace PNP.Concrete.CookLevin.BuilderUnaryTagMatch

open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)

def rewindState (expected : Nat) (equal : Bool) : Nat :=
  if equal then expected + 2 else expected + 3

def resultState (expected : Nat) (equal : Bool) : Nat :=
  if equal then expected + 4 else expected + 5

private def rewindSpec (expected : Nat) (equal : Bool) : StateSpec := fun read =>
  if read = unitSymbol then keepAction (rewindState expected equal) .left read
  else if read = scratchEndSymbol then keepAction (resultState expected equal) .stay read
  else deadAction (expected + 6) read

private def scanSpec (expected seen : Nat) : StateSpec := fun read =>
  if read = unitSymbol then
    if seen < expected then keepAction (seen + 2) .right read
    else keepAction (rewindState expected false) .left read
  else if read = separatorSymbol then
    keepAction (rewindState expected (decide (seen = expected))) .left read
  else deadAction (expected + 6) read

private def stateSpec (expected state : Nat) : StateSpec := fun read =>
  if state = 0 then
    if read = scratchEndSymbol then keepAction 1 .right read
    else deadAction (expected + 6) read
  else if state ≤ expected + 1 then scanSpec expected (state - 1) read
  else if state = expected + 2 then rewindSpec expected true read
  else rewindSpec expected false read

private def stateSpecs (expected : Nat) : List StateSpec :=
  List.ofFn (fun state : Fin (expected + 4) => stateSpec expected state.val)

/-- The finite program depends on the expected tag, never on the tag read. -/
def machine (expected : Nat) : WorkMachine :=
  { rules := rulesFrom 0 (stateSpecs expected),     startState := 0,     acceptState := expected + 4,     rejectState := expected + 5 }

private theorem lookup_at (specs : List StateSpec) (base index : Nat)
    (hIndex : index < specs.length) (symbol : WorkSymbol) :
    findWorkRule (rulesFrom base specs) (base + index) symbol =
      some (ruleOf (base + index) specs[index] symbol) := by
  induction specs generalizing base index with
  | nil => simp only [List.length_nil] at hIndex; omega
  | cons spec rest ih =>
      cases index with
      | zero => simpa using findWorkRule_rulesFrom_head base spec rest symbol
      | succ index =>
          have hRest : index < rest.length := by
            simp only [List.length_cons] at hIndex
            omega
          rw [rulesFrom, findWorkRule_append_of_none]
          · simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using ih (base + 1) index hRest
          · exact findWorkRule_rulesAt_none_of_state_ne base (base + (index + 1))
              spec symbol (by omega)

private theorem lookup (expected state : Nat) (hState : state < expected + 4)
    (symbol : WorkSymbol) :
    findWorkRule (machine expected).rules state symbol =
      some (ruleOf state (stateSpec expected state) symbol) := by
  have hIndex : state < (stateSpecs expected).length := by
    simpa only [stateSpecs, List.length_ofFn] using hState
  simpa only [machine, stateSpecs, Nat.zero_add, List.getElem_ofFn] using
    lookup_at (stateSpecs expected) 0 state hIndex symbol

private theorem step_at (expected state : Nat) (tape : WorkTape)
    (hState : state < expected + 4) :
    workStep? (machine expected) { state := state, tape := tape } =
      some (applyWorkRule (ruleOf state (stateSpec expected state) tape.head)
        { state := state, tape := tape }) := by
  apply workStep?_eq_apply_of_find
  · simp only [WorkMachine.isHalted, machine, Bool.or_eq_false_iff,
      beq_eq_false_iff_ne]
    constructor <;> omega
  · exact lookup expected state hState tape.head

private theorem source_lt (specs : List StateSpec) (base : Nat) (rule : WorkRule)
    (hMem : rule ∈ rulesFrom base specs) : rule.sourceState < base + specs.length := by
  induction specs generalizing base with
  | nil => cases hMem
  | cons spec rest ih =>
      rw [rulesFrom, List.mem_append] at hMem
      rcases hMem with hHead | hTail
      · rcases List.mem_map.mp hHead with ⟨symbol, _, hRule⟩
        rw [← hRule]
        simp only [ruleOf, List.length_cons]
        omega
      · have h := ih (base + 1) hTail
        simp only [List.length_cons]
        omega

theorem rules_length (expected : Nat) :
    (machine expected).rules.length = 9 * (expected + 4) := by
  simp only [machine, rulesFrom_length, stateSpecs, List.length_ofFn]

theorem rules_pairwise_query_distinct (expected : Nat) :
    (machine expected).rules.Pairwise WorkMachineChain.QueryDistinct :=
  rulesFrom_pairwise_query_distinct 0 (stateSpecs expected)

theorem noRuleAtAccept (expected : Nat) : WorkMachineChain.NoRuleAtAccept (machine expected) := by
  intro rule hMem
  have h := source_lt (stateSpecs expected) 0 rule hMem
  simp only [stateSpecs, List.length_ofFn, Nat.zero_add] at h
  exact Nat.ne_of_lt h

theorem noRuleAtReject (expected : Nat) :
    WorkMachineProgramGraph.NoRuleAt (machine expected) (machine expected).rejectState := by
  intro rule hMem
  have h := source_lt (stateSpecs expected) 0 rule hMem
  simp only [stateSpecs, List.length_ofFn, Nat.zero_add] at h
  change rule.sourceState ≠ expected + 5
  omega

theorem acceptState_ne_rejectState (expected : Nat) :
    (machine expected).acceptState ≠ (machine expected).rejectState := by
  change expected + 4 ≠ expected + 5
  omega

private def restoredTape (tag : Nat) (suffix tail : List WorkSymbol) : WorkTape :=
  { left := tail, head := scratchEndSymbol,     right := List.replicate tag unitSymbol ++ separatorSymbol :: suffix }

private def scanTape (seen : Nat) : Nat → List WorkSymbol → List WorkSymbol → WorkTape
  | 0, suffix, tail =>
      { left := List.replicate seen unitSymbol ++ scratchEndSymbol :: tail,         head := separatorSymbol, right := suffix }
  | remaining + 1, suffix, tail =>
      { left := List.replicate seen unitSymbol ++ scratchEndSymbol :: tail,         head := unitSymbol, right := List.replicate remaining unitSymbol ++ separatorSymbol :: suffix }

private def rewindTape : Nat → List WorkSymbol → List WorkSymbol → WorkTape
  | 0, suffix, tail => { left := tail, head := scratchEndSymbol, right := suffix }
  | seen + 1, suffix, tail =>
      { left := List.replicate seen unitSymbol ++ scratchEndSymbol :: tail,         head := unitSymbol, right := suffix }

private theorem rewind_spec_eq (expected : Nat) (equal : Bool) :
    stateSpec expected (rewindState expected equal) = rewindSpec expected equal := by
  funext read
  cases equal <;> simp [stateSpec, rewindState]

private theorem end_ne_unit : scratchEndSymbol ≠ unitSymbol := by decide

private theorem separator_ne_unit : separatorSymbol ≠ unitSymbol := by decide

private theorem rewind_run (expected : Nat) (equal : Bool) (seen : Nat)
    (suffix tail : List WorkSymbol) :
    workRunExact? (machine expected) (seen + 1)
      { state := rewindState expected equal, tape := rewindTape seen suffix tail } =
      some { state := resultState expected equal, tape := { left := tail, head := scratchEndSymbol,           right := List.replicate seen unitSymbol ++ suffix } } := by
  have hState : rewindState expected equal < expected + 4 := by
    cases equal <;> simp [rewindState]
  induction seen generalizing suffix with
  | zero =>
      have hStep : workStep? (machine expected)
          { state := rewindState expected equal, tape := rewindTape 0 suffix tail } =
          some { state := resultState expected equal, tape := { left := tail,             head := scratchEndSymbol, right := suffix } } := by
        have h := step_at expected (rewindState expected equal) (rewindTape 0 suffix tail) hState
        simpa [rewind_spec_eq, ruleOf, rewindSpec, rewindTape, applyWorkRule,
          keepAction, WorkTape.write, WorkTape.move, end_ne_unit] using h
      simp only [workRunExact?, hStep, List.replicate_zero, List.nil_append]
  | succ seen ih =>
      have hStep : workStep? (machine expected)
          { state := rewindState expected equal, tape := rewindTape (seen + 1) suffix tail } =
          some { state := rewindState expected equal, tape := rewindTape seen (unitSymbol :: suffix) tail } := by
        have h := step_at expected (rewindState expected equal) (rewindTape (seen + 1) suffix tail) hState
        cases seen <;> simpa [rewind_spec_eq, ruleOf, rewindSpec, rewindTape, applyWorkRule,
          keepAction, WorkTape.write, WorkTape.move, WorkTape.moveLeft,
          List.replicate_succ] using h
      rw [workRunExact?, hStep]
      simpa only [List.replicate_succ', List.append_assoc, List.singleton_append] using
        ih (unitSymbol :: suffix)

private theorem scan_spec_eq (expected seen : Nat) (hSeen : seen ≤ expected) :
    stateSpec expected (seen + 1) = scanSpec expected seen := by
  funext read
  simp [stateSpec, show seen + 1 ≤ expected + 1 by omega]

private theorem replicate_sum (left right : Nat) :
    List.replicate (left + right) unitSymbol =
      List.replicate left unitSymbol ++ List.replicate right unitSymbol := by
  induction left with
  | zero => simp only [Nat.zero_add, List.replicate_zero, List.nil_append]
  | succ left ih =>
      simp only [Nat.succ_add, List.replicate_succ, ih, List.cons_append]

private theorem scan_run (expected remaining seen : Nat) (hSeen : seen ≤ expected)
    (suffix tail : List WorkSymbol) :
    workRunExact? (machine expected) (seen + 2 * min remaining (expected - seen) + 2)
      { state := seen + 1, tape := scanTape seen remaining suffix tail } =
      some { state := resultState expected (decide (seen + remaining = expected)), tape := restoredTape (seen + remaining) suffix tail } := by
  induction remaining generalizing seen with
  | zero =>
      have hStep : workStep? (machine expected)
          { state := seen + 1, tape := scanTape seen 0 suffix tail } =
          some { state := rewindState expected (decide (seen = expected)), tape := rewindTape seen (separatorSymbol :: suffix) tail } := by
        have h := step_at expected (seen + 1) (scanTape seen 0 suffix tail) (by omega)
        cases seen <;> simpa [scan_spec_eq, hSeen, ruleOf, scanSpec, scanTape,
          rewindTape, applyWorkRule, keepAction, WorkTape.write, WorkTape.move,
          WorkTape.moveLeft, List.replicate_succ, separator_ne_unit] using h
      have hMin : min 0 (expected - seen) = 0 := by omega
      simp only [hMin, Nat.mul_zero, Nat.add_zero]
      rw [show seen + 2 = (seen + 1) + 1 by omega, workRunExact?, hStep]
      exact rewind_run expected (decide (seen = expected)) seen (separatorSymbol :: suffix) tail
  | succ remaining ih =>
      by_cases hEqual : seen = expected
      · subst seen
        have hStep : workStep? (machine expected)
            { state := expected + 1, tape := scanTape expected (remaining + 1) suffix tail } =
            some { state := rewindState expected false, tape := rewindTape expected                 (List.replicate (remaining + 1) unitSymbol ++ separatorSymbol :: suffix) tail } := by
          have h := step_at expected (expected + 1)
            (scanTape expected (remaining + 1) suffix tail) (by omega)
          cases expected <;> simpa [scan_spec_eq, ruleOf, scanSpec, scanTape,
            rewindTape, applyWorkRule, keepAction, WorkTape.write, WorkTape.move,
            WorkTape.moveLeft, List.replicate_succ] using h
        have hMin : min (remaining + 1) (expected - expected) = 0 := by omega
        simp only [hMin, Nat.mul_zero, Nat.add_zero]
        rw [show expected + 2 = (expected + 1) + 1 by omega, workRunExact?, hStep]
        have hNot : expected + (remaining + 1) ≠ expected := by omega
        simpa only [hNot, decide_false, restoredTape, replicate_sum, List.append_assoc] using
          rewind_run expected false expected
            (List.replicate (remaining + 1) unitSymbol ++ separatorSymbol :: suffix) tail
      · have hLt : seen < expected := by omega
        have hStep : workStep? (machine expected)
            { state := seen + 1, tape := scanTape seen (remaining + 1) suffix tail } =
            some { state := (seen + 1) + 1, tape := scanTape (seen + 1) remaining suffix tail } := by
          have h := step_at expected (seen + 1) (scanTape seen (remaining + 1) suffix tail) (by omega)
          cases remaining <;> simpa [scan_spec_eq, hSeen, ruleOf, scanSpec, hLt, scanTape,
            applyWorkRule, keepAction, WorkTape.write, WorkTape.move, WorkTape.moveRight,
            List.replicate_succ] using h
        have hMin : min (remaining + 1) (expected - seen) =
            min remaining (expected - (seen + 1)) + 1 := by omega
        rw [hMin, show seen + 2 * (min remaining (expected - (seen + 1)) + 1) + 2 =
          ((seen + 1) + 2 * min remaining (expected - (seen + 1)) + 2) + 1 by omega,
          workRunExact?, hStep]
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          ih (seen + 1) (by omega)

def workSteps (expected actual : Nat) : Nat := 2 * min actual expected + 3

def finalConfiguration (expected actual : Nat) (older : List Nat)
    (workspace tail : List WorkSymbol) : WorkConfiguration :=
  { state := resultState expected (decide (actual = expected)),     tape := endTape (older ++ [actual]) workspace tail }

/-- Both outcomes restore every register, both tape tails and the original focus. -/
theorem workRunExact (expected actual : Nat) (older : List Nat)
    (workspace tail : List WorkSymbol) :
    workRunExact? (machine expected) (workSteps expected actual)
      (workStartConfiguration (machine expected) (endTape (older ++ [actual]) workspace tail)) =
      some (finalConfiguration expected actual older workspace tail) := by
  let suffix := (registerWord older).reverse ++ workspace
  have hTape : endTape (older ++ [actual]) workspace tail = restoredTape actual suffix tail := by
    simp only [endTape, restoredTape, suffix, registerWord_append, registerWord,
      List.append_nil, List.reverse_append, List.reverse_cons, List.nil_append,
      List.reverse_replicate, List.append_assoc, List.cons_append]
  rw [hTape]
  have hStep : workStep? (machine expected)
      (workStartConfiguration (machine expected) (restoredTape actual suffix tail)) =
      some { state := 1, tape := scanTape 0 actual suffix tail } := by
    have h := step_at expected 0 (restoredTape actual suffix tail) (by omega)
    cases actual <;> simpa [stateSpec, ruleOf, applyWorkRule, keepAction,
      restoredTape, scanTape, workStartConfiguration, machine, WorkTape.write,
      WorkTape.move, WorkTape.moveRight, List.replicate_succ] using h
  unfold workSteps
  rw [show 2 * min actual expected + 3 = (2 * min actual expected + 2) + 1 by omega,
    workRunExact?, hStep]
  have hRun := scan_run expected actual 0 (by omega) suffix tail
  simpa only [Nat.zero_add, Nat.sub_zero, finalConfiguration, hTape] using hRun

theorem run_compile_exact (expected actual : Nat) (older : List Nat)
    (workspace tail : List WorkSymbol) :
    run (compileWorkMachine (machine expected)) (6 * workSteps expected actual)
      (encodeWorkConfiguration (workStartConfiguration (machine expected)
        (endTape (older ++ [actual]) workspace tail))) =
      encodeWorkConfiguration (finalConfiguration expected actual older workspace tail) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact expected actual older workspace tail)

theorem accept_workRunExact (expected : Nat) (older : List Nat) (workspace tail : List WorkSymbol) :
    workRunExact? (machine expected) (workSteps expected expected)
      (workStartConfiguration (machine expected) (endTape (older ++ [expected]) workspace tail)) =
      some { state := (machine expected).acceptState, tape := endTape (older ++ [expected]) workspace tail } := by
  simpa [finalConfiguration, resultState, machine] using workRunExact expected expected older workspace tail

theorem reject_workRunExact (expected actual : Nat) (older : List Nat)
    (workspace tail : List WorkSymbol) (hNe : actual ≠ expected) :
    workRunExact? (machine expected) (workSteps expected actual)
      (workStartConfiguration (machine expected) (endTape (older ++ [actual]) workspace tail)) =
      some { state := (machine expected).rejectState, tape := endTape (older ++ [actual]) workspace tail } := by
  simpa [finalConfiguration, resultState, hNe, machine] using workRunExact expected actual older workspace tail

theorem workSteps_le (expected actual : Nat) : workSteps expected actual ≤ 2 * expected + 3 := by
  unfold workSteps
  omega

theorem invalid_entry (expected : Nat) (tape : WorkTape) (hHead : tape.head ≠ scratchEndSymbol) :
    workStep? (machine expected) (workStartConfiguration (machine expected) tape) =
      some { state := expected + 6, tape := tape } := by
  have h := step_at expected 0 tape (by omega)
  simpa [stateSpec, hHead, ruleOf, deadAction, keepAction, applyWorkRule,
    WorkTape.write, WorkTape.move, workStartConfiguration, machine] using h

end PNP.Concrete.CookLevin.BuilderUnaryTagMatch
