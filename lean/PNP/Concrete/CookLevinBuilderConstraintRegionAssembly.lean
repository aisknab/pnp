/-
Copyright (c) 2026 PNP Labs.

Physically assemble all five source-derived constraint-region lengths and the
computed constraint coordinate. The initial region's three fixed opportunities
and final acceptance are written by literal machines. Control depends only on
the verifier, not the input or a supplied selected region. Original registers
and the represented input/output remain intact.

This prepares the general dispatcher. It does not execute region selection,
local constraint decoding, clause occupancy, emission, Finish or the full loop.
-/

import PNP.Concrete.CookLevinBuilderConstraintRegionRegisters

namespace PNP.Concrete.CookLevin.BuilderConstraintRegionAssembly

open PipelineTape PipelineStateNamespace BuilderUnaryPolynomial
open BuilderDividerOperands (endTape inside count width quadratic)
open BuilderClauseDividerOperands (clauseWidth quotient)
open BuilderClauseDividerExecution (constraintIndex clauseIndex)
open BuilderConstraintRegionRegisters (termValue regionLength orderedLengths)
open BuilderDividerSourceExecution (sourceSpan)

private theorem chain_run (first second : WorkMachine) (firstSteps secondSteps : Nat)
    (initial middle final : WorkTape)
    (hFirst : workRunExact? first firstSteps (workStartConfiguration first initial) =
      some { state := first.acceptState, tape := middle })
    (hSecond : workRunExact? second secondSteps (workStartConfiguration second middle) =
      some { state := second.acceptState, tape := final }) :
    workRunExact? (WorkMachineChain.machine first second) (firstSteps + 1 + secondSteps)
      (workStartConfiguration (WorkMachineChain.machine first second) initial) =
      some { state := (WorkMachineChain.machine first second).acceptState, tape := final } :=
  WorkMachineChain.workRunExact first second firstSteps secondSteps _ _ _ hFirst rfl hSecond

private theorem configuration_eq_of_fields (config : WorkConfiguration) (state : Nat)
    (tape : WorkTape) (hState : config.state = state) (hTape : config.tape = tape) :
    config = { state := state, tape := tape } := by
  cases config with
  | mk currentState currentTape =>
    change currentState = state at hState
    change currentTape = tape at hTape
    subst currentState
    subst currentTape
    rfl

private def Good (machine : WorkMachine) : Prop :=
  machine.rules.Pairwise WorkMachineChain.QueryDistinct ∧
  WorkMachineChain.NoRuleAtAccept machine ∧ machine.acceptState ≠ machine.rejectState

private theorem chain_good (first second : WorkMachine) (hFirst : Good first) (hSecond : Good second) :
    Good (WorkMachineChain.machine first second) :=
  ⟨WorkMachineChain.rules_pairwise_query_distinct first second hFirst.1 hSecond.1 hFirst.2.1,
   WorkMachineChain.noRuleAtAccept first second hSecond.2.1,
   WorkMachineChain.machine_acceptState_ne_rejectState first second hSecond.2.2⟩

namespace Increment

private def firstSpec : StateSpec := fun read =>
  if read = scratchEndSymbol then writeAction 1 unitSymbol .left else deadAction 3 read

private def secondSpec : StateSpec := fun _ => writeAction 2 scratchEndSymbol .stay

/-- Extend the most recent unary value by one actual cell. -/
def machine : WorkMachine :=
  { rules := rulesFrom 0 [firstSpec, secondSpec],
    startState := 0, acceptState := 2, rejectState := 3 }

theorem rules_length : machine.rules.length = 18 := rfl

theorem rules_pairwise_query_distinct :
    machine.rules.Pairwise WorkMachineChain.QueryDistinct :=
  rulesFrom_pairwise_query_distinct 0 [firstSpec, secondSpec]

theorem noRuleAtAccept : WorkMachineChain.NoRuleAtAccept machine := by
  intro rule hRule
  change rule.sourceState ≠ 2
  change rule ∈ rulesFrom 0 [firstSpec, secondSpec] at hRule
  decide +revert

theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := by decide

private theorem second_step (left right : List WorkSymbol) (symbol : WorkSymbol) :
    workStep? machine { state := 1, tape := { left := left, head := symbol, right := right } } =
      some { state := 2, tape := { left := left, head := scratchEndSymbol, right := right } } := by
  have hFind := findWorkRule_rulesFrom_at_append 0 [firstSpec] secondSpec [] symbol
  exact workStep?_eq_apply_of_find machine _ (ruleOf 1 secondSpec symbol) rfl hFind

theorem reverse_word_increment (older : List Nat) (value : Nat) :
    (registerWord (older ++ [value + 1])).reverse =
      unitSymbol :: (registerWord (older ++ [value])).reverse := by
  simp only [registerWord_append, registerWord, List.append_nil,
    List.reverse_append, List.reverse_cons, List.reverse_replicate, List.reverse_nil,
    List.nil_append, List.replicate_succ', List.cons_append, List.append_assoc]

theorem workRunExact (older : List Nat) (value : Nat) (workspace tail : List WorkSymbol) :
    workRunExact? machine 2
      (workStartConfiguration machine (endTape (older ++ [value]) workspace tail)) =
      some {
        state := machine.acceptState
        tape := endTape (older ++ [value + 1]) workspace (tail.drop 1)
      } := by
  let middle : WorkConfiguration :=
    {
      state := 1
      tape := {
        left := tail.drop 1
        head := tail.headD .blank
        right := unitSymbol :: ((registerWord (older ++ [value])).reverse ++ workspace)
      }
    }
  have hFirst : workStep? machine
      (workStartConfiguration machine (endTape (older ++ [value]) workspace tail)) =
      some middle := by
    cases tail <;> rfl
  have hSecond : workStep? machine middle =
      some { state := machine.acceptState, tape := endTape (older ++ [value + 1]) workspace (tail.drop 1) } := by
    rw [show machine.acceptState = 2 from rfl]
    simpa only [middle, endTape, reverse_word_increment, List.cons_append] using
      second_step (tail.drop 1)
        (unitSymbol :: ((registerWord (older ++ [value])).reverse ++ workspace)) (tail.headD .blank)
  simp only [workRunExact?, hFirst, hSecond]

end Increment

private theorem increment_good : Good Increment.machine :=
  ⟨Increment.rules_pairwise_query_distinct, Increment.noRuleAtAccept, Increment.acceptState_ne_rejectState⟩

private theorem delimiter_good : Good BuilderDividerOperands.Delimiter.machine :=
  ⟨BuilderDividerOperands.Delimiter.rules_pairwise_query_distinct,
   BuilderDividerOperands.Delimiter.noRuleAtAccept,
   BuilderDividerOperands.Delimiter.acceptState_ne_rejectState⟩

/-- Allocate the literal one, never a supplied acceptance length. -/
def oneMachine : WorkMachine :=
  WorkMachineChain.machine BuilderDividerOperands.Delimiter.machine Increment.machine

theorem one_workRunExact (values : List Nat) (workspace tail : List WorkSymbol) :
    workRunExact? oneMachine 5
      (workStartConfiguration oneMachine (endTape values workspace tail)) =
      some { state := oneMachine.acceptState, tape := endTape (values ++ [1]) workspace (tail.drop 2) } := by
  have hFirst := BuilderDividerOperands.Delimiter.workRunExact values workspace tail
  have hSecond := Increment.workRunExact values 0 workspace (tail.drop 1)
  have h := chain_run BuilderDividerOperands.Delimiter.machine Increment.machine 2 2 _ _ _ hFirst hSecond
  simpa only [oneMachine, List.drop_drop] using h

/-- Three literal increments, with both internal control bridges charged. -/
def threeMachine : WorkMachine :=
  WorkMachineChain.machine Increment.machine
    (WorkMachineChain.machine Increment.machine Increment.machine)

theorem three_workRunExact (older : List Nat) (value : Nat) (workspace tail : List WorkSymbol) :
    workRunExact? threeMachine 8
      (workStartConfiguration threeMachine (endTape (older ++ [value]) workspace tail)) =
      some { state := threeMachine.acceptState, tape := endTape (older ++ [value + 3]) workspace (tail.drop 3) } := by
  have hFirst := Increment.workRunExact older value workspace tail
  have hSecond := Increment.workRunExact older (value + 1) workspace (tail.drop 1)
  have hThird := Increment.workRunExact older (value + 1 + 1) workspace ((tail.drop 1).drop 1)
  have hLast := chain_run Increment.machine Increment.machine 2 2 _ _ _ hSecond hThird
  have h := chain_run Increment.machine (WorkMachineChain.machine Increment.machine Increment.machine)
    2 5 _ _ _ hFirst hLast
  simpa only [threeMachine, Nat.add_assoc, List.drop_drop] using h

private theorem one_good : Good oneMachine :=
  chain_good _ _ delimiter_good increment_good

private theorem three_good : Good threeMachine :=
  chain_good _ _ increment_good (chain_good _ _ increment_good increment_good)

def afterPreservation {language : Language} (problem : VerifierTableauProblem language) : List Nat :=
  [1, termValue problem .preservation]

def afterControl {language : Language} (problem : VerifierTableauProblem language) : List Nat :=
  [1, termValue problem .preservation, termValue problem .control]

def beforeInitialAdjustment {language : Language} (problem : VerifierTableauProblem language) : List Nat :=
  [1, termValue problem .preservation, termValue problem .control, termValue problem .initialTail]

def afterInitial {language : Language} (problem : VerifierTableauProblem language) : List Nat :=
  [1, termValue problem .preservation, termValue problem .control, regionLength problem .initial]

/-- Reverse physical order lets the dispatcher read the coordinate, then shape through acceptance. -/
def lengthFrame {language : Language} (problem : VerifierTableauProblem language) : List Nat :=
  [1, termValue problem .preservation, termValue problem .control,
   regionLength problem .initial, termValue problem .shape]

theorem lengthFrame_reverse {language : Language} (problem : VerifierTableauProblem language) :
    (lengthFrame problem).reverse = orderedLengths problem := by
  rw [BuilderConstraintRegionRegisters.orderedLengths_values]
  rfl

theorem lengthFrame_sum {language : Language} (problem : VerifierTableauProblem language) :
    (lengthFrame problem).sum = problem.formulaConstraintSlotCount := by
  have h := BuilderConstraintRegionRegisters.orderedLengths_sum problem
  rw [← lengthFrame_reverse, List.sum_reverse] at h
  exact h

def preparedFrame {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : List Nat :=
  lengthFrame problem ++ [constraintIndex problem index]

theorem preparedFrame_reverse {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    (preparedFrame problem index).reverse = constraintIndex problem index :: orderedLengths problem := by
  simp only [preparedFrame, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, lengthFrame_reverse]

theorem preparedFrame_length {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    (preparedFrame problem index).length = 6 := rfl

theorem preparedFrame_sum {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    (preparedFrame problem index).sum = problem.formulaConstraintSlotCount + constraintIndex problem index := by
  simp only [preparedFrame, List.sum_append, lengthFrame_sum, List.sum_cons, List.sum_nil, Nat.add_zero]

private def beforeIndex {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) : List Nat :=
  BuilderOperandRegisters.retainedValues problem index remaining ++
    [count problem, 0, index, width problem, quotient problem index, count problem, 0,
     constraintIndex problem index * clauseWidth problem, clauseIndex problem index, clauseWidth problem]

private theorem coordinate_word_split {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) :
    BuilderClauseCoordinateRegisters.finalValues problem index remaining =
      beforeIndex problem index remaining ++ [constraintIndex problem index] := by
  rw [BuilderClauseCoordinateRegisters.finalValues_eq]
  simp only [beforeIndex, List.append_assoc, List.cons_append, List.nil_append]

private theorem index_copy (older newer : List Nat) (index : Nat) (workspace tail : List WorkSymbol)
    (hLength : newer.length = 5) :
    workRunExact? (RegisterCopy.machine 5) (RegisterCopy.steps newer index)
      (workStartConfiguration (RegisterCopy.machine 5) (endTape (older ++ [index] ++ newer) workspace tail)) =
      some {
        state := (RegisterCopy.machine 5).acceptState
        tape := endTape (older ++ [index] ++ newer ++ [index]) workspace (tail.drop (index + 1))
      } := by
  rw [← hLength, RegisterCopy.machine_acceptState]
  have h := RegisterCopy.workRunExact (registerWord older) workspace tail index newer
  change workRunExact? (RegisterCopy.machine newer.length) (RegisterCopy.steps newer index)
      {
        state := 0
        tape := {
          left := tail
          head := scratchEndSymbol
          right := (registerWord older ++ registerWord ([index] ++ newer)).reverse ++ workspace
        }
      } = some {
        state := RegisterCopy.stateCount newer.length
        tape := {
          left := tail.drop (index + 1)
          head := scratchEndSymbol
          right := (registerWord older ++ registerWord ([index] ++ newer ++ [index])).reverse ++ workspace
        }
      } at h
  simpa only [workStartConfiguration, RegisterCopy.machine_startState, endTape,
    registerWord_append, List.append_assoc] using h

/-- Seven real stages. Every copy count is fixed independently of the input. -/
def machine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineChain.machine oneMachine
    (WorkMachineChain.machine (BuilderConstraintRegionRegisters.copyMachine verifier .preservation 1)
      (WorkMachineChain.machine (BuilderConstraintRegionRegisters.copyMachine verifier .control 2)
        (WorkMachineChain.machine (BuilderConstraintRegionRegisters.copyMachine verifier .initialTail 3)
          (WorkMachineChain.machine threeMachine
            (WorkMachineChain.machine (BuilderConstraintRegionRegisters.copyMachine verifier .shape 4)
              (RegisterCopy.machine 5))))))

def workSteps {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) : Nat :=
  BuilderConstraintRegionRegisters.copySteps problem index remaining [1] .preservation +
    BuilderConstraintRegionRegisters.copySteps problem index remaining (afterPreservation problem) .control +
    BuilderConstraintRegionRegisters.copySteps problem index remaining (afterControl problem) .initialTail +
    BuilderConstraintRegionRegisters.copySteps problem index remaining (afterInitial problem) .shape +
    RegisterCopy.steps (lengthFrame problem) (constraintIndex problem index) + 19

def finalValues {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) : List Nat :=
  BuilderClauseCoordinateRegisters.finalValues problem index remaining ++ preparedFrame problem index

def consumedCells {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : Nat :=
  problem.formulaConstraintSlotCount + constraintIndex problem index + 6

theorem workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (workspace tail : List WorkSymbol) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
      (workStartConfiguration (machine problem.verifier)
        (endTape (BuilderClauseCoordinateRegisters.finalValues problem index remaining) workspace tail)) =
      some {
        state := (machine problem.verifier).acceptState
        tape := endTape (finalValues problem index remaining) workspace (tail.drop (consumedCells problem index))
      } := by
  let base := BuilderClauseCoordinateRegisters.finalValues problem index remaining
  let tail1 := tail.drop 2
  let tail2 := tail1.drop (termValue problem .preservation + 1)
  let tail3 := tail2.drop (termValue problem .control + 1)
  let tail4 := tail3.drop (termValue problem .initialTail + 1)
  let tail5 := tail4.drop 3
  let tail6 := tail5.drop (termValue problem .shape + 1)
  have hOne := one_workRunExact base workspace tail
  have hPreservation := BuilderConstraintRegionRegisters.copy_workRunExact
    problem index remaining [1] .preservation workspace tail1
  have hControl := BuilderConstraintRegionRegisters.copy_workRunExact
    problem index remaining (afterPreservation problem) .control workspace tail2
  have hInitial := BuilderConstraintRegionRegisters.copy_workRunExact
    problem index remaining (afterControl problem) .initialTail workspace tail3
  have hAdjust := three_workRunExact (base ++ afterControl problem) (termValue problem .initialTail) workspace tail4
  have hShape := BuilderConstraintRegionRegisters.copy_workRunExact
    problem index remaining (afterInitial problem) .shape workspace tail5
  have hIndex : workRunExact? (RegisterCopy.machine 5)
      (RegisterCopy.steps (lengthFrame problem) (constraintIndex problem index))
      (workStartConfiguration (RegisterCopy.machine 5) (endTape (base ++ lengthFrame problem) workspace tail6)) =
      some {
        state := (RegisterCopy.machine 5).acceptState
        tape := endTape (base ++ preparedFrame problem index) workspace (tail6.drop (constraintIndex problem index + 1))
      } := by
    dsimp only [base]
    rw [coordinate_word_split]
    simpa only [preparedFrame, List.append_assoc] using
      index_copy (beforeIndex problem index remaining) (lengthFrame problem)
        (constraintIndex problem index) workspace tail6 rfl
  have hInitialLength : termValue problem .initialTail + 3 = regionLength problem .initial := by
    change termValue problem .initialTail + 3 = 3 + termValue problem .initialTail
    omega
  simp only [BuilderConstraintRegionRegisters.inputValues, List.append_assoc, List.cons_append,
    List.nil_append] at hPreservation hControl hInitial hShape
  simp only [hInitialLength, List.append_assoc] at hAdjust
  have hTail : tail6.drop (constraintIndex problem index + 1) =
      tail.drop (consumedCells problem index) := by
    have hCount := BuilderConstraintRegionRegisters.orderedLengths_sum problem
    rw [BuilderConstraintRegionRegisters.orderedLengths_values] at hCount
    simp only [List.sum_cons, List.sum_nil] at hCount
    simp only [tail6, tail5, tail4, tail3, tail2, tail1, List.drop_drop]
    apply congrArg (fun offset : Nat => tail.drop offset)
    unfold consumedCells
    omega
  have hLast := chain_run _ _ _ _ _ _ _ hShape hIndex
  have hAdjusted := chain_run _ _ _ _ _ _ _ hAdjust hLast
  have hInitialFull := chain_run _ _ _ _ _ _ _ hInitial hAdjusted
  have hControlFull := chain_run _ _ _ _ _ _ _ hControl hInitialFull
  have hPreservationFull := chain_run _ _ _ _ _ _ _ hPreservation hControlFull
  have h := chain_run _ _ _ _ _ _ _ hOne hPreservationFull
  have hCost : 5 + 1 +
      (BuilderConstraintRegionRegisters.copySteps problem index remaining [1] .preservation + 1 +
        (BuilderConstraintRegionRegisters.copySteps problem index remaining (afterPreservation problem) .control + 1 +
          (BuilderConstraintRegionRegisters.copySteps problem index remaining (afterControl problem) .initialTail + 1 +
            (8 + 1 + (BuilderConstraintRegionRegisters.copySteps problem index remaining (afterInitial problem) .shape + 1 +
              RegisterCopy.steps (lengthFrame problem) (constraintIndex problem index)))))) =
      workSteps problem index remaining := by
    unfold workSteps
    omega
  have hLength1 : ([1] : List Nat).length = 1 := rfl
  have hLength2 : (afterPreservation problem).length = 2 := rfl
  have hLength3 : (afterControl problem).length = 3 := rfl
  have hLength4 : (afterInitial problem).length = 4 := rfl
  unfold machine
  simpa only [hCost, hTail, finalValues, base, hLength1, hLength2, hLength3, hLength4] using h

theorem run_compile_exact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (workspace tail : List WorkSymbol) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining)
      (encodeWorkConfiguration (workStartConfiguration (machine problem.verifier)
        (endTape (BuilderClauseCoordinateRegisters.finalValues problem index remaining) workspace tail))) =
      encodeWorkConfiguration {
        state := (machine problem.verifier).acceptState
        tape := endTape (finalValues problem index remaining) workspace (tail.drop (consumedCells problem index))
      } :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact problem index remaining workspace tail)

private theorem copy_good {language : Language} (verifier : PolynomialTimeVerifier language)
    (term : BuilderConstraintRegionRegisters.Term) (extra : Nat) :
    Good (BuilderConstraintRegionRegisters.copyMachine verifier term extra) :=
  ⟨BuilderConstraintRegionRegisters.copy_rules_pairwise_query_distinct verifier term extra,
   BuilderConstraintRegionRegisters.copy_noRuleAtAccept verifier term extra,
   BuilderConstraintRegionRegisters.copy_acceptState_ne_rejectState verifier term extra⟩

private theorem index_good : Good (RegisterCopy.machine 5) := by
  refine ⟨RegisterCopy.rules_pairwise_query_distinct 5, ?_, RegisterCopy.machine_acceptState_ne_rejectState 5⟩
  intro rule hRule
  exact Nat.ne_of_lt (RegisterCopy.rule_source_lt_acceptState 5 rule hRule)

private theorem machine_good {language : Language} (verifier : PolynomialTimeVerifier language) :
    Good (machine verifier) :=
  chain_good _ _ one_good
    (chain_good _ _ (copy_good verifier .preservation 1)
      (chain_good _ _ (copy_good verifier .control 2)
        (chain_good _ _ (copy_good verifier .initialTail 3)
          (chain_good _ _ three_good
            (chain_good _ _ (copy_good verifier .shape 4) index_good)))))

theorem rules_pairwise_query_distinct {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct :=
  (machine_good verifier).1

theorem noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (machine verifier) := (machine_good verifier).2.1

theorem acceptState_ne_rejectState {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState := (machine_good verifier).2.2

/-- The full constraint count is bounded by the already-retained clause count. -/
theorem constraintCount_le_sourceSpan {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    problem.formulaConstraintSlotCount ≤ (sourceSpan problem.verifier).eval problem.input.length := by
  have hWidth := BuilderClauseDividerOperands.clauseWidth_pos problem
  have hOne : 1 ≤ clauseWidth problem := by omega
  calc
    problem.formulaConstraintSlotCount = problem.formulaConstraintSlotCount * 1 := (Nat.mul_one _).symm
    _ ≤ problem.formulaConstraintSlotCount * clauseWidth problem := Nat.mul_le_mul_left _ hOne
    _ = count problem := (BuilderClauseDividerOperands.clauseCount_product problem).symm
    _ ≤ (sourceSpan problem.verifier).eval problem.input.length :=
      BuilderDividerSourceExecution.operand_le_sourceSpan problem .clauseCount index remaining hBalance

private theorem constraintIndex_le_sourceSpan {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    constraintIndex problem index ≤ (sourceSpan problem.verifier).eval problem.input.length :=
  (BuilderClauseCoordinateRegisters.source_magnitudes_le problem index remaining hBalance).1

theorem consumedCells_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    consumedCells problem index ≤ 2 * (sourceSpan problem.verifier).eval problem.input.length + 6 := by
  have hCount := constraintCount_le_sourceSpan problem index remaining hBalance
  have hIndex := constraintIndex_le_sourceSpan problem index remaining hBalance
  unfold consumedCells
  omega

theorem final_register_span_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    (registerWord (finalValues problem index remaining)).length ≤
      11 * (sourceSpan problem.verifier).eval problem.input.length + 17 := by
  have hOld := BuilderClauseCoordinateRegisters.final_register_span_le problem index remaining hBalance
  have hConsumed := consumedCells_le problem index remaining hBalance
  have hLength : (registerWord (finalValues problem index remaining)).length =
      (registerWord (BuilderClauseCoordinateRegisters.finalValues problem index remaining)).length +
        consumedCells problem index := by
    simp only [finalValues, registerWord_length, List.length_append, List.sum_append,
      preparedFrame_length, preparedFrame_sum, consumedCells]
    omega
  rw [hLength]
  omega

private def copyFrame {language : Language} (problem : VerifierTableauProblem language) :
    BuilderConstraintRegionRegisters.Term → List Nat
  | .preservation => [1]
  | .control => afterPreservation problem
  | .initialTail => afterControl problem
  | .shape => afterInitial problem

private theorem copyFrame_bounds {language : Language} (problem : VerifierTableauProblem language)
    (term : BuilderConstraintRegionRegisters.Term) :
    (copyFrame problem term).length ≤ 5 ∧ (copyFrame problem term).sum ≤ problem.formulaConstraintSlotCount := by
  have hCount := lengthFrame_sum problem
  have hInitial : regionLength problem .initial = 3 + termValue problem .initialTail := rfl
  simp only [lengthFrame, List.sum_cons, List.sum_nil, hInitial] at hCount
  cases term <;>
    simp only [copyFrame, afterPreservation, afterControl, afterInitial, List.length_cons,
      List.length_nil, List.sum_cons, List.sum_nil, hInitial] <;> constructor <;> omega

private theorem quadratic_mono (left right : Nat) (h : left ≤ right) :
    quadratic left ≤ quadratic right := by
  have hPlus : left + 1 ≤ right + 1 := by omega
  unfold quadratic
  exact Nat.add_le_add_right
    (Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul_left 4 hPlus) hPlus)
      (Nat.mul_le_mul_left 9 hPlus)) 5

/-- Original source span plus all five length registers, without the final index copy. -/
def copyBudget {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (.mul (.constant 10) (sourceSpan verifier)) (.constant 16)

private theorem term_copy_steps_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (term : BuilderConstraintRegionRegisters.Term)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    BuilderConstraintRegionRegisters.copySteps problem index remaining (copyFrame problem term) term ≤
      quadratic ((copyBudget problem.verifier).eval problem.input.length) := by
  have hFrame := copyFrame_bounds problem term
  have hCount := constraintCount_le_sourceSpan problem index remaining hBalance
  have h := BuilderConstraintRegionRegisters.copySteps_le problem index remaining (copyFrame problem term) term hBalance
  have hBudget : 9 * (sourceSpan problem.verifier).eval problem.input.length + 11 +
      (copyFrame problem term).length + (copyFrame problem term).sum ≤
      (copyBudget problem.verifier).eval problem.input.length := by
    simp only [copyBudget, NatPolynomial.eval_add, NatPolynomial.eval_mul, NatPolynomial.eval_constant]
    omega
  apply Nat.le_trans _ (quadratic_mono _ _ hBudget)
  simpa only [quadratic, Nat.pow_two, Nat.mul_assoc] using h

private theorem index_copy_steps_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    RegisterCopy.steps (lengthFrame problem) (constraintIndex problem index) ≤
      quadratic ((copyBudget problem.verifier).eval problem.input.length) := by
  have hCount := constraintCount_le_sourceSpan problem index remaining hBalance
  have hIndex := constraintIndex_le_sourceSpan problem index remaining hBalance
  have hValue : constraintIndex problem index ≤ (copyBudget problem.verifier).eval problem.input.length := by
    simp only [copyBudget, NatPolynomial.eval_add, NatPolynomial.eval_mul, NatPolynomial.eval_constant]
    omega
  have hFrame : (lengthFrame problem).length + (lengthFrame problem).sum ≤
      (copyBudget problem.verifier).eval problem.input.length := by
    rw [lengthFrame_sum]
    change 5 + problem.formulaConstraintSlotCount ≤ _
    simp only [copyBudget, NatPolynomial.eval_add, NatPolynomial.eval_mul, NatPolynomial.eval_constant]
    omega
  exact RegisterCopy.steps_le _ _ _ hValue hFrame

theorem workSteps_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    workSteps problem index remaining ≤ 5 * quadratic ((copyBudget problem.verifier).eval problem.input.length) + 19 := by
  have hPreservation := term_copy_steps_le problem index remaining .preservation hBalance
  have hControl := term_copy_steps_le problem index remaining .control hBalance
  have hInitial := term_copy_steps_le problem index remaining .initialTail hBalance
  have hShape := term_copy_steps_le problem index remaining .shape hBalance
  have hIndex := index_copy_steps_le problem index remaining hBalance
  simp only [copyFrame] at hPreservation hControl hInitial hShape
  unfold workSteps
  omega

private def quadraticPolynomial (bound : NatPolynomial) : NatPolynomial :=
  let plus := NatPolynomial.add bound (.constant 1)
  .add (.add (.mul (.mul (.constant 4) plus) plus) (.mul (.constant 9) plus)) (.constant 5)

private theorem quadraticPolynomial_eval (bound : NatPolynomial) (input : Nat) :
    (quadraticPolynomial bound).eval input = quadratic (bound.eval input) := rfl

def rawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .mul (.constant 6)
    (.add (.mul (.constant 5) (quadraticPolynomial (copyBudget verifier))) (.constant 19))

theorem rawTimeBound_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    6 * workSteps problem index remaining ≤ (rawTimeBound problem.verifier).eval problem.input.length := by
  have h := workSteps_le problem index remaining hBalance
  simp only [rawTimeBound, NatPolynomial.eval_mul, NatPolynomial.eval_add,
    NatPolynomial.eval_constant, quadraticPolynomial_eval]
  exact Nat.mul_le_mul_left 6 h

/-- The previously verified source body is executed once, followed by real assembly. -/
def bodyMachine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineChain.machine (BuilderClauseCoordinateRegisters.machine verifier) (machine verifier)

def bodySteps {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) : Nat :=
  BuilderClauseCoordinateRegisters.workSteps problem index remaining + 1 + workSteps problem index remaining

def bodyInitial {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  workStartConfiguration (bodyMachine problem.verifier)
    (BuilderCursorSource.cursorTape problem index remaining output)

def bodyFinal {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  {
    state := (bodyMachine problem.verifier).acceptState
    tape := endTape (finalValues problem index remaining) (inside problem.input output) []
  }

private theorem source_initial_eq {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    BuilderClauseCoordinateRegisters.initialConfiguration problem index remaining output =
      workStartConfiguration (BuilderClauseCoordinateRegisters.machine problem.verifier)
        (BuilderCursorSource.cursorTape problem index remaining output) := rfl

private theorem source_final_eq {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    BuilderClauseCoordinateRegisters.finalConfiguration problem index remaining output =
      {
        state := (BuilderClauseCoordinateRegisters.machine problem.verifier).acceptState
        tape := endTape (BuilderClauseCoordinateRegisters.finalValues problem index remaining)
          (inside problem.input output) []
      } := by
  apply configuration_eq_of_fields
  · exact BuilderClauseCoordinateRegisters.finalConfiguration_state problem index remaining output
  · exact BuilderClauseCoordinateRegisters.final_tape_layout problem index remaining output

theorem body_workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (hBody : quotient problem index < count problem) :
    workRunExact? (bodyMachine problem.verifier) (bodySteps problem index remaining)
      (bodyInitial problem index remaining output) = some (bodyFinal problem index remaining output) := by
  have hSource := BuilderClauseCoordinateRegisters.workRunExact problem index remaining output hBody
  rw [source_initial_eq, source_final_eq] at hSource
  have hAssembly := workRunExact problem index remaining (inside problem.input output) []
  simp only [List.drop_nil] at hAssembly
  exact chain_run _ _ _ _ _ _ _ hSource hAssembly

theorem body_run_compile_exact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (hBody : quotient problem index < count problem) :
    run (compileWorkMachine (bodyMachine problem.verifier)) (6 * bodySteps problem index remaining)
      (encodeWorkConfiguration (bodyInitial problem index remaining output)) =
      encodeWorkConfiguration (bodyFinal problem index remaining output) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (body_workRunExact problem index remaining output hBody)

theorem body_constraintIndex_valid {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hBody : quotient problem index < count problem) :
    constraintIndex problem index < (lengthFrame problem).sum := by
  rw [lengthFrame_sum]
  exact BuilderClauseDividerExecution.constraintIndex_lt problem index hBody

def bodyRawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderClauseCoordinateRegisters.rawTimeBound verifier)
    (.add (.constant 6) (rawTimeBound verifier))

theorem body_rawTimeBound_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    6 * bodySteps problem index remaining ≤ (bodyRawTimeBound problem.verifier).eval problem.input.length := by
  have hSource := BuilderClauseCoordinateRegisters.rawTimeBound_le problem index remaining hBalance
  have hAssembly := rawTimeBound_le problem index remaining hBalance
  simp only [bodyRawTimeBound, NatPolynomial.eval_add, NatPolynomial.eval_constant]
  unfold bodySteps
  omega

private theorem body_good {language : Language} (verifier : PolynomialTimeVerifier language) :
    Good (bodyMachine verifier) :=
  chain_good _ _
    ⟨BuilderClauseCoordinateRegisters.rules_pairwise_query_distinct verifier,
     BuilderClauseCoordinateRegisters.noRuleAtAccept verifier,
     BuilderClauseCoordinateRegisters.acceptState_ne_rejectState verifier⟩ (machine_good verifier)

theorem body_rules_pairwise_query_distinct {language : Language} (verifier : PolynomialTimeVerifier language) :
    (bodyMachine verifier).rules.Pairwise WorkMachineChain.QueryDistinct := (body_good verifier).1

theorem body_noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (bodyMachine verifier) := (body_good verifier).2.1

theorem body_acceptState_ne_rejectState {language : Language} (verifier : PolynomialTimeVerifier language) :
    (bodyMachine verifier).acceptState ≠ (bodyMachine verifier).rejectState := (body_good verifier).2.2

end PNP.Concrete.CookLevin.BuilderConstraintRegionAssembly
