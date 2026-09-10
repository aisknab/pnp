/-
Copyright (c) 2026 PNP Labs.

Source-derived body-coordinate division for the complete Cook--Levin builder.
The verifier-fixed machine copies retained operands, converts their actual tape
layout, and runs the existing literal divider through spatial reflection.
No caller supplies a divider entry, operand certificate, or positive-width premise.

The original registers, input, and emitted output remain behind two boundaries.
This phase does not yet classify every body slot, restore the cursor workspace,
emit body tokens, or implement the complete schedule loop and reduction.
-/

import PNP.Concrete.CookLevinBuilderDividerLayout
import PNP.Concrete.CookLevinBuilderDividerFootprint
import PNP.Concrete.CookLevinBuilderPhysicalClassifierFinishMirroredDispatch

namespace PNP.Concrete.CookLevin.BuilderDividerSourceExecution

open PipelineTape PipelineStateNamespace BuilderUnaryPolynomial
open BuilderDividerOperands (count width)
open BuilderPhysicalClassifierFinishMirroredDispatch
  (mirrorTape mirrorMachine mirrorRule mirrorConfiguration workRunExact?_mirror_of_some
    mirrorRules_pairwise_query_distinct mirrorMachine_acceptState_ne_rejectState)

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

def preservedWorkspace {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : List WorkSymbol :=
  (registerWord (BuilderOperandRegisters.retainedValues problem index remaining)).reverse ++
    BuilderDividerOperands.inside problem.input output

/-- The divider supplies the first boundary; this exterior retains the second. -/
def exterior {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : List WorkSymbol :=
  leftMarker :: (List.replicate (count problem) unitSymbol ++ scratchEndSymbol ::
    preservedWorkspace problem index remaining output)

def layoutInitial {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  BuilderDividerLayout.initialConfiguration (count problem) index (width problem)
    (BuilderOperandRegisters.retainedValues problem index remaining)
    (BuilderDividerOperands.inside problem.input output) []

def layoutFinal {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  BuilderDividerLayout.finalConfiguration (count problem) index (width problem)
    (BuilderOperandRegisters.retainedValues problem index remaining)
    (BuilderDividerOperands.inside problem.input output) []

theorem operand_layout_handoff {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (BuilderDividerOperands.finalConfiguration problem index remaining output).tape =
      (layoutInitial problem index remaining output).tape := by
  rw [BuilderDividerOperands.final_tape_layout, BuilderDividerFootprint.preservedTail_eq_nil]
  simp only [List.drop_nil, layoutInitial, BuilderDividerLayout.initialConfiguration,
    workStartConfiguration, BuilderDividerOperands.endTape]

theorem convertedTape_eq_mirroredDividerInput (count index width : Nat)
    (workspace : List WorkSymbol) :
    BuilderDividerLayout.convertedTape count index width workspace [] =
      mirrorTape (BuilderPostHeaderRawTapeBridge.shieldedDividerInputTape index width
        (leftMarker :: (List.replicate count unitSymbol ++ scratchEndSymbol :: workspace))) := by
  unfold BuilderDividerLayout.convertedTape
  rw [List.append_nil]
  cases index <;>
    simp only [BuilderDividerLayout.dividerWord,
      BuilderPostHeaderRawTapeBridge.shieldedDividerInputTape,
      BuilderPostHeaderRawTapeBridge.dividerWord,
      List.replicate_zero, List.replicate_succ, List.nil_append, List.cons_append] <;> rfl

theorem layout_divider_handoff {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (layoutFinal problem index remaining output).tape =
      mirrorTape (BuilderPostHeaderRawTapeBridge.shieldedDividerInputTape index (width problem)
        (exterior problem index remaining output)) :=
  convertedTape_eq_mirroredDividerInput (count problem) index (width problem)
    (preservedWorkspace problem index remaining output)

theorem width_pos {language : Language} (problem : VerifierTableauProblem language) :
    0 < width problem := by
  change 0 < 2 + (problem.formulaVariableSlotBound + 4) * (problem.formulaVariableSlotBound + 1)
  omega

def preparedMachine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineChain.machine (BuilderDividerOperands.machine verifier) BuilderDividerLayout.machine

def dividerMachine : WorkMachine := mirrorMachine BuilderPostHeaderRawDivider.machine

/-- Only the verifier determines the finite control; operands come from the tape. -/
def machine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineChain.machine (preparedMachine verifier) dividerMachine

def dividerFinalTape {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkTape :=
  mirrorTape (BuilderPostHeaderRawTapeBridge.shieldedDividerFinalConfiguration index (width problem)
    (exterior problem index remaining output)).tape

def initialConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  workStartConfiguration (machine problem.verifier)
    (BuilderCursorSource.cursorTape problem index remaining output)

def finalConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  {
    state := (machine problem.verifier).acceptState
    tape := dividerFinalTape problem index remaining output
  }

def preparedSteps {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) : Nat :=
  BuilderDividerOperands.workSteps problem index remaining + 1 +
    BuilderDividerLayout.workSteps (count problem) index (width problem)

def workSteps {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) : Nat :=
  preparedSteps problem index remaining + 1 +
    BuilderPostHeaderRawDivider.workSteps index (width problem)

theorem prepared_workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    workRunExact? (preparedMachine problem.verifier) (preparedSteps problem index remaining)
        (workStartConfiguration (preparedMachine problem.verifier)
          (BuilderCursorSource.cursorTape problem index remaining output)) =
      some {
        state := (preparedMachine problem.verifier).acceptState
        tape := mirrorTape (BuilderPostHeaderRawTapeBridge.shieldedDividerInputTape index
          (width problem) (exterior problem index remaining output))
      } := by
  have hOperands := BuilderDividerOperands.workRunExact problem index remaining output
  have hOperandFinal : BuilderDividerOperands.finalConfiguration problem index remaining output =
      {
        state := (BuilderDividerOperands.machine problem.verifier).acceptState
        tape := (layoutInitial problem index remaining output).tape
      } :=
    configuration_eq_of_fields _ _ _ rfl (operand_layout_handoff problem index remaining output)
  rw [hOperandFinal] at hOperands
  have hLayout := BuilderDividerLayout.workRunExact (count problem) index (width problem)
    (BuilderOperandRegisters.retainedValues problem index remaining)
    (BuilderDividerOperands.inside problem.input output) []
  have hLayoutFinal : layoutFinal problem index remaining output =
      {
        state := BuilderDividerLayout.machine.acceptState
        tape := mirrorTape (BuilderPostHeaderRawTapeBridge.shieldedDividerInputTape index
          (width problem) (exterior problem index remaining output))
      } :=
    configuration_eq_of_fields _ _ _ rfl (layout_divider_handoff problem index remaining output)
  change workRunExact? BuilderDividerLayout.machine
    (BuilderDividerLayout.workSteps (count problem) index (width problem))
    (layoutInitial problem index remaining output) = some (layoutFinal problem index remaining output) at hLayout
  rw [hLayoutFinal] at hLayout
  exact chain_run (BuilderDividerOperands.machine problem.verifier) BuilderDividerLayout.machine
    (BuilderDividerOperands.workSteps problem index remaining)
    (BuilderDividerLayout.workSteps (count problem) index (width problem)) _ _ _ hOperands hLayout

/-- The actual source-derived operand tape is accepted by the fixed divider. -/
theorem workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
        (initialConfiguration problem index remaining output) =
      some (finalConfiguration problem index remaining output) := by
  have hDivider := workRunExact?_mirror_of_some BuilderPostHeaderRawTapeBridge.dividerMachine
    (BuilderPostHeaderRawDivider.workSteps index (width problem))
    (BuilderPostHeaderRawTapeBridge.shieldedDividerStartConfiguration index (width problem)
      (exterior problem index remaining output))
    (BuilderPostHeaderRawTapeBridge.shieldedDividerFinalConfiguration index (width problem)
      (exterior problem index remaining output))
    (BuilderPostHeaderRawTapeBridge.shielded_divider_workRunExact index (width problem)
      (exterior problem index remaining output) (width_pos problem))
  exact chain_run (preparedMachine problem.verifier) dividerMachine
    (preparedSteps problem index remaining)
    (BuilderPostHeaderRawDivider.workSteps index (width problem)) _ _ _
    (prepared_workRunExact problem index remaining output) hDivider

theorem run_compile_exact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining)
        (encodeWorkConfiguration (initialConfiguration problem index remaining output)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining output) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact problem index remaining output)

theorem finalConfiguration_state {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).state = (machine problem.verifier).acceptState := rfl

/-- Exact quotient, remainder, sidecar and preserved source-workspace layout. -/
theorem final_tape_layout {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).tape =
      {
        left := List.replicate (index / width problem) BuilderPostHeaderRawDivider.quotientMark
        head := scratchEndSymbol
        right := List.replicate (width problem) unitSymbol ++ separatorSymbol ::
          (List.replicate (index % width problem) unitSymbol ++
            List.replicate ((index / width problem) * width problem) BuilderPostHeaderRawDivider.consumedDividend ++
            leftMarker :: leftMarker :: (List.replicate (count problem) unitSymbol ++
              scratchEndSymbol :: preservedWorkspace problem index remaining output))
      } := by
  simp only [finalConfiguration, dividerFinalTape, mirrorTape,
    BuilderPhysicalClassifierFinishWorkspaceOrientation.mirrorTape,
    BuilderPostHeaderRawTapeBridge.shieldedDividerFinalConfiguration,
    BuilderPostHeaderRawTapeBridge.appendExteriorConfiguration,
    BuilderPostHeaderRawTapeBridge.appendExteriorTape,
    BuilderPostHeaderRawDivider.finalConfiguration, BuilderPostHeaderRawDivider.terminalConfiguration,
    BuilderPostHeaderRawDivider.terminalTape, exterior,
    List.append_assoc, List.cons_append, List.nil_append]
  rfl

theorem quotient_mark_count {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).tape.left.length = index / width problem := by
  rw [final_tape_layout]
  exact List.length_replicate

theorem remainder_lt_width {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) : index % width problem < width problem :=
  BuilderPostHeaderRawDivider.remainder_lt_width index (width problem) (width_pos problem)

theorem quotient_remainder_reconstruct {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    (index / width problem) * width problem + index % width problem = index :=
  BuilderPostHeaderRawDivider.quotient_remainder_reconstruct index (width problem)

theorem divider_rules_length : dividerMachine.rules.length = 99 := by
  change (BuilderPostHeaderRawDivider.machine.rules.map mirrorRule).length = 99
  rw [List.length_map]
  exact BuilderPostHeaderRawDivider.rules_length

private theorem divider_noRule : WorkMachineChain.NoRuleAtAccept dividerMachine := by
  intro selected hMem
  change selected ∈ BuilderPostHeaderRawDivider.machine.rules.map mirrorRule at hMem
  rcases List.mem_map.mp hMem with ⟨original, hOriginal, hEqual⟩
  subst selected
  exact BuilderPostHeaderRawDivider.rule_source_ne_acceptState original hOriginal

theorem rules_pairwise_query_distinct {language : Language}
    (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct := by
  have hPrepared := WorkMachineChain.rules_pairwise_query_distinct
    (BuilderDividerOperands.machine verifier) BuilderDividerLayout.machine
    (BuilderDividerOperands.rules_pairwise_query_distinct verifier)
    BuilderDividerLayout.rules_pairwise_query_distinct (BuilderDividerOperands.noRuleAtAccept verifier)
  have hPreparedNo : WorkMachineChain.NoRuleAtAccept (preparedMachine verifier) := by
    apply WorkMachineChain.noRuleAtAccept
    exact BuilderDividerLayout.noRuleAtAccept
  have hDivider := mirrorRules_pairwise_query_distinct BuilderPostHeaderRawDivider.machine
    BuilderPostHeaderRawDivider.rules_pairwise_query_distinct
  exact WorkMachineChain.rules_pairwise_query_distinct (preparedMachine verifier) dividerMachine
    hPrepared hDivider hPreparedNo

theorem noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (machine verifier) := by
  apply WorkMachineChain.noRuleAtAccept
  exact divider_noRule

theorem machine_acceptState_ne_rejectState {language : Language}
    (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState :=
  WorkMachineChain.machine_acceptState_ne_rejectState _ _
    (mirrorMachine_acceptState_ne_rejectState BuilderPostHeaderRawDivider.machine
      BuilderPostHeaderRawDivider.machine_acceptState_ne_rejectState)

def sourceSpan {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  registerSpanPolynomial (BuilderDimensionRegisters.polynomial verifier)

theorem operand_le_sourceSpan {language : Language} (problem : VerifierTableauProblem language)
    (operand : BuilderOperandRegisters.Operand) (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    BuilderOperandRegisters.copiedValue problem index operand ≤
      (sourceSpan problem.verifier).eval problem.input.length := by
  have hValues := BuilderOperandRegisters.retainedValues_selection problem operand index remaining
  have hLength := congrArg (fun values => (registerWord values).length) hValues
  have hValue : BuilderOperandRegisters.copiedValue problem index operand ≤
      (registerWord (BuilderOperandRegisters.retainedValues problem index remaining)).length := by
    simp only [registerWord_length, List.length_append, List.length_cons, List.length_nil,
      List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero] at hLength ⊢
    omega
  have hSpan := BuilderCursorSource.invariant_span problem index remaining hBalance
  rw [BuilderOperandRegisters.cursorWord_values] at hSpan
  rw [hSpan, scratchWord_length] at hValue
  exact hValue

/-- Full operand preparation, converter, both bridges and encoded divider cost. -/
def rawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  let span := sourceSpan verifier
  let larger := NatPolynomial.add (.mul (.constant 2) span) (.constant 1)
  let overhead := NatPolynomial.add (.add (.mul (.constant 4) span) (.constant 9))
    (.mul (.mul (.constant 20) larger) larger)
  .add (BuilderDividerOperands.rawTimeBound verifier) (.mul (.constant 6) overhead)

theorem rawTimeBound_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    6 * workSteps problem index remaining ≤
      (rawTimeBound problem.verifier).eval problem.input.length := by
  let span := (sourceSpan problem.verifier).eval problem.input.length
  have hCount : count problem ≤ span :=
    operand_le_sourceSpan problem .clauseCount index remaining hBalance
  have hIndex : index ≤ span := operand_le_sourceSpan problem .index index remaining hBalance
  have hWidth : width problem ≤ span :=
    operand_le_sourceSpan problem .tokenWidth index remaining hBalance
  have hLayout := BuilderDividerLayout.workSteps_le (count problem) index (width problem)
    span hCount hIndex hWidth
  have hSum : index + width problem + 1 ≤ 2 * span + 1 := by omega
  have hSquare := Nat.mul_le_mul (Nat.mul_le_mul_left 20 hSum) hSum
  have hDivider := Nat.le_trans
    (BuilderPostHeaderRawDivider.workSteps_le_quadratic index (width problem) (width_pos problem))
    hSquare
  have hOperands := BuilderDividerOperands.rawTimeBound_le problem index remaining hBalance
  change 6 * workSteps problem index remaining ≤
    (BuilderDividerOperands.rawTimeBound problem.verifier).eval problem.input.length +
      6 * (4 * span + 9 + 20 * (2 * span + 1) * (2 * span + 1))
  unfold workSteps preparedSteps
  omega

def fromRawMachine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineChain.machine (BuilderInitialization.machine verifier) (machine verifier)

def fromRawInitial {language : Language} (problem : VerifierTableauProblem language) : WorkConfiguration :=
  workStartConfiguration (fromRawMachine problem.verifier) (rawInputWorkTape problem.input)

def fromRawFinal {language : Language} (problem : VerifierTableauProblem language) : WorkConfiguration :=
  {
    state := (fromRawMachine problem.verifier).acceptState
    tape := (finalConfiguration problem 0
      (BuilderFullScheduleCursorController.bodySlotCount problem)
      (encodeUnaryTokens problem.FormulaWidth)).tape
  }

def fromRawSteps {language : Language} (problem : VerifierTableauProblem language) : Nat :=
  BuilderInitialization.workSteps problem + 1 +
    workSteps problem 0 (BuilderFullScheduleCursorController.bodySlotCount problem)

/-- Every raw source input reaches its actual first body-coordinate quotient and remainder. -/
theorem fromRaw_workRunExact {language : Language} (problem : VerifierTableauProblem language) :
    workRunExact? (fromRawMachine problem.verifier) (fromRawSteps problem)
        (fromRawInitial problem) = some (fromRawFinal problem) := by
  have hInit := BuilderInitialization.workRunExact problem
  have hInitFinal : BuilderInitialization.finalConfiguration problem =
      {
        state := (BuilderInitialization.machine problem.verifier).acceptState
        tape := BuilderCursorSource.cursorTape problem 0
          (BuilderFullScheduleCursorController.bodySlotCount problem)
          (encodeUnaryTokens problem.FormulaWidth)
      } :=
    configuration_eq_of_fields _ _ _
      (BuilderInitialization.finalConfiguration_state problem)
      (BuilderCursorSource.initializer_tape_handoff problem)
  rw [hInitFinal] at hInit
  exact chain_run (BuilderInitialization.machine problem.verifier) (machine problem.verifier)
    (BuilderInitialization.workSteps problem)
    (workSteps problem 0 (BuilderFullScheduleCursorController.bodySlotCount problem)) _ _ _ hInit
    (workRunExact problem 0 (BuilderFullScheduleCursorController.bodySlotCount problem)
      (encodeUnaryTokens problem.FormulaWidth))

theorem fromRaw_run_compile_exact {language : Language} (problem : VerifierTableauProblem language) :
    run (compileWorkMachine (fromRawMachine problem.verifier)) (6 * fromRawSteps problem)
        (encodeWorkConfiguration (fromRawInitial problem)) =
      encodeWorkConfiguration (fromRawFinal problem) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (fromRaw_workRunExact problem)

def fromRawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (.add (BuilderInitialization.rawTimeBound verifier) (.constant 6)) (rawTimeBound verifier)

theorem fromRawTimeBound_le {language : Language} (problem : VerifierTableauProblem language) :
    6 * fromRawSteps problem ≤ (fromRawTimeBound problem.verifier).eval problem.input.length := by
  have hInit := BuilderInitialization.rawTimeBound_le problem
  have hDivision := rawTimeBound_le problem 0
    (BuilderFullScheduleCursorController.bodySlotCount problem) (Nat.zero_add _)
  simp only [fromRawTimeBound, NatPolynomial.eval_add, NatPolynomial.eval_constant]
  unfold fromRawSteps
  omega

end PNP.Concrete.CookLevin.BuilderDividerSourceExecution
