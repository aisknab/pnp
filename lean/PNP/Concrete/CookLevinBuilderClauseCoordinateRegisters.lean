/-
Copyright (c) 2026 PNP Labs.

Bind coordinate-register restoration to the actual source-derived clause
division. The guarded body path starts at the source cursor, computes both
divisions, and preserves their constraint/local-clause coordinates as ordinary
registers. No coordinates, selected constraint or correctness certificate are
supplied to the machine. Control depends only on the fixed verifier.

The occupancy equation reuses the existing semantic decoder. Executing that
decoder, emission, Finish and the complete builder loop remain separate.
-/

import PNP.Concrete.CookLevinBuilderDividerCoordinateRegisters
import PNP.Concrete.CookLevinClauseOccupancyDivision

namespace PNP.Concrete.CookLevin.BuilderClauseCoordinateRegisters

open PipelineTape PipelineStateNamespace BuilderUnaryPolynomial
open BuilderDividerOperands (endTape inside count width)
open BuilderClauseDividerOperands (clauseWidth quotient dividerOlder)
open BuilderDividerSourceExecution (sourceSpan)

def sourceView {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) : BuilderDividerCoordinateRegisters.RestoreView :=
  {
    quotient := BuilderClauseDividerExecution.constraintIndex problem index
    width := clauseWidth problem
    remainder := BuilderClauseDividerExecution.clauseIndex problem index
    consumed := BuilderClauseDividerExecution.constraintIndex problem index * clauseWidth problem
    sidecarCount := count problem
  }

def workspace {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : List WorkSymbol :=
  (registerWord (dividerOlder problem index remaining)).reverse ++ inside problem.input output

def finalValues {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) : List Nat :=
  dividerOlder problem index remaining ++ BuilderDividerCoordinateRegisters.restoredValues (sourceView problem index)

def restorationFinal {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  BuilderDividerCoordinateRegisters.finalConfiguration (sourceView problem index) (workspace problem index remaining output) []

def restorationSteps {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) : Nat :=
  BuilderDividerCoordinateRegisters.workSteps (sourceView problem index)

theorem input_tape_handoff {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (BuilderClauseDividerExecution.finalConfiguration problem index remaining output).tape =
      (BuilderDividerCoordinateRegisters.initialConfiguration (sourceView problem index)
        (workspace problem index remaining output) []).tape := by
  rw [BuilderClauseDividerExecution.final_tape_layout]
  simp only [BuilderDividerCoordinateRegisters.initialConfiguration, workStartConfiguration, BuilderDividerCoordinateRegisters.inputTape,
    sourceView, workspace, List.append_nil, List.append_assoc]

theorem restoration_final_tape {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (restorationFinal problem index remaining output).tape =
      endTape (finalValues problem index remaining) (inside problem.input output) [] := by
  simp only [restorationFinal, BuilderDividerCoordinateRegisters.finalConfiguration, finalValues, workspace,
    endTape, registerWord_append, List.reverse_append, List.append_assoc, List.drop_nil]

theorem restoration_workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    workRunExact? BuilderDividerCoordinateRegisters.machine (restorationSteps problem index)
      (workStartConfiguration BuilderDividerCoordinateRegisters.machine
        (BuilderClauseDividerExecution.finalConfiguration problem index remaining output).tape) =
      some (restorationFinal problem index remaining output) := by
  rw [input_tape_handoff]
  exact BuilderDividerCoordinateRegisters.workRunExact (sourceView problem index)
    (workspace problem index remaining output) [] rfl rfl

def machine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineChain.machine (BuilderClauseDividerExecution.bodyMachine verifier) BuilderDividerCoordinateRegisters.machine

def initialConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  workStartConfiguration (machine problem.verifier)
    (BuilderCursorSource.cursorTape problem index remaining output)

def finalConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.secondState (restorationFinal problem index remaining output)

def workSteps {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) : Nat :=
  BuilderClauseDividerExecution.bodySteps problem index remaining + 1 + restorationSteps problem index

private theorem initial_eq {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    initialConfiguration problem index remaining output =
      renameConfiguration WorkMachineChain.firstState
        (BuilderClauseDividerExecution.bodyInitial problem index remaining output) := rfl

theorem workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (hBody : quotient problem index < count problem) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
      (initialConfiguration problem index remaining output) =
      some (finalConfiguration problem index remaining output) := by
  have h := WorkMachineChain.workRunExact (BuilderClauseDividerExecution.bodyMachine problem.verifier)
    BuilderDividerCoordinateRegisters.machine (BuilderClauseDividerExecution.bodySteps problem index remaining) (restorationSteps problem index)
    (BuilderClauseDividerExecution.bodyInitial problem index remaining output)
    (BuilderClauseDividerExecution.finalConfiguration problem index remaining output)
    (restorationFinal problem index remaining output)
    (BuilderClauseDividerExecution.body_workRunExact problem index remaining output hBody)
    (BuilderClauseDividerExecution.body_finalConfiguration_state problem index remaining output)
    (restoration_workRunExact problem index remaining output)
  simpa only [machine, workSteps, finalConfiguration, initial_eq] using h

theorem run_compile_exact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (hBody : quotient problem index < count problem) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining)
      (encodeWorkConfiguration (initialConfiguration problem index remaining output)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining output) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact problem index remaining output hBody)

theorem finalConfiguration_state {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).state = (machine problem.verifier).acceptState := rfl

theorem final_tape_layout {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).tape =
      endTape (finalValues problem index remaining) (inside problem.input output) [] :=
  restoration_final_tape problem index remaining output

theorem finalValues_eq {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) :
    finalValues problem index remaining =
      BuilderOperandRegisters.retainedValues problem index remaining ++
        [count problem, 0, index, width problem, quotient problem index,
         count problem, 0, BuilderClauseDividerExecution.constraintIndex problem index * clauseWidth problem,
         BuilderClauseDividerExecution.clauseIndex problem index, clauseWidth problem, BuilderClauseDividerExecution.constraintIndex problem index] := by
  simp only [finalValues, dividerOlder, BuilderDividerCoordinateRegisters.restoredValues, sourceView,
    List.append_assoc, List.cons_append, List.nil_append]

/-- Semantic meaning of the actual preserved coordinates, not execution of the decoder. -/
theorem coordinates_match_schedule {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hBody : quotient problem index < count problem) :
    ClauseOccupancy.constraintSlot problem
      (sourceView problem index).quotient (sourceView problem index).remainder =
      (problem.formulaClauseSchedule[quotient problem index]?).map Option.isSome := by
  have h := (ClauseOccupancy.constraintSlot_div_mod problem
    ⟨quotient problem index, hBody⟩).trans
    (ClauseOccupancy.formulaSlot_eq_schedule problem (quotient problem index))
  simpa only [sourceView, BuilderClauseDividerExecution.constraintIndex, BuilderClauseDividerExecution.clauseIndex,
    BuilderClauseDividerOperands.clauseWidth_value] using h

theorem source_magnitudes_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    let span := (sourceSpan problem.verifier).eval problem.input.length
    (sourceView problem index).quotient ≤ span ∧
    (sourceView problem index).width ≤ span ∧
    (sourceView problem index).remainder ≤ span ∧
    (sourceView problem index).consumed ≤ span ∧
    (sourceView problem index).sidecarCount ≤ span := by
  let span := (sourceSpan problem.verifier).eval problem.input.length
  have hIndex : index ≤ span :=
    BuilderDividerSourceExecution.operand_le_sourceSpan problem .index index remaining hBalance
  have hQuotient : quotient problem index ≤ span :=
    Nat.le_trans (Nat.div_le_self index (width problem)) hIndex
  have hConstraint : BuilderClauseDividerExecution.constraintIndex problem index ≤ quotient problem index :=
    Nat.div_le_self (quotient problem index) (clauseWidth problem)
  have hParts := BuilderClauseDividerExecution.coordinate_reconstruction problem index
  have hRemainder : BuilderClauseDividerExecution.clauseIndex problem index ≤ quotient problem index := by omega
  have hConsumed : BuilderClauseDividerExecution.constraintIndex problem index * clauseWidth problem ≤ quotient problem index := by omega
  exact ⟨Nat.le_trans hConstraint hQuotient,
    (BuilderClauseDividerOperands.source_selection_bounds problem index remaining hBalance).1,
    Nat.le_trans hRemainder hQuotient, Nat.le_trans hConsumed hQuotient,
    BuilderDividerSourceExecution.operand_le_sourceSpan problem .clauseCount index remaining hBalance⟩

theorem restorationSteps_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    restorationSteps problem index ≤
      15 * (sourceSpan problem.verifier).eval problem.input.length + 19 := by
  rcases source_magnitudes_le problem index remaining hBalance with
    ⟨hQuotient, hWidth, hRemainder, hConsumed, hSidecar⟩
  exact BuilderDividerCoordinateRegisters.workSteps_le _ _ hQuotient hWidth hRemainder hConsumed hSidecar

def rawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderClauseDividerExecution.bodyRawTimeBound verifier)
    (.mul (.constant 6) (.add (.mul (.constant 15) (sourceSpan verifier)) (.constant 20)))

theorem rawTimeBound_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    6 * workSteps problem index remaining ≤
      (rawTimeBound problem.verifier).eval problem.input.length := by
  have hBody := BuilderClauseDividerExecution.body_rawTimeBound_le problem index remaining hBalance
  have hRestore := restorationSteps_le problem index remaining hBalance
  simp only [rawTimeBound, NatPolynomial.eval_add, NatPolynomial.eval_mul, NatPolynomial.eval_constant]
  unfold workSteps
  omega

theorem final_register_span_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    (registerWord (finalValues problem index remaining)).length ≤
      9 * (sourceSpan problem.verifier).eval problem.input.length + 11 := by
  have hPrepared := BuilderClauseDividerOperands.final_register_span_le problem index remaining hBalance
  have hConstraint := (source_magnitudes_le problem index remaining hBalance).1
  change BuilderClauseDividerExecution.constraintIndex problem index ≤
    (sourceSpan problem.verifier).eval problem.input.length at hConstraint
  have hReconstruct := BuilderClauseDividerExecution.coordinate_reconstruction problem index
  have hLength : (registerWord (finalValues problem index remaining)).length =
      (registerWord (BuilderOperandRegisters.retainedValues problem index remaining ++
        BuilderClauseDividerOperands.preparedExtra problem index)).length +
        BuilderClauseDividerExecution.constraintIndex problem index + 2 := by
    simp only [registerWord_length, finalValues, dividerOlder, BuilderDividerCoordinateRegisters.restoredValues,
      sourceView, BuilderClauseDividerOperands.preparedExtra, BuilderSourceRegisterRestore.appended,
      quotient, List.length_append, List.length_cons, List.length_nil, List.sum_append,
      List.sum_cons, List.sum_nil, Nat.add_zero, Nat.zero_add]
    simp only [quotient] at hReconstruct
    omega
  rw [hLength]
  omega

theorem rules_pairwise_query_distinct {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineChain.rules_pairwise_query_distinct (BuilderClauseDividerExecution.bodyMachine verifier) BuilderDividerCoordinateRegisters.machine
    (BuilderClauseDividerExecution.body_rules_pairwise_query_distinct verifier) BuilderDividerCoordinateRegisters.rules_pairwise_query_distinct
    (BuilderClauseDividerExecution.body_noRuleAtAccept verifier)

theorem noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (machine verifier) :=
  WorkMachineChain.noRuleAtAccept (BuilderClauseDividerExecution.bodyMachine verifier) BuilderDividerCoordinateRegisters.machine BuilderDividerCoordinateRegisters.noRuleAtAccept

theorem acceptState_ne_rejectState {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState :=
  WorkMachineChain.machine_acceptState_ne_rejectState _ _ BuilderDividerCoordinateRegisters.acceptState_ne_rejectState

end PNP.Concrete.CookLevin.BuilderClauseCoordinateRegisters
