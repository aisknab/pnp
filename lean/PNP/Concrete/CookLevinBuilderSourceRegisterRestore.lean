/-
Copyright (c) 2026 PNP Labs.

Bind literal register restoration to the actual source classifier endpoint.
Recover the quotient and count from every comparator result, not from supplied
values or a prepared tape. The resulting ordinary registers retain the original
workspace. A serial body machine continues only under the actual body guard;
Finish/non-body remains a distinct endpoint, not an assumed accepting branch.

This is a source-to-restored-register component. The second division, clause
occupancy, emission, cleanup, full loop and packaged reduction remain open.
-/

import PNP.Concrete.CookLevinBuilderClassifierRegisterRestore

namespace PNP.Concrete.CookLevin.BuilderSourceRegisterRestore

open PipelineTape PipelineStateNamespace BuilderUnaryPolynomial
open BuilderDividerOperands (count width)
open BuilderDividerSourceExecution (preservedWorkspace sourceSpan)
open BuilderClassifierRegisterRestore (RestoreView)
open BuilderArbitrarySlotHeaderRouter
open BuilderPhysicalClassifierFinishMirroredDispatch (mirrorTape)

def resultQuotient : RawRouter.ComparisonResult → Nat
  | .less processed _ => processed
  | .equal processed => processed
  | .greater processed remaining => remaining + (processed + 1)

def resultCount : RawRouter.ComparisonResult → Nat
  | .less processed remaining => (remaining + 1) + processed
  | .equal processed => processed
  | .greater processed _ => processed

/-- Comparison consumes paired cells without losing either original magnitude. -/
theorem compareResult_totals (processed coordinate boundary : Nat) :
    resultQuotient (RawRouter.compareResult processed coordinate boundary) = processed + coordinate ∧
      resultCount (RawRouter.compareResult processed coordinate boundary) = processed + boundary := by
  induction coordinate generalizing processed boundary with
  | zero =>
    cases boundary <;> constructor <;>
      simp only [RawRouter.compareResult, resultQuotient, resultCount] <;> omega
  | succ coordinate ih =>
    cases boundary with
    | zero =>
      constructor <;> simp only [RawRouter.compareResult, resultQuotient, resultCount] <;> omega
    | succ boundary =>
      have h := ih (processed + 1) boundary
      change resultQuotient (RawRouter.compareResult (processed + 1) coordinate boundary) =
          processed + (coordinate + 1) ∧
        resultCount (RawRouter.compareResult (processed + 1) coordinate boundary) =
          processed + (boundary + 1)
      constructor <;> omega

def ofComparison (consumed remainder divisor sidecar : Nat) :
    RawRouter.ComparisonResult → RestoreView
  | .less processed remaining =>
      {
        countRest := remaining + 1
        countMarked := processed
        quotientRest := 0
        quotientMarked := processed
        consumed := consumed
        remainder := remainder
        width := divisor
        sidecarCount := sidecar
      }
  | .equal processed =>
      {
        countRest := 0
        countMarked := processed
        quotientRest := 0
        quotientMarked := processed
        consumed := consumed
        remainder := remainder
        width := divisor
        sidecarCount := sidecar
      }
  | .greater processed remaining =>
      {
        countRest := 0
        countMarked := processed
        quotientRest := remaining
        quotientMarked := processed + 1
        consumed := consumed
        remainder := remainder
        width := divisor
        sidecarCount := sidecar
      }

theorem ofComparison_fields (consumed remainder divisor sidecar : Nat)
    (result : RawRouter.ComparisonResult) :
    (ofComparison consumed remainder divisor sidecar result).countTotal = resultCount result ∧
      (ofComparison consumed remainder divisor sidecar result).quotientTotal = resultQuotient result ∧
      (ofComparison consumed remainder divisor sidecar result).dividend = remainder + consumed ∧
      (ofComparison consumed remainder divisor sidecar result).width = divisor ∧
      (ofComparison consumed remainder divisor sidecar result).sidecarCount = sidecar := by
  cases result <;> simp only [ofComparison, RestoreView.countTotal, RestoreView.quotientTotal,
    RestoreView.dividend, resultCount, resultQuotient, Nat.zero_add] <;>
    exact ⟨True.intro, True.intro, True.intro, True.intro, True.intro⟩

/-- The tape view is extracted from all three literal comparator endpoints. -/
theorem inputTape_ofComparison (consumed remainder divisor sidecar : Nat)
    (result : RawRouter.ComparisonResult) (workspace : List WorkSymbol) :
    BuilderClassifierRegisterRestore.inputTape
        (ofComparison consumed remainder divisor sidecar result) workspace [] =
      mirrorTape (BuilderPostDividerRawRouteClassifier.appendExteriorTape
        (RawRouter.resultConfiguration result).tape
        (BuilderPostDividerRawRouteClassifier.preservedExterior
          consumed remainder divisor [] sidecar workspace)) := by
  cases result <;>
    simp only [ofComparison, BuilderClassifierRegisterRestore.inputTape,
      BuilderDividerLayout.leftFocus, mirrorTape,
      BuilderPhysicalClassifierFinishWorkspaceOrientation.mirrorTape,
      BuilderPostDividerRawRouteClassifier.appendExteriorTape, RawRouter.resultConfiguration,
      BuilderPostDividerRawRouteClassifier.preservedExterior,
      BuilderPostDividerRawRouteClassifier.terminalPrefix, BuilderPostDividerRawRouteClassifier.sidecar,
      List.replicate_zero, List.replicate_succ, List.nil_append,
      List.cons_append, List.append_assoc] <;> rfl

def view {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : RestoreView :=
  ofComparison ((index / width problem) * width problem) (index % width problem)
    (width problem) (count problem) (RawRouter.compareResult 0 (index / width problem) (count problem))

theorem view_totals {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    (view problem index).countTotal = count problem ∧
      (view problem index).quotientTotal = index / width problem ∧
      (view problem index).dividend = index ∧
      (view problem index).width = width problem ∧
      (view problem index).sidecarCount = count problem := by
  have hFields := ofComparison_fields ((index / width problem) * width problem)
    (index % width problem) (width problem) (count problem)
    (RawRouter.compareResult 0 (index / width problem) (count problem))
  have hTotals := compareResult_totals 0 (index / width problem) (count problem)
  have hDivision := BuilderDividerSourceExecution.quotient_remainder_reconstruct problem index
  change (view problem index).countTotal = _ ∧ (view problem index).quotientTotal = _ ∧
    (view problem index).dividend = _ ∧ (view problem index).width = _ ∧
    (view problem index).sidecarCount = _
  refine ⟨?_, ?_, ?_, hFields.2.2.2.1, hFields.2.2.2.2⟩
  · change (ofComparison _ _ _ _ _).countTotal = _
    rw [hFields.1, hTotals.2, Nat.zero_add]
  · change (ofComparison _ _ _ _ _).quotientTotal = _
    rw [hFields.2.1, hTotals.1, Nat.zero_add]
  · change (ofComparison _ _ _ _ _).dividend = _
    rw [hFields.2.2.1]
    omega

def appended {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : List Nat :=
  [count problem, 0, index, width problem, index / width problem, count problem]

theorem restoredValues_eq {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    BuilderClassifierRegisterRestore.restoredValues (view problem index) = appended problem index := by
  have h := view_totals problem index
  unfold BuilderClassifierRegisterRestore.restoredValues appended
  rw [h.2.2.2.2, h.2.2.1, h.2.2.2.1, h.2.1, h.1]

/-- No supplied tape equality: this is the tape produced by the source classifier. -/
theorem classifier_restore_handoff {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    BuilderClassifierRegisterRestore.inputTape (view problem index)
        (preservedWorkspace problem index remaining output) [] =
      (BuilderSourceClassifier.finalConfiguration problem index remaining output).tape := by
  exact inputTape_ofComparison ((index / width problem) * width problem) (index % width problem)
    (width problem) (count problem) (RawRouter.compareResult 0 (index / width problem) (count problem))
    (preservedWorkspace problem index remaining output)

def restorationInitial {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  workStartConfiguration BuilderClassifierRegisterRestore.machine
    (BuilderSourceClassifier.finalConfiguration problem index remaining output).tape

def restorationFinal {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  {
    state := BuilderClassifierRegisterRestore.machine.acceptState
    tape := BuilderDividerOperands.endTape
      (BuilderOperandRegisters.retainedValues problem index remaining ++ appended problem index)
      (BuilderDividerOperands.inside problem.input output) []
  }

def restorationSteps {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : Nat :=
  BuilderClassifierRegisterRestore.workSteps (view problem index)

private theorem restoration_initial_eq {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    restorationInitial problem index remaining output =
      BuilderClassifierRegisterRestore.initialConfiguration (view problem index)
        (preservedWorkspace problem index remaining output) [] :=
  congrArg (workStartConfiguration BuilderClassifierRegisterRestore.machine)
    (classifier_restore_handoff problem index remaining output).symm

private theorem restoration_final_eq {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    BuilderClassifierRegisterRestore.finalConfiguration (view problem index)
        (preservedWorkspace problem index remaining output) [] =
      restorationFinal problem index remaining output := by
  simp only [BuilderClassifierRegisterRestore.finalConfiguration, restorationFinal,
    BuilderDividerOperands.endTape, preservedWorkspace, restoredValues_eq,
    registerWord_append, List.reverse_append, List.append_assoc]

/-- Exact restoration starts on the produced tape, regardless of comparison outcome. -/
theorem restoration_workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    workRunExact? BuilderClassifierRegisterRestore.machine (restorationSteps problem index)
        (restorationInitial problem index remaining output) =
      some (restorationFinal problem index remaining output) := by
  rw [restoration_initial_eq, ← restoration_final_eq]
  exact BuilderClassifierRegisterRestore.workRunExact (view problem index)
    (preservedWorkspace problem index remaining output) []

theorem restoration_run_compile_exact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    run (compileWorkMachine BuilderClassifierRegisterRestore.machine) (6 * restorationSteps problem index)
        (encodeWorkConfiguration (restorationInitial problem index remaining output)) =
      encodeWorkConfiguration (restorationFinal problem index remaining output) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (restoration_workRunExact problem index remaining output)

theorem restoration_final_tape_layout {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (restorationFinal problem index remaining output).tape =
      {
        left := []
        head := scratchEndSymbol
        right := (registerWord
          (BuilderOperandRegisters.retainedValues problem index remaining ++ appended problem index)).reverse ++
            BuilderDividerOperands.inside problem.input output
      } := rfl

theorem restoration_workSteps_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    restorationSteps problem index ≤
      11 * (sourceSpan problem.verifier).eval problem.input.length + 13 := by
  let span := (sourceSpan problem.verifier).eval problem.input.length
  have h := view_totals problem index
  have hCount : count problem ≤ span :=
    BuilderDividerSourceExecution.operand_le_sourceSpan problem .clauseCount index remaining hBalance
  have hIndex : index ≤ span :=
    BuilderDividerSourceExecution.operand_le_sourceSpan problem .index index remaining hBalance
  have hWidth : width problem ≤ span :=
    BuilderDividerSourceExecution.operand_le_sourceSpan problem .tokenWidth index remaining hBalance
  have hQuotient := Nat.le_trans (Nat.div_le_self index (width problem)) hIndex
  exact BuilderClassifierRegisterRestore.workSteps_le (view problem index) span
    (by rw [h.1]; exact hCount) (by rw [h.2.1]; exact hQuotient)
    (by rw [h.2.2.2.1]; exact hWidth) (by rw [h.2.2.1]; exact hIndex)
    (by rw [h.2.2.2.2]; exact hCount)

theorem classifier_accept_of_body {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (hBody : index / width problem < count problem) :
    (BuilderSourceClassifier.finalConfiguration problem index remaining output).state =
      (BuilderSourceClassifier.machine problem.verifier).acceptState := by
  rw [BuilderSourceClassifier.finalConfiguration_state]
  exact congrArg (fun state => WorkMachineChain.secondState (WorkMachineChain.secondState state))
    ((RawRouter.finalConfiguration_accept_iff (index / width problem) (count problem)).mpr hBody)

theorem classifier_reject_of_nonbody {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (hNonbody : count problem ≤ index / width problem) :
    (BuilderSourceClassifier.finalConfiguration problem index remaining output).state =
      (BuilderSourceClassifier.machine problem.verifier).rejectState := by
  rw [BuilderSourceClassifier.finalConfiguration_state]
  exact congrArg (fun state => WorkMachineChain.secondState (WorkMachineChain.secondState state))
    ((RawRouter.finalConfiguration_reject_iff (index / width problem) (count problem)).mpr hNonbody)

def bodyMachine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineChain.machine (BuilderSourceClassifier.machine verifier) BuilderClassifierRegisterRestore.machine

def bodyInitial {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  workStartConfiguration (bodyMachine problem.verifier)
    (BuilderCursorSource.cursorTape problem index remaining output)

def bodyFinal {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.secondState (restorationFinal problem index remaining output)

def bodySteps {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) : Nat :=
  BuilderSourceClassifier.workSteps problem index remaining + 1 + restorationSteps problem index

private theorem body_initial_eq {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    bodyInitial problem index remaining output =
      renameConfiguration WorkMachineChain.firstState
        (BuilderSourceClassifier.initialConfiguration problem index remaining output) := rfl

/-- The branch guard is the actual computed quotient comparison, not a supplied route certificate. -/
theorem body_workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (hBody : index / width problem < count problem) :
    workRunExact? (bodyMachine problem.verifier) (bodySteps problem index remaining)
        (bodyInitial problem index remaining output) =
      some (bodyFinal problem index remaining output) := by
  have h := WorkMachineChain.workRunExact (BuilderSourceClassifier.machine problem.verifier)
    BuilderClassifierRegisterRestore.machine (BuilderSourceClassifier.workSteps problem index remaining)
    (restorationSteps problem index)
    (BuilderSourceClassifier.initialConfiguration problem index remaining output)
    (BuilderSourceClassifier.finalConfiguration problem index remaining output)
    (restorationFinal problem index remaining output)
    (BuilderSourceClassifier.workRunExact problem index remaining output)
    (classifier_accept_of_body problem index remaining output hBody)
    (restoration_workRunExact problem index remaining output)
  simpa only [bodyMachine, bodySteps, bodyFinal, body_initial_eq] using h

theorem body_run_compile_exact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (hBody : index / width problem < count problem) :
    run (compileWorkMachine (bodyMachine problem.verifier)) (6 * bodySteps problem index remaining)
        (encodeWorkConfiguration (bodyInitial problem index remaining output)) =
      encodeWorkConfiguration (bodyFinal problem index remaining output) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (body_workRunExact problem index remaining output hBody)

theorem body_finalConfiguration_state {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (bodyFinal problem index remaining output).state = (bodyMachine problem.verifier).acceptState := rfl

theorem body_final_tape_layout {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (bodyFinal problem index remaining output).tape = (restorationFinal problem index remaining output).tape := rfl

def bodyRawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderSourceClassifier.rawTimeBound verifier)
    (.mul (.constant 6) (.add (.mul (.constant 11) (sourceSpan verifier)) (.constant 14)))

theorem body_rawTimeBound_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    6 * bodySteps problem index remaining ≤ (bodyRawTimeBound problem.verifier).eval problem.input.length := by
  have hClassifier := BuilderSourceClassifier.rawTimeBound_le problem index remaining hBalance
  have hRestore := restoration_workSteps_le problem index remaining hBalance
  change 6 * bodySteps problem index remaining ≤
    (BuilderSourceClassifier.rawTimeBound problem.verifier).eval problem.input.length +
      6 * (11 * (sourceSpan problem.verifier).eval problem.input.length + 14)
  unfold bodySteps
  omega

theorem body_rules_pairwise_query_distinct {language : Language} (verifier : PolynomialTimeVerifier language) :
    (bodyMachine verifier).rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineChain.rules_pairwise_query_distinct (BuilderSourceClassifier.machine verifier)
    BuilderClassifierRegisterRestore.machine (BuilderSourceClassifier.rules_pairwise_query_distinct verifier)
    BuilderClassifierRegisterRestore.rules_pairwise_query_distinct (BuilderSourceClassifier.noRuleAtAccept verifier)

theorem body_noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (bodyMachine verifier) :=
  WorkMachineChain.noRuleAtAccept (BuilderSourceClassifier.machine verifier)
    BuilderClassifierRegisterRestore.machine BuilderClassifierRegisterRestore.noRuleAtAccept

theorem body_acceptState_ne_rejectState {language : Language} (verifier : PolynomialTimeVerifier language) :
    (bodyMachine verifier).acceptState ≠ (bodyMachine verifier).rejectState :=
  WorkMachineChain.machine_acceptState_ne_rejectState _ _ BuilderClassifierRegisterRestore.acceptState_ne_rejectState

end PNP.Concrete.CookLevin.BuilderSourceRegisterRestore
