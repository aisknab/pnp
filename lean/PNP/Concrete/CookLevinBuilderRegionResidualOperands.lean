/-
Copyright (c) 2026 PNP Labs.

Copy the actual coordinate and a fixed-offset region boundary, then run the
verified residual selector. The original frame remains unchanged and exactly
four ordinary scratch registers are appended. No verdict or residual is supplied.

The source entry executes the existing assembly once and charges its complete
work together with preparation, selection and all bridges. Full five-region
dispatch, decoding, emission and the complete formula builder remain open.
-/

import PNP.Concrete.CookLevinBuilderRegionResidualSelection

namespace PNP.Concrete.CookLevin.BuilderRegionResidualOperands

open PipelineTape PipelineStateNamespace BuilderUnaryPolynomial
open BuilderDividerOperands (endTape inside count quadratic)
open BuilderClauseDividerOperands (quotient)
open BuilderClauseDividerExecution (constraintIndex)
open BuilderDividerSourceExecution (sourceSpan)
open BuilderRegionComparisonOperands (inputValues prepareMachine prepareSteps)
open BuilderArbitrarySlotHeaderRouter

private theorem chain_run_any (first second : WorkMachine) (firstSteps secondSteps : Nat)
    (initial middle : WorkTape) (final : WorkConfiguration)
    (hFirst : workRunExact? first firstSteps (workStartConfiguration first initial) =
      some { state := first.acceptState, tape := middle })
    (hSecond : workRunExact? second secondSteps (workStartConfiguration second middle) = some final) :
    workRunExact? (WorkMachineChain.machine first second) (firstSteps + 1 + secondSteps)
      (workStartConfiguration (WorkMachineChain.machine first second) initial) =
      some (renameConfiguration WorkMachineChain.secondState final) :=
  WorkMachineChain.workRunExact first second firstSteps secondSteps _ _ _ hFirst rfl hSecond

private theorem chain_noRuleAtReject (first second : WorkMachine)
    (hSecond : WorkMachineProgramGraph.NoRuleAt second second.rejectState) :
    WorkMachineProgramGraph.NoRuleAt (WorkMachineChain.machine first second)
      (WorkMachineChain.machine first second).rejectState :=
  WorkMachineChain.noRuleAtAccept first { second with acceptState := second.rejectState } hSecond

private theorem chain_rules_length (first second : WorkMachine) :
    (WorkMachineChain.machine first second).rules.length =
      9 + first.rules.length + second.rules.length := by
  change (WorkMachineChain.bridgeRules first second ++
    (first.rules.map (renameRule WorkMachineChain.firstState) ++
      second.rules.map (renameRule WorkMachineChain.secondState))).length = _
  have hBridge : (WorkMachineChain.bridgeRules first second).length = 9 := rfl
  simp only [List.length_append, List.length_map, hBridge, Nat.add_assoc]

/-- The offset is fixed by control, not computed from a selected input. -/
def machine (offset : Nat) : WorkMachine :=
  WorkMachineChain.machine (prepareMachine offset) BuilderRegionResidualSelection.machine

def workSteps (newer : List Nat) (coordinate boundary : Nat) : Nat :=
  prepareSteps newer coordinate boundary + 1 + BuilderRegionResidualSelection.workSteps coordinate boundary

def finalValues (older newer : List Nat) (coordinate boundary : Nat) : List Nat :=
  inputValues older newer coordinate boundary ++
    BuilderRegionResidualSelection.scratchValues (RawRouter.compareResult 0 coordinate boundary)

def initialConfiguration (offset : Nat) (older newer : List Nat) (coordinate boundary : Nat)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration (machine offset)
    (endTape (inputValues older newer coordinate boundary) workspace [])

def finalConfiguration (older newer : List Nat) (coordinate boundary : Nat)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.secondState
    (BuilderRegionResidualSelection.finalConfiguration coordinate boundary
      (inputValues older newer coordinate boundary) workspace)

theorem workRunExact (offset : Nat) (older newer : List Nat) (coordinate boundary : Nat)
    (workspace : List WorkSymbol) (hLength : newer.length = offset) :
    workRunExact? (machine offset) (workSteps newer coordinate boundary)
      (initialConfiguration offset older newer coordinate boundary workspace) =
      some (finalConfiguration older newer coordinate boundary workspace) := by
  have hPrepare := BuilderRegionComparisonOperands.prepare_workRunExact
    offset older newer coordinate boundary workspace [] hLength
  simp only [List.drop_nil] at hPrepare
  have hSelect := BuilderRegionResidualSelection.workRunExact coordinate boundary
    (inputValues older newer coordinate boundary) workspace
  exact chain_run_any (prepareMachine offset) BuilderRegionResidualSelection.machine
    (prepareSteps newer coordinate boundary) (BuilderRegionResidualSelection.workSteps coordinate boundary)
    _ _ _ hPrepare hSelect

theorem run_compile_exact (offset : Nat) (older newer : List Nat) (coordinate boundary : Nat)
    (workspace : List WorkSymbol) (hLength : newer.length = offset) :
    run (compileWorkMachine (machine offset)) (6 * workSteps newer coordinate boundary)
      (encodeWorkConfiguration (initialConfiguration offset older newer coordinate boundary workspace)) =
      encodeWorkConfiguration (finalConfiguration older newer coordinate boundary workspace) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _
    (workRunExact offset older newer coordinate boundary workspace hLength)

theorem final_tape (older newer : List Nat) (coordinate boundary : Nat) (workspace : List WorkSymbol) :
    (finalConfiguration older newer coordinate boundary workspace).tape =
      endTape (finalValues older newer coordinate boundary) workspace [] := rfl

/-- The new coordinate is the last physical register, after three restored fields. -/
theorem finalValues_eq (older newer : List Nat) (coordinate boundary : Nat) :
    finalValues older newer coordinate boundary =
      (inputValues older newer coordinate boundary ++
        BuilderRegionResidualRegisters.restoredValues
          (BuilderRegionResidualRegisters.ofComparison (RawRouter.compareResult 0 coordinate boundary))) ++
      [if coordinate < boundary then coordinate else coordinate - boundary] := by
  rw [← BuilderRegionResidualSelection.nextCoordinate_eq]
  simp only [finalValues, BuilderRegionResidualSelection.scratchValues,
    BuilderRegionResidualSelection.nextCoordinate, List.append_assoc]

theorem finalValues_length (older newer : List Nat) (coordinate boundary : Nat) :
    (finalValues older newer coordinate boundary).length =
      (inputValues older newer coordinate boundary).length + 4 := by
  simp only [finalValues, List.length_append, BuilderRegionResidualSelection.scratchValues_length]

theorem nextCoordinate_le (coordinate boundary : Nat) :
    BuilderRegionResidualSelection.nextCoordinate coordinate boundary ≤ coordinate := by
  rw [BuilderRegionResidualSelection.nextCoordinate_eq]
  split
  · exact Nat.le_refl _
  · exact Nat.sub_le _ _

/-- Bound the appended tape span needed by later fixed-offset region copies. -/
theorem scratch_size_le (coordinate boundary bound : Nat)
    (hCoordinate : coordinate ≤ bound) (hBoundary : boundary ≤ bound) :
    let values := BuilderRegionResidualSelection.scratchValues (RawRouter.compareResult 0 coordinate boundary)
    values.length + values.sum ≤ 4 + 4 * bound := by
  have hNext := nextCoordinate_le coordinate boundary
  have hBoundaryRestored := BuilderRegionResidualSelection.restoredBoundary_eq coordinate boundary
  cases hResult : RawRouter.compareResult 0 coordinate boundary <;>
    simp only [BuilderRegionResidualSelection.nextCoordinate, hResult,
      BuilderRegionResidualSelection.resultCoordinate] at hNext <;>
    simp only [hResult, BuilderRegionResidualRegisters.ofComparison, Nat.zero_add] at hBoundaryRestored <;>
    simp only [hResult, BuilderRegionResidualSelection.scratchValues,
      BuilderRegionResidualRegisters.ofComparison, BuilderRegionResidualRegisters.restoredValues,
      BuilderRegionResidualSelection.resultCoordinate, List.length_append, List.length_cons,
      List.length_nil, List.sum_append, List.sum_cons, List.sum_nil] <;> omega

theorem final_accept_iff (offset : Nat) (older newer : List Nat) (coordinate boundary : Nat)
    (workspace : List WorkSymbol) :
    (finalConfiguration older newer coordinate boundary workspace).state = (machine offset).acceptState ↔
      coordinate < boundary := by
  change WorkMachineChain.secondState
      (BuilderRegionResidualSelection.finalConfiguration coordinate boundary
        (inputValues older newer coordinate boundary) workspace).state =
    WorkMachineChain.secondState BuilderRegionResidualSelection.machine.acceptState ↔ _
  constructor
  · intro h
    exact (BuilderRegionResidualSelection.final_accept_iff coordinate boundary _ workspace).1
      (WorkMachineChain.secondState_injective h)
  · intro h
    exact congrArg WorkMachineChain.secondState
      ((BuilderRegionResidualSelection.final_accept_iff coordinate boundary _ workspace).2 h)

theorem final_reject_iff (offset : Nat) (older newer : List Nat) (coordinate boundary : Nat)
    (workspace : List WorkSymbol) :
    (finalConfiguration older newer coordinate boundary workspace).state = (machine offset).rejectState ↔
      boundary ≤ coordinate := by
  change WorkMachineChain.secondState
      (BuilderRegionResidualSelection.finalConfiguration coordinate boundary
        (inputValues older newer coordinate boundary) workspace).state =
    WorkMachineChain.secondState BuilderRegionResidualSelection.machine.rejectState ↔ _
  constructor
  · intro h
    exact (BuilderRegionResidualSelection.final_reject_iff coordinate boundary _ workspace).1
      (WorkMachineChain.secondState_injective h)
  · intro h
    exact congrArg WorkMachineChain.secondState
      ((BuilderRegionResidualSelection.final_reject_iff coordinate boundary _ workspace).2 h)

theorem final_exterior_preserved (older newer : List Nat) (coordinate boundary : Nat)
    (workspace : List WorkSymbol) :
    (finalConfiguration older newer coordinate boundary workspace).tape.right =
      (registerWord (BuilderRegionResidualSelection.scratchValues
        (RawRouter.compareResult 0 coordinate boundary))).reverse ++
      ((registerWord (inputValues older newer coordinate boundary)).reverse ++ workspace) :=
  BuilderRegionResidualSelection.final_exterior_preserved coordinate boundary _ workspace

theorem final_outer_empty (older newer : List Nat) (coordinate boundary : Nat)
    (workspace : List WorkSymbol) :
    (finalConfiguration older newer coordinate boundary workspace).tape.left = [] := rfl

theorem rules_length (offset : Nat) : (machine offset).rules.length = 9 * offset + 818 := by
  change (WorkMachineChain.machine (prepareMachine offset) BuilderRegionResidualSelection.machine).rules.length = _
  rw [chain_rules_length, BuilderRegionResidualSelection.rules_length]
  change 9 + (WorkMachineChain.machine (RegisterCopy.machine 0)
    (RegisterCopy.machine (offset + 2))).rules.length + 602 = _
  rw [chain_rules_length]
  simp only [RegisterCopy.rules_length, RegisterCopy.stateCount]
  omega

theorem rules_pairwise_query_distinct (offset : Nat) :
    (machine offset).rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineChain.rules_pairwise_query_distinct _ _
    (BuilderRegionComparisonOperands.prepare_rules_pairwise_query_distinct offset)
    BuilderRegionResidualSelection.rules_pairwise_query_distinct
    (BuilderRegionComparisonOperands.prepare_noRuleAtAccept offset)

theorem noRuleAtAccept (offset : Nat) : WorkMachineChain.NoRuleAtAccept (machine offset) :=
  WorkMachineChain.noRuleAtAccept _ _ BuilderRegionResidualSelection.noRuleAtAccept

theorem noRuleAtReject (offset : Nat) :
    WorkMachineProgramGraph.NoRuleAt (machine offset) (machine offset).rejectState :=
  chain_noRuleAtReject _ _ BuilderRegionResidualSelection.noRuleAtReject

theorem acceptState_ne_rejectState (offset : Nat) :
    (machine offset).acceptState ≠ (machine offset).rejectState :=
  WorkMachineChain.machine_acceptState_ne_rejectState _ _ BuilderRegionResidualSelection.acceptState_ne_rejectState

def workBound (bound : Nat) : Nat :=
  2 * quadratic (3 * bound + 2) + 2 + BuilderRegionResidualSelection.workBound bound

theorem workSteps_le (newer : List Nat) (coordinate boundary bound : Nat)
    (hCoordinate : coordinate ≤ bound) (hBoundary : boundary ≤ bound)
    (hNewer : newer.length + newer.sum ≤ bound) :
    workSteps newer coordinate boundary ≤ workBound bound := by
  have hPrepare := BuilderRegionComparisonOperands.prepareSteps_le
    newer coordinate boundary bound hCoordinate hBoundary hNewer
  have hSelect := BuilderRegionResidualSelection.workSteps_le coordinate boundary bound hCoordinate hBoundary
  unfold workSteps workBound
  omega

private def quadraticPolynomial (bound : NatPolynomial) : NatPolynomial :=
  let plus := NatPolynomial.add bound (.constant 1)
  .add (.add (.mul (.mul (.constant 4) plus) plus) (.mul (.constant 9) plus)) (.constant 5)

/-- Charge preparation and its bridge, then reuse the complete selector polynomial. -/
def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add
    (.mul (.constant 6)
      (.add (.mul (.constant 2)
        (quadraticPolynomial (.add (.mul (.constant 3) bound) (.constant 2)))) (.constant 2)))
    (BuilderRegionResidualSelection.rawTimePolynomial bound)

theorem rawTimePolynomial_eval (bound : NatPolynomial) (input : Nat) :
    (rawTimePolynomial bound).eval input = 6 * workBound (bound.eval input) := by
  change 6 * (2 * quadratic (3 * bound.eval input + 2) + 2) +
    (BuilderRegionResidualSelection.rawTimePolynomial bound).eval input = _
  rw [BuilderRegionResidualSelection.rawTimePolynomial_eval]
  simp only [workBound, Nat.mul_add]

theorem rawTimePolynomial_le (newer : List Nat) (coordinate boundary input : Nat) (bound : NatPolynomial)
    (hCoordinate : coordinate ≤ bound.eval input) (hBoundary : boundary ≤ bound.eval input)
    (hNewer : newer.length + newer.sum ≤ bound.eval input) :
    6 * workSteps newer coordinate boundary ≤ (rawTimePolynomial bound).eval input := by
  rw [rawTimePolynomial_eval]
  exact Nat.mul_le_mul_left 6 (workSteps_le newer coordinate boundary (bound.eval input)
    hCoordinate hBoundary hNewer)

namespace Source

open BuilderConstraintRegionRegisters (termValue)
open BuilderRegionComparisonOperands.Source (olderValues assembled_values_eq source_values_le)

/-- Execute the actual source assembly once, followed by actual preparation and selection. -/
def machine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineChain.machine (BuilderConstraintRegionAssembly.bodyMachine verifier)
    (BuilderRegionResidualOperands.machine 0)

def workSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : Nat :=
  BuilderConstraintRegionAssembly.bodySteps problem index remaining + 1 +
    BuilderRegionResidualOperands.workSteps [] (constraintIndex problem index) (termValue problem .shape)

def initialConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  workStartConfiguration (machine problem.verifier) (BuilderCursorSource.cursorTape problem index remaining output)

def finalValues {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : List Nat :=
  BuilderRegionResidualOperands.finalValues (olderValues problem index remaining) []
    (constraintIndex problem index) (termValue problem .shape)

def finalConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.secondState
    (BuilderRegionResidualOperands.finalConfiguration (olderValues problem index remaining) []
      (constraintIndex problem index) (termValue problem .shape) (inside problem.input output))

theorem workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (hBody : quotient problem index < count problem) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
      (initialConfiguration problem index remaining output) =
      some (finalConfiguration problem index remaining output) := by
  have hAssembly := BuilderConstraintRegionAssembly.body_workRunExact problem index remaining output hBody
  unfold BuilderConstraintRegionAssembly.bodyInitial BuilderConstraintRegionAssembly.bodyFinal at hAssembly
  rw [assembled_values_eq] at hAssembly
  have hSelect := BuilderRegionResidualOperands.workRunExact 0
    (olderValues problem index remaining) [] (constraintIndex problem index) (termValue problem .shape)
    (inside problem.input output) rfl
  exact chain_run_any (BuilderConstraintRegionAssembly.bodyMachine problem.verifier)
    (BuilderRegionResidualOperands.machine 0) (BuilderConstraintRegionAssembly.bodySteps problem index remaining)
    (BuilderRegionResidualOperands.workSteps [] (constraintIndex problem index) (termValue problem .shape))
    _ _ _ hAssembly hSelect

theorem run_compile_exact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (hBody : quotient problem index < count problem) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining)
      (encodeWorkConfiguration (initialConfiguration problem index remaining output)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining output) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact problem index remaining output hBody)

theorem final_tape {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).tape =
      endTape (finalValues problem index remaining) (inside problem.input output) [] :=
  BuilderRegionResidualOperands.final_tape (olderValues problem index remaining) []
    (constraintIndex problem index) (termValue problem .shape) (inside problem.input output)

theorem finalValues_eq {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    finalValues problem index remaining =
      (BuilderConstraintRegionAssembly.finalValues problem index remaining ++
        BuilderRegionResidualRegisters.restoredValues (BuilderRegionResidualRegisters.ofComparison
          (RawRouter.compareResult 0 (constraintIndex problem index) (termValue problem .shape)))) ++
      [if constraintIndex problem index < termValue problem .shape then constraintIndex problem index
        else constraintIndex problem index - termValue problem .shape] := by
  rw [assembled_values_eq]
  exact BuilderRegionResidualOperands.finalValues_eq _ [] _ _

theorem final_accept_iff {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).state = (machine problem.verifier).acceptState ↔
      constraintIndex problem index < termValue problem .shape := by
  change WorkMachineChain.secondState
      (BuilderRegionResidualOperands.finalConfiguration (olderValues problem index remaining) []
        (constraintIndex problem index) (termValue problem .shape) (inside problem.input output)).state =
    WorkMachineChain.secondState (BuilderRegionResidualOperands.machine 0).acceptState ↔ _
  constructor
  · intro h
    exact (BuilderRegionResidualOperands.final_accept_iff 0 _ [] _ _ _).1
      (WorkMachineChain.secondState_injective h)
  · intro h
    exact congrArg WorkMachineChain.secondState
      ((BuilderRegionResidualOperands.final_accept_iff 0 _ [] _ _ _).2 h)

theorem final_reject_iff {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).state = (machine problem.verifier).rejectState ↔
      termValue problem .shape ≤ constraintIndex problem index := by
  change WorkMachineChain.secondState
      (BuilderRegionResidualOperands.finalConfiguration (olderValues problem index remaining) []
        (constraintIndex problem index) (termValue problem .shape) (inside problem.input output)).state =
    WorkMachineChain.secondState (BuilderRegionResidualOperands.machine 0).rejectState ↔ _
  constructor
  · intro h
    exact (BuilderRegionResidualOperands.final_reject_iff 0 _ [] _ _ _).1
      (WorkMachineChain.secondState_injective h)
  · intro h
    exact congrArg WorkMachineChain.secondState
      ((BuilderRegionResidualOperands.final_reject_iff 0 _ [] _ _ _).2 h)

def rawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderConstraintRegionAssembly.bodyRawTimeBound verifier)
    (.add (.constant 6) (rawTimePolynomial (sourceSpan verifier)))

theorem rawTimeBound_le {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    6 * workSteps problem index remaining ≤ (rawTimeBound problem.verifier).eval problem.input.length := by
  have hAssembly := BuilderConstraintRegionAssembly.body_rawTimeBound_le problem index remaining hBalance
  have hValues := source_values_le problem index remaining hBalance
  have hNewer : ([] : List Nat).length + ([] : List Nat).sum ≤
      (sourceSpan problem.verifier).eval problem.input.length := Nat.zero_le _
  have hSelect := rawTimePolynomial_le [] (constraintIndex problem index) (termValue problem .shape)
    problem.input.length (sourceSpan problem.verifier) hValues.1 hValues.2 hNewer
  simp only [rawTimeBound, NatPolynomial.eval_add, NatPolynomial.eval_constant]
  unfold workSteps
  omega

theorem scratch_size_le {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    let values := BuilderRegionResidualSelection.scratchValues
      (RawRouter.compareResult 0 (constraintIndex problem index) (termValue problem .shape))
    values.length + values.sum ≤ 4 + 4 * (sourceSpan problem.verifier).eval problem.input.length := by
  have hValues := source_values_le problem index remaining hBalance
  exact BuilderRegionResidualOperands.scratch_size_le _ _ _ hValues.1 hValues.2

theorem rules_pairwise_query_distinct {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineChain.rules_pairwise_query_distinct _ _
    (BuilderConstraintRegionAssembly.body_rules_pairwise_query_distinct verifier)
    (BuilderRegionResidualOperands.rules_pairwise_query_distinct 0)
    (BuilderConstraintRegionAssembly.body_noRuleAtAccept verifier)

theorem noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (machine verifier) :=
  WorkMachineChain.noRuleAtAccept _ _ (BuilderRegionResidualOperands.noRuleAtAccept 0)

theorem noRuleAtReject {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier) (machine verifier).rejectState :=
  chain_noRuleAtReject _ _ (BuilderRegionResidualOperands.noRuleAtReject 0)

theorem acceptState_ne_rejectState {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState :=
  WorkMachineChain.machine_acceptState_ne_rejectState _ _ (BuilderRegionResidualOperands.acceptState_ne_rejectState 0)

end Source
end PNP.Concrete.CookLevin.BuilderRegionResidualOperands
