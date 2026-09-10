/-
Copyright (c) 2026 PNP Labs.

Derive the five-region frame from the actual source cursor once, then execute
the complete fixed dispatcher. Both its local coordinate and literal tag are
written by machine transitions. The canonical direct decoder below is only a
specification of those outputs, not an executable shortcut.

Region-local decoding, clause occupancy, emission, scratch recovery, Finish,
cleared padding and the complete formula-builder loop remain separate.
-/

import PNP.Concrete.CookLevinBuilderConstraintRegionDispatch

namespace PNP.Concrete.CookLevin.BuilderConstraintRegionSource

open PipelineTape PipelineStateNamespace BuilderUnaryPolynomial
open BuilderDividerOperands (endTape inside count)
open BuilderClauseDividerOperands (quotient)
open BuilderClauseDividerExecution (constraintIndex)
open BuilderDividerSourceExecution (sourceSpan)
open BuilderConstraintRegionRegisters (Region regionLength)
open BuilderConstraintRegionDispatch (Lengths regionTag)
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

/-- These are specifications of values written by the actual assembly. -/
def lengths {language : Language} (problem : VerifierTableauProblem language) : Lengths :=
  { shape := regionLength problem .shape
    initial := regionLength problem .initial
    control := regionLength problem .control
    preservation := regionLength problem .preservation
    accepting := regionLength problem .accepting }

theorem boundary_eq {language : Language} (problem : VerifierTableauProblem language) (region : Region) :
    BuilderConstraintRegionDispatch.boundary (lengths problem) region = regionLength problem region := by
  cases region <;> rfl

theorem frame_eq {language : Language} (problem : VerifierTableauProblem language) :
    BuilderConstraintRegionDispatch.frame (lengths problem) = BuilderConstraintRegionAssembly.lengthFrame problem := rfl

theorem total_eq {language : Language} (problem : VerifierTableauProblem language) :
    BuilderConstraintRegionDispatch.total (lengths problem) = problem.formulaConstraintSlotCount := by
  calc
    BuilderConstraintRegionDispatch.total (lengths problem) =
        (BuilderConstraintRegionDispatch.frame (lengths problem)).sum := by
      simp only [BuilderConstraintRegionDispatch.total, BuilderConstraintRegionDispatch.frame,
        List.sum_cons, List.sum_nil]
      omega
    _ = (BuilderConstraintRegionAssembly.lengthFrame problem).sum := congrArg List.sum (frame_eq problem)
    _ = problem.formulaConstraintSlotCount := BuilderConstraintRegionAssembly.lengthFrame_sum problem

def olderValues {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : List Nat :=
  BuilderClauseCoordinateRegisters.finalValues problem index remaining

theorem assembled_values_eq {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) :
    BuilderConstraintRegionAssembly.finalValues problem index remaining =
      BuilderConstraintRegionDispatch.initialValues (lengths problem) (constraintIndex problem index)
        (olderValues problem index remaining) := by
  unfold BuilderConstraintRegionDispatch.initialValues
  rw [frame_eq]
  simp only [BuilderConstraintRegionAssembly.finalValues, BuilderConstraintRegionAssembly.preparedFrame,
    olderValues, List.append_assoc]

/-- One source assembly and one data-independent dispatcher; no per-region rebuild. -/
def machine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineChain.machine (BuilderConstraintRegionAssembly.bodyMachine verifier)
    BuilderConstraintRegionDispatch.machine

def workSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : Nat :=
  BuilderConstraintRegionAssembly.bodySteps problem index remaining + 1 +
    BuilderConstraintRegionDispatch.workSteps (lengths problem) (constraintIndex problem index)

def initialConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  workStartConfiguration (machine problem.verifier) (BuilderCursorSource.cursorTape problem index remaining output)

def finalValues {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : List Nat :=
  (BuilderConstraintRegionDispatch.outcome (lengths problem) (constraintIndex problem index)
    (olderValues problem index remaining)).values

def finalConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.secondState
    (BuilderConstraintRegionDispatch.finalConfiguration (lengths problem) (constraintIndex problem index)
      (olderValues problem index remaining) (inside problem.input output))

theorem workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (hBody : quotient problem index < count problem) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
      (initialConfiguration problem index remaining output) =
      some (finalConfiguration problem index remaining output) := by
  have hAssembly := BuilderConstraintRegionAssembly.body_workRunExact problem index remaining output hBody
  unfold BuilderConstraintRegionAssembly.bodyInitial BuilderConstraintRegionAssembly.bodyFinal at hAssembly
  rw [assembled_values_eq] at hAssembly
  have hDispatch := BuilderConstraintRegionDispatch.workRunExact (lengths problem) (constraintIndex problem index)
    (olderValues problem index remaining) (inside problem.input output)
  exact chain_run_any (BuilderConstraintRegionAssembly.bodyMachine problem.verifier)
    BuilderConstraintRegionDispatch.machine (BuilderConstraintRegionAssembly.bodySteps problem index remaining)
    (BuilderConstraintRegionDispatch.workSteps (lengths problem) (constraintIndex problem index))
    _ _ _ hAssembly hDispatch

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
  BuilderConstraintRegionDispatch.final_tape _ _ _ _

theorem final_accept_iff {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).state = (machine problem.verifier).acceptState ↔
      constraintIndex problem index < problem.formulaConstraintSlotCount := by
  change WorkMachineChain.secondState
      (BuilderConstraintRegionDispatch.finalConfiguration (lengths problem) (constraintIndex problem index)
        (olderValues problem index remaining) (inside problem.input output)).state =
    WorkMachineChain.secondState BuilderConstraintRegionDispatch.machine.acceptState ↔ _
  rw [← total_eq problem]
  constructor
  · intro h
    exact (BuilderConstraintRegionDispatch.final_accept_iff _ _ _ _).1
      (WorkMachineChain.secondState_injective h)
  · intro h
    exact congrArg WorkMachineChain.secondState ((BuilderConstraintRegionDispatch.final_accept_iff _ _ _ _).2 h)

theorem final_reject_iff {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).state = (machine problem.verifier).rejectState ↔
      problem.formulaConstraintSlotCount ≤ constraintIndex problem index := by
  change WorkMachineChain.secondState
      (BuilderConstraintRegionDispatch.finalConfiguration (lengths problem) (constraintIndex problem index)
        (olderValues problem index remaining) (inside problem.input output)).state =
    WorkMachineChain.secondState BuilderConstraintRegionDispatch.machine.rejectState ↔ _
  rw [← total_eq problem]
  constructor
  · intro h
    exact (BuilderConstraintRegionDispatch.final_reject_iff _ _ _ _).1
      (WorkMachineChain.secondState_injective h)
  · intro h
    exact congrArg WorkMachineChain.secondState ((BuilderConstraintRegionDispatch.final_reject_iff _ _ _ _).2 h)

theorem final_accept_of_body {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (hBody : quotient problem index < count problem) :
    (finalConfiguration problem index remaining output).state = (machine problem.verifier).acceptState :=
  (final_accept_iff problem index remaining output).2
    (BuilderClauseDividerExecution.constraintIndex_lt problem index hBody)

def selectedRegion {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : Option Region :=
  BuilderConstraintRegionDispatch.selectedRegion (lengths problem) (constraintIndex problem index)

def localCoordinate {language : Language} (problem : VerifierTableauProblem language) (index : Nat) (region : Region) : Nat :=
  BuilderConstraintRegionDispatch.remaining (lengths problem) (constraintIndex problem index) region

theorem selectedRegion_some_of_body {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hBody : quotient problem index < count problem) :
    ∃ region, selectedRegion problem index = some region := by
  cases hRegion : selectedRegion problem index with
  | none =>
    have hLe := (BuilderConstraintRegionDispatch.selectedRegion_none_iff
      (lengths problem) (constraintIndex problem index)).1 hRegion
    rw [total_eq] at hLe
    have hLt := BuilderClauseDividerExecution.constraintIndex_lt problem index hBody
    have hFalse : False := by omega
    exact False.elim hFalse
  | some region => exact ⟨region, rfl⟩

theorem localCoordinate_valid {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (region : Region) (hRegion : selectedRegion problem index = some region) :
    localCoordinate problem index region < regionLength problem region := by
  rw [← boundary_eq problem region]
  exact BuilderConstraintRegionDispatch.selectedRegion_local_valid _ _ _ hRegion

def selectedScratch {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (region : Region) : List Nat :=
  BuilderConstraintRegionDispatch.prefixScratch (lengths problem) (constraintIndex problem index) region ++
    BuilderConstraintRegionDispatch.restored (localCoordinate problem index region) (regionLength problem region) ++
    [localCoordinate problem index region, regionTag region]

theorem final_selected_tape {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (region : Region)
    (hRegion : selectedRegion problem index = some region) :
    (finalConfiguration problem index remaining output).tape =
      endTape (BuilderConstraintRegionAssembly.finalValues problem index remaining ++
        selectedScratch problem index region) (inside problem.input output) [] := by
  have h := BuilderConstraintRegionDispatch.final_selected_preserves_frame (lengths problem)
    (constraintIndex problem index) (olderValues problem index remaining) (inside problem.input output) region hRegion
  rw [← assembled_values_eq, boundary_eq] at h
  exact h

theorem final_outer_empty {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).tape.left = [] :=
  BuilderConstraintRegionDispatch.final_outer_empty _ _ _ _

theorem source_values_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    constraintIndex problem index ≤ (sourceSpan problem.verifier).eval problem.input.length ∧
      ∀ region, regionLength problem region ≤ (sourceSpan problem.verifier).eval problem.input.length := by
  have hIndex := (BuilderClauseCoordinateRegisters.source_magnitudes_le problem index remaining hBalance).1
  have hCount := BuilderConstraintRegionAssembly.constraintCount_le_sourceSpan problem index remaining hBalance
  have hTotal := total_eq problem
  change regionLength problem .shape + regionLength problem .initial +
    regionLength problem .control + regionLength problem .preservation +
    regionLength problem .accepting = problem.formulaConstraintSlotCount at hTotal
  refine ⟨hIndex, ?_⟩
  intro region
  cases region <;> omega

def rawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderConstraintRegionAssembly.bodyRawTimeBound verifier)
    (.add (.constant 6) (BuilderConstraintRegionDispatch.rawTimePolynomial (sourceSpan verifier)))

theorem rawTimeBound_le {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    6 * workSteps problem index remaining ≤ (rawTimeBound problem.verifier).eval problem.input.length := by
  have hAssembly := BuilderConstraintRegionAssembly.body_rawTimeBound_le problem index remaining hBalance
  have hValues := source_values_le problem index remaining hBalance
  have hDispatch := BuilderConstraintRegionDispatch.rawTimePolynomial_le (lengths problem)
    (constraintIndex problem index) problem.input.length (sourceSpan problem.verifier) hValues.1
    (fun region => (boundary_eq problem region).symm ▸ hValues.2 region)
  simp only [rawTimeBound, NatPolynomial.eval_add, NatPolynomial.eval_constant]
  unfold workSteps
  omega

theorem rules_pairwise_query_distinct {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineChain.rules_pairwise_query_distinct _ _
    (BuilderConstraintRegionAssembly.body_rules_pairwise_query_distinct verifier)
    BuilderConstraintRegionDispatch.rules_pairwise_query_distinct
    (BuilderConstraintRegionAssembly.body_noRuleAtAccept verifier)

theorem noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (machine verifier) :=
  WorkMachineChain.noRuleAtAccept _ _ BuilderConstraintRegionDispatch.noRuleAtAccept

theorem noRuleAtReject {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier) (machine verifier).rejectState :=
  WorkMachineChain.noRuleAtAccept (BuilderConstraintRegionAssembly.bodyMachine verifier)
    { BuilderConstraintRegionDispatch.machine with acceptState := BuilderConstraintRegionDispatch.machine.rejectState }
    BuilderConstraintRegionDispatch.noRuleAtReject

theorem acceptState_ne_rejectState {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState :=
  WorkMachineChain.machine_acceptState_ne_rejectState _ _ BuilderConstraintRegionDispatch.acceptState_ne_rejectState

/-- Semantic interpretation of a physically selected region, including padded slots.
This definition is not called by the finite machine. -/
def regionSlot {language : Language} (problem : VerifierTableauProblem language)
    (region : Region) (coordinate : Nat) : Option (Option (LocalConstraint problem.FormulaWidth)) :=
  match region with
  | .shape => problem.shapeConstraintSlotDirect coordinate
  | .initial => problem.initialConstraintSlotDirect coordinate
  | .control => problem.controlConstraintSlotDirect coordinate
  | .preservation => problem.preservationConstraintSlotDirect coordinate
  | .accepting => DirectSlot.singleton
      (some (.require (problem.stateLiteral problem.finalTime problem.acceptingState))) coordinate

def slotForCoordinate {language : Language} (problem : VerifierTableauProblem language)
    (coordinate : Nat) : Option (Option (LocalConstraint problem.FormulaWidth)) :=
  match BuilderConstraintRegionDispatch.selectedRegion (lengths problem) coordinate with
  | none => none
  | some region => regionSlot problem region
      (BuilderConstraintRegionDispatch.remaining (lengths problem) coordinate region)

private theorem singleton_none_of_not_lt (value : α) (index : Nat) (hOutside : ¬ index < 1) :
    DirectSlot.singleton value index = none := by
  cases index with
  | zero => exact False.elim (hOutside (by decide))
  | succ index => rfl

/-- Preserve both option layers: an absent region is not a padded empty constraint. -/
theorem slotForCoordinate_eq {language : Language} (problem : VerifierTableauProblem language) (coordinate : Nat) :
    slotForCoordinate problem coordinate = problem.formulaConstraintSlotDirect coordinate := by
  rw [← BuilderConstraintRegionRegisters.orderedSlot_eq problem coordinate]
  unfold slotForCoordinate BuilderConstraintRegionDispatch.selectedRegion
    BuilderConstraintRegionRegisters.orderedSlot DirectSlot.append
  simp only [lengths, BuilderConstraintRegionDispatch.remaining]
  by_cases hShape : coordinate < regionLength problem .shape
  · simp only [if_pos hShape]
    rfl
  · simp only [if_neg hShape]
    by_cases hInitial : coordinate - regionLength problem .shape < regionLength problem .initial
    · simp only [if_pos hInitial]
      rfl
    · simp only [if_neg hInitial]
      by_cases hControl : coordinate - regionLength problem .shape - regionLength problem .initial < regionLength problem .control
      · simp only [if_pos hControl]
        rfl
      · simp only [if_neg hControl]
        by_cases hPreservation : coordinate - regionLength problem .shape - regionLength problem .initial - regionLength problem .control < regionLength problem .preservation
        · simp only [if_pos hPreservation]
          rfl
        · simp only [if_neg hPreservation]
          by_cases hAccepting : coordinate - regionLength problem .shape - regionLength problem .initial - regionLength problem .control - regionLength problem .preservation < regionLength problem .accepting
          · simp only [if_pos hAccepting]
            rfl
          · simp only [if_neg hAccepting]
            exact (singleton_none_of_not_lt _ _ hAccepting).symm

def selectedSlot {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) : Option (Option (LocalConstraint problem.FormulaWidth)) :=
  slotForCoordinate problem (constraintIndex problem index)

theorem selectedSlot_eq {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    selectedSlot problem index = problem.formulaConstraintSlotDirect (constraintIndex problem index) :=
  slotForCoordinate_eq problem (constraintIndex problem index)

theorem regionSlot_eq {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (region : Region) (hRegion : selectedRegion problem index = some region) :
    regionSlot problem region (localCoordinate problem index region) =
      problem.formulaConstraintSlotDirect (constraintIndex problem index) := by
  have h := selectedSlot_eq problem index
  change (match selectedRegion problem index with
    | none => none
    | some region => regionSlot problem region (localCoordinate problem index region)) = _ at h
  rw [hRegion] at h
  exact h

private theorem configuration_eq (configuration : WorkConfiguration) (state : Nat) (tape : WorkTape)
    (hState : configuration.state = state) (hTape : configuration.tape = tape) :
    configuration = { state := state, tape := tape } := by
  cases configuration
  cases hState
  cases hTape
  rfl

/-- The actual body execution writes a tag/local-coordinate pair interpreting to
the canonical direct constraint. Region-local decoder execution is still required. -/
theorem body_dispatch_correct {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (hBody : quotient problem index < count problem) :
    ∃ region,
      workRunExact? (machine problem.verifier) (workSteps problem index remaining)
        (initialConfiguration problem index remaining output) =
        some {
          state := (machine problem.verifier).acceptState
          tape := endTape (BuilderConstraintRegionAssembly.finalValues problem index remaining ++
            selectedScratch problem index region) (inside problem.input output) []
        } ∧
      localCoordinate problem index region < regionLength problem region ∧
      regionSlot problem region (localCoordinate problem index region) =
        problem.formulaConstraintSlotDirect (constraintIndex problem index) := by
  obtain ⟨region, hRegion⟩ := selectedRegion_some_of_body problem index hBody
  refine ⟨region, ?_, localCoordinate_valid problem index region hRegion, regionSlot_eq problem index region hRegion⟩
  have hRun := workRunExact problem index remaining output hBody
  rw [configuration_eq _ _ _ (final_accept_of_body problem index remaining output hBody)
    (final_selected_tape problem index remaining output region hRegion)] at hRun
  exact hRun

theorem finalValues_of_region {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) (hRegion : selectedRegion problem index = some region) :
    finalValues problem index remaining = BuilderConstraintRegionAssembly.finalValues problem index remaining ++
      selectedScratch problem index region := by
  have hRegion' : BuilderConstraintRegionDispatch.selectedRegion (lengths problem) (constraintIndex problem index) =
      some region := hRegion
  unfold finalValues
  rw [BuilderConstraintRegionDispatch.outcome_values_eq, hRegion']
  change ((BuilderConstraintRegionDispatch.stageInput (lengths problem) (constraintIndex problem index)
    (olderValues problem index remaining) region ++
      BuilderConstraintRegionDispatch.restored (localCoordinate problem index region)
        (BuilderConstraintRegionDispatch.boundary (lengths problem) region)) ++
      [localCoordinate problem index region, regionTag region]) = _
  rw [BuilderConstraintRegionDispatch.stageInput_preserves_frame, ← assembled_values_eq, boundary_eq]
  simp only [selectedScratch, List.append_assoc]

private theorem residualScratch_eq (coordinate boundary : Nat) :
    BuilderRegionResidualSelection.scratchValues (RawRouter.compareResult 0 coordinate boundary) =
      BuilderConstraintRegionDispatch.restored coordinate boundary ++
        [BuilderRegionResidualSelection.nextCoordinate coordinate boundary] := rfl

private theorem rejectScratch_size_le (regionLengths : Lengths) (coordinate bound : Nat) (region : Region)
    (hCoordinate : coordinate ≤ bound)
    (hBoundary : ∀ region, BuilderConstraintRegionDispatch.boundary regionLengths region ≤ bound) :
    (BuilderConstraintRegionDispatch.rejectScratch regionLengths coordinate region).length +
      (BuilderConstraintRegionDispatch.rejectScratch regionLengths coordinate region).sum ≤ 4 + 4 * bound := by
  have hRemaining := Nat.le_trans (BuilderConstraintRegionDispatch.remaining_le regionLengths coordinate region) hCoordinate
  have hSize := BuilderRegionResidualOperands.scratch_size_le
    (BuilderConstraintRegionDispatch.remaining regionLengths coordinate region)
    (BuilderConstraintRegionDispatch.boundary regionLengths region) bound hRemaining (hBoundary region)
  have hSub :
      BuilderConstraintRegionDispatch.remaining regionLengths coordinate region -
        BuilderConstraintRegionDispatch.boundary regionLengths region ≤
      BuilderRegionResidualSelection.nextCoordinate
        (BuilderConstraintRegionDispatch.remaining regionLengths coordinate region)
        (BuilderConstraintRegionDispatch.boundary regionLengths region) := by
    rw [BuilderRegionResidualSelection.nextCoordinate_eq]
    split
    · exact Nat.sub_le _ _
    · exact Nat.le_refl _
  simp only [residualScratch_eq, List.length_append, List.length_cons, List.length_nil,
    List.sum_append, List.sum_cons, List.sum_nil] at hSize
  simp only [BuilderConstraintRegionDispatch.rejectScratch, List.length_append, List.length_cons,
    List.length_nil, List.sum_append, List.sum_cons, List.sum_nil]
  omega

private theorem prefixScratch_size_le (regionLengths : Lengths) (coordinate bound : Nat) (region : Region)
    (hCoordinate : coordinate ≤ bound)
    (hBoundary : ∀ region, BuilderConstraintRegionDispatch.boundary regionLengths region ≤ bound) :
    (BuilderConstraintRegionDispatch.prefixScratch regionLengths coordinate region).length +
      (BuilderConstraintRegionDispatch.prefixScratch regionLengths coordinate region).sum ≤ 16 + 16 * bound := by
  have hShape := rejectScratch_size_le regionLengths coordinate bound .shape hCoordinate hBoundary
  have hInitial := rejectScratch_size_le regionLengths coordinate bound .initial hCoordinate hBoundary
  have hControl := rejectScratch_size_le regionLengths coordinate bound .control hCoordinate hBoundary
  have hPreservation := rejectScratch_size_le regionLengths coordinate bound .preservation hCoordinate hBoundary
  cases region <;>
    simp only [BuilderConstraintRegionDispatch.prefixScratch, List.length_append, List.sum_append,
      List.length_nil, List.sum_nil] <;> omega

/-- Scratch growth includes every rejected predecessor and the physically written tag. -/
theorem selectedScratch_size_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : selectedRegion problem index = some region) :
    (selectedScratch problem index region).length + (selectedScratch problem index region).sum ≤
      20 * (sourceSpan problem.verifier).eval problem.input.length + 25 := by
  have hValues := source_values_le problem index remaining hBalance
  have hBound : ∀ region, BuilderConstraintRegionDispatch.boundary (lengths problem) region ≤
      (sourceSpan problem.verifier).eval problem.input.length :=
    fun region => (boundary_eq problem region).symm ▸ hValues.2 region
  have hPrefix := prefixScratch_size_le (lengths problem) (constraintIndex problem index)
    ((sourceSpan problem.verifier).eval problem.input.length) region hValues.1 hBound
  have hCoordinate := Nat.le_trans
    (BuilderConstraintRegionDispatch.remaining_le (lengths problem) (constraintIndex problem index) region) hValues.1
  have hSize := BuilderRegionResidualOperands.scratch_size_le (localCoordinate problem index region)
    (regionLength problem region) ((sourceSpan problem.verifier).eval problem.input.length) hCoordinate (hValues.2 region)
  rw [residualScratch_eq, BuilderRegionResidualSelection.nextCoordinate_eq,
    if_pos (localCoordinate_valid problem index region hRegion)] at hSize
  have hTag : regionTag region ≤ 4 := by cases region <;> decide
  simp only [List.length_append, List.length_cons, List.length_nil,
    List.sum_append, List.sum_cons, List.sum_nil] at hSize
  simp only [selectedScratch, List.length_append, List.length_cons, List.length_nil,
    List.sum_append, List.sum_cons, List.sum_nil]
  omega

/-- Bound the retained register word, not an arbitrarily supplied output prefix. -/
theorem final_register_span_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (hBody : quotient problem index < count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    (registerWord (finalValues problem index remaining)).length ≤
      31 * (sourceSpan problem.verifier).eval problem.input.length + 42 := by
  obtain ⟨region, hRegion⟩ := selectedRegion_some_of_body problem index hBody
  have hOld := BuilderConstraintRegionAssembly.final_register_span_le problem index remaining hBalance
  have hScratch : (registerWord (selectedScratch problem index region)).length ≤
      20 * (sourceSpan problem.verifier).eval problem.input.length + 25 := by
    rw [registerWord_length]
    exact selectedScratch_size_le problem index remaining region hBalance hRegion
  rw [finalValues_of_region problem index remaining region hRegion, registerWord_append, List.length_append]
  omega

end PNP.Concrete.CookLevin.BuilderConstraintRegionSource
