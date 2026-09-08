/-
Copyright (c) 2026 PNP Labs.

The actual source payload preserves the clause-divider coordinate through every
family, including variable-length paired-cell histories. A verifier-fixed root
ordinal retrieves that physical register and appends its value. No coordinate,
payload, family, ordinal or correctness certificate is supplied to the theorem.
This handoff is not yet occupancy dispatch, token emission or the full builder.
-/
import PNP.Concrete.CookLevinBuilderSourcePayload
import PNP.Concrete.CookLevinBuilderRegisterRootCopy

namespace PNP.Concrete.CookLevin.BuilderSourceClauseCoordinate

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape inside count width)
open BuilderClauseDividerOperands (quotient clauseWidth)
open BuilderClauseDividerExecution (clauseIndex constraintIndex)
open BuilderConstraintRegionRegisters (Region)

private theorem extend (leading values extra : List Nat)
    (h : ∃ tail, values = leading ++ tail) :
    ∃ tail, values ++ extra = leading ++ tail := by
  obtain ⟨tail, h⟩ := h
  exact ⟨tail ++ extra, by rw [h, List.append_assoc]⟩

private theorem compose_prefix (first middle final : List Nat)
    (hFirst : ∃ tail, middle = first ++ tail)
    (hSecond : ∃ tail, final = middle ++ tail) :
    ∃ tail, final = first ++ tail := by
  obtain ⟨left, hLeft⟩ := hFirst
  obtain ⟨right, hRight⟩ := hSecond
  exact ⟨left ++ right, by rw [hRight, hLeft, List.append_assoc]⟩

private theorem argument_prefix {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) (after : List Nat) :
    ∃ tail, BuilderLiteralArgumentSource.inputValues problem index remaining region after =
      BuilderClauseCoordinateRegisters.finalValues problem index remaining ++ tail := by
  simp only [BuilderLiteralArgumentSource.inputValues, BuilderRegionRadixSource.finalValues,
    BuilderRegionRadixDecoder.finalValues_eq, BuilderRegionRadixDecoder.inputValues,
    BuilderRegionRadixSource.selectedValues, BuilderConstraintRegionAssembly.finalValues, List.append_assoc]
  exact ⟨_, rfl⟩

private theorem take_without_suffix (leading suffix : List Nat) :
    (leading ++ suffix).take ((leading ++ suffix).length - suffix.length) = leading := by
  rw [List.length_append, Nat.add_sub_cancel]
  exact List.take_left

private theorem paired_source_prefix {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) :
    ∃ tail, BuilderInitialPairedCellSource.finalValues problem index remaining =
      BuilderLiteralArgumentSource.inputValues problem index remaining .initial [] ++ tail := by
  simp only [BuilderInitialPairedCellSource.finalValues, BuilderInitialPairedCellSource.prefixBase,
    BuilderInitialPairedCellSource.sourceFrame, List.append_assoc]
  exact ⟨_, rfl⟩

private theorem paired_cut_prefix {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (length : Fin (problem.certificateLimit + 1)) (offset : Nat)
    (hPrefix : ¬ BuilderInitialPairedCellSource.coordinate problem index < 3)
    (hFound : BuilderInitialPairedCellSource.selection problem index = some (length, offset)) :
    ∃ tail, BuilderInitialPairedCellResolution.sourcePrefix problem index remaining =
      BuilderLiteralArgumentSource.inputValues problem index remaining .initial [] ++ tail := by
  obtain ⟨history, hRequest⟩ := BuilderInitialPairedRequest.output_suffix
    (BuilderInitialPairedCellSource.metadata problem length.val)
    (BuilderInitialPairedCellResolution.cell problem length offset).1
    (BuilderInitialPairedCellResolution.cell problem length offset).2
  simp only [BuilderInitialPairedCellResolution.cell] at hRequest
  have hValues : BuilderInitialPairedCellSource.finalValues problem index remaining =
      (BuilderInitialPairedCellSource.prefixBase problem index remaining ++
        BuilderInitialPairedCellSource.rowFinish problem index ++
        BuilderInitialPairedCellSource.startValues problem length.val ++
        BuilderInitialPairedCellSource.handoffHistory problem length.val offset ++ history) ++
      BuilderInitialPairedCellSource.requestFrame problem length.val offset := by
    simp only [BuilderInitialPairedCellSource.finalValues, if_neg hPrefix,
      BuilderInitialPairedCellSource.tailValues, hFound, BuilderInitialPairedCellSource.requestOutput,
      hRequest, BuilderInitialPairedCellSource.requestFrame, BuilderInitialPairedCellSource.requestCode,
      List.append_assoc]
  have hCut : BuilderInitialPairedCellResolution.sourcePrefix problem index remaining =
      BuilderInitialPairedCellSource.prefixBase problem index remaining ++
        BuilderInitialPairedCellSource.rowFinish problem index ++
        BuilderInitialPairedCellSource.startValues problem length.val ++
        BuilderInitialPairedCellSource.handoffHistory problem length.val offset ++ history := by
    simpa only [BuilderInitialPairedCellResolution.sourcePrefix, hValues,
      BuilderInitialPairedCellSource.requestFrame_length] using
      take_without_suffix
        (BuilderInitialPairedCellSource.prefixBase problem index remaining ++
          BuilderInitialPairedCellSource.rowFinish problem index ++
          BuilderInitialPairedCellSource.startValues problem length.val ++
          BuilderInitialPairedCellSource.handoffHistory problem length.val offset ++ history)
        (BuilderInitialPairedCellSource.requestFrame problem length.val offset)
  rw [hCut]
  simp only [BuilderInitialPairedCellSource.prefixBase, BuilderInitialPairedCellSource.sourceFrame, List.append_assoc]
  exact ⟨_, rfl⟩

private theorem paired_resolution_prefix {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) :
    ∃ tail, BuilderInitialPairedCellResolution.finalValues problem index remaining =
      BuilderLiteralArgumentSource.inputValues problem index remaining .initial [] ++ tail := by
  by_cases hPrefix : BuilderInitialPairedCellSource.coordinate problem index < 3
  · simpa only [BuilderInitialPairedCellResolution.finalValues, if_pos hPrefix] using
      paired_source_prefix problem index remaining
  · cases hFound : BuilderInitialPairedCellSource.selection problem index with
    | none =>
        simpa only [BuilderInitialPairedCellResolution.finalValues, if_neg hPrefix, hFound] using
          paired_source_prefix problem index remaining
    | some found =>
        simp only [BuilderInitialPairedCellResolution.finalValues, if_neg hPrefix, hFound,
          BuilderInitialPairedCellResolution.resolvedValues]
        exact extend _ _ _ (paired_cut_prefix problem index remaining found.1 found.2 hPrefix hFound)

private theorem paired_history_prefix {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (length : Fin (problem.certificateLimit + 1)) (offset : Nat)
    (hPrefix : ¬ BuilderInitialPairedCellSource.coordinate problem index < 3)
    (hFound : BuilderInitialPairedCellSource.selection problem index = some (length, offset)) :
    ∃ tail, BuilderInitialPairedCellPayload.sourceHistory problem index remaining =
      BuilderLiteralArgumentSource.inputValues problem index remaining .initial [] ++ tail := by
  obtain ⟨history, hOutput⟩ := BuilderInitialRequestResolution.output_suffix
    (BuilderInitialPairedCellSource.metadata problem length.val)
    (BuilderInitialPairedCellResolution.cell problem length offset).1
    (BuilderInitialPairedCellResolution.cell problem length offset).2
    (BuilderInitialPairedCellResolution.request problem length offset) problem.input
  have hValues : BuilderInitialPairedCellResolution.finalValues problem index remaining =
      (BuilderInitialPairedCellResolution.sourcePrefix problem index remaining ++ history) ++
        BuilderInitialPairedCellResolution.resultFrame problem length offset := by
    simp only [BuilderInitialPairedCellResolution.finalValues, if_neg hPrefix, hFound,
      BuilderInitialPairedCellResolution.resolvedValues, hOutput,
      BuilderInitialPairedCellResolution.resultFrame, List.append_assoc]
  have hCut : BuilderInitialPairedCellPayload.sourceHistory problem index remaining =
      BuilderInitialPairedCellResolution.sourcePrefix problem index remaining ++ history := by
    simpa only [BuilderInitialPairedCellPayload.sourceHistory, hValues,
      BuilderInitialPairedCellResolution.resultFrame_length] using
      take_without_suffix (BuilderInitialPairedCellResolution.sourcePrefix problem index remaining ++ history)
        (BuilderInitialPairedCellResolution.resultFrame problem length offset)
  rw [hCut]
  exact extend _ _ _ (paired_cut_prefix problem index remaining length offset hPrefix hFound)

private theorem paired_payload_prefix {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) :
    ∃ tail, BuilderInitialPairedCellPayload.finalValues problem index remaining =
      BuilderLiteralArgumentSource.inputValues problem index remaining .initial [] ++ tail := by
  by_cases hPrefix : BuilderInitialPairedCellSource.coordinate problem index < 3
  · simpa only [BuilderInitialPairedCellPayload.finalValues, if_pos hPrefix] using
      paired_resolution_prefix problem index remaining
  · cases hFound : BuilderInitialPairedCellSource.selection problem index with
    | none =>
        simpa only [BuilderInitialPairedCellPayload.finalValues, if_neg hPrefix, hFound] using
          paired_resolution_prefix problem index remaining
    | some found =>
        simp only [BuilderInitialPairedCellPayload.finalValues, if_neg hPrefix, hFound,
          BuilderInitialPairedCellPayload.writtenValues]
        exact extend _ _ _ (paired_history_prefix problem index remaining found.1 found.2 hPrefix hFound)

private theorem initial_prefix {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) :
    ∃ tail, BuilderInitialPayload.finalValues problem index remaining =
      BuilderLiteralArgumentSource.inputValues problem index remaining .initial [] ++ tail := by
  unfold BuilderInitialPayload.finalValues
  cases BuilderInitialPayload.selectedRole problem index with
  | state =>
      simp only [BuilderInitialPayload.branchValues, BuilderBoundaryPayload.finalValues,
        BuilderBoundaryPayload.literalValues, BuilderLiteralArgumentSource.finalValues,
        BuilderBoundaryPayload.region, List.append_assoc]
      exact ⟨_, rfl⟩
  | head =>
      simp only [BuilderInitialPayload.branchValues, BuilderBoundaryPayload.finalValues,
        BuilderBoundaryPayload.literalValues, BuilderLiteralArgumentSource.finalValues,
        BuilderBoundaryPayload.region, List.append_assoc]
      exact ⟨_, rfl⟩
  | length =>
      simp only [BuilderInitialPayload.branchValues, BuilderInitialLengthPayload.finalValues,
        BuilderInitialLengthPayload.scratchValues, BuilderInitialLengthPayload.baseValues,
        BuilderLiteralArgumentSource.finalValues, List.append_assoc]
      exact ⟨_, rfl⟩
  | pairedCells =>
      simp only [BuilderInitialPayload.branchValues, BuilderInitialPayload.pairedValues]
      cases BuilderInitialPairedCellSource.selection problem index with
      | none => exact extend _ _ _ (paired_payload_prefix problem index remaining)
      | some found => exact paired_payload_prefix problem index remaining
  | inputCells =>
      simp only [BuilderInitialPayload.branchValues, BuilderInitialInputOnlySource.finalValues,
        BuilderInitialInputOnlySource.sourceFrame]
      exact ⟨_, rfl⟩

theorem family_preserves_coordinate_frame {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some region) :
    ∃ tail, BuilderFamilyPayload.finalValues problem index remaining region hRegion =
      BuilderClauseCoordinateRegisters.finalValues problem index remaining ++ tail := by
  cases region with
  | shape =>
      obtain ⟨tail, h⟩ := argument_prefix problem index remaining .shape []
      simp only [BuilderFamilyPayload.finalValues, BuilderShapePayload.finalValues,
        BuilderShapeBranchPayload.finalValues, BuilderShapeBranchPayload.scratchValues, h, List.append_assoc]
      exact ⟨_, rfl⟩
  | initial =>
      exact compose_prefix _ _ _ (argument_prefix problem index remaining .initial [])
        (initial_prefix problem index remaining)
  | control =>
      obtain ⟨tail, h⟩ := argument_prefix problem index remaining .control
        (BuilderControlImplicationPayload.allValues problem index
          (BuilderControlPayload.selectedConclusion problem index hRegion) hRegion)
      simp only [BuilderFamilyPayload.finalValues, BuilderControlPayload.finalValues,
        BuilderControlImplicationPayload.finalValues, h, List.append_assoc]
      exact ⟨_, rfl⟩
  | preservation =>
      obtain ⟨tail, h⟩ := argument_prefix problem index remaining .preservation []
      simp only [BuilderFamilyPayload.finalValues, BuilderPreservationPayload.finalValues,
        BuilderPreservationPayload.frame, h, List.append_assoc]
      exact ⟨_, rfl⟩
  | accepting =>
      obtain ⟨tail, h⟩ := argument_prefix problem index remaining .accepting []
      simp only [BuilderFamilyPayload.finalValues, BuilderBoundaryPayload.finalValues,
        BuilderBoundaryPayload.literalValues, BuilderLiteralArgumentSource.finalValues,
        BuilderBoundaryPayload.region, h, List.append_assoc]
      exact ⟨_, rfl⟩

theorem source_preserves_coordinate_frame {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (hBody : quotient problem index < count problem) :
    ∃ tail, BuilderSourcePayload.finalValues problem index remaining hBody =
      BuilderClauseCoordinateRegisters.finalValues problem index remaining ++ tail :=
  family_preserves_coordinate_frame problem index remaining (BuilderSourcePayload.selected problem index)
    (BuilderSourcePayload.selected_valid problem index hBody)

def before {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : List Nat :=
  BuilderOperandRegisters.retainedValues problem index remaining ++
    [count problem, 0, index, width problem, quotient problem index, count problem, 0,
      constraintIndex problem index * clauseWidth problem]

/-- Only the verifier determines the finite locator; runtime data does not. -/
def rootOrdinal {language : Language} (verifier : PolynomialTimeVerifier language) : Nat :=
  nodeCount (BuilderFullScheduleCursorController.bodySlotCountPolynomial verifier) +
    nodeCount (BuilderDimensionRegisters.widthPolynomial verifier) + 11

theorem before_length {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    (before problem index remaining).length = rootOrdinal problem.verifier := by
  simp only [before, BuilderOperandRegisters.retainedValues, BuilderOperandRegisters.prefixValues,
    List.length_append, List.length_cons, List.length_nil, registerValues_length, rootOrdinal]
  omega

theorem coordinate_frame_layout {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) :
    BuilderClauseCoordinateRegisters.finalValues problem index remaining =
      before problem index remaining ++ [clauseIndex problem index, clauseWidth problem, constraintIndex problem index] := by
  simp only [BuilderClauseCoordinateRegisters.finalValues_eq, before, List.append_assoc,
    List.cons_append, List.nil_append]

def after {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : quotient problem index < count problem) : List Nat :=
  (BuilderSourcePayload.finalValues problem index remaining hBody).drop (rootOrdinal problem.verifier + 1)

theorem source_coordinate_layout {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (hBody : quotient problem index < count problem) :
    BuilderSourcePayload.finalValues problem index remaining hBody =
      before problem index remaining ++ [clauseIndex problem index] ++ after problem index remaining hBody := by
  obtain ⟨tail, hTail⟩ := source_preserves_coordinate_frame problem index remaining hBody
  rw [coordinate_frame_layout] at hTail
  have hSplit : BuilderSourcePayload.finalValues problem index remaining hBody =
      (before problem index remaining ++ [clauseIndex problem index]) ++
        (clauseWidth problem :: constraintIndex problem index :: tail) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using hTail
  have hLength : (before problem index remaining ++ [clauseIndex problem index]).length =
      rootOrdinal problem.verifier + 1 := by
    simp only [List.length_append, List.length_cons, List.length_nil, before_length]
  have hAfter : after problem index remaining hBody = clauseWidth problem :: constraintIndex problem index :: tail := by
    rw [after, hSplit, ← hLength, List.drop_left]
  rw [hAfter]
  exact hSplit

def copier {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  BuilderRegisterRootCopy.machine (rootOrdinal verifier)
def machine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineChain.machine (BuilderSourcePayload.machine verifier) (copier verifier)

def copySteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : quotient problem index < count problem) : Nat :=
  BuilderRegisterRootCopy.workSteps (before problem index remaining) (clauseIndex problem index)
    (after problem index remaining hBody)
def workSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : quotient problem index < count problem) : Nat :=
  BuilderSourcePayload.workSteps problem index remaining hBody + 1 + copySteps problem index remaining hBody

def finalValues {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : quotient problem index < count problem) : List Nat :=
  BuilderSourcePayload.finalValues problem index remaining hBody ++ [clauseIndex problem index]
def exterior {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : quotient problem index < count problem) : List WorkSymbol :=
  (BuilderSourcePayload.exterior problem index remaining hBody).drop (clauseIndex problem index + 1)
def initialConfiguration {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) : WorkConfiguration :=
  workStartConfiguration (machine problem.verifier) (BuilderCursorSource.cursorTape problem index remaining output)
def finalConfiguration {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hBody : quotient problem index < count problem) : WorkConfiguration :=
  {state := (machine problem.verifier).acceptState,
   tape := endTape (finalValues problem index remaining hBody) (inside problem.input output) (exterior problem index remaining hBody)}

theorem copy_workRunExact {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hBody : quotient problem index < count problem) :
    workRunExact? (copier problem.verifier) (copySteps problem index remaining hBody)
      (workStartConfiguration (copier problem.verifier)
        (BuilderSourcePayload.finalConfiguration problem index remaining output hBody).tape) =
      some {state := (copier problem.verifier).acceptState,
            tape := endTape (finalValues problem index remaining hBody) (inside problem.input output)
              (exterior problem index remaining hBody)} := by
  have h := BuilderRegisterRootCopy.workRunExact (rootOrdinal problem.verifier)
    (before problem index remaining) (clauseIndex problem index) (after problem index remaining hBody)
    (inside problem.input output).tail (BuilderSourcePayload.exterior problem index remaining hBody)
    (before_length problem index remaining)
  have hInside : PipelineTape.leftMarker :: (inside problem.input output).tail = inside problem.input output := rfl
  simpa only [BuilderRegisterRootCopy.initialConfiguration, BuilderRegisterRootCopy.finalConfiguration,
    ← source_coordinate_layout problem index remaining hBody, hInside,
    BuilderSourcePayload.finalConfiguration, copier, copySteps, finalValues, exterior] using h

private theorem chain_run (first second : WorkMachine) (n m : Nat) (initial middle final : WorkTape)
    (hFirst : workRunExact? first n (workStartConfiguration first initial) =
      some {state := first.acceptState, tape := middle})
    (hSecond : workRunExact? second m (workStartConfiguration second middle) =
      some {state := second.acceptState, tape := final}) :
    workRunExact? (WorkMachineChain.machine first second) (n + 1 + m)
      (workStartConfiguration (WorkMachineChain.machine first second) initial) =
      some {state := (WorkMachineChain.machine first second).acceptState, tape := final} :=
  WorkMachineChain.workRunExact first second n m _ _ _ hFirst rfl hSecond

theorem workRunExact {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hBody : quotient problem index < count problem) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining hBody)
      (initialConfiguration problem index remaining output) =
      some (finalConfiguration problem index remaining output hBody) := by
  have hSource := BuilderSourcePayload.workRunExact problem index remaining output hBody
  simp only [BuilderSourcePayload.initialConfiguration, BuilderSourcePayload.finalConfiguration] at hSource
  have hCopy := copy_workRunExact problem index remaining output hBody
  simp only [BuilderSourcePayload.finalConfiguration] at hCopy
  have h := chain_run (BuilderSourcePayload.machine problem.verifier) (copier problem.verifier)
    (BuilderSourcePayload.workSteps problem index remaining hBody) (copySteps problem index remaining hBody)
    _ _ _ hSource hCopy
  simpa only [machine, workSteps, initialConfiguration, finalConfiguration] using h

theorem run_compile_exact {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hBody : quotient problem index < count problem) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining hBody)
      (encodeWorkConfiguration (initialConfiguration problem index remaining output)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining output hBody) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact problem index remaining output hBody)

theorem final_tape {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hBody : quotient problem index < count problem) :
    (finalConfiguration problem index remaining output hBody).tape =
      endTape (BuilderSourcePayload.finalValues problem index remaining hBody ++ [clauseIndex problem index])
        (inside problem.input output)
        ((BuilderSourcePayload.exterior problem index remaining hBody).drop (clauseIndex problem index + 1)) := rfl

theorem final_tape_canonical {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hBody : quotient problem index < count problem) :
    (finalConfiguration problem index remaining output hBody).tape =
      endTape (BuilderSourcePayload.history problem index remaining hBody ++
        BuilderLocalConstraintPayload.values
          (problem.formulaConstraintSlotDirect (constraintIndex problem index)) ++ [clauseIndex problem index])
        (inside problem.input output) (exterior problem index remaining hBody) := by
  rw [final_tape, BuilderSourcePayload.final_suffix, BuilderSourcePayload.payload_canonical]
  rfl

theorem final_accept {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hBody : quotient problem index < count problem) :
    (finalConfiguration problem index remaining output hBody).state = (machine problem.verifier).acceptState := rfl

theorem rules_pairwise_query_distinct {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineChain.rules_pairwise_query_distinct _ _
    (BuilderSourcePayload.rules_pairwise_query_distinct verifier)
    (BuilderRegisterRootCopy.rules_pairwise_query_distinct (rootOrdinal verifier))
    (BuilderSourcePayload.noRuleAtAccept verifier)
theorem noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (machine verifier) :=
  WorkMachineChain.noRuleAtAccept _ _ (BuilderRegisterRootCopy.noRuleAtAccept (rootOrdinal verifier))
theorem noRuleAtReject {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier) (machine verifier).rejectState :=
  WorkMachineChain.noRuleAtAccept (BuilderSourcePayload.machine verifier)
    {copier verifier with acceptState := (copier verifier).rejectState}
    (BuilderRegisterRootCopy.noRuleAtReject (rootOrdinal verifier))
theorem acceptState_ne_rejectState {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState :=
  WorkMachineChain.machine_acceptState_ne_rejectState _ _
    (BuilderRegisterRootCopy.acceptState_ne_rejectState (rootOrdinal verifier))

def spanBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  BuilderRegisterRootCopy.spanPolynomial (BuilderSourcePayload.spanBound verifier)
def rawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderSourcePayload.rawTimeBound verifier)
    (.add (.constant 6) (BuilderRegisterRootCopy.rawTimePolynomial (BuilderSourcePayload.spanBound verifier)))

theorem source_polynomial_bounds {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : quotient problem index < count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    (registerWord (finalValues problem index remaining hBody)).length + (exterior problem index remaining hBody).length ≤
        (spanBound problem.verifier).eval problem.input.length ∧
      6 * workSteps problem index remaining hBody ≤ (rawTimeBound problem.verifier).eval problem.input.length := by
  have hSource := BuilderSourcePayload.source_polynomial_bounds problem index remaining hBody hBalance
  have hSpan : (registerWord (before problem index remaining ++ [clauseIndex problem index] ++
      after problem index remaining hBody)).length + (BuilderSourcePayload.exterior problem index remaining hBody).length ≤
        (BuilderSourcePayload.spanBound problem.verifier).eval problem.input.length := by
    rw [← source_coordinate_layout problem index remaining hBody]
    exact hSource.1
  have hCopy := BuilderRegisterRootCopy.source_polynomial_bounds (before problem index remaining)
    (clauseIndex problem index) (after problem index remaining hBody)
    (BuilderSourcePayload.exterior problem index remaining hBody)
    (BuilderSourcePayload.spanBound problem.verifier) problem.input.length hSpan
  constructor
  · simpa only [← source_coordinate_layout problem index remaining hBody, finalValues, exterior, spanBound] using hCopy.1
  · simp only [workSteps, copySteps, rawTimeBound, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

end PNP.Concrete.CookLevin.BuilderSourceClauseCoordinate
