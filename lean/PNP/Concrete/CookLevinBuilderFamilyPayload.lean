/-
Copyright (c) 2026 PNP Labs.

One exact interface for all five source-derived radix/payload entries.
The region fixes a branch of the finite dispatcher, not a runtime oracle:
the following source dispatcher must select that branch from its written tag.
Retained history and each family's actual exterior are explicit.
-/
import PNP.Concrete.CookLevinBuilderShapePayload
import PNP.Concrete.CookLevinBuilderInitialPayload
import PNP.Concrete.CookLevinBuilderControlPayload
import PNP.Concrete.CookLevinBuilderPreservationPayload

namespace PNP.Concrete.CookLevin.BuilderFamilyPayload

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape inside)
open BuilderConstraintRegionRegisters (Region)
open BuilderConstraintRegionDispatch (regionTag)

def leafMachine {language : Language} (verifier : PolynomialTimeVerifier language) : Region → WorkMachine
  | .shape => BuilderShapePayload.machine verifier
  | .initial => BuilderInitialPayload.machine verifier
  | .control => BuilderControlPayload.machine verifier
  | .preservation => BuilderPreservationPayload.machine verifier
  | .accepting => BuilderBoundaryPayload.machine verifier .acceptingState

def machine {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) : WorkMachine :=
  WorkMachineChain.machine (BuilderRegionRadixSource.machine verifier region) (leafMachine verifier region)

def leafSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    (region : Region) → BuilderConstraintRegionSource.selectedRegion problem index = some region → Nat
  | .shape, _ => BuilderShapePayload.workSteps problem index remaining
  | .initial, _ => BuilderInitialPayload.workSteps problem index remaining
  | .control, h => BuilderControlPayload.workSteps problem index remaining h
  | .preservation, _ => BuilderPreservationPayload.workSteps problem index remaining
  | .accepting, _ => BuilderBoundaryPayload.workSteps problem index remaining .acceptingState
def workSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (region : Region) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some region) : Nat :=
  BuilderRegionRadixSource.workSteps problem index remaining region + 1 + leafSteps problem index remaining region hRegion

def finalValues {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    (region : Region) → BuilderConstraintRegionSource.selectedRegion problem index = some region → List Nat
  | .shape, _ => BuilderShapePayload.finalValues problem index remaining
  | .initial, _ => BuilderInitialPayload.finalValues problem index remaining
  | .control, h => BuilderControlPayload.finalValues problem index remaining h
  | .preservation, _ => BuilderPreservationPayload.finalValues problem index remaining
  | .accepting, _ => BuilderBoundaryPayload.finalValues problem index remaining .acceptingState
def payloadValues {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    (region : Region) → BuilderConstraintRegionSource.selectedRegion problem index = some region → List Nat
  | .shape, _ => BuilderShapePayload.payloadValues problem index
  | .initial, _ => BuilderInitialPayload.payloadValues problem index
  | .control, h => BuilderControlPayload.payloadValues problem index remaining h
  | .preservation, _ => BuilderPreservationPayload.payloadValues problem index remaining
  | .accepting, _ => BuilderBoundaryPayload.payloadValues problem index .acceptingState
def history {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    (region : Region) → BuilderConstraintRegionSource.selectedRegion problem index = some region → List Nat
  | .shape, _ => BuilderShapeBranchPayload.scratchValues problem index remaining 0 [] (BuilderShapePayload.selectedKind problem index) ++
      [BuilderShapeBranchPayload.countValue problem (BuilderShapePayload.selectedKind problem index)]
  | .initial, _ => BuilderInitialPayload.history problem index remaining
  | .control, h => BuilderLiteralArgumentSource.inputValues problem index remaining .control
      (BuilderControlImplicationPayload.allValues problem index (BuilderControlPayload.selectedConclusion problem index h) h)
  | .preservation, _ => BuilderPreservationPayload.frame problem index remaining ++
      BuilderPreservationPayload.retainedValues problem index
  | .accepting, _ => BuilderBoundaryPayload.literalValues problem index remaining .acceptingState
def exterior {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    (region : Region) → BuilderConstraintRegionSource.selectedRegion problem index = some region → List WorkSymbol
  | .shape, _ => (BuilderShapePayload.finalConfiguration problem index remaining []).tape.left
  | .initial, _ => BuilderInitialPayload.exterior problem index
  | .control, h => BuilderControlPayload.finalOutside problem index remaining [] h
  | .preservation, _ => (BuilderPreservationPayload.finalConfiguration problem index remaining []).tape.left
  | .accepting, _ => []

def initialConfiguration {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (region : Region) : WorkConfiguration :=
  workStartConfiguration (machine problem.verifier region)
    (endTape (BuilderRegionRadixSource.selectedValues problem index remaining region) (inside problem.input output) [])
def finalConfiguration {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (region : Region)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some region) : WorkConfiguration :=
  {state := (machine problem.verifier region).acceptState,
   tape := endTape (finalValues problem index remaining region hRegion) (inside problem.input output)
     (exterior problem index remaining region hRegion)}

theorem final_suffix {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (region : Region) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some region) :
    finalValues problem index remaining region hRegion =
      history problem index remaining region hRegion ++ payloadValues problem index remaining region hRegion := by
  cases region with
  | shape => rfl
  | initial => exact BuilderInitialPayload.final_suffix problem index remaining
  | control => rfl
  | preservation => rfl
  | accepting => rfl

theorem payload_canonical {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (region : Region) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some region) :
    payloadValues problem index remaining region hRegion = BuilderLocalConstraintPayload.values
      (problem.formulaConstraintSlotDirect (BuilderClauseDividerExecution.constraintIndex problem index)) := by
  cases region with
  | shape =>
      rw [← BuilderConstraintRegionSource.regionSlot_eq problem index .shape hRegion]
      exact BuilderShapePayload.payload_canonical problem index hRegion
  | initial => exact BuilderInitialPayload.whole_formula_payload problem index hRegion
  | control =>
      rw [← BuilderConstraintRegionSource.regionSlot_eq problem index .control hRegion]
      exact BuilderControlPayload.payload_source_values problem index remaining hRegion
  | preservation =>
      rw [← BuilderConstraintRegionSource.regionSlot_eq problem index .preservation hRegion]
      exact BuilderPreservationPayload.payload_canonical problem index remaining hRegion
  | accepting => exact BuilderBoundaryPayload.accepting_source_payload problem index hRegion

theorem payload_decode {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (region : Region) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some region) :
    BuilderLocalConstraintPayload.decode problem.FormulaWidth (payloadValues problem index remaining region hRegion) =
      some (problem.formulaConstraintSlotDirect (BuilderClauseDividerExecution.constraintIndex problem index)) := by
  rw [payload_canonical problem index remaining region hRegion, BuilderLocalConstraintPayload.decode_values]

private theorem leaf_run {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (region : Region)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some region) :
    workRunExact? (leafMachine problem.verifier region) (leafSteps problem index remaining region hRegion)
      (workStartConfiguration (leafMachine problem.verifier region)
        (endTape (BuilderRegionRadixSource.finalValues problem index remaining region) (inside problem.input output) [])) =
      some
        {state := (leafMachine problem.verifier region).acceptState,
         tape := endTape (finalValues problem index remaining region hRegion) (inside problem.input output)
          (exterior problem index remaining region hRegion)} := by
  cases region with
  | shape =>
      have h := BuilderShapePayload.workRunExact problem index remaining (inside problem.input output)
      have hInitial : BuilderShapePayload.initialConfiguration problem index remaining (inside problem.input output) =
          workStartConfiguration (leafMachine problem.verifier .shape)
            (endTape (BuilderRegionRadixSource.finalValues problem index remaining .shape) (inside problem.input output) []) := by
        simp only [BuilderShapePayload.initialConfiguration, BuilderShapePayload.frame,
          BuilderLiteralArgumentSource.inputValues, List.append_nil]
        rfl
      have hFinal : BuilderShapePayload.finalConfiguration problem index remaining (inside problem.input output) =
          {state := (leafMachine problem.verifier .shape).acceptState,
           tape := endTape (finalValues problem index remaining .shape hRegion) (inside problem.input output)
             (exterior problem index remaining .shape hRegion)} := rfl
      rw [hInitial, hFinal] at h
      exact h
  | initial =>
      have h := BuilderInitialPayload.workRunExact problem index remaining output
      have hInitial : BuilderInitialPayload.initialConfiguration problem index remaining output =
          workStartConfiguration (leafMachine problem.verifier .initial)
            (endTape (BuilderRegionRadixSource.finalValues problem index remaining .initial) (inside problem.input output) []) := by
        simp only [BuilderInitialPayload.initialConfiguration, BuilderInitialPayload.sourceFrame,
          BuilderLiteralArgumentSource.inputValues, List.append_nil]
        rfl
      rw [hInitial] at h
      exact h
  | control =>
      have h := BuilderControlPayload.workRunExact problem index remaining (inside problem.input output) [] hRegion
      have hInitial : BuilderControlPayload.initialConfiguration problem index remaining (inside problem.input output) [] =
          workStartConfiguration (leafMachine problem.verifier .control)
            (endTape (BuilderRegionRadixSource.finalValues problem index remaining .control) (inside problem.input output) []) := by
        simp only [BuilderControlPayload.initialConfiguration, BuilderControlActionSource.frame,
          BuilderLiteralArgumentSource.inputValues, List.append_nil]
        rfl
      rw [hInitial] at h
      exact h
  | preservation =>
      have h := BuilderPreservationPayload.workRunExact problem index remaining (inside problem.input output)
      have hInitial : BuilderPreservationPayload.initialConfiguration problem index remaining (inside problem.input output) =
          workStartConfiguration (leafMachine problem.verifier .preservation)
            (endTape (BuilderRegionRadixSource.finalValues problem index remaining .preservation) (inside problem.input output) []) := by
        simp only [BuilderPreservationPayload.initialConfiguration, BuilderPreservationPayload.frame,
          BuilderLiteralArgumentSource.inputValues, List.append_nil]
        rfl
      have hFinal : BuilderPreservationPayload.finalConfiguration problem index remaining (inside problem.input output) =
          {state := (leafMachine problem.verifier .preservation).acceptState,
           tape := endTape (finalValues problem index remaining .preservation hRegion) (inside problem.input output)
             (exterior problem index remaining .preservation hRegion)} := rfl
      rw [hInitial, hFinal] at h
      exact h
  | accepting =>
      have h := BuilderBoundaryPayload.workRunExact problem index remaining .acceptingState (inside problem.input output) []
      simpa only [leafMachine, leafSteps, finalValues, exterior,
        BuilderBoundaryPayload.initialConfiguration, BuilderBoundaryPayload.finalConfiguration,
        BuilderBoundaryPayload.region, BuilderBoundaryPayload.finalOutside_nil,
        BuilderLiteralArgumentSource.inputValues, List.append_nil] using h

theorem workRunExact {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (region : Region)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some region) :
    workRunExact? (machine problem.verifier region) (workSteps problem index remaining region hRegion)
      (initialConfiguration problem index remaining output region) =
      some (finalConfiguration problem index remaining output region hRegion) := by
  have hRadix := BuilderRegionRadixSource.workRunExact problem index remaining (inside problem.input output) region
  have hLeaf := leaf_run problem index remaining output region hRegion
  exact WorkMachineChain.workRunExact (BuilderRegionRadixSource.machine problem.verifier region)
    (leafMachine problem.verifier region) _ _ _ _ _ hRadix rfl hLeaf

theorem run_compile_exact {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (region : Region)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some region) :
    run (compileWorkMachine (machine problem.verifier region)) (6 * workSteps problem index remaining region hRegion)
      (encodeWorkConfiguration (initialConfiguration problem index remaining output region)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining output region hRegion) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact problem index remaining output region hRegion)

theorem canonical_workRunExact {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (region : Region)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some region) :
    workRunExact? (machine problem.verifier region) (workSteps problem index remaining region hRegion)
      (initialConfiguration problem index remaining output region) =
      some
        {state := (machine problem.verifier region).acceptState,
         tape := endTape (history problem index remaining region hRegion ++ BuilderLocalConstraintPayload.values
          (problem.formulaConstraintSlotDirect (BuilderClauseDividerExecution.constraintIndex problem index)))
          (inside problem.input output) (exterior problem index remaining region hRegion)} := by
  have h := workRunExact problem index remaining output region hRegion
  rw [finalConfiguration, final_suffix, payload_canonical] at h
  exact h

theorem final_tape {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (region : Region)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some region) :
    (finalConfiguration problem index remaining output region hRegion).tape =
      endTape (finalValues problem index remaining region hRegion) (inside problem.input output)
        (exterior problem index remaining region hRegion) := rfl
theorem final_exterior {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (region : Region)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some region) :
    (finalConfiguration problem index remaining output region hRegion).tape.left =
      exterior problem index remaining region hRegion := rfl

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineProgramGraph.QueryDistinct ∧
    WorkMachineProgramGraph.NoRuleAt program program.acceptState ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧
    program.acceptState ≠ program.rejectState
private theorem leaf_good {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) :
    Good (leafMachine verifier region) := by
  cases region with
  | shape => exact ⟨BuilderShapePayload.rules_pairwise_query_distinct verifier, BuilderShapePayload.noRuleAtAccept verifier,
      BuilderShapePayload.noRuleAtReject verifier, BuilderShapePayload.acceptState_ne_rejectState verifier⟩
  | initial => exact ⟨BuilderInitialPayload.rules_pairwise_query_distinct verifier, BuilderInitialPayload.noRuleAtAccept verifier,
      BuilderInitialPayload.noRuleAtReject verifier, BuilderInitialPayload.acceptState_ne_rejectState verifier⟩
  | control => exact ⟨BuilderControlPayload.rules_pairwise_query_distinct verifier, BuilderControlPayload.noRuleAtAccept verifier,
      BuilderControlPayload.noRuleAtReject verifier, BuilderControlPayload.acceptState_ne_rejectState verifier⟩
  | preservation => exact ⟨BuilderPreservationPayload.rules_pairwise_query_distinct verifier, BuilderPreservationPayload.noRuleAtAccept verifier,
      BuilderPreservationPayload.noRuleAtReject verifier, BuilderPreservationPayload.acceptState_ne_rejectState verifier⟩
  | accepting => exact ⟨BuilderBoundaryPayload.rules_pairwise_query_distinct verifier .acceptingState,
      BuilderBoundaryPayload.noRuleAtAccept verifier .acceptingState, BuilderBoundaryPayload.noRuleAtReject verifier .acceptingState,
      BuilderBoundaryPayload.acceptState_ne_rejectState verifier .acceptingState⟩

theorem rules_pairwise_query_distinct {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) :
    (machine verifier region).rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  WorkMachineChain.rules_pairwise_query_distinct _ _
    (BuilderRegionRadixSource.rules_pairwise_query_distinct verifier region) (leaf_good verifier region).1
    (BuilderRegionRadixSource.noRuleAtAccept verifier region)
theorem noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier region) (machine verifier region).acceptState :=
  WorkMachineChain.noRuleAtAccept _ _ (leaf_good verifier region).2.1
theorem noRuleAtReject {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier region) (machine verifier region).rejectState :=
  WorkMachineChain.noRuleAtAccept (BuilderRegionRadixSource.machine verifier region)
    {(leafMachine verifier region) with acceptState := (leafMachine verifier region).rejectState}
    (leaf_good verifier region).2.2.1
theorem acceptState_ne_rejectState {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) :
    (machine verifier region).acceptState ≠ (machine verifier region).rejectState :=
  WorkMachineChain.machine_acceptState_ne_rejectState _ _ (leaf_good verifier region).2.2.2

def controlExteriorBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (.mul (.constant 2) (formulaTapeWidthPolynomial verifier)) (.constant 8)

/-- The control branch's head-move blank exterior is charged, not assumed erased. -/
theorem control_exterior_le {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    (exterior problem index remaining .control hRegion).length ≤
      (controlExteriorBound problem.verifier).eval problem.input.length := by
  have hTag := BuilderControlPayload.tag_lt problem index hRegion
  have hPack : (BuilderControlHeadSource.packOutside problem index
      (BuilderControlPayload.restoredOutside (BuilderControlPayload.tagValue problem index) []) hRegion).length ≤ 3 := by
    simp only [BuilderControlHeadSource.packOutside, BuilderControlActionSource.finalOutside,
      BuilderControlPayload.restoredOutside, List.drop_nil, List.append_nil, List.length_drop, List.length_replicate]
    omega
  have hHead := BuilderRegisterHeadMove.finalOutside_length_le (BuilderControlHeadSource.widthValue problem)
    (BuilderControlHeadSource.positionValue problem index) (BuilderControlHeadSource.actualMove problem index hRegion)
    (BuilderControlHeadSource.packOutside problem index
      (BuilderControlPayload.restoredOutside (BuilderControlPayload.tagValue problem index) []) hRegion)
  have hPosition : BuilderControlHeadSource.positionValue problem index < BuilderControlHeadSource.widthValue problem := by
    rw [BuilderControlHeadSource.position_canonical problem index hRegion]
    exact (BuilderControlCoordinates.ofSource problem index hRegion).position.isLt
  have hWidth : BuilderControlHeadSource.widthValue problem =
      (formulaTapeWidthPolynomial problem.verifier).eval problem.input.length :=
    problem.formulaTapeWidthPolynomial_eval.symm
  have hDrop : (exterior problem index remaining .control hRegion).length ≤
      (BuilderControlHeadSource.finalOutside problem index
        (BuilderControlPayload.restoredOutside (BuilderControlPayload.tagValue problem index) []) hRegion).length := by
    simp only [exterior, BuilderControlPayload.finalOutside, BuilderControlImplicationPayload.finalOutside,
      BuilderControlLiteralSources.finalOutside, List.length_drop]
    omega
  change (BuilderControlHeadSource.finalOutside problem index
    (BuilderControlPayload.restoredOutside (BuilderControlPayload.tagValue problem index) []) hRegion).length ≤ _ at hHead
  simp only [controlExteriorBound, NatPolynomial.eval_add, NatPolynomial.eval_mul, NatPolynomial.eval_constant]
  omega

def spanBound {language : Language} (verifier : PolynomialTimeVerifier language) : Region → NatPolynomial
  | .shape => BuilderShapePayload.spanBound verifier
  | .initial => BuilderInitialPayload.spanPolynomial verifier
  | .control => .add (BuilderControlPayload.spanBound verifier) (controlExteriorBound verifier)
  | .preservation => BuilderPreservationPayload.spanBound verifier
  | .accepting => BuilderBoundaryPayload.spanPolynomial verifier .acceptingState
def leafRawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : Region → NatPolynomial
  | .shape => BuilderShapePayload.rawTimeBound verifier
  | .initial => BuilderInitialPayload.rawTimePolynomial verifier
  | .control => BuilderControlPayload.rawTimeBound verifier
  | .preservation => BuilderPreservationPayload.rawTimeBound verifier
  | .accepting => BuilderBoundaryPayload.rawTimePolynomial verifier .acceptingState
def rawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) : NatPolynomial :=
  .add (BuilderRegionRadixSource.rawTimeBound verifier region) (.add (.constant 6) (leafRawTimeBound verifier region))

private theorem leaf_bounds {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (region : Region) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some region)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    (registerWord (finalValues problem index remaining region hRegion)).length +
        (exterior problem index remaining region hRegion).length ≤ (spanBound problem.verifier region).eval problem.input.length ∧
      6 * leafSteps problem index remaining region hRegion ≤ (leafRawTimeBound problem.verifier region).eval problem.input.length := by
  cases region with
  | shape => exact BuilderShapePayload.source_polynomial_bounds problem index remaining [] hBody hBalance hRegion
  | initial => exact BuilderInitialPayload.source_polynomial_bounds problem index remaining hBody hBalance hRegion
  | control =>
      have h := BuilderControlPayload.source_polynomial_bounds problem index remaining hBody hBalance hRegion
      have hExterior := control_exterior_le problem index remaining hRegion
      constructor
      · simp only [spanBound, NatPolynomial.eval_add, finalValues]
        omega
      · exact h.2
  | preservation => exact BuilderPreservationPayload.source_polynomial_bounds problem index remaining [] hBody hBalance hRegion
  | accepting =>
      have h := BuilderBoundaryPayload.source_polynomial_bounds problem index remaining .acceptingState hBody hBalance hRegion
      simpa only [finalValues, exterior, spanBound, leafSteps, leafRawTimeBound, List.length_nil, Nat.add_zero] using h

theorem source_polynomial_bounds {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (region : Region) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some region)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    (registerWord (finalValues problem index remaining region hRegion)).length +
        (exterior problem index remaining region hRegion).length ≤ (spanBound problem.verifier region).eval problem.input.length ∧
      6 * workSteps problem index remaining region hRegion ≤ (rawTimeBound problem.verifier region).eval problem.input.length := by
  have hLeaf := leaf_bounds problem index remaining region hRegion hBody hBalance
  have hRadix := BuilderRegionRadixSource.rawTimeBound_le problem index remaining region hBody hBalance hRegion
  constructor
  · exact hLeaf.1
  · simp only [workSteps, rawTimeBound, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

end PNP.Concrete.CookLevin.BuilderFamilyPayload
