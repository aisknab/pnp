/-
Copyright (c) 2026 PNP Labs.

All-input control-head movement bound to the source-derived action lookup.
The verifier fixes the program. Width, position and movement code are copied
from the existing runtime frame; no action or moved position is supplied.
The region premise identifies a valid control slot, not an executable answer.
-/

import PNP.Concrete.CookLevinBuilderRegisterHeadMove

namespace PNP.Concrete.CookLevin.BuilderControlHeadSource

open BuilderUnaryPolynomial (registerWord registerWord_length)
open BuilderDividerOperands (endTape)
open BuilderLiteralArgumentSource
  (Reference field field_eval inputValues inputCount environment environment_values referenceValue)

def retainedValues {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : List Nat :=
  BuilderControlActionSource.keyValues problem index ++ BuilderControlActionSource.selectedValues problem index

theorem retainedValues_length {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    (retainedValues problem index).length = 8 := by
  simp only [retainedValues, List.length_append, BuilderControlActionSource.keyValues_length,
    BuilderControlActionSource.selected_canonical problem index hRegion, BuilderControlActionSource.rowValues_length]

def widthReference : Reference .control 8 := .source .tapeWidth
def positionReference : Reference .control 8 := .digit ⟨3, by decide⟩
def moveReference : Reference .control 8 := .retained ⟨7, by decide⟩

def widthValue {language : Language} (problem : VerifierTableauProblem language) : Nat :=
  BuilderLiteralArgumentSource.sourceValue problem .tapeWidth
def positionValue {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : Nat :=
  referenceValue problem index .control (retainedValues problem index) positionReference

/-- Canonical execution specification only; the program below reads the written tag. -/
def actualMove {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : HeadMove :=
  (BuilderControlCoordinates.action (BuilderControlCoordinates.ofSource problem index hRegion)).move

theorem position_canonical {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    positionValue problem index = (BuilderControlCoordinates.ofSource problem index hRegion).position.val := by
  have h := (BuilderControlCoordinates.source_radix_coordinates problem index hRegion).1
  simp only [positionValue, referenceValue, positionReference, h, List.getD_cons_zero, List.getD_cons_succ]

theorem move_reference_canonical {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    referenceValue problem index .control (retainedValues problem index) moveReference =
      BuilderRegisterHeadMove.moveCode (actualMove problem index hRegion) := by
  simp only [referenceValue, moveReference, retainedValues, BuilderControlActionSource.keyValues,
    BuilderControlActionSource.keyPrefix, BuilderControlActionSource.selected_canonical problem index hRegion,
    BuilderControlActionSource.rowValues, List.cons_append, List.nil_append,
    List.getD_cons_zero, List.getD_cons_succ, actualMove, BuilderControlCoordinates.action,
    BuilderRegisterHeadMove.moveCode]

def fields {language : Language} (verifier : PolynomialTimeVerifier language) :
    List (BuilderRegisterPack.Field (inputCount verifier .control 8)) :=
  [field verifier .control 8 widthReference, field verifier .control 8 positionReference,
    field verifier .control 8 moveReference]

def packedValues {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : List Nat :=
  BuilderRegisterHeadMove.inputValues (widthValue problem) (positionValue problem index)
    (actualMove problem index hRegion)

theorem fields_values {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    BuilderRegisterPack.values (fields problem.verifier)
      (environment problem index remaining .control 8 (retainedValues problem index)) =
      packedValues problem index hRegion := by
  have hWidth : (field problem.verifier .control 8 widthReference).eval
      (environment problem index remaining .control 8 (retainedValues problem index)) = widthValue problem :=
    field_eval problem index remaining .control 8 (retainedValues problem index) widthReference
  have hPosition : (field problem.verifier .control 8 positionReference).eval
      (environment problem index remaining .control 8 (retainedValues problem index)) = positionValue problem index :=
    field_eval problem index remaining .control 8 (retainedValues problem index) positionReference
  have hMove : (field problem.verifier .control 8 moveReference).eval
      (environment problem index remaining .control 8 (retainedValues problem index)) =
        BuilderRegisterHeadMove.moveCode (actualMove problem index hRegion) :=
    (field_eval problem index remaining .control 8 (retainedValues problem index) moveReference).trans
      (move_reference_canonical problem index hRegion)
  simp only [fields, BuilderRegisterPack.values, List.map_cons, List.map_nil,
    hWidth, hPosition, hMove, packedValues, BuilderRegisterHeadMove.inputValues]

theorem environment_frame {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    List.ofFn (environment problem index remaining .control 8 (retainedValues problem index)) =
      BuilderControlActionSource.finalValues problem index remaining := by
  have h := environment_values problem index remaining .control 8 (retainedValues problem index)
    (retainedValues_length problem index hRegion)
  simpa only [inputValues, retainedValues, BuilderControlActionSource.finalValues,
    BuilderControlActionSource.frame, List.append_nil, List.append_assoc] using h

def packMachine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  BuilderRegisterPack.machine (fields verifier) 0
def continuation {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineChain.machine (packMachine verifier) BuilderRegisterHeadMove.machine
def machine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineChain.machine (BuilderControlActionSource.machine verifier) (continuation verifier)

def packSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : Nat :=
  BuilderRegisterPack.workSteps (fields problem.verifier)
    (environment problem index remaining .control 8 (retainedValues problem index)) []
def workSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : Nat :=
  BuilderControlActionSource.workSteps problem index remaining + 1 +
    (packSteps problem index remaining + 1 +
      BuilderRegisterHeadMove.workSteps (widthValue problem) (positionValue problem index)
        (actualMove problem index hRegion))

def headValues {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : List Nat :=
  BuilderRegisterHeadMove.finalValues (widthValue problem) (positionValue problem index)
    (actualMove problem index hRegion)
def finalRetainedValues {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : List Nat :=
  retainedValues problem index ++ headValues problem index hRegion
def finalValues {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : List Nat :=
  BuilderControlActionSource.finalValues problem index remaining ++ headValues problem index hRegion

theorem finalRetainedValues_length {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    (finalRetainedValues problem index hRegion).length = 12 := by
  simp only [finalRetainedValues, List.length_append, retainedValues_length problem index hRegion,
    headValues, BuilderRegisterHeadMove.finalValues_length]

theorem finalValues_frame {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    finalValues problem index remaining hRegion =
      inputValues problem index remaining .control (finalRetainedValues problem index hRegion) := by
  simp only [finalValues, BuilderControlActionSource.finalValues, BuilderControlActionSource.frame,
    inputValues, finalRetainedValues, retainedValues, List.append_nil, List.append_assoc]

theorem moved_canonical {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    BuilderRegisterHeadMove.moved (widthValue problem) (positionValue problem index)
        (actualMove problem index hRegion) =
      (VerifierTableauProblem.movePosition
        (BuilderControlCoordinates.ofSource problem index hRegion).position
        (BuilderControlCoordinates.action (BuilderControlCoordinates.ofSource problem index hRegion)).move).val := by
  rw [position_canonical problem index hRegion]
  exact BuilderRegisterHeadMove.moved_eq_canonical _ _

def packOutside {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : List WorkSymbol :=
  (BuilderControlActionSource.finalOutside problem index outside).drop (registerWord (packedValues problem index hRegion)).length
def finalOutside {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : List WorkSymbol :=
  BuilderRegisterHeadMove.finalOutside (widthValue problem) (positionValue problem index)
    (actualMove problem index hRegion) (packOutside problem index outside hRegion)

def initialConfiguration {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration (machine problem.verifier)
    (endTape (BuilderControlActionSource.frame problem index remaining) inside outside)
def finalConfiguration {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (inside outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : WorkConfiguration :=
  {
    state := (machine problem.verifier).acceptState
    tape := endTape (finalValues problem index remaining hRegion) inside (finalOutside problem index outside hRegion) }

theorem pack_workRunExact {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (inside outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    workRunExact? (packMachine problem.verifier) (packSteps problem index remaining)
      (workStartConfiguration (packMachine problem.verifier)
        (endTape (BuilderControlActionSource.finalValues problem index remaining) inside outside)) =
      some {
        state := (packMachine problem.verifier).acceptState
        tape := endTape (BuilderControlActionSource.finalValues problem index remaining ++ packedValues problem index hRegion)
          inside (outside.drop (registerWord (packedValues problem index hRegion)).length) } := by
  have h := BuilderRegisterPack.workRunExact (fields problem.verifier) 0 []
    (environment problem index remaining .control 8 (retainedValues problem index)) [] inside outside rfl
  simpa only [BuilderRegisterPack.initialConfiguration, BuilderRegisterPack.finalConfiguration,
    List.nil_append, List.append_nil, environment_frame problem index remaining hRegion,
    fields_values problem index remaining hRegion, packMachine, packSteps] using h

private theorem chain_run (first second : WorkMachine) (firstSteps secondSteps : Nat)
    (initial middle final : WorkTape)
    (hFirst : workRunExact? first firstSteps (workStartConfiguration first initial) =
      some {state := first.acceptState, tape := middle})
    (hSecond : workRunExact? second secondSteps (workStartConfiguration second middle) =
      some {state := second.acceptState, tape := final}) :
    workRunExact? (WorkMachineChain.machine first second) (firstSteps + 1 + secondSteps)
      (workStartConfiguration (WorkMachineChain.machine first second) initial) =
      some {state := (WorkMachineChain.machine first second).acceptState, tape := final} :=
  WorkMachineChain.workRunExact first second firstSteps secondSteps _ _ _ hFirst rfl hSecond

theorem workRunExact {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (inside outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining hRegion)
      (initialConfiguration problem index remaining inside outside) =
      some (finalConfiguration problem index remaining inside outside hRegion) := by
  have hAction := BuilderControlActionSource.workRunExact problem index remaining inside outside hRegion
  simp only [BuilderControlActionSource.initialConfiguration, BuilderControlActionSource.finalConfiguration] at hAction
  have hPack := pack_workRunExact problem index remaining inside
    (BuilderControlActionSource.finalOutside problem index outside) hRegion
  have hMove := BuilderRegisterHeadMove.workRunExact (widthValue problem) (positionValue problem index)
    (actualMove problem index hRegion) (BuilderControlActionSource.finalValues problem index remaining)
    inside (packOutside problem index outside hRegion)
  simp only [BuilderRegisterHeadMove.initialConfiguration, BuilderRegisterHeadMove.finalConfiguration] at hMove
  have hNext := chain_run (packMachine problem.verifier) BuilderRegisterHeadMove.machine
    (packSteps problem index remaining)
    (BuilderRegisterHeadMove.workSteps (widthValue problem) (positionValue problem index) (actualMove problem index hRegion))
    _ _ _ hPack hMove
  have h := chain_run (BuilderControlActionSource.machine problem.verifier) (continuation problem.verifier)
    (BuilderControlActionSource.workSteps problem index remaining)
    (packSteps problem index remaining + 1 +
      BuilderRegisterHeadMove.workSteps (widthValue problem) (positionValue problem index) (actualMove problem index hRegion))
    _ _ _ hAction hNext
  simpa only [machine, continuation, workSteps, initialConfiguration, finalConfiguration,
    finalValues, headValues, finalOutside] using h

theorem run_compile_exact {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (inside outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining hRegion)
      (encodeWorkConfiguration (initialConfiguration problem index remaining inside outside)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining inside outside hRegion) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact problem index remaining inside outside hRegion)

def packSpanBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  BuilderRegisterPack.spanPolynomial (fields verifier) (BuilderControlActionSource.spanBound verifier)
def spanBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  BuilderRegisterHeadMove.spanPolynomial (packSpanBound verifier)
def rawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (.add (BuilderControlActionSource.rawTimeBound verifier) (.constant 6))
    (.add (.add (BuilderRegisterPack.rawTimePolynomial (fields verifier)
      (BuilderControlActionSource.spanBound verifier)) (.constant 6))
      (BuilderRegisterHeadMove.rawTimePolynomial (packSpanBound verifier)))

/-- Bounds are in the actual encoded source-input length, including lookup, packing and movement. -/
theorem source_polynomial_bounds {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    (registerWord (finalValues problem index remaining hRegion)).length ≤
        (spanBound problem.verifier).eval problem.input.length ∧
      6 * workSteps problem index remaining hRegion ≤ (rawTimeBound problem.verifier).eval problem.input.length := by
  have hAction := BuilderControlActionSource.source_polynomial_bounds problem index remaining hBody hBalance hRegion
  have hStart :
      (registerWord ([] ++ List.ofFn (environment problem index remaining .control 8 (retainedValues problem index)) ++ [])).length ≤
        (BuilderControlActionSource.spanBound problem.verifier).eval problem.input.length := by
    simpa only [List.nil_append, List.append_nil, environment_frame problem index remaining hRegion] using hAction.1
  have hPack := BuilderRegisterPack.source_polynomial_bounds (fields problem.verifier)
    (BuilderControlActionSource.spanBound problem.verifier) problem.input.length []
    (environment problem index remaining .control 8 (retainedValues problem index)) [] hStart
  simp only [List.nil_append, List.append_nil, environment_frame problem index remaining hRegion,
    fields_values problem index remaining hRegion] at hPack
  have hMove := BuilderRegisterHeadMove.source_polynomial_bounds (widthValue problem) (positionValue problem index)
    (actualMove problem index hRegion) (BuilderControlActionSource.finalValues problem index remaining)
    (packSpanBound problem.verifier) problem.input.length hPack.1
  constructor
  · exact hMove.1
  · have hPackTime := hPack.2
    have hMoveTime := hMove.2
    simp only [rawTimeBound, NatPolynomial.eval_add, NatPolynomial.eval_constant, workSteps, packSteps]
    omega

theorem final_inside_preserved {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (inside outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    (finalConfiguration problem index remaining inside outside hRegion).tape.right =
      (registerWord (finalValues problem index remaining hRegion)).reverse ++ inside := rfl

theorem final_exterior_accounted {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (inside outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    (finalConfiguration problem index remaining inside outside hRegion).tape.left =
      finalOutside problem index outside hRegion := rfl

theorem final_exterior_length_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    (finalConfiguration problem index remaining inside outside hRegion).tape.left.length ≤
      outside.length + positionValue problem index + widthValue problem + 5 := by
  have hPack : (packOutside problem index outside hRegion).length ≤ outside.length := by
    simp only [packOutside, BuilderControlActionSource.finalOutside, List.length_drop]
    omega
  have h := BuilderRegisterHeadMove.finalOutside_length_le (widthValue problem) (positionValue problem index)
    (actualMove problem index hRegion) (packOutside problem index outside hRegion)
  change (BuilderRegisterHeadMove.finalOutside _ _ _ _).length ≤ _
  omega

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineProgramGraph.QueryDistinct ∧
    WorkMachineProgramGraph.NoRuleAt program program.acceptState ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧
    program.acceptState ≠ program.rejectState

private theorem chain_good (first second : WorkMachine) (hFirst : Good first) (hSecond : Good second) :
    Good (WorkMachineChain.machine first second) :=
  ⟨WorkMachineChain.rules_pairwise_query_distinct first second hFirst.1 hSecond.1 hFirst.2.1,
    WorkMachineChain.noRuleAtAccept first second hSecond.2.1,
    WorkMachineChain.noRuleAtAccept first {second with acceptState := second.rejectState} hSecond.2.2.1,
    WorkMachineChain.machine_acceptState_ne_rejectState first second hSecond.2.2.2⟩

private theorem machine_good {language : Language} (verifier : PolynomialTimeVerifier language) :
    Good (machine verifier) :=
  chain_good _ _
    ⟨BuilderControlActionSource.rules_pairwise_query_distinct verifier,
      BuilderControlActionSource.noRuleAtAccept verifier, BuilderControlActionSource.noRuleAtReject verifier,
      BuilderControlActionSource.acceptState_ne_rejectState verifier⟩
    (chain_good _ _
      ⟨BuilderRegisterPack.rules_pairwise_query_distinct (fields verifier) 0,
        BuilderRegisterPack.noRuleAtAccept (fields verifier) 0, BuilderRegisterPack.noRuleAtReject (fields verifier) 0,
        BuilderRegisterPack.acceptState_ne_rejectState (fields verifier) 0⟩
      ⟨BuilderRegisterHeadMove.rules_pairwise_query_distinct, BuilderRegisterHeadMove.noRuleAtAccept,
        BuilderRegisterHeadMove.noRuleAtReject, BuilderRegisterHeadMove.acceptState_ne_rejectState⟩)

theorem rules_pairwise_query_distinct {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineProgramGraph.QueryDistinct := (machine_good verifier).1
theorem noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier) (machine verifier).acceptState := (machine_good verifier).2.1
theorem noRuleAtReject {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier) (machine verifier).rejectState := (machine_good verifier).2.2.1
theorem acceptState_ne_rejectState {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState := (machine_good verifier).2.2.2

end PNP.Concrete.CookLevin.BuilderControlHeadSource
