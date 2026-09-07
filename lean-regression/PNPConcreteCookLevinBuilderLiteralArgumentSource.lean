/-
Copyright (c) 2026 PNP Labs.
Source dimensions and packet coordinates must come from their proved physical
addresses. The fixed plan cannot replace dimensions or supply a literal answer.
Existing pack/expression literal executions remain the primitive evidence.
-/
import PNP.Concrete.CookLevinBuilderLiteralArgumentSource

namespace PNP.Concrete.CookLevin.BuilderLiteralArgumentSource.Regression

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderConstraintRegionRegisters (Region)

private def coordinates (region : Region) (afterCount : Nat) : Plan region afterCount :=
  fun i => match i.val with
  | 0 => .quotient
  | 1 => .constant 7
  | 2 => .constant 0
  | _ => .constant 2

private def controlPlan : Plan .control 0 :=
  fun i => match i.val with
  | 0 => .quotient
  | 1 => .digit ⟨3, by decide⟩
  | 2 => .digit ⟨2, by decide⟩
  | _ => .digit ⟨1, by decide⟩

example : splitCount .shape = 1 := rfl
example : splitCount .initial = 0 := rfl
example : splitCount .control = 4 := rfl
example : splitCount .preservation = 3 := rfl
example : splitCount .accepting = 0 := rfl
example (region : Region) (afterCount : Nat) (plan : Plan region afterCount) :
    references plan ⟨0, by decide⟩ = .source .timeCount := rfl
example (region : Region) (afterCount : Nat) (plan : Plan region afterCount) :
    references plan ⟨1, by decide⟩ = .source .tapeWidth := rfl
example (region : Region) (afterCount : Nat) (plan : Plan region afterCount) :
    references plan ⟨2, by decide⟩ = .source .stateCount := rfl
example (region : Region) (afterCount : Nat) (plan : Plan region afterCount) :
    references plan ⟨3, by decide⟩ = .source .certificateWidth := rfl
example (region : Region) (afterCount : Nat) (plan : Plan region afterCount) :
    references plan ⟨4, by decide⟩ = plan ⟨0, by decide⟩ := rfl
example (region : Region) (afterCount : Nat) (plan : Plan region afterCount) :
    references plan ⟨7, by decide⟩ = plan ⟨3, by decide⟩ := rfl

section Source
variable {language : Language} (problem : VerifierTableauProblem language)

example (field : SourceField) :
    (sourceAddress problem.verifier field).selected = sourcePolynomial problem.verifier field :=
  sourceAddress_selected problem.verifier field
example : (sourceAddress problem.verifier .timeCount).selected = formulaTimeCountPolynomial problem.verifier := rfl
example : (sourceAddress problem.verifier .tapeWidth).selected = formulaTapeWidthPolynomial problem.verifier := rfl
example : (sourceAddress problem.verifier .stateCount).selected = formulaStateCountPolynomial problem.verifier := rfl
example : (sourceAddress problem.verifier .certificateWidth).selected = problem.verifier.certificateBound := rfl
example : (sourceAddress problem.verifier .fuel).selected = formulaFuelPolynomial problem.verifier := rfl

example (index remaining : Nat) (region : Region) :
    (BuilderRegionRadixSource.finalValues problem index remaining region).length =
      frameCount problem.verifier region := frame_length problem index remaining region
example (index remaining : Nat) (region : Region) (afterCount : Nat) (after : List Nat)
    (hAfter : after.length = afterCount) :
    (inputValues problem index remaining region after).length = inputCount problem.verifier region afterCount :=
  inputValues_length problem index remaining region afterCount after hAfter
example (index remaining : Nat) (region : Region) (afterCount : Nat) (after : List Nat)
    (hAfter : after.length = afterCount) :
    List.ofFn (environment problem index remaining region afterCount after) =
      inputValues problem index remaining region after :=
  environment_values problem index remaining region afterCount after hAfter
example (index remaining : Nat) (region : Region) (afterCount : Nat) (after : List Nat)
    (reference : Reference region afterCount) :
    (field problem.verifier region afterCount reference).eval
      (environment problem index remaining region afterCount after) =
      referenceValue problem index region after reference :=
  field_eval problem index remaining region afterCount after reference

example (index : Nat) (region : Region) :
    referenceValue problem index region ([] : List Nat) (.constant 0 : Reference region 0) = 0 := rfl
example (index : Nat) (region : Region) :
    referenceValue problem index region [7, 13] (.retained ⟨1, by decide⟩ : Reference region 2) = 13 := rfl
example (index : Nat) :
    referenceValue problem index .initial [] (.quotient : Reference .initial 0) =
      BuilderConstraintRegionSource.localCoordinate problem index .initial := rfl
example (index : Nat) :
    referenceValue problem index .accepting [] (.quotient : Reference .accepting 0) =
      BuilderConstraintRegionSource.localCoordinate problem index .accepting := rfl
example (index : Nat) :
    referenceValue problem index .control [] (.digit ⟨0, by decide⟩ : Reference .control 0) =
      BuilderConstraintRegionSource.localCoordinate problem index .control % 3 := rfl
example (index : Nat) :
    referenceValue problem index .control [] (.digit ⟨1, by decide⟩ : Reference .control 0) =
      (BuilderConstraintRegionSource.localCoordinate problem index .control / 3) % 3 := rfl
example (index : Nat) :
    referenceValue problem index .control [] (.digit ⟨2, by decide⟩ : Reference .control 0) =
      (BuilderConstraintRegionSource.localCoordinate problem index .control / 3 / 3) %
        BuilderRegionRadixSource.fieldValue problem .states := rfl
example (index : Nat) :
    referenceValue problem index .control [] (.digit ⟨3, by decide⟩ : Reference .control 0) =
      (BuilderConstraintRegionSource.localCoordinate problem index .control / 3 / 3 /
        BuilderRegionRadixSource.fieldValue problem .states) %
        BuilderRegionRadixSource.fieldValue problem .tapeWidth := rfl
example (index : Nat) :
    referenceValue problem index .preservation [] (.digit ⟨0, by decide⟩ : Reference .preservation 0) =
      BuilderConstraintRegionSource.localCoordinate problem index .preservation % 3 := rfl
example (index : Nat) :
    referenceValue problem index .preservation [] (.digit ⟨1, by decide⟩ : Reference .preservation 0) =
      (BuilderConstraintRegionSource.localCoordinate problem index .preservation / 3) %
        BuilderRegionRadixSource.fieldValue problem .tapeWidth := rfl
example (index : Nat) :
    referenceValue problem index .preservation [] (.digit ⟨2, by decide⟩ : Reference .preservation 0) =
      (BuilderConstraintRegionSource.localCoordinate problem index .preservation / 3 /
        BuilderRegionRadixSource.fieldValue problem .tapeWidth) %
        BuilderRegionRadixSource.fieldValue problem .tapeWidth := rfl

example (region : Region) (afterCount : Nat) (plan : Plan region afterCount) :
    (fields problem.verifier region afterCount plan).length = 8 := fields_length problem.verifier region afterCount plan
example (index : Nat) (region : Region) (afterCount : Nat) (after : List Nat) (plan : Plan region afterCount) :
    (List.ofFn (argumentEnvironment problem index region after plan)).take 4 =
      [problem.dimensions.timeCount, problem.dimensions.tapeWidth problem.tableauInputMode,
        problem.dimensions.stateBound, problem.layout.certificateBitWidth] :=
  argument_dimensions problem index region after plan
example (index : Nat) (region : Region) (after : List Nat) :
    argumentEnvironment problem index region after (coordinates region after.length) ⟨5, by decide⟩ = 7 := rfl
example (index : Nat) (region : Region) (after : List Nat) :
    argumentEnvironment problem index region after (coordinates region after.length) ⟨6, by decide⟩ = 0 := rfl
example (index : Nat) (region : Region) (after : List Nat) :
    argumentEnvironment problem index region after (coordinates region after.length) ⟨7, by decide⟩ = 2 := rfl
example (index : Nat) :
    argumentEnvironment problem index .control [] controlPlan ⟨7, by decide⟩ =
      (BuilderConstraintRegionSource.localCoordinate problem index .control / 3) % 3 := rfl
example (index remaining : Nat) (region : Region) (afterCount : Nat) (after : List Nat) (plan : Plan region afterCount) :
    BuilderRegisterPack.values (fields problem.verifier region afterCount plan)
      (environment problem index remaining region afterCount after) =
      List.ofFn (argumentEnvironment problem index region after plan) :=
  argument_values problem index remaining region afterCount after plan

example (index remaining : Nat) (region : Region) (afterCount : Nat) (after : List Nat) (plan : Plan region afterCount)
    (inside outside : List WorkSymbol) (hAfter : after.length = afterCount) :
    workRunExact? (packMachine problem.verifier region afterCount plan)
      (packSteps problem index remaining region afterCount after plan)
      (workStartConfiguration (packMachine problem.verifier region afterCount plan)
        (endTape (inputValues problem index remaining region after) inside outside)) =
      some {
        state := (packMachine problem.verifier region afterCount plan).acceptState
        tape := endTape (inputValues problem index remaining region after ++
          List.ofFn (argumentEnvironment problem index region after plan)) inside
          (outside.drop (registerWord (List.ofFn (argumentEnvironment problem index region after plan))).length)
      } := pack_workRunExact problem index remaining region afterCount after plan inside outside hAfter
example (index remaining : Nat) (region : Region) (afterCount : Nat) (after : List Nat)
    (plan : Plan region afterCount) (kind : BuilderLiteralIndexExpression.Kind) (inside outside : List WorkSymbol)
    (hAfter : after.length = afterCount) :
    workRunExact? (BuilderLiteralArgumentSource.machine problem.verifier region afterCount plan kind)
      (workSteps problem index remaining region afterCount after plan kind)
      (initialConfiguration problem index remaining region afterCount after plan kind inside outside) =
      some (finalConfiguration problem index remaining region afterCount after plan kind inside outside) :=
  workRunExact problem index remaining region afterCount after plan kind inside outside hAfter
example (index remaining : Nat) (region : Region) (afterCount : Nat) (after : List Nat)
    (plan : Plan region afterCount) (kind : BuilderLiteralIndexExpression.Kind) (inside outside : List WorkSymbol)
    (hAfter : after.length = afterCount) :
    run (compileWorkMachine (BuilderLiteralArgumentSource.machine problem.verifier region afterCount plan kind))
      (6 * workSteps problem index remaining region afterCount after plan kind)
      (encodeWorkConfiguration (initialConfiguration problem index remaining region afterCount after plan kind inside outside)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining region afterCount after plan kind inside outside) :=
  run_compile_exact problem index remaining region afterCount after plan kind inside outside hAfter
example (index remaining : Nat) (region : Region) (afterCount : Nat) (after : List Nat)
    (plan : Plan region afterCount) (kind : BuilderLiteralIndexExpression.Kind) :
    finalValues problem index remaining region after plan kind =
      (inputValues problem index remaining region after ++ List.ofFn (argumentEnvironment problem index region after plan) ++
        BuilderRegisterExpression.prefixValues (BuilderLiteralIndexExpression.expression kind)
          (argumentEnvironment problem index region after plan)) ++
        [BuilderRegisterExpression.eval (BuilderLiteralIndexExpression.expression kind)
          (argumentEnvironment problem index region after plan)] :=
  final_index_register problem index remaining region after plan kind

example (index remaining : Nat) (region : Region) (afterCount : Nat) (after : List Nat)
    (plan : Plan region afterCount) (kind : BuilderLiteralIndexExpression.Kind) (retainedBound : NatPolynomial)
    (hAfter : after.length = afterCount)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some region)
    (hRetained : (registerWord after).length ≤ retainedBound.eval problem.input.length) :
    (registerWord (finalValues problem index remaining region after plan kind)).length ≤
        (finalSpanBound problem.verifier region afterCount plan kind retainedBound).eval problem.input.length ∧
      6 * workSteps problem index remaining region afterCount after plan kind ≤
        (rawTimeBound problem.verifier region afterCount plan kind retainedBound).eval problem.input.length :=
  source_polynomial_bounds problem index remaining region afterCount after plan kind retainedBound hAfter hBody hBalance hRegion hRetained

example (region : Region) (afterCount : Nat) (plan : Plan region afterCount) (kind : BuilderLiteralIndexExpression.Kind) :
    (BuilderLiteralArgumentSource.machine problem.verifier region afterCount plan kind).rules.Pairwise WorkMachineChain.QueryDistinct :=
  rules_pairwise_query_distinct problem.verifier region afterCount plan kind
example (region : Region) (afterCount : Nat) (plan : Plan region afterCount) (kind : BuilderLiteralIndexExpression.Kind) :
    WorkMachineChain.NoRuleAtAccept (BuilderLiteralArgumentSource.machine problem.verifier region afterCount plan kind) :=
  noRuleAtAccept problem.verifier region afterCount plan kind
example (region : Region) (afterCount : Nat) (plan : Plan region afterCount) (kind : BuilderLiteralIndexExpression.Kind) :
    WorkMachineProgramGraph.NoRuleAt (BuilderLiteralArgumentSource.machine problem.verifier region afterCount plan kind)
      (BuilderLiteralArgumentSource.machine problem.verifier region afterCount plan kind).rejectState :=
  noRuleAtReject problem.verifier region afterCount plan kind
example (region : Region) (afterCount : Nat) (plan : Plan region afterCount) (kind : BuilderLiteralIndexExpression.Kind) :
    (BuilderLiteralArgumentSource.machine problem.verifier region afterCount plan kind).acceptState ≠
      (BuilderLiteralArgumentSource.machine problem.verifier region afterCount plan kind).rejectState :=
  acceptState_ne_rejectState problem.verifier region afterCount plan kind

example (hMode : problem.verifier.program.inputMode = .inputOnly) :
    sourceValue problem .certificateWidth = 0 := by
  simp only [sourceValue, VerifierTableauProblem.layout, VariableLayout.certificateBitWidth,
    VerifierTableauProblem.tableauInputMode, hMode, inputModeOfVerifier]
example (hMode : problem.verifier.program.inputMode = .paired) :
    sourceValue problem .certificateWidth = problem.verifier.certificateBound.eval problem.input.length := by
  simp only [sourceValue, VerifierTableauProblem.layout, VariableLayout.certificateBitWidth,
    VerifierTableauProblem.tableauInputMode, hMode, inputModeOfVerifier]
  rfl
example (index remaining : Nat) (region : Region) (afterCount : Nat) (after : List Nat)
    (hMode : problem.verifier.program.inputMode = .inputOnly) :
    (field problem.verifier region afterCount (.source .certificateWidth)).eval
      (environment problem index remaining region afterCount after) = 0 := by
  simp only [field, hMode, BuilderRegisterPack.Field.eval, BuilderRegisterPack.Field.expression,
    BuilderRegisterExpression.eval]
example (index remaining : Nat) (region : Region) (afterCount : Nat) (after : List Nat)
    (hMode : problem.verifier.program.inputMode = .paired) :
    (field problem.verifier region afterCount (.source .certificateWidth)).eval
      (environment problem index remaining region afterCount after) =
        problem.verifier.certificateBound.eval problem.input.length := by
  rw [field_eval]
  simp only [referenceValue, sourceValue, VerifierTableauProblem.layout, VariableLayout.certificateBitWidth,
    VerifierTableauProblem.tableauInputMode, hMode, inputModeOfVerifier]
  rfl
end Source

end PNP.Concrete.CookLevin.BuilderLiteralArgumentSource.Regression
