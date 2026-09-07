/-
Copyright (c) 2026 PNP Labs.

Physical source-bound payload construction for each of the three fixed shape
branches. The expression compiler reads dimensions and row coordinates from
the actual written source/radix frame. Its postorder output already ends in
[count, upper], so the complete range machine needs no supplied field values.

The branch parameter selects fixed program syntax, not a runtime oracle.
Selecting that branch inside one machine is a separate dispatch obligation.
-/
import PNP.Concrete.CookLevinBuilderShapeCoordinates

namespace PNP.Concrete.CookLevin.BuilderShapeBranchPayload

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderRegisterExpression (Expr)
open BuilderShapeCoordinates (Kind Width)

abbrev Arity {language : Language} (verifier : PolynomialTimeVerifier language)
    (afterCount : Nat) := BuilderLiteralArgumentSource.inputCount verifier .shape afterCount

private def referenceExpression {language : Language} (verifier : PolynomialTimeVerifier language)
    (afterCount : Nat) (reference : BuilderLiteralArgumentSource.Reference .shape afterCount) :
    Expr (Arity verifier afterCount) :=
  (BuilderLiteralArgumentSource.field verifier .shape afterCount reference).expression

def countField {language : Language} (verifier : PolynomialTimeVerifier language)
    (afterCount : Nat) : Kind → BuilderRegisterPack.Field (Arity verifier afterCount)
  | .symbol => .constant 3
  | .head => BuilderLiteralArgumentSource.field verifier .shape afterCount (.source .tapeWidth)
  | .state => BuilderLiteralArgumentSource.field verifier .shape afterCount (.source .stateCount)

def baseExpression {language : Language} (verifier : PolynomialTimeVerifier language)
    (afterCount : Nat) (branch : Kind) : Expr (Arity verifier afterCount) :=
  let times := referenceExpression verifier afterCount (.source .timeCount)
  let width := referenceExpression verifier afterCount (.source .tapeWidth)
  let states := referenceExpression verifier afterCount (.source .stateCount)
  let time := referenceExpression verifier afterCount .quotient
  let row := referenceExpression verifier afterCount (.digit ⟨0, by decide⟩)
  let cells := Expr.binary .mul times width
  let symbols := Expr.binary .mul cells (.constant 3)
  match branch with
  | .symbol => .binary .mul (.binary .add (.binary .mul time width) row) (.constant 3)
  | .head => .binary .add symbols (.binary .mul time width)
  | .state => .binary .add (.binary .add symbols cells) (.binary .mul time states)

/-- A leaf right operand makes the actual postorder suffix exactly [count, upper]. -/
def expression {language : Language} (verifier : PolynomialTimeVerifier language)
    (afterCount : Nat) (branch : Kind) : Expr (Arity verifier afterCount) :=
  .binary .add (baseExpression verifier afterCount branch) (countField verifier afterCount branch).expression

def countValue {language : Language} (problem : VerifierTableauProblem language) : Kind → Nat
  | .symbol => 3
  | .head => Width problem
  | .state => problem.dimensions.stateBound

def timeValue {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : Nat :=
  BuilderRegionRadixDecoder.finalQuotient (BuilderRegionRadixSource.radices problem .shape)
    (BuilderConstraintRegionSource.localCoordinate problem index .shape)

def rowValue {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : Nat :=
  (BuilderRegionRadixDecoder.digits (BuilderRegionRadixSource.radices problem .shape)
    (BuilderConstraintRegionSource.localCoordinate problem index .shape)).getD 0 0

def baseValue {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) : Kind → Nat
  | .symbol => BuilderShapeCoordinates.symbolBase problem (timeValue problem index) (rowValue problem index)
  | .head => BuilderShapeCoordinates.headBase problem (timeValue problem index)
  | .state => BuilderShapeCoordinates.stateBase problem (timeValue problem index)

def upperValue {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (branch : Kind) : Nat := baseValue problem index branch + countValue problem branch

private theorem reference_eval {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat)
    (reference : BuilderLiteralArgumentSource.Reference .shape afterCount) :
    BuilderRegisterExpression.eval (referenceExpression problem.verifier afterCount reference)
        (BuilderLiteralArgumentSource.environment problem index remaining .shape afterCount after) =
      BuilderLiteralArgumentSource.referenceValue problem index .shape after reference :=
  BuilderLiteralArgumentSource.field_eval problem index remaining .shape afterCount after reference

theorem countField_eval {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat) (branch : Kind) :
    (countField problem.verifier afterCount branch).eval
        (BuilderLiteralArgumentSource.environment problem index remaining .shape afterCount after) =
      countValue problem branch := by
  cases branch with
  | symbol => rfl
  | head => exact BuilderLiteralArgumentSource.field_eval problem index remaining .shape afterCount after (.source .tapeWidth)
  | state => exact BuilderLiteralArgumentSource.field_eval problem index remaining .shape afterCount after (.source .stateCount)

theorem base_eval {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat) (branch : Kind) :
    BuilderRegisterExpression.eval (baseExpression problem.verifier afterCount branch)
        (BuilderLiteralArgumentSource.environment problem index remaining .shape afterCount after) =
      baseValue problem index branch := by
  cases branch <;>
    simp only [baseExpression, BuilderRegisterExpression.eval, RegisterBinary.value, reference_eval,
      BuilderLiteralArgumentSource.referenceValue, BuilderLiteralArgumentSource.sourceValue,
      baseValue, timeValue, rowValue, BuilderShapeCoordinates.symbolBase,
      BuilderShapeCoordinates.headBase, BuilderShapeCoordinates.stateBase, Width,
      VariableLayout.symbolWidth, VariableLayout.headWidth, VerifierTableauProblem.layout]

theorem expression_eval {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat) (branch : Kind) :
    BuilderRegisterExpression.eval (expression problem.verifier afterCount branch)
        (BuilderLiteralArgumentSource.environment problem index remaining .shape afterCount after) =
      upperValue problem index branch := by
  change BuilderRegisterExpression.eval (baseExpression problem.verifier afterCount branch)
      (BuilderLiteralArgumentSource.environment problem index remaining .shape afterCount after) +
    (countField problem.verifier afterCount branch).eval
      (BuilderLiteralArgumentSource.environment problem index remaining .shape afterCount after) =
      baseValue problem index branch + countValue problem branch
  rw [base_eval, countField_eval]

theorem expression_values {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat) (branch : Kind) :
    BuilderRegisterExpression.values (expression problem.verifier afterCount branch)
        (BuilderLiteralArgumentSource.environment problem index remaining .shape afterCount after) =
      BuilderRegisterExpression.values (baseExpression problem.verifier afterCount branch)
        (BuilderLiteralArgumentSource.environment problem index remaining .shape afterCount after) ++
      [countValue problem branch, upperValue problem index branch] := by
  change BuilderRegisterExpression.values (baseExpression problem.verifier afterCount branch) _ ++
    BuilderRegisterExpression.values (countField problem.verifier afterCount branch).expression _ ++
    [BuilderRegisterExpression.eval (baseExpression problem.verifier afterCount branch) _ +
      (countField problem.verifier afterCount branch).eval _] = _
  rw [BuilderRegisterPack.Field.expression_values, base_eval, countField_eval]
  simp only [upperValue, List.append_assoc, List.cons_append, List.nil_append]

theorem count_le_upper {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (branch : Kind) : countValue problem branch ≤ upperValue problem index branch := by
  unfold upperValue
  omega

def scratchValues {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat) (branch : Kind) : List Nat :=
  BuilderLiteralArgumentSource.inputValues problem index remaining .shape after ++
    BuilderRegisterExpression.values (baseExpression problem.verifier afterCount branch)
      (BuilderLiteralArgumentSource.environment problem index remaining .shape afterCount after)

def fieldsMachine {language : Language} (verifier : PolynomialTimeVerifier language)
    (afterCount : Nat) (branch : Kind) : WorkMachine :=
  BuilderRegisterExpression.machine (expression verifier afterCount branch) 0

def fieldsSteps {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat) (branch : Kind) : Nat :=
  BuilderRegisterExpression.workSteps (expression problem.verifier afterCount branch)
    (BuilderLiteralArgumentSource.environment problem index remaining .shape afterCount after) []

theorem fields_workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat) (branch : Kind)
    (inside outside : List WorkSymbol) (hAfter : after.length = afterCount) :
    workRunExact? (fieldsMachine problem.verifier afterCount branch)
      (fieldsSteps problem index remaining afterCount after branch)
      (workStartConfiguration (fieldsMachine problem.verifier afterCount branch)
        (endTape (BuilderLiteralArgumentSource.inputValues problem index remaining .shape after) inside outside)) =
      some {
        state := (fieldsMachine problem.verifier afterCount branch).acceptState
        tape := endTape (scratchValues problem index remaining afterCount after branch ++
            [countValue problem branch, upperValue problem index branch]) inside
          (outside.drop (registerWord (BuilderRegisterExpression.values
            (expression problem.verifier afterCount branch)
            (BuilderLiteralArgumentSource.environment problem index remaining .shape afterCount after))).length) } := by
  have h := BuilderRegisterExpression.workRunExact (expression problem.verifier afterCount branch) 0 []
    (BuilderLiteralArgumentSource.environment problem index remaining .shape afterCount after) [] inside outside rfl
  simpa only [fieldsMachine, fieldsSteps, BuilderRegisterExpression.initialConfiguration,
    BuilderRegisterExpression.finalConfiguration,
    BuilderLiteralArgumentSource.environment_values problem index remaining .shape afterCount after hAfter,
    expression_values, scratchValues, List.nil_append, List.append_nil, List.append_assoc] using h

def machine {language : Language} (verifier : PolynomialTimeVerifier language)
    (afterCount : Nat) (branch : Kind) : WorkMachine :=
  WorkMachineChain.machine (fieldsMachine verifier afterCount branch) BuilderRegisterExactlyOnePayload.machine

def workSteps {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat) (branch : Kind) : Nat :=
  fieldsSteps problem index remaining afterCount after branch + 1 +
    BuilderRegisterExactlyOnePayload.workSteps (countValue problem branch) (upperValue problem index branch)

def finalValues {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat) (branch : Kind) : List Nat :=
  scratchValues problem index remaining afterCount after branch ++ [countValue problem branch] ++
    BuilderRegisterExactlyOnePayload.payloadValues (countValue problem branch) (upperValue problem index branch)

def exterior {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (branch : Kind) : List WorkSymbol :=
  (List.replicate (upperValue problem index branch - countValue problem branch + 1) .blank).drop
    (countValue problem branch + 6)

def initialConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat) (branch : Kind)
    (inside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration (machine problem.verifier afterCount branch)
    (endTape (BuilderLiteralArgumentSource.inputValues problem index remaining .shape after) inside [])

def finalConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat) (branch : Kind)
    (inside : List WorkSymbol) : WorkConfiguration :=
  { state := (machine problem.verifier afterCount branch).acceptState
    tape := endTape (finalValues problem index remaining afterCount after branch) inside (exterior problem index branch) }

def fieldsWrittenSpan {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat) (branch : Kind) : Nat :=
  (registerWord (BuilderRegisterExpression.values (expression problem.verifier afterCount branch)
    (BuilderLiteralArgumentSource.environment problem index remaining .shape afterCount after))).length

def exteriorWithOutside {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat) (branch : Kind) (outside : List WorkSymbol) : List WorkSymbol :=
  BuilderRegisterExactlyOnePayload.exteriorFrom (countValue problem branch) (upperValue problem index branch)
    (outside.drop (fieldsWrittenSpan problem index remaining afterCount after branch))

def initialConfigurationWithOutside {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat) (branch : Kind)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration (machine problem.verifier afterCount branch)
    (endTape (BuilderLiteralArgumentSource.inputValues problem index remaining .shape after) inside outside)

def finalConfigurationWithOutside {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat) (branch : Kind)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  { state := (machine problem.verifier afterCount branch).acceptState
    tape := endTape (finalValues problem index remaining afterCount after branch) inside
      (exteriorWithOutside problem index remaining afterCount after branch outside) }

theorem initialConfigurationWithOutside_nil {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat) (branch : Kind) (inside : List WorkSymbol) :
    initialConfigurationWithOutside problem index remaining afterCount after branch inside [] =
      initialConfiguration problem index remaining afterCount after branch inside := rfl

theorem finalConfigurationWithOutside_nil {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat) (branch : Kind) (inside : List WorkSymbol) :
    finalConfigurationWithOutside problem index remaining afterCount after branch inside [] =
      finalConfiguration problem index remaining afterCount after branch inside := by
  simp only [finalConfigurationWithOutside, exteriorWithOutside,
    BuilderRegisterExactlyOnePayload.exteriorFrom, BuilderRegisterDescendingRange.exteriorFrom,
    List.drop_nil, List.append_nil, finalConfiguration, exterior]

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

theorem workRunExactWithOutside {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat) (branch : Kind)
    (inside outside : List WorkSymbol) (hAfter : after.length = afterCount) :
    workRunExact? (machine problem.verifier afterCount branch)
      (workSteps problem index remaining afterCount after branch)
      (initialConfigurationWithOutside problem index remaining afterCount after branch inside outside) =
      some (finalConfigurationWithOutside problem index remaining afterCount after branch inside outside) := by
  have hFields := fields_workRunExact problem index remaining afterCount after branch inside outside hAfter
  have hPayload := BuilderRegisterExactlyOnePayload.workRunExactWithOutside (countValue problem branch)
    (upperValue problem index branch) (scratchValues problem index remaining afterCount after branch) inside
    (outside.drop (fieldsWrittenSpan problem index remaining afterCount after branch))
    (count_le_upper problem index branch)
  simp only [BuilderRegisterExactlyOnePayload.finalTapeWithOutside] at hPayload
  have h := chain_run (fieldsMachine problem.verifier afterCount branch)
    BuilderRegisterExactlyOnePayload.machine _ _ _ _ _ hFields hPayload
  simpa only [machine, workSteps, initialConfigurationWithOutside, finalConfigurationWithOutside,
    finalValues, exteriorWithOutside, fieldsWrittenSpan] using h

theorem workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat) (branch : Kind)
    (inside : List WorkSymbol) (hAfter : after.length = afterCount) :
    workRunExact? (machine problem.verifier afterCount branch)
      (workSteps problem index remaining afterCount after branch)
      (initialConfiguration problem index remaining afterCount after branch inside) =
      some (finalConfiguration problem index remaining afterCount after branch inside) := by
  simpa only [initialConfigurationWithOutside_nil, finalConfigurationWithOutside_nil] using
    workRunExactWithOutside problem index remaining afterCount after branch inside [] hAfter

theorem run_compile_exactWithOutside {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat) (branch : Kind)
    (inside outside : List WorkSymbol) (hAfter : after.length = afterCount) :
    run (compileWorkMachine (machine problem.verifier afterCount branch))
      (6 * workSteps problem index remaining afterCount after branch)
      (encodeWorkConfiguration
        (initialConfigurationWithOutside problem index remaining afterCount after branch inside outside)) =
      encodeWorkConfiguration
        (finalConfigurationWithOutside problem index remaining afterCount after branch inside outside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _
    (workRunExactWithOutside problem index remaining afterCount after branch inside outside hAfter)

theorem run_compile_exact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat) (branch : Kind)
    (inside : List WorkSymbol) (hAfter : after.length = afterCount) :
    run (compileWorkMachine (machine problem.verifier afterCount branch))
      (6 * workSteps problem index remaining afterCount after branch)
      (encodeWorkConfiguration (initialConfiguration problem index remaining afterCount after branch inside)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining afterCount after branch inside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _
    (workRunExact problem index remaining afterCount after branch inside hAfter)

theorem source_coordinates {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape) :
    timeValue problem index = (BuilderShapeCoordinates.ofSource problem index hRegion).time.val ∧
    rowValue problem index = (BuilderShapeCoordinates.ofSource problem index hRegion).row.val := by
  have h := BuilderShapeCoordinates.source_radix_coordinates problem index hRegion
  constructor
  · exact h.2
  · unfold rowValue
    rw [h.1]
    rfl

theorem source_count {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape)
    (branch : Kind) (hBranch : BuilderShapeCoordinates.kind (BuilderShapeCoordinates.ofSource problem index hRegion) = branch) :
    countValue problem branch = BuilderShapeCoordinates.count (BuilderShapeCoordinates.ofSource problem index hRegion) := by
  cases branch <;> simp only [BuilderShapeCoordinates.count, hBranch, countValue]

theorem source_base {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape)
    (branch : Kind) (hBranch : BuilderShapeCoordinates.kind (BuilderShapeCoordinates.ofSource problem index hRegion) = branch) :
    baseValue problem index branch = BuilderShapeCoordinates.base (BuilderShapeCoordinates.ofSource problem index hRegion) := by
  have h := source_coordinates problem index hRegion
  cases branch <;> simp only [BuilderShapeCoordinates.base, hBranch, baseValue, h.1, h.2]

theorem source_upper {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape)
    (branch : Kind) (hBranch : BuilderShapeCoordinates.kind (BuilderShapeCoordinates.ofSource problem index hRegion) = branch) :
    upperValue problem index branch = BuilderShapeCoordinates.upper (BuilderShapeCoordinates.ofSource problem index hRegion) := by
  unfold upperValue BuilderShapeCoordinates.upper
  rw [source_base problem index hRegion branch hBranch, source_count problem index hRegion branch hBranch]

theorem source_payload {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape)
    (branch : Kind) (hBranch : BuilderShapeCoordinates.kind (BuilderShapeCoordinates.ofSource problem index hRegion) = branch) :
    BuilderRegisterExactlyOnePayload.payloadValues (countValue problem branch) (upperValue problem index branch) =
      BuilderLocalConstraintPayload.values
        (problem.shapeConstraintSlotDirect (BuilderConstraintRegionSource.localCoordinate problem index .shape)) := by
  rw [source_count problem index hRegion branch hBranch, source_upper problem index hRegion branch hBranch]
  exact BuilderShapeCoordinates.source_payload problem index hRegion

theorem payload_decode {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape)
    (branch : Kind) (hBranch : BuilderShapeCoordinates.kind (BuilderShapeCoordinates.ofSource problem index hRegion) = branch) :
    BuilderLocalConstraintPayload.decode problem.FormulaWidth
      (BuilderRegisterExactlyOnePayload.payloadValues (countValue problem branch) (upperValue problem index branch)) =
      some (problem.shapeConstraintSlotDirect (BuilderConstraintRegionSource.localCoordinate problem index .shape)) := by
  rw [source_payload problem index hRegion branch hBranch, BuilderLocalConstraintPayload.decode_values]

theorem canonical_final_values {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape)
    (branch : Kind) (hBranch : BuilderShapeCoordinates.kind (BuilderShapeCoordinates.ofSource problem index hRegion) = branch) :
    finalValues problem index remaining afterCount after branch =
      scratchValues problem index remaining afterCount after branch ++ [countValue problem branch] ++
        BuilderLocalConstraintPayload.values
          (problem.shapeConstraintSlotDirect (BuilderConstraintRegionSource.localCoordinate problem index .shape)) := by
  rw [finalValues, source_payload problem index hRegion branch hBranch]

theorem canonical_workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat) (branch : Kind)
    (inside : List WorkSymbol) (hAfter : after.length = afterCount)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape)
    (hBranch : BuilderShapeCoordinates.kind (BuilderShapeCoordinates.ofSource problem index hRegion) = branch) :
    workRunExact? (machine problem.verifier afterCount branch)
      (workSteps problem index remaining afterCount after branch)
      (initialConfiguration problem index remaining afterCount after branch inside) =
      some {
        state := (machine problem.verifier afterCount branch).acceptState
        tape := endTape (scratchValues problem index remaining afterCount after branch ++
          [countValue problem branch] ++ BuilderLocalConstraintPayload.values
            (problem.shapeConstraintSlotDirect (BuilderConstraintRegionSource.localCoordinate problem index .shape)))
          inside (exterior problem index branch) } := by
  have h := workRunExact problem index remaining afterCount after branch inside hAfter
  simpa only [finalConfiguration, canonical_final_values problem index remaining afterCount after hRegion branch hBranch] using h

theorem canonical_workRunExactWithOutside {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat) (branch : Kind)
    (inside outside : List WorkSymbol) (hAfter : after.length = afterCount)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape)
    (hBranch : BuilderShapeCoordinates.kind (BuilderShapeCoordinates.ofSource problem index hRegion) = branch) :
    workRunExact? (machine problem.verifier afterCount branch)
      (workSteps problem index remaining afterCount after branch)
      (initialConfigurationWithOutside problem index remaining afterCount after branch inside outside) =
      some {
        state := (machine problem.verifier afterCount branch).acceptState
        tape := endTape (scratchValues problem index remaining afterCount after branch ++
          [countValue problem branch] ++ BuilderLocalConstraintPayload.values
            (problem.shapeConstraintSlotDirect (BuilderConstraintRegionSource.localCoordinate problem index .shape)))
          inside (exteriorWithOutside problem index remaining afterCount after branch outside) } := by
  have h := workRunExactWithOutside problem index remaining afterCount after branch inside outside hAfter
  simpa only [finalConfigurationWithOutside,
    canonical_final_values problem index remaining afterCount after hRegion branch hBranch] using h

def fieldsSpanPolynomial {language : Language} (verifier : PolynomialTimeVerifier language)
    (afterCount : Nat) (branch : Kind) (retainedBound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterExpression.spanPolynomial (expression verifier afterCount branch)
    (BuilderLiteralArgumentSource.inputBound verifier .shape retainedBound)

def fieldsRawTimePolynomial {language : Language} (verifier : PolynomialTimeVerifier language)
    (afterCount : Nat) (branch : Kind) (retainedBound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterExpression.rawTimePolynomial (expression verifier afterCount branch)
    (BuilderLiteralArgumentSource.inputBound verifier .shape retainedBound)

theorem fields_source_polynomial_bounds {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat) (branch : Kind) (retainedBound : NatPolynomial)
    (hAfter : after.length = afterCount)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape)
    (hRetained : (registerWord after).length ≤ retainedBound.eval problem.input.length) :
    (registerWord (scratchValues problem index remaining afterCount after branch ++
        [countValue problem branch, upperValue problem index branch])).length ≤
      (fieldsSpanPolynomial problem.verifier afterCount branch retainedBound).eval problem.input.length ∧
    6 * fieldsSteps problem index remaining afterCount after branch ≤
      (fieldsRawTimePolynomial problem.verifier afterCount branch retainedBound).eval problem.input.length := by
  have hInput := BuilderLiteralArgumentSource.input_span_le problem index remaining .shape after retainedBound
    hBody hBalance hRegion hRetained
  have hEnvironment :
      (registerWord ([] ++ List.ofFn (BuilderLiteralArgumentSource.environment problem index remaining .shape afterCount after) ++ [])).length ≤
        (BuilderLiteralArgumentSource.inputBound problem.verifier .shape retainedBound).eval problem.input.length := by
    simpa only [List.nil_append, List.append_nil,
      BuilderLiteralArgumentSource.environment_values problem index remaining .shape afterCount after hAfter] using hInput
  have h := BuilderRegisterExpression.source_polynomial_bounds (expression problem.verifier afterCount branch)
    (BuilderLiteralArgumentSource.inputBound problem.verifier .shape retainedBound) problem.input.length []
    (BuilderLiteralArgumentSource.environment problem index remaining .shape afterCount after) [] hEnvironment
  simpa only [List.nil_append, List.append_nil,
    BuilderLiteralArgumentSource.environment_values problem index remaining .shape afterCount after hAfter,
    expression_values, scratchValues, List.append_assoc, fieldsSpanPolynomial, fieldsRawTimePolynomial, fieldsSteps] using h

def spanPolynomial {language : Language} (verifier : PolynomialTimeVerifier language)
    (afterCount : Nat) (branch : Kind) (retainedBound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterExactlyOnePayload.spanPolynomial (fieldsSpanPolynomial verifier afterCount branch retainedBound)

def rawTimePolynomial {language : Language} (verifier : PolynomialTimeVerifier language)
    (afterCount : Nat) (branch : Kind) (retainedBound : NatPolynomial) : NatPolynomial :=
  .add (.add (fieldsRawTimePolynomial verifier afterCount branch retainedBound) (.constant 6))
    (BuilderRegisterExactlyOnePayload.rawTimePolynomial (fieldsSpanPolynomial verifier afterCount branch retainedBound))

theorem source_polynomial_bounds {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat) (branch : Kind) (retainedBound : NatPolynomial)
    (hAfter : after.length = afterCount)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape)
    (hRetained : (registerWord after).length ≤ retainedBound.eval problem.input.length) :
    (registerWord (finalValues problem index remaining afterCount after branch)).length +
        (finalConfiguration problem index remaining afterCount after branch []).tape.left.length ≤
      (spanPolynomial problem.verifier afterCount branch retainedBound).eval problem.input.length ∧
    6 * workSteps problem index remaining afterCount after branch ≤
      (rawTimePolynomial problem.verifier afterCount branch retainedBound).eval problem.input.length := by
  have hFields := fields_source_polynomial_bounds problem index remaining afterCount after branch retainedBound
    hAfter hBody hBalance hRegion hRetained
  have hSpan := hFields.1
  simp only [registerWord_append, List.length_append, registerWord_length,
    List.length_cons, List.length_nil, List.sum_cons, List.sum_nil] at hSpan
  have hCount : countValue problem branch ≤
      (fieldsSpanPolynomial problem.verifier afterCount branch retainedBound).eval problem.input.length := by omega
  have hUpper : upperValue problem index branch ≤
      (fieldsSpanPolynomial problem.verifier afterCount branch retainedBound).eval problem.input.length := by omega
  have hOlder : (registerWord (scratchValues problem index remaining afterCount after branch)).length ≤
      (fieldsSpanPolynomial problem.verifier afterCount branch retainedBound).eval problem.input.length := by
    rw [registerWord_length]
    omega
  have hPayload := BuilderRegisterExactlyOnePayload.source_polynomial_bounds
    (fieldsSpanPolynomial problem.verifier afterCount branch retainedBound) problem.input.length
    (countValue problem branch) (upperValue problem index branch)
    (scratchValues problem index remaining afterCount after branch) [] hCount hUpper hOlder
  constructor
  · simpa only [finalValues, finalConfiguration, exterior, spanPolynomial,
      BuilderRegisterExactlyOnePayload.finalConfiguration, BuilderRegisterExactlyOnePayload.finalTape, endTape] using hPayload.1
  · have hTime := hFields.2
    have hPayloadTime := hPayload.2
    simp only [workSteps, rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

theorem exteriorWithOutside_length_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat) (branch : Kind) (outside : List WorkSymbol) :
    (exteriorWithOutside problem index remaining afterCount after branch outside).length ≤
      (exterior problem index branch).length + outside.length := by
  have h := BuilderRegisterExactlyOnePayload.exteriorFrom_length_le (countValue problem branch)
    (upperValue problem index branch)
    (outside.drop (fieldsWrittenSpan problem index remaining afterCount after branch))
  simp only [List.length_drop] at h
  change (BuilderRegisterExactlyOnePayload.exteriorFrom (countValue problem branch) (upperValue problem index branch)
    (outside.drop (fieldsWrittenSpan problem index remaining afterCount after branch))).length ≤ _
  unfold exterior
  simp only [List.length_drop]
  omega

theorem source_polynomial_boundsWithOutside {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat) (branch : Kind)
    (retainedBound outsideBound : NatPolynomial) (outside : List WorkSymbol)
    (hAfter : after.length = afterCount)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape)
    (hRetained : (registerWord after).length ≤ retainedBound.eval problem.input.length)
    (hOutside : outside.length ≤ outsideBound.eval problem.input.length) :
    (registerWord (finalValues problem index remaining afterCount after branch)).length +
        (finalConfigurationWithOutside problem index remaining afterCount after branch [] outside).tape.left.length ≤
      (NatPolynomial.add (spanPolynomial problem.verifier afterCount branch retainedBound) outsideBound).eval problem.input.length ∧
    6 * workSteps problem index remaining afterCount after branch ≤
      (rawTimePolynomial problem.verifier afterCount branch retainedBound).eval problem.input.length := by
  have hOld := source_polynomial_bounds problem index remaining afterCount after branch retainedBound
    hAfter hBody hBalance hRegion hRetained
  have hExterior := exteriorWithOutside_length_le problem index remaining afterCount after branch outside
  constructor
  · have hSpace := hOld.1
    change (registerWord (finalValues problem index remaining afterCount after branch)).length +
      (exterior problem index branch).length ≤ _ at hSpace
    change (registerWord (finalValues problem index remaining afterCount after branch)).length +
      (exteriorWithOutside problem index remaining afterCount after branch outside).length ≤ _
    rw [NatPolynomial.eval_add]
    omega
  · exact hOld.2

theorem rules_pairwise_query_distinct {language : Language} (verifier : PolynomialTimeVerifier language)
    (afterCount : Nat) (branch : Kind) :
    (machine verifier afterCount branch).rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineChain.rules_pairwise_query_distinct _ _
    (BuilderRegisterExpression.rules_pairwise_query_distinct (expression verifier afterCount branch) 0)
    BuilderRegisterExactlyOnePayload.rules_pairwise_query_distinct
    (BuilderRegisterExpression.noRuleAtAccept (expression verifier afterCount branch) 0)

theorem noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language)
    (afterCount : Nat) (branch : Kind) : WorkMachineChain.NoRuleAtAccept (machine verifier afterCount branch) :=
  WorkMachineChain.noRuleAtAccept _ _ BuilderRegisterExactlyOnePayload.noRuleAtAccept

theorem noRuleAtReject {language : Language} (verifier : PolynomialTimeVerifier language)
    (afterCount : Nat) (branch : Kind) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier afterCount branch) (machine verifier afterCount branch).rejectState :=
  WorkMachineChain.noRuleAtAccept (fieldsMachine verifier afterCount branch)
    { BuilderRegisterExactlyOnePayload.machine with acceptState := BuilderRegisterExactlyOnePayload.machine.rejectState }
    BuilderRegisterExactlyOnePayload.noRuleAtReject

theorem acceptState_ne_rejectState {language : Language} (verifier : PolynomialTimeVerifier language)
    (afterCount : Nat) (branch : Kind) :
    (machine verifier afterCount branch).acceptState ≠ (machine verifier afterCount branch).rejectState :=
  WorkMachineChain.machine_acceptState_ne_rejectState _ _ BuilderRegisterExactlyOnePayload.acceptState_ne_rejectState

end PNP.Concrete.CookLevin.BuilderShapeBranchPayload
