/-
Copyright (c) 2026 PNP Labs.

Physical literal arguments from the existing source-derived radix frame.
The four dimensions are fixed source fields; four coordinate references are
finite branch-program syntax. Runtime source values, digits and retained
counters are copied from the tape, never supplied as an argument environment.
Canonical family selection/iteration and uniform continuation wiring remain
separate obligations.
-/

import PNP.Concrete.CookLevinBuilderRegisterPack
import PNP.Concrete.CookLevinBuilderLiteralIndexExpression
import PNP.Concrete.CookLevinBuilderRegionRadixDispatch

namespace PNP.Concrete.CookLevin.BuilderLiteralArgumentSource

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderConstraintRegionRegisters (Region)
open BuilderPolynomialRegisterCopies (Address)

inductive SourceField where
  | timeCount | tapeWidth | stateCount | certificateWidth | fuel
  deriving DecidableEq, Repr

def sourceAddress {language : Language} (verifier : PolynomialTimeVerifier language) :
    SourceField → Address (formulaClauseCountPolynomial verifier)
  | .timeCount => .mulLeft (.addLeft (.addLeft (.addLeft (.addLeft (.mulLeft (.root _))))))
  | .tapeWidth => BuilderRegionRadixSource.fieldAddress verifier .tapeWidth
  | .stateCount => BuilderRegionRadixSource.fieldAddress verifier .states
  | .certificateWidth => .mulLeft (.addRight (.mulRight (.mulLeft (.addLeft (.root _)))))
  | .fuel => .mulLeft (.addLeft (.addLeft (.addLeft (.addLeft (.mulLeft (.addLeft (.root _)))))))

def sourcePolynomial {language : Language} (verifier : PolynomialTimeVerifier language) :
    SourceField → NatPolynomial
  | .timeCount => formulaTimeCountPolynomial verifier
  | .tapeWidth => formulaTapeWidthPolynomial verifier
  | .stateCount => formulaStateCountPolynomial verifier
  | .certificateWidth => verifier.certificateBound
  | .fuel => formulaFuelPolynomial verifier

theorem sourceAddress_selected {language : Language} (verifier : PolynomialTimeVerifier language)
    (field : SourceField) : (sourceAddress verifier field).selected = sourcePolynomial verifier field := by
  cases field <;> rfl

def sourceValue {language : Language} (problem : VerifierTableauProblem language) : SourceField → Nat
  | .timeCount => problem.dimensions.timeCount
  | .tapeWidth => problem.dimensions.tapeWidth problem.tableauInputMode
  | .stateCount => problem.dimensions.stateBound
  | .certificateWidth => problem.layout.certificateBitWidth
  | .fuel => problem.uniformFuel

def splitCount (region : Region) : Nat := (BuilderRegionRadixSource.radixFields region).length

def frameCount {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) : Nat :=
  nodeCount (formulaClauseCountPolynomial verifier) +
    BuilderRegionRadixSource.sourceCount verifier region + 7 * splitCount region + 1

private def frameSuffix {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) : List Nat :=
  BuilderRegionRadixSource.sourceSuffix problem index remaining region ++
    (BuilderRegionRadixSource.radices problem region).reverse ++
    [BuilderConstraintRegionSource.localCoordinate problem index region] ++
    BuilderRegionRadixDecoder.extraValues (BuilderRegionRadixSource.radices problem region)
      (BuilderConstraintRegionSource.localCoordinate problem index region)

private theorem frame_layout {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) :
    BuilderRegionRadixSource.finalValues problem index remaining region =
      registerValues (formulaClauseCountPolynomial problem.verifier) problem.input.length ++
        frameSuffix problem index remaining region := by
  rw [BuilderRegionRadixSource.finalValues_preserve_source]
  simp only [BuilderRegionRadixSource.preparedValues, BuilderRegionRadixSource.selectedValues_layout,
    BuilderPolynomialRegisterCopies.inputValues, frameSuffix, List.nil_append, List.append_assoc]

theorem frame_length {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) :
    (BuilderRegionRadixSource.finalValues problem index remaining region).length =
      frameCount problem.verifier region := by
  rw [frame_layout]
  simp only [frameSuffix, List.length_append, registerValues_length,
    BuilderRegionRadixSource.sourceSuffix_length, List.length_reverse,
    List.length_cons, List.length_nil, BuilderRegionRadixDecoder.extraValues_length,
    BuilderRegionRadixSource.radices_length, frameCount, splitCount]
  omega

def inputCount {language : Language} (verifier : PolynomialTimeVerifier language)
    (region : Region) (afterCount : Nat) : Nat := frameCount verifier region + afterCount

def inputValues {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) (after : List Nat) : List Nat :=
  BuilderRegionRadixSource.finalValues problem index remaining region ++ after

theorem inputValues_length {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) (afterCount : Nat) (after : List Nat)
    (hAfter : after.length = afterCount) :
    (inputValues problem index remaining region after).length = inputCount problem.verifier region afterCount := by
  simp only [inputValues, List.length_append, frame_length, inputCount, hAfter]

/-- A view of written cells, used only in the execution specification. -/
def environment {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) (afterCount : Nat) (after : List Nat) :
    Fin (inputCount problem.verifier region afterCount) → Nat :=
  fun field => (inputValues problem index remaining region after).getD field.val 0

theorem environment_values {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) (afterCount : Nat) (after : List Nat)
    (hAfter : after.length = afterCount) :
    List.ofFn (environment problem index remaining region afterCount after) =
      inputValues problem index remaining region after := by
  apply List.ext_getElem
  · simp only [List.length_ofFn]
    exact (inputValues_length problem index remaining region afterCount after hAfter).symm
  · intro i hLeft hRight
    rw [List.getElem_ofFn hLeft]
    simp only [environment, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hRight, Option.getD_some]

private theorem address_position_eq {polynomial : NatPolynomial} (address : Address polynomial) (input : Nat) :
    nodeCount polynomial - (address.newerCount + 1) = (address.older input).length := by
  have h := congrArg List.length (address.layout input)
  simp only [registerValues_length, List.length_append, List.length_cons, List.length_nil,
    address.newer_length] at h
  omega

private def addressPosition {polynomial : NatPolynomial} (address : Address polynomial) :
    Fin (nodeCount polynomial) :=
  ⟨nodeCount polynomial - (address.newerCount + 1), by
    have h := congrArg List.length (address.layout 0)
    simp only [registerValues_length, List.length_append, List.length_cons, List.length_nil,
      address.newer_length] at h
    omega⟩

inductive Reference (region : Region) (afterCount : Nat) where
  | source (field : SourceField)
  | constant (value : Nat)
  | quotient
  | digit (index : Fin (splitCount region))
  | retained (index : Fin afterCount)
  deriving Repr

private def sourcePosition {language : Language} (verifier : PolynomialTimeVerifier language)
    (region : Region) (afterCount : Nat) (field : SourceField) :
    Fin (inputCount verifier region afterCount) :=
  let position := addressPosition (sourceAddress verifier field)
  ⟨position.val, by
    have h := position.isLt
    simp only [inputCount, frameCount]
    omega⟩

private def quotientPosition {language : Language} (verifier : PolynomialTimeVerifier language)
    (region : Region) (afterCount : Nat) : Fin (inputCount verifier region afterCount) :=
  ⟨frameCount verifier region - 1, by simp only [inputCount, frameCount]; omega⟩

private def digitPosition {language : Language} (verifier : PolynomialTimeVerifier language)
    (region : Region) (afterCount : Nat) (index : Fin (splitCount region)) :
    Fin (inputCount verifier region afterCount) :=
  ⟨frameCount verifier region - 6 * splitCount region + 6 * index.val + 3, by
    have h := index.isLt
    simp only [inputCount, frameCount]
    omega⟩

private def retainedPosition {language : Language} (verifier : PolynomialTimeVerifier language)
    (region : Region) (afterCount : Nat) (index : Fin afterCount) :
    Fin (inputCount verifier region afterCount) :=
  ⟨frameCount verifier region + index.val, Nat.add_lt_add_left index.isLt _⟩

def field {language : Language} (verifier : PolynomialTimeVerifier language)
    (region : Region) (afterCount : Nat) :
    Reference region afterCount → BuilderRegisterPack.Field (inputCount verifier region afterCount)
  | .constant value => .constant value
  | .source .certificateWidth =>
      match verifier.program.inputMode with
      | .inputOnly => .constant 0
      | .paired => .argument (sourcePosition verifier region afterCount .certificateWidth)
  | .source sourceField => .argument (sourcePosition verifier region afterCount sourceField)
  | .quotient => .argument (quotientPosition verifier region afterCount)
  | .digit index => .argument (digitPosition verifier region afterCount index)
  | .retained index => .argument (retainedPosition verifier region afterCount index)

def referenceValue {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (region : Region) {afterCount : Nat} (after : List Nat) :
    Reference region afterCount → Nat
  | .constant value => value
  | .source sourceField => sourceValue problem sourceField
  | .quotient => BuilderRegionRadixDecoder.finalQuotient (BuilderRegionRadixSource.radices problem region)
      (BuilderConstraintRegionSource.localCoordinate problem index region)
  | .digit indexInPacket =>
      (BuilderRegionRadixDecoder.digits (BuilderRegionRadixSource.radices problem region)
        (BuilderConstraintRegionSource.localCoordinate problem index region)).getD indexInPacket.val 0
  | .retained indexInFrame => after.getD indexInFrame.val 0

private theorem getD_append_right (before after : List Nat) (index : Nat) :
    (before ++ after).getD (before.length + index) 0 = after.getD index 0 := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

private theorem getD_at_append (before after : List Nat) (value : Nat) :
    (before ++ [value] ++ after).getD before.length 0 = value := by
  rw [List.append_assoc]
  change (before ++ value :: after).getD (before.length + 0) 0 = value
  rw [getD_append_right]
  rfl

private theorem source_read {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) (afterCount : Nat) (after : List Nat) (sourceField : SourceField) :
    environment problem index remaining region afterCount after
        (sourcePosition problem.verifier region afterCount sourceField) =
      (sourcePolynomial problem.verifier sourceField).eval problem.input.length := by
  let address := sourceAddress problem.verifier sourceField
  simp only [environment, inputValues, sourcePosition, addressPosition]
  rw [frame_layout, (sourceAddress problem.verifier sourceField).layout]
  rw [address_position_eq (sourceAddress problem.verifier sourceField) problem.input.length]
  simpa only [address, List.append_assoc, sourceAddress_selected] using
    getD_at_append (address.older problem.input.length)
      (address.newer problem.input.length ++ frameSuffix problem index remaining region ++ after)
      (address.selected.eval problem.input.length)

private theorem extra_digit (radices : List Nat) (coordinate index : Nat) :
    (BuilderRegionRadixDecoder.extraValues radices coordinate).getD (6 * index + 3) 0 =
      (BuilderRegionRadixDecoder.digits radices coordinate).getD index 0 := by
  induction radices generalizing coordinate index with
  | nil => rfl
  | cons radix rest ih =>
      cases index with
      | zero => rfl
      | succ index =>
          simpa only [BuilderRegionRadixDecoder.extraValues, BuilderRegionCoordinateDivision.scratchValues,
            BuilderRegionRadixDecoder.digits, List.cons_append, List.nil_append, Nat.mul_succ,
            Nat.add_assoc, List.getD_cons_succ] using ih (coordinate / radix) index

private theorem final_has_quotient (older radices newer : List Nat) (coordinate : Nat) :
    ∃ leadingValues, BuilderRegionRadixDecoder.finalValues older radices newer coordinate =
      leadingValues ++ [BuilderRegionRadixDecoder.finalQuotient radices coordinate] := by
  induction radices generalizing newer coordinate with
  | nil => exact ⟨older ++ newer, rfl⟩
  | cons radix rest ih =>
      exact ih (BuilderRegionRadixDecoder.nextNewer newer coordinate radix) (coordinate / radix)

private theorem quotient_read {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) (afterCount : Nat) (after : List Nat) :
    environment problem index remaining region afterCount after
        (quotientPosition problem.verifier region afterCount) =
      BuilderRegionRadixDecoder.finalQuotient (BuilderRegionRadixSource.radices problem region)
        (BuilderConstraintRegionSource.localCoordinate problem index region) := by
  obtain ⟨leadingValues, hPrefix⟩ := final_has_quotient (BuilderRegionRadixSource.selectedValues problem index remaining region)
    (BuilderRegionRadixSource.radices problem region) []
    (BuilderConstraintRegionSource.localCoordinate problem index region)
  have hFrame : BuilderRegionRadixSource.finalValues problem index remaining region =
      leadingValues ++ [BuilderRegionRadixDecoder.finalQuotient (BuilderRegionRadixSource.radices problem region)
        (BuilderConstraintRegionSource.localCoordinate problem index region)] := hPrefix
  have hLength := frame_length problem index remaining region
  rw [hFrame] at hLength
  simp only [List.length_append, List.length_cons, List.length_nil] at hLength
  simp only [environment, inputValues, quotientPosition]
  rw [hFrame, show frameCount problem.verifier region - 1 = leadingValues.length by omega]
  exact getD_at_append leadingValues after _

private theorem digit_read {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) (afterCount : Nat) (after : List Nat)
    (digitIndex : Fin (splitCount region)) :
    environment problem index remaining region afterCount after
        (digitPosition problem.verifier region afterCount digitIndex) =
      (BuilderRegionRadixDecoder.digits (BuilderRegionRadixSource.radices problem region)
        (BuilderConstraintRegionSource.localCoordinate problem index region)).getD digitIndex.val 0 := by
  have hFrame := BuilderRegionRadixSource.finalValues_preserve_source problem index remaining region
  have hLength := frame_length problem index remaining region
  rw [hFrame] at hLength
  simp only [List.length_append, BuilderRegionRadixDecoder.extraValues_length,
    BuilderRegionRadixSource.radices_length] at hLength
  have hOffset : frameCount problem.verifier region - 6 * splitCount region + 6 * digitIndex.val + 3 =
      (BuilderRegionRadixSource.preparedValues problem index remaining region).length + (6 * digitIndex.val + 3) := by
    unfold splitCount
    omega
  have hDigit : 6 * digitIndex.val + 3 <
      (BuilderRegionRadixDecoder.extraValues (BuilderRegionRadixSource.radices problem region)
        (BuilderConstraintRegionSource.localCoordinate problem index region)).length := by
    have h := digitIndex.isLt
    simp only [BuilderRegionRadixDecoder.extraValues_length, BuilderRegionRadixSource.radices_length]
    unfold splitCount at h
    omega
  simp only [environment, inputValues, digitPosition]
  rw [hFrame, hOffset, List.append_assoc, getD_append_right]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left hDigit]
  exact extra_digit (BuilderRegionRadixSource.radices problem region)
    (BuilderConstraintRegionSource.localCoordinate problem index region) digitIndex.val

private theorem retained_read {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) (afterCount : Nat) (after : List Nat) (retainedIndex : Fin afterCount) :
    environment problem index remaining region afterCount after
        (retainedPosition problem.verifier region afterCount retainedIndex) = after.getD retainedIndex.val 0 := by
  simp only [environment, inputValues, retainedPosition]
  rw [← frame_length problem index remaining region]
  exact getD_append_right _ _ _

theorem field_eval {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) (afterCount : Nat) (after : List Nat)
    (reference : Reference region afterCount) :
    (field problem.verifier region afterCount reference).eval
        (environment problem index remaining region afterCount after) =
      referenceValue problem index region after reference := by
  cases reference with
  | constant value => rfl
  | quotient => exact quotient_read problem index remaining region afterCount after
  | digit digitIndex => exact digit_read problem index remaining region afterCount after digitIndex
  | retained retainedIndex => exact retained_read problem index remaining region afterCount after retainedIndex
  | source sourceField =>
      cases sourceField with
      | timeCount =>
          exact (source_read problem index remaining region afterCount after .timeCount).trans
            problem.formulaTimeCountPolynomial_eval
      | tapeWidth =>
          exact (source_read problem index remaining region afterCount after .tapeWidth).trans
            problem.formulaTapeWidthPolynomial_eval
      | stateCount =>
          exact (source_read problem index remaining region afterCount after .stateCount).trans
            problem.formulaStateCountPolynomial_eval
      | fuel =>
          exact (source_read problem index remaining region afterCount after .fuel).trans
            problem.formulaFuelPolynomial_eval
      | certificateWidth =>
          cases hMode : problem.verifier.program.inputMode with
          | inputOnly =>
              simp only [field, hMode, BuilderRegisterPack.Field.eval, BuilderRegisterPack.Field.expression,
                BuilderRegisterExpression.eval, referenceValue, sourceValue, VerifierTableauProblem.layout,
                VariableLayout.certificateBitWidth, VerifierTableauProblem.tableauInputMode, inputModeOfVerifier]
          | paired =>
              have hValue :
                  (sourcePolynomial problem.verifier .certificateWidth).eval problem.input.length =
                    sourceValue problem .certificateWidth := by
                simp only [sourcePolynomial, sourceValue, VerifierTableauProblem.layout,
                  VariableLayout.certificateBitWidth, VerifierTableauProblem.tableauInputMode, hMode,
                  inputModeOfVerifier]
                rfl
              simpa only [field, hMode, BuilderRegisterPack.Field.eval, BuilderRegisterPack.Field.expression,
                BuilderRegisterExpression.eval, referenceValue] using
                  (source_read problem index remaining region afterCount after .certificateWidth).trans hValue

/-- Four coordinate references; source dimensions cannot be supplied by the plan. -/
def Plan (region : Region) (afterCount : Nat) := Fin 4 → Reference region afterCount

def references {region : Region} {afterCount : Nat} (plan : Plan region afterCount) :
    Fin 8 → Reference region afterCount :=
  fun index => match index.val with
  | 0 => .source .timeCount
  | 1 => .source .tapeWidth
  | 2 => .source .stateCount
  | 3 => .source .certificateWidth
  | 4 => plan ⟨0, by decide⟩
  | 5 => plan ⟨1, by decide⟩
  | 6 => plan ⟨2, by decide⟩
  | 7 => plan ⟨3, by decide⟩
  | _ => .constant 0

def fields {language : Language} (verifier : PolynomialTimeVerifier language)
    (region : Region) (afterCount : Nat) (plan : Plan region afterCount) :
    List (BuilderRegisterPack.Field (inputCount verifier region afterCount)) :=
  List.ofFn (fun index => field verifier region afterCount (references plan index))

theorem fields_length {language : Language} (verifier : PolynomialTimeVerifier language)
    (region : Region) (afterCount : Nat) (plan : Plan region afterCount) :
    (fields verifier region afterCount plan).length = 8 := List.length_ofFn

def argumentEnvironment {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (region : Region) {afterCount : Nat} (after : List Nat) (plan : Plan region afterCount) :
    Fin 8 → Nat :=
  fun fieldIndex => referenceValue problem index region after (references plan fieldIndex)

theorem argument_dimensions {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (region : Region) {afterCount : Nat} (after : List Nat) (plan : Plan region afterCount) :
    (List.ofFn (argumentEnvironment problem index region after plan)).take 4 =
      [problem.dimensions.timeCount, problem.dimensions.tapeWidth problem.tableauInputMode,
        problem.dimensions.stateBound, problem.layout.certificateBitWidth] := rfl

theorem argument_values {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) (afterCount : Nat) (after : List Nat) (plan : Plan region afterCount) :
    BuilderRegisterPack.values (fields problem.verifier region afterCount plan)
        (environment problem index remaining region afterCount after) =
      List.ofFn (argumentEnvironment problem index region after plan) := by
  rw [fields, BuilderRegisterPack.values_ofFn]
  apply congrArg List.ofFn
  funext fieldIndex
  exact field_eval problem index remaining region afterCount after (references plan fieldIndex)

def packMachine {language : Language} (verifier : PolynomialTimeVerifier language)
    (region : Region) (afterCount : Nat) (plan : Plan region afterCount) : WorkMachine :=
  BuilderRegisterPack.machine (fields verifier region afterCount plan) 0

def packSteps {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) (afterCount : Nat) (after : List Nat) (plan : Plan region afterCount) : Nat :=
  BuilderRegisterPack.workSteps (fields problem.verifier region afterCount plan)
    (environment problem index remaining region afterCount after) []

theorem pack_workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) (afterCount : Nat) (after : List Nat) (plan : Plan region afterCount)
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
      } := by
  have h := BuilderRegisterPack.workRunExact (fields problem.verifier region afterCount plan) 0 []
    (environment problem index remaining region afterCount after) [] inside outside rfl
  simpa only [packMachine, packSteps, BuilderRegisterPack.initialConfiguration,
    BuilderRegisterPack.finalConfiguration, environment_values problem index remaining region afterCount after hAfter,
    argument_values, List.nil_append, List.append_nil] using h

def machine {language : Language} (verifier : PolynomialTimeVerifier language)
    (region : Region) (afterCount : Nat) (plan : Plan region afterCount) (kind : BuilderLiteralIndexExpression.Kind) : WorkMachine :=
  WorkMachineChain.machine (packMachine verifier region afterCount plan)
    (BuilderLiteralIndexExpression.machine kind 0)

def workSteps {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) (afterCount : Nat) (after : List Nat)
    (plan : Plan region afterCount) (kind : BuilderLiteralIndexExpression.Kind) : Nat :=
  packSteps problem index remaining region afterCount after plan + 1 +
    BuilderRegisterExpression.workSteps (BuilderLiteralIndexExpression.expression kind)
      (argumentEnvironment problem index region after plan) []

def writtenValues {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (region : Region) {afterCount : Nat} (after : List Nat)
    (plan : Plan region afterCount) (kind : BuilderLiteralIndexExpression.Kind) : List Nat :=
  List.ofFn (argumentEnvironment problem index region after plan) ++
    BuilderRegisterExpression.values (BuilderLiteralIndexExpression.expression kind)
      (argumentEnvironment problem index region after plan)

def finalValues {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) {afterCount : Nat} (after : List Nat)
    (plan : Plan region afterCount) (kind : BuilderLiteralIndexExpression.Kind) : List Nat :=
  inputValues problem index remaining region after ++ writtenValues problem index region after plan kind

def initialConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) (afterCount : Nat) (after : List Nat)
    (plan : Plan region afterCount) (kind : BuilderLiteralIndexExpression.Kind) (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration (machine problem.verifier region afterCount plan kind)
    (endTape (inputValues problem index remaining region after) inside outside)

def finalConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) (afterCount : Nat) (after : List Nat)
    (plan : Plan region afterCount) (kind : BuilderLiteralIndexExpression.Kind) (inside outside : List WorkSymbol) : WorkConfiguration :=
  { state := (machine problem.verifier region afterCount plan kind).acceptState
    tape := endTape (finalValues problem index remaining region after plan kind) inside
      (outside.drop (registerWord (writtenValues problem index region after plan kind)).length) }

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

theorem workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) (afterCount : Nat) (after : List Nat)
    (plan : Plan region afterCount) (kind : BuilderLiteralIndexExpression.Kind)
    (inside outside : List WorkSymbol) (hAfter : after.length = afterCount) :
    workRunExact? (machine problem.verifier region afterCount plan kind)
      (workSteps problem index remaining region afterCount after plan kind)
      (initialConfiguration problem index remaining region afterCount after plan kind inside outside) =
      some (finalConfiguration problem index remaining region afterCount after plan kind inside outside) := by
  have hPack := pack_workRunExact problem index remaining region afterCount after plan inside outside hAfter
  have hIndex := BuilderRegisterExpression.workRunExact (BuilderLiteralIndexExpression.expression kind) 0
    (inputValues problem index remaining region after) (argumentEnvironment problem index region after plan) [] inside
    (outside.drop (registerWord (List.ofFn (argumentEnvironment problem index region after plan))).length) rfl
  simp only [BuilderRegisterExpression.initialConfiguration, BuilderRegisterExpression.finalConfiguration,
    List.append_nil] at hIndex
  have h := chain_run (packMachine problem.verifier region afterCount plan)
    (BuilderLiteralIndexExpression.machine kind 0) _ _ _ _ _ hPack hIndex
  simpa only [machine, workSteps, initialConfiguration, finalConfiguration, finalValues, writtenValues,
    List.drop_drop, registerWord_append, List.length_append, List.append_assoc] using h

theorem run_compile_exact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) (afterCount : Nat) (after : List Nat)
    (plan : Plan region afterCount) (kind : BuilderLiteralIndexExpression.Kind)
    (inside outside : List WorkSymbol) (hAfter : after.length = afterCount) :
    run (compileWorkMachine (machine problem.verifier region afterCount plan kind))
      (6 * workSteps problem index remaining region afterCount after plan kind)
      (encodeWorkConfiguration (initialConfiguration problem index remaining region afterCount after plan kind inside outside)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining region afterCount after plan kind inside outside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _
    (workRunExact problem index remaining region afterCount after plan kind inside outside hAfter)

theorem final_index_register {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) {afterCount : Nat} (after : List Nat)
    (plan : Plan region afterCount) (kind : BuilderLiteralIndexExpression.Kind) :
    finalValues problem index remaining region after plan kind =
      (inputValues problem index remaining region after ++
        List.ofFn (argumentEnvironment problem index region after plan) ++
        BuilderRegisterExpression.prefixValues (BuilderLiteralIndexExpression.expression kind)
          (argumentEnvironment problem index region after plan)) ++
      [BuilderRegisterExpression.eval (BuilderLiteralIndexExpression.expression kind)
        (argumentEnvironment problem index region after plan)] := by
  simp only [finalValues, writtenValues, BuilderRegisterExpression.values_root, List.append_assoc]

def inputBound {language : Language} (verifier : PolynomialTimeVerifier language)
    (region : Region) (retainedBound : NatPolynomial) : NatPolynomial :=
  .add (BuilderRegionRadixDispatch.entrySpanPolynomial verifier region) retainedBound

theorem input_span_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) (after : List Nat) (retainedBound : NatPolynomial)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some region)
    (hRetained : (registerWord after).length ≤ retainedBound.eval problem.input.length) :
    (registerWord (inputValues problem index remaining region after)).length ≤
      (inputBound problem.verifier region retainedBound).eval problem.input.length := by
  have hSelected := BuilderRegionRadixSource.selected_span_le problem index remaining region hBody hBalance hRegion
  have hFrame := BuilderRegionRadixSource.final_span_le problem index remaining region _ hSelected
  have hFrameBound :
      (registerWord (BuilderRegionRadixSource.finalValues problem index remaining region)).length ≤
        (BuilderRegionRadixDispatch.entrySpanPolynomial problem.verifier region).eval problem.input.length := by
    simpa only [BuilderRegionRadixDispatch.entrySpanPolynomial_eval] using hFrame
  simp only [inputValues, registerWord_append, List.length_append,
    inputBound, NatPolynomial.eval_add]
  exact Nat.add_le_add hFrameBound hRetained

def packedSpanBound {language : Language} (verifier : PolynomialTimeVerifier language)
    (region : Region) (afterCount : Nat) (plan : Plan region afterCount) (retainedBound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterPack.spanPolynomial (fields verifier region afterCount plan) (inputBound verifier region retainedBound)

def finalSpanBound {language : Language} (verifier : PolynomialTimeVerifier language)
    (region : Region) (afterCount : Nat) (plan : Plan region afterCount)
    (kind : BuilderLiteralIndexExpression.Kind) (retainedBound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterExpression.spanPolynomial (BuilderLiteralIndexExpression.expression kind)
    (packedSpanBound verifier region afterCount plan retainedBound)

def rawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language)
    (region : Region) (afterCount : Nat) (plan : Plan region afterCount)
    (kind : BuilderLiteralIndexExpression.Kind) (retainedBound : NatPolynomial) : NatPolynomial :=
  .add (.add (BuilderRegisterPack.rawTimePolynomial (fields verifier region afterCount plan)
      (inputBound verifier region retainedBound)) (.constant 6))
    (BuilderRegisterExpression.rawTimePolynomial (BuilderLiteralIndexExpression.expression kind)
      (packedSpanBound verifier region afterCount plan retainedBound))

theorem source_polynomial_bounds {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) (afterCount : Nat) (after : List Nat)
    (plan : Plan region afterCount) (kind : BuilderLiteralIndexExpression.Kind) (retainedBound : NatPolynomial)
    (hAfter : after.length = afterCount)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some region)
    (hRetained : (registerWord after).length ≤ retainedBound.eval problem.input.length) :
    (registerWord (finalValues problem index remaining region after plan kind)).length ≤
        (finalSpanBound problem.verifier region afterCount plan kind retainedBound).eval problem.input.length ∧
      6 * workSteps problem index remaining region afterCount after plan kind ≤
        (rawTimeBound problem.verifier region afterCount plan kind retainedBound).eval problem.input.length := by
  have hInput := input_span_le problem index remaining region after retainedBound hBody hBalance hRegion hRetained
  have hEnvironment :
      (registerWord ([] ++ List.ofFn (environment problem index remaining region afterCount after) ++ [])).length ≤
        (inputBound problem.verifier region retainedBound).eval problem.input.length := by
    simpa only [List.nil_append, List.append_nil, environment_values problem index remaining region afterCount after hAfter]
      using hInput
  have hPack := BuilderRegisterPack.source_polynomial_bounds (fields problem.verifier region afterCount plan)
    (inputBound problem.verifier region retainedBound) problem.input.length []
    (environment problem index remaining region afterCount after) [] hEnvironment
  simp only [List.nil_append, List.append_nil,
    environment_values problem index remaining region afterCount after hAfter, argument_values] at hPack
  have hPacked :
      (registerWord (inputValues problem index remaining region after ++
        List.ofFn (argumentEnvironment problem index region after plan) ++ [])).length ≤
        (packedSpanBound problem.verifier region afterCount plan retainedBound).eval problem.input.length := by
    simpa only [List.append_nil, packedSpanBound] using hPack.1
  have hIndex := BuilderRegisterExpression.source_polynomial_bounds
    (BuilderLiteralIndexExpression.expression kind)
    (packedSpanBound problem.verifier region afterCount plan retainedBound) problem.input.length
    (inputValues problem index remaining region after) (argumentEnvironment problem index region after plan) [] hPacked
  constructor
  · simpa only [finalValues, writtenValues, finalSpanBound, List.append_nil, List.append_assoc] using hIndex.1
  · simp only [workSteps, packSteps, rawTimeBound, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

theorem rules_pairwise_query_distinct {language : Language} (verifier : PolynomialTimeVerifier language)
    (region : Region) (afterCount : Nat) (plan : Plan region afterCount) (kind : BuilderLiteralIndexExpression.Kind) :
    (machine verifier region afterCount plan kind).rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineChain.rules_pairwise_query_distinct _ _
    (BuilderRegisterPack.rules_pairwise_query_distinct (fields verifier region afterCount plan) 0)
    (BuilderLiteralIndexExpression.rules_pairwise_query_distinct kind 0)
    (BuilderRegisterPack.noRuleAtAccept (fields verifier region afterCount plan) 0)

theorem noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language)
    (region : Region) (afterCount : Nat) (plan : Plan region afterCount) (kind : BuilderLiteralIndexExpression.Kind) :
    WorkMachineChain.NoRuleAtAccept (machine verifier region afterCount plan kind) :=
  WorkMachineChain.noRuleAtAccept _ _ (BuilderLiteralIndexExpression.noRuleAtAccept kind 0)

theorem noRuleAtReject {language : Language} (verifier : PolynomialTimeVerifier language)
    (region : Region) (afterCount : Nat) (plan : Plan region afterCount) (kind : BuilderLiteralIndexExpression.Kind) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier region afterCount plan kind)
      (machine verifier region afterCount plan kind).rejectState :=
  WorkMachineChain.noRuleAtAccept (packMachine verifier region afterCount plan)
    { BuilderLiteralIndexExpression.machine kind 0 with acceptState :=
        (BuilderLiteralIndexExpression.machine kind 0).rejectState }
    (BuilderLiteralIndexExpression.noRuleAtReject kind 0)

theorem acceptState_ne_rejectState {language : Language} (verifier : PolynomialTimeVerifier language)
    (region : Region) (afterCount : Nat) (plan : Plan region afterCount) (kind : BuilderLiteralIndexExpression.Kind) :
    (machine verifier region afterCount plan kind).acceptState ≠ (machine verifier region afterCount plan kind).rejectState :=
  WorkMachineChain.machine_acceptState_ne_rejectState _ _ (BuilderLiteralIndexExpression.acceptState_ne_rejectState kind 0)

end PNP.Concrete.CookLevin.BuilderLiteralArgumentSource
