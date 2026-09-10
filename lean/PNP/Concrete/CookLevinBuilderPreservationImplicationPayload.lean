/-
Copyright (c) 2026 PNP Labs.

Physical preservation implication payloads from the source-derived radix frame.
The fixed program computes the conclusion, head and current-symbol indices,
then copies their retained roots into the existing exact payload format.
Input-dependent values never generate control or enter as supplied answers.

This is the implication branch for every preservation coordinate. Runtime
diagonal selection of padding, other families and the full builder remain
separate obligations; the candidate must not be emitted on a diagonal slot.
-/

import PNP.Concrete.CookLevinBuilderPreservationLiteralSources

namespace PNP.Concrete.CookLevin.BuilderPreservationImplicationPayload

open BuilderUnaryPolynomial (registerWord registerWord_append)
open BuilderDividerOperands (endTape)
open BuilderLiteralArgumentSource
  (Plan Reference writtenValues inputValues inputCount environment field referenceValue
    field_eval environment_values)
open BuilderPreservationLiteralSources
  (headPlan oldSymbolPlan newSymbolPlan nextTimeValues newSymbolMachine newSymbolSteps)
open BuilderPreservationCoordinates (ofSource headRequest oldSymbolRequest newSymbolRequest)

def literalCount (kind : BuilderLiteralIndexExpression.Kind) : Nat :=
  8 + BuilderRegisterExpression.nodeCount (BuilderLiteralIndexExpression.expression kind)

def newCount : Nat := 3 + literalCount .symbol
def headCount : Nat := newCount + literalCount .head
def allCount : Nat := headCount + literalCount .symbol

private theorem writtenValues_length {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) {afterCount : Nat} (after : List Nat) (plan : Plan .preservation afterCount)
    (kind : BuilderLiteralIndexExpression.Kind) :
    (writtenValues problem index .preservation after plan kind).length = literalCount kind := by
  simp only [writtenValues, List.length_append, List.length_ofFn, BuilderRegisterExpression.values_length, literalCount]

def newValues {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : List Nat :=
  nextTimeValues problem index ++
    writtenValues problem index .preservation (nextTimeValues problem index) (newSymbolPlan 0) .symbol

def headValues {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : List Nat :=
  newValues problem index ++
    writtenValues problem index .preservation (newValues problem index) (headPlan newCount) .head

def allValues {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : List Nat :=
  headValues problem index ++
    writtenValues problem index .preservation (headValues problem index) (oldSymbolPlan headCount) .symbol

theorem newValues_length {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    (newValues problem index).length = newCount := by
  simp only [newValues, List.length_append, BuilderPreservationLiteralSources.nextTimeValues_length,
    writtenValues_length, newCount]

theorem headValues_length {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    (headValues problem index).length = headCount := by
  simp only [headValues, List.length_append, newValues_length, writtenValues_length, headCount]

theorem allValues_length {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    (allValues problem index).length = allCount := by
  simp only [allValues, List.length_append, headValues_length, writtenValues_length, allCount]

private theorem appended_literal_end {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) {afterCount : Nat} (after : List Nat) (plan : Plan .preservation afterCount)
    (kind : BuilderLiteralIndexExpression.Kind) (value : Nat)
    (hIndex : BuilderRegisterExpression.eval (BuilderLiteralIndexExpression.expression kind)
      (BuilderLiteralArgumentSource.argumentEnvironment problem index .preservation after plan) = value) :
    ∃ leadingValues, after ++ writtenValues problem index .preservation after plan kind = leadingValues ++ [value] := by
  refine ⟨after ++ List.ofFn (BuilderLiteralArgumentSource.argumentEnvironment problem index .preservation after plan) ++
    BuilderRegisterExpression.prefixValues (BuilderLiteralIndexExpression.expression kind)
      (BuilderLiteralArgumentSource.argumentEnvironment problem index .preservation after plan), ?_⟩
  simp only [writtenValues, BuilderRegisterExpression.values_root, hIndex, List.append_assoc]

private theorem newValues_end {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    ∃ leadingValues, newValues problem index =
      leadingValues ++ [(newSymbolRequest (ofSource problem index hRegion)).index] := by
  have hIndex := BuilderPreservationLiteralSources.newSymbol_index_eq problem index 0 [] hRegion
  simp only [List.append_nil] at hIndex
  exact appended_literal_end problem index (nextTimeValues problem index) (newSymbolPlan 0) .symbol _ hIndex

private theorem headValues_end {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    ∃ leadingValues, headValues problem index =
      leadingValues ++ [(headRequest (ofSource problem index hRegion)).index] :=
  appended_literal_end problem index (newValues problem index) (headPlan newCount) .head _
    (BuilderPreservationLiteralSources.head_index_eq problem index newCount (newValues problem index) hRegion)

private theorem allValues_end {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    ∃ leadingValues, allValues problem index =
      leadingValues ++ [(oldSymbolRequest (ofSource problem index hRegion)).index] :=
  appended_literal_end problem index (headValues problem index) (oldSymbolPlan headCount) .symbol _
    (BuilderPreservationLiteralSources.oldSymbol_index_eq problem index headCount (headValues problem index) hRegion)

private theorem getD_last (values : List Nat) (count value : Nat) (hLength : values.length = count)
    (hEnd : ∃ leadingValues, values = leadingValues ++ [value]) : values.getD (count - 1) 0 = value := by
  rcases hEnd with ⟨leadingValues, rfl⟩
  have hIndex : count - 1 = leadingValues.length := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hLength
    omega
  rw [hIndex]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl leadingValues.length),
    Nat.sub_self]
  rfl

private theorem getD_append_left (first second : List Nat) (index : Nat) (hIndex : index < first.length) :
    (first ++ second).getD index 0 = first.getD index 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hIndex]

theorem retained_indices {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    (allValues problem index).getD (newCount - 1) 0 = (newSymbolRequest (ofSource problem index hRegion)).index ∧
    (allValues problem index).getD (headCount - 1) 0 = (headRequest (ofSource problem index hRegion)).index ∧
    (allValues problem index).getD (allCount - 1) 0 = (oldSymbolRequest (ofSource problem index hRegion)).index := by
  have hNew := getD_last (newValues problem index) newCount _ (newValues_length problem index)
    (newValues_end problem index hRegion)
  have hHead := getD_last (headValues problem index) headCount _ (headValues_length problem index)
    (headValues_end problem index hRegion)
  have hOld := getD_last (allValues problem index) allCount _ (allValues_length problem index)
    (allValues_end problem index hRegion)
  have hNewNew : newCount - 1 < (newValues problem index).length := by
    rw [newValues_length]
    simp only [newCount, literalCount]
    omega
  have hNewHead : newCount - 1 < (headValues problem index).length := by
    rw [headValues_length]
    simp only [headCount, newCount, literalCount]
    omega
  have hHeadHead : headCount - 1 < (headValues problem index).length := by
    rw [headValues_length]
    simp only [headCount, newCount, literalCount]
    omega
  refine ⟨?_, ?_, hOld⟩
  · rw [allValues, getD_append_left _ _ _ hNewHead, headValues, getD_append_left _ _ _ hNewNew]
    exact hNew
  · rw [allValues, getD_append_left _ _ _ hHeadHead]
    exact hHead

/-- Fixed copied-root order required by the reversed canonical payload. -/
def payloadReferences : List (Reference .preservation allCount) :=
  [.retained ⟨allCount - 1, by simp only [allCount, headCount, newCount, literalCount]; omega⟩,
   .constant 1,
   .retained ⟨headCount - 1, by simp only [allCount, headCount, newCount, literalCount]; omega⟩,
   .constant 1,
   .retained ⟨newCount - 1, by simp only [allCount, headCount, newCount, literalCount]; omega⟩,
   .constant 1, .constant 2, .constant 3]

def payloadFields {language : Language} (verifier : PolynomialTimeVerifier language) :
    List (BuilderRegisterPack.Field (inputCount verifier .preservation allCount)) :=
  payloadReferences.map (field verifier .preservation allCount)

def payloadValues {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : List Nat :=
  BuilderRegisterPack.values (payloadFields problem.verifier)
    (environment problem index remaining .preservation allCount (allValues problem index))

theorem payloadFields_length {language : Language} (verifier : PolynomialTimeVerifier language) :
    (payloadFields verifier).length = 8 := rfl

theorem payloadValues_length {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    (payloadValues problem index remaining).length = 8 :=
  (BuilderRegisterPack.values_length _ _).trans (payloadFields_length problem.verifier)

theorem payload_values_eq {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    payloadValues problem index remaining =
      BuilderLocalConstraintPayload.values (some (some (BuilderPreservationCoordinates.constraint
        (ofSource problem index hRegion)))) := by
  have hRoots := retained_indices problem index hRegion
  rw [BuilderPreservationCoordinates.candidate_payload]
  simp only [payloadValues, payloadFields, payloadReferences, BuilderRegisterPack.values,
    List.map_cons, List.map_nil, field_eval, referenceValue, hRoots.1, hRoots.2.1, hRoots.2.2]

theorem payload_decode {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    BuilderLocalConstraintPayload.decode problem.FormulaWidth (payloadValues problem index remaining) =
      some (some (some (BuilderPreservationCoordinates.constraint (ofSource problem index hRegion)))) := by
  rw [payload_values_eq problem index remaining hRegion, BuilderLocalConstraintPayload.decode_values]

theorem payload_decode_off_diagonal {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation)
    (hDifferent : (ofSource problem index hRegion).head ≠ (ofSource problem index hRegion).other) :
    BuilderLocalConstraintPayload.decode problem.FormulaWidth (payloadValues problem index remaining) =
      some (problem.preservationConstraintSlotDirect
        (BuilderConstraintRegionSource.localCoordinate problem index .preservation)) := by
  rw [payload_decode problem index remaining hRegion]
  have hSlot := BuilderPreservationCoordinates.source_slot problem index hRegion
  rw [BuilderPreservationCoordinates.slot_off_diagonal _ hDifferent] at hSlot
  exact congrArg some hSlot.symm

def headMachine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  BuilderLiteralArgumentSource.machine verifier .preservation newCount (headPlan newCount) .head

def oldMachine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  BuilderLiteralArgumentSource.machine verifier .preservation headCount (oldSymbolPlan headCount) .symbol

def headSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : Nat :=
  BuilderLiteralArgumentSource.workSteps problem index remaining .preservation newCount
    (newValues problem index) (headPlan newCount) .head

def oldSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : Nat :=
  BuilderLiteralArgumentSource.workSteps problem index remaining .preservation headCount
    (headValues problem index) (oldSymbolPlan headCount) .symbol

def prefixMachine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineChain.machine (newSymbolMachine verifier) (WorkMachineChain.machine (headMachine verifier) (oldMachine verifier))

def prefixSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : Nat :=
  newSymbolSteps problem index remaining + 1 + (headSteps problem index remaining + 1 + oldSteps problem index remaining)

def prefixInitial {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration (prefixMachine problem.verifier)
    (endTape (inputValues problem index remaining .preservation []) inside outside)

def prefixFinal {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside outside : List WorkSymbol) : WorkConfiguration :=
  { state := (prefixMachine problem.verifier).acceptState
    tape := endTape (inputValues problem index remaining .preservation (allValues problem index))
      inside (outside.drop (registerWord (allValues problem index)).length) }

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

private theorem new_run {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside outside : List WorkSymbol) :
    workRunExact? (newSymbolMachine problem.verifier) (newSymbolSteps problem index remaining)
      (workStartConfiguration (newSymbolMachine problem.verifier)
        (endTape (inputValues problem index remaining .preservation []) inside outside)) =
      some {
        state := (newSymbolMachine problem.verifier).acceptState
        tape := endTape (inputValues problem index remaining .preservation (newValues problem index))
          inside (outside.drop (registerWord (newValues problem index)).length) } := by
  have h := BuilderPreservationLiteralSources.newSymbol_workRunExact problem index remaining inside outside
  simpa only [BuilderPreservationLiteralSources.newSymbolInitial, BuilderPreservationLiteralSources.newSymbolFinal,
    BuilderLiteralArgumentSource.finalConfiguration, BuilderLiteralArgumentSource.finalValues,
    inputValues, newValues, List.append_nil, List.append_assoc,
    List.drop_drop, registerWord_append, List.length_append] using h

private theorem head_run {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside outside : List WorkSymbol) :
    workRunExact? (headMachine problem.verifier) (headSteps problem index remaining)
      (workStartConfiguration (headMachine problem.verifier)
        (endTape (inputValues problem index remaining .preservation (newValues problem index))
          inside (outside.drop (registerWord (newValues problem index)).length))) =
      some {
        state := (headMachine problem.verifier).acceptState
        tape := endTape (inputValues problem index remaining .preservation (headValues problem index))
          inside (outside.drop (registerWord (headValues problem index)).length) } := by
  have h := BuilderLiteralArgumentSource.workRunExact problem index remaining .preservation newCount (newValues problem index)
    (headPlan newCount) .head inside (outside.drop (registerWord (newValues problem index)).length)
    (newValues_length problem index)
  simpa only [headMachine, headSteps, BuilderLiteralArgumentSource.initialConfiguration,
    BuilderLiteralArgumentSource.finalConfiguration, BuilderLiteralArgumentSource.finalValues,
    inputValues, headValues, List.append_assoc, List.drop_drop, registerWord_append, List.length_append] using h

private theorem old_run {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside outside : List WorkSymbol) :
    workRunExact? (oldMachine problem.verifier) (oldSteps problem index remaining)
      (workStartConfiguration (oldMachine problem.verifier)
        (endTape (inputValues problem index remaining .preservation (headValues problem index))
          inside (outside.drop (registerWord (headValues problem index)).length))) =
      some {
        state := (oldMachine problem.verifier).acceptState
        tape := endTape (inputValues problem index remaining .preservation (allValues problem index))
          inside (outside.drop (registerWord (allValues problem index)).length) } := by
  have h := BuilderLiteralArgumentSource.workRunExact problem index remaining .preservation headCount (headValues problem index)
    (oldSymbolPlan headCount) .symbol inside (outside.drop (registerWord (headValues problem index)).length)
    (headValues_length problem index)
  simpa only [oldMachine, oldSteps, BuilderLiteralArgumentSource.initialConfiguration,
    BuilderLiteralArgumentSource.finalConfiguration, BuilderLiteralArgumentSource.finalValues,
    inputValues, allValues, List.append_assoc, List.drop_drop, registerWord_append, List.length_append] using h

theorem prefix_workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside outside : List WorkSymbol) :
    workRunExact? (prefixMachine problem.verifier) (prefixSteps problem index remaining)
      (prefixInitial problem index remaining inside outside) =
        some (prefixFinal problem index remaining inside outside) := by
  have hRest := chain_run (headMachine problem.verifier) (oldMachine problem.verifier)
    (headSteps problem index remaining) (oldSteps problem index remaining) _ _ _
    (head_run problem index remaining inside outside) (old_run problem index remaining inside outside)
  have hAll := chain_run (newSymbolMachine problem.verifier)
    (WorkMachineChain.machine (headMachine problem.verifier) (oldMachine problem.verifier))
    (newSymbolSteps problem index remaining) (headSteps problem index remaining + 1 + oldSteps problem index remaining)
    _ _ _ (new_run problem index remaining inside outside) hRest
  exact hAll

theorem prefix_run_compile_exact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine (prefixMachine problem.verifier)) (6 * prefixSteps problem index remaining)
      (encodeWorkConfiguration (prefixInitial problem index remaining inside outside)) =
        encodeWorkConfiguration (prefixFinal problem index remaining inside outside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (prefix_workRunExact problem index remaining inside outside)

def packMachine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  BuilderRegisterPack.machine (payloadFields verifier) 0

def packSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : Nat :=
  BuilderRegisterPack.workSteps (payloadFields problem.verifier)
    (environment problem index remaining .preservation allCount (allValues problem index)) []

def machine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineChain.machine (prefixMachine verifier) (packMachine verifier)

def workSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : Nat :=
  prefixSteps problem index remaining + 1 + packSteps problem index remaining

def finalValues {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : List Nat :=
  inputValues problem index remaining .preservation (allValues problem index) ++ payloadValues problem index remaining

def initialConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration (machine problem.verifier)
    (endTape (inputValues problem index remaining .preservation []) inside outside)

def finalConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside outside : List WorkSymbol) : WorkConfiguration :=
  { state := (machine problem.verifier).acceptState
    tape := endTape (finalValues problem index remaining) inside
      (outside.drop (registerWord (allValues problem index ++ payloadValues problem index remaining)).length) }

theorem workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside outside : List WorkSymbol) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
      (initialConfiguration problem index remaining inside outside) =
        some (finalConfiguration problem index remaining inside outside) := by
  have hPrefix := prefix_workRunExact problem index remaining inside outside
  simp only [prefixInitial, prefixFinal] at hPrefix
  have hPack := BuilderRegisterPack.workRunExact (payloadFields problem.verifier) 0 []
    (environment problem index remaining .preservation allCount (allValues problem index)) [] inside
    (outside.drop (registerWord (allValues problem index)).length) rfl
  simp only [BuilderRegisterPack.initialConfiguration, BuilderRegisterPack.finalConfiguration,
    environment_values problem index remaining .preservation allCount (allValues problem index) (allValues_length problem index),
    List.nil_append, List.append_nil, List.drop_drop] at hPack
  have hAll := chain_run (prefixMachine problem.verifier) (packMachine problem.verifier)
    (prefixSteps problem index remaining) (packSteps problem index remaining) _ _ _ hPrefix hPack
  simpa only [machine, workSteps, initialConfiguration, finalConfiguration, finalValues, payloadValues,
    registerWord_append, List.length_append] using hAll

theorem run_compile_exact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining)
      (encodeWorkConfiguration (initialConfiguration problem index remaining inside outside)) =
        encodeWorkConfiguration (finalConfiguration problem index remaining inside outside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact problem index remaining inside outside)

theorem final_canonical_payload {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    finalValues problem index remaining =
      inputValues problem index remaining .preservation (allValues problem index) ++
        BuilderLocalConstraintPayload.values (some (some (BuilderPreservationCoordinates.constraint
          (ofSource problem index hRegion)))) := by
  rw [finalValues, payload_values_eq problem index remaining hRegion]

def headSpanBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  BuilderLiteralArgumentSource.finalSpanBound verifier .preservation newCount (headPlan newCount) .head
    (BuilderPreservationLiteralSources.newSymbolSpanBound verifier)

def headRawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  BuilderLiteralArgumentSource.rawTimeBound verifier .preservation newCount (headPlan newCount) .head
    (BuilderPreservationLiteralSources.newSymbolSpanBound verifier)

def prefixSpanBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  BuilderLiteralArgumentSource.finalSpanBound verifier .preservation headCount (oldSymbolPlan headCount) .symbol
    (headSpanBound verifier)

def oldRawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  BuilderLiteralArgumentSource.rawTimeBound verifier .preservation headCount (oldSymbolPlan headCount) .symbol
    (headSpanBound verifier)

def prefixRawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (.add (BuilderPreservationLiteralSources.newSymbolRawTimeBound verifier) (.constant 6))
    (.add (.add (headRawTimeBound verifier) (.constant 6)) (oldRawTimeBound verifier))

private theorem retained_span_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (after : List Nat) (bound : Nat)
    (hWhole : (registerWord (inputValues problem index remaining .preservation after)).length ≤ bound) :
    (registerWord after).length ≤ bound := by
  simp only [inputValues, registerWord_append, List.length_append] at hWhole
  omega

theorem prefix_source_polynomial_bounds {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    (registerWord (inputValues problem index remaining .preservation (allValues problem index))).length ≤
      (prefixSpanBound problem.verifier).eval problem.input.length ∧
    6 * prefixSteps problem index remaining ≤ (prefixRawTimeBound problem.verifier).eval problem.input.length := by
  have hNew := BuilderPreservationLiteralSources.newSymbol_source_polynomial_bounds problem index remaining
    hBody hBalance hRegion
  have hNewWhole : (registerWord (inputValues problem index remaining .preservation (newValues problem index))).length ≤
      (BuilderPreservationLiteralSources.newSymbolSpanBound problem.verifier).eval problem.input.length := by
    simpa only [BuilderLiteralArgumentSource.finalValues, inputValues, newValues, List.append_assoc] using hNew.1
  have hNewRetained := retained_span_le problem index remaining (newValues problem index) _ hNewWhole
  have hHead := BuilderLiteralArgumentSource.source_polynomial_bounds problem index remaining .preservation newCount
    (newValues problem index) (headPlan newCount) .head (BuilderPreservationLiteralSources.newSymbolSpanBound problem.verifier)
    (newValues_length problem index) hBody hBalance hRegion hNewRetained
  have hHeadWhole : (registerWord (inputValues problem index remaining .preservation (headValues problem index))).length ≤
      (headSpanBound problem.verifier).eval problem.input.length := by
    simpa only [BuilderLiteralArgumentSource.finalValues, inputValues, headValues, headSpanBound, List.append_assoc] using hHead.1
  have hHeadRetained := retained_span_le problem index remaining (headValues problem index) _ hHeadWhole
  have hOld := BuilderLiteralArgumentSource.source_polynomial_bounds problem index remaining .preservation headCount
    (headValues problem index) (oldSymbolPlan headCount) .symbol (headSpanBound problem.verifier)
    (headValues_length problem index) hBody hBalance hRegion hHeadRetained
  constructor
  · simpa only [BuilderLiteralArgumentSource.finalValues, inputValues, allValues, prefixSpanBound, List.append_assoc] using hOld.1
  · simp only [prefixSteps, headSteps, oldSteps, prefixRawTimeBound, headRawTimeBound, oldRawTimeBound,
      NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

def spanBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  BuilderRegisterPack.spanPolynomial (payloadFields verifier) (prefixSpanBound verifier)

def rawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (.add (prefixRawTimeBound verifier) (.constant 6))
    (BuilderRegisterPack.rawTimePolynomial (payloadFields verifier) (prefixSpanBound verifier))

theorem source_polynomial_bounds {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    (registerWord (finalValues problem index remaining)).length ≤ (spanBound problem.verifier).eval problem.input.length ∧
    6 * workSteps problem index remaining ≤ (rawTimeBound problem.verifier).eval problem.input.length := by
  have hPrefix := prefix_source_polynomial_bounds problem index remaining hBody hBalance hRegion
  have hEnv :
      (registerWord ([] ++ List.ofFn (environment problem index remaining .preservation allCount (allValues problem index)) ++ [])).length ≤
        (prefixSpanBound problem.verifier).eval problem.input.length := by
    simpa only [List.nil_append, List.append_nil,
      environment_values problem index remaining .preservation allCount (allValues problem index) (allValues_length problem index)]
      using hPrefix.1
  have hPack := BuilderRegisterPack.source_polynomial_bounds (payloadFields problem.verifier)
    (prefixSpanBound problem.verifier) problem.input.length []
    (environment problem index remaining .preservation allCount (allValues problem index)) [] hEnv
  constructor
  · simpa only [List.nil_append, List.append_nil,
      environment_values problem index remaining .preservation allCount (allValues problem index) (allValues_length problem index),
      finalValues, payloadValues, spanBound] using hPack.1
  · simp only [workSteps, packSteps, rawTimeBound, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineChain.QueryDistinct ∧
    WorkMachineChain.NoRuleAtAccept program ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧
    program.acceptState ≠ program.rejectState

private theorem chain_noRuleAtReject (first second : WorkMachine)
    (hSecond : WorkMachineProgramGraph.NoRuleAt second second.rejectState) :
    WorkMachineProgramGraph.NoRuleAt (WorkMachineChain.machine first second)
      (WorkMachineChain.machine first second).rejectState :=
  WorkMachineChain.noRuleAtAccept first { second with acceptState := second.rejectState } hSecond

private theorem chain_good (first second : WorkMachine) (hFirst : Good first) (hSecond : Good second) :
    Good (WorkMachineChain.machine first second) :=
  ⟨WorkMachineChain.rules_pairwise_query_distinct first second hFirst.1 hSecond.1 hFirst.2.1,
    WorkMachineChain.noRuleAtAccept first second hSecond.2.1,
    chain_noRuleAtReject first second hSecond.2.2.1,
    WorkMachineChain.machine_acceptState_ne_rejectState first second hSecond.2.2.2⟩

private theorem literal_good {language : Language} (verifier : PolynomialTimeVerifier language)
    (afterCount : Nat) (plan : Plan .preservation afterCount) (kind : BuilderLiteralIndexExpression.Kind) :
    Good (BuilderLiteralArgumentSource.machine verifier .preservation afterCount plan kind) :=
  ⟨BuilderLiteralArgumentSource.rules_pairwise_query_distinct verifier .preservation afterCount plan kind,
    BuilderLiteralArgumentSource.noRuleAtAccept verifier .preservation afterCount plan kind,
    BuilderLiteralArgumentSource.noRuleAtReject verifier .preservation afterCount plan kind,
    BuilderLiteralArgumentSource.acceptState_ne_rejectState verifier .preservation afterCount plan kind⟩

private theorem new_good {language : Language} (verifier : PolynomialTimeVerifier language) :
    Good (newSymbolMachine verifier) :=
  ⟨BuilderPreservationLiteralSources.newSymbol_rules_pairwise_query_distinct verifier,
    BuilderPreservationLiteralSources.newSymbol_noRuleAtAccept verifier,
    BuilderPreservationLiteralSources.newSymbol_noRuleAtReject verifier,
    BuilderPreservationLiteralSources.newSymbol_acceptState_ne_rejectState verifier⟩

private theorem prefix_good {language : Language} (verifier : PolynomialTimeVerifier language) : Good (prefixMachine verifier) :=
  chain_good (newSymbolMachine verifier) (WorkMachineChain.machine (headMachine verifier) (oldMachine verifier))
    (new_good verifier) (chain_good (headMachine verifier) (oldMachine verifier)
      (literal_good verifier newCount (headPlan newCount) .head)
      (literal_good verifier headCount (oldSymbolPlan headCount) .symbol))

private theorem good {language : Language} (verifier : PolynomialTimeVerifier language) : Good (machine verifier) :=
  chain_good (prefixMachine verifier) (packMachine verifier) (prefix_good verifier)
    ⟨BuilderRegisterPack.rules_pairwise_query_distinct (payloadFields verifier) 0,
      BuilderRegisterPack.noRuleAtAccept (payloadFields verifier) 0,
      BuilderRegisterPack.noRuleAtReject (payloadFields verifier) 0,
      BuilderRegisterPack.acceptState_ne_rejectState (payloadFields verifier) 0⟩

theorem prefix_rules_pairwise_query_distinct {language : Language} (verifier : PolynomialTimeVerifier language) :
    (prefixMachine verifier).rules.Pairwise WorkMachineChain.QueryDistinct := (prefix_good verifier).1

theorem prefix_noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (prefixMachine verifier) := (prefix_good verifier).2.1

theorem prefix_noRuleAtReject {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineProgramGraph.NoRuleAt (prefixMachine verifier) (prefixMachine verifier).rejectState := (prefix_good verifier).2.2.1

theorem prefix_acceptState_ne_rejectState {language : Language} (verifier : PolynomialTimeVerifier language) :
    (prefixMachine verifier).acceptState ≠ (prefixMachine verifier).rejectState := (prefix_good verifier).2.2.2

theorem rules_pairwise_query_distinct {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct := (good verifier).1

theorem noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (machine verifier) := (good verifier).2.1

theorem noRuleAtReject {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier) (machine verifier).rejectState := (good verifier).2.2.1

theorem acceptState_ne_rejectState {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState := (good verifier).2.2.2

end PNP.Concrete.CookLevin.BuilderPreservationImplicationPayload
