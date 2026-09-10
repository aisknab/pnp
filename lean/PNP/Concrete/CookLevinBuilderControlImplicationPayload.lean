/-
Copyright (c) 2026 PNP Labs.

Physical control-implication candidates for all three static conclusion branches.
Each branch computes its conclusion and all three premise indices from the
source frame, then copies the four roots into the canonical ten-register
payload. The runtime conclusion dispatcher is a separate required boundary.
-/

import PNP.Concrete.CookLevinBuilderControlLiteralSources

namespace PNP.Concrete.CookLevin.BuilderControlImplicationPayload

open BuilderUnaryPolynomial (registerWord registerWord_append)
open BuilderDividerOperands (endTape)
open BuilderLiteralArgumentSource
  (Plan Reference writtenValues inputValues inputCount environment field referenceValue
    field_eval environment_values)
open BuilderControlLiteralSources (Role preparedValues plan literalCount)
open BuilderControlCoordinates (Coordinates ofSource)

inductive Conclusion where
  | state | head | symbol
  deriving DecidableEq, Repr

def conclusionCode : Conclusion → Fin 3
  | .state => ⟨0, by decide⟩
  | .head => ⟨1, by decide⟩
  | .symbol => ⟨2, by decide⟩
def conclusionRole : Conclusion → Role
  | .state => .nextState
  | .head => .nextHead
  | .symbol => .nextWrite

def targetCoordinates {language : Language} {problem : VerifierTableauProblem language}
    (conclusion : Conclusion) (coordinates : Coordinates problem) : Coordinates problem :=
  {coordinates with conclusion := conclusionCode conclusion}

theorem conclusion_request {language : Language} {problem : VerifierTableauProblem language}
    (conclusion : Conclusion) (coordinates : Coordinates problem) :
    BuilderControlLiteralSources.request (conclusionRole conclusion) coordinates =
      BuilderControlCoordinates.conclusionRequest (targetCoordinates conclusion coordinates) := by
  cases conclusion <;> rfl

def newExtra (conclusion : Conclusion) : Nat := literalCount (conclusionRole conclusion)
def stateExtra (conclusion : Conclusion) : Nat := newExtra conclusion + literalCount .currentState
def headExtra (conclusion : Conclusion) : Nat := stateExtra conclusion + literalCount .currentHead
def allExtra (conclusion : Conclusion) : Nat := headExtra conclusion + literalCount .currentRead
def newCount (conclusion : Conclusion) : Nat := 15 + newExtra conclusion
def stateCount (conclusion : Conclusion) : Nat := 15 + stateExtra conclusion
def headCount (conclusion : Conclusion) : Nat := 15 + headExtra conclusion
def allCount (conclusion : Conclusion) : Nat := 15 + allExtra conclusion

def newScratch {language : Language} (problem : VerifierTableauProblem language) (index : Nat) (conclusion : Conclusion)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : List Nat :=
  BuilderControlLiteralSources.literalWrittenValues problem index (conclusionRole conclusion) hRegion
def newValues {language : Language} (problem : VerifierTableauProblem language) (index : Nat) (conclusion : Conclusion)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : List Nat :=
  preparedValues problem index hRegion ++ newScratch problem index conclusion hRegion
def stateScratch {language : Language} (problem : VerifierTableauProblem language) (index : Nat) (conclusion : Conclusion)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : List Nat :=
  newScratch problem index conclusion hRegion ++
    writtenValues problem index .control (newValues problem index conclusion hRegion)
      (plan .currentState (newExtra conclusion)) .state
def stateValues {language : Language} (problem : VerifierTableauProblem language) (index : Nat) (conclusion : Conclusion)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : List Nat :=
  preparedValues problem index hRegion ++ stateScratch problem index conclusion hRegion
def headScratch {language : Language} (problem : VerifierTableauProblem language) (index : Nat) (conclusion : Conclusion)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : List Nat :=
  stateScratch problem index conclusion hRegion ++
    writtenValues problem index .control (stateValues problem index conclusion hRegion)
      (plan .currentHead (stateExtra conclusion)) .head
def headValues {language : Language} (problem : VerifierTableauProblem language) (index : Nat) (conclusion : Conclusion)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : List Nat :=
  preparedValues problem index hRegion ++ headScratch problem index conclusion hRegion
def allScratch {language : Language} (problem : VerifierTableauProblem language) (index : Nat) (conclusion : Conclusion)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : List Nat :=
  headScratch problem index conclusion hRegion ++
    writtenValues problem index .control (headValues problem index conclusion hRegion)
      (plan .currentRead (headExtra conclusion)) .symbol
def allValues {language : Language} (problem : VerifierTableauProblem language) (index : Nat) (conclusion : Conclusion)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : List Nat :=
  preparedValues problem index hRegion ++ allScratch problem index conclusion hRegion

private theorem written_length {language : Language} (problem : VerifierTableauProblem language)
    (index afterCount : Nat) (after : List Nat) (literalPlan : Plan .control afterCount)
    (literalKind : BuilderLiteralIndexExpression.Kind) :
    (writtenValues problem index .control after literalPlan literalKind).length =
      8 + BuilderRegisterExpression.nodeCount (BuilderLiteralIndexExpression.expression literalKind) := by
  simp only [writtenValues, List.length_append, List.length_ofFn, BuilderRegisterExpression.values_length]

theorem newValues_length {language : Language} (problem : VerifierTableauProblem language) (index : Nat) (conclusion : Conclusion)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    (newValues problem index conclusion hRegion).length = newCount conclusion := by
  simp only [newValues, newScratch, List.length_append, BuilderControlLiteralSources.preparedValues_length,
    BuilderControlLiteralSources.literalWrittenValues_length, newCount, newExtra]
theorem stateValues_length {language : Language} (problem : VerifierTableauProblem language) (index : Nat) (conclusion : Conclusion)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    (stateValues problem index conclusion hRegion).length = stateCount conclusion := by
  simp only [stateValues, stateScratch, newScratch, List.length_append,
    BuilderControlLiteralSources.preparedValues_length, BuilderControlLiteralSources.literalWrittenValues_length,
    written_length, literalCount, BuilderControlLiteralSources.kind, stateCount, stateExtra, newExtra]
theorem headValues_length {language : Language} (problem : VerifierTableauProblem language) (index : Nat) (conclusion : Conclusion)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    (headValues problem index conclusion hRegion).length = headCount conclusion := by
  simp only [headValues, headScratch, stateScratch, newScratch, List.length_append,
    BuilderControlLiteralSources.preparedValues_length, BuilderControlLiteralSources.literalWrittenValues_length,
    written_length, literalCount, BuilderControlLiteralSources.kind, headCount, headExtra, stateExtra, newExtra]
theorem allValues_length {language : Language} (problem : VerifierTableauProblem language) (index : Nat) (conclusion : Conclusion)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    (allValues problem index conclusion hRegion).length = allCount conclusion := by
  simp only [allValues, allScratch, headScratch, stateScratch, newScratch, List.length_append,
    BuilderControlLiteralSources.preparedValues_length, BuilderControlLiteralSources.literalWrittenValues_length,
    written_length, literalCount, BuilderControlLiteralSources.kind, allCount, allExtra, headExtra, stateExtra, newExtra]

private theorem appended_literal_end {language : Language} (problem : VerifierTableauProblem language)
    (index extraCount : Nat) (extra : List Nat) (role : Role)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    ∃ leadingValues, preparedValues problem index hRegion ++ extra ++
      writtenValues problem index .control (preparedValues problem index hRegion ++ extra)
        (plan role extraCount) (BuilderControlLiteralSources.kind role) =
      leadingValues ++ [(BuilderControlLiteralSources.request role (ofSource problem index hRegion)).index] := by
  refine ⟨preparedValues problem index hRegion ++ extra ++
    List.ofFn (BuilderLiteralArgumentSource.argumentEnvironment problem index .control
      (preparedValues problem index hRegion ++ extra) (plan role extraCount)) ++
    BuilderRegisterExpression.prefixValues (BuilderLiteralIndexExpression.expression (BuilderControlLiteralSources.kind role))
      (BuilderLiteralArgumentSource.argumentEnvironment problem index .control
        (preparedValues problem index hRegion ++ extra) (plan role extraCount)), ?_⟩
  simp only [writtenValues, BuilderRegisterExpression.values_root,
    BuilderControlLiteralSources.index_eq problem index extraCount extra role hRegion, List.append_assoc]

private theorem getD_last (values : List Nat) (count value : Nat) (hLength : values.length = count)
    (hEnd : ∃ leadingValues, values = leadingValues ++ [value]) : values.getD (count - 1) 0 = value := by
  rcases hEnd with ⟨leadingValues, rfl⟩
  have hIndex : count - 1 = leadingValues.length := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hLength
    omega
  rw [hIndex]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl leadingValues.length), Nat.sub_self]
  rfl

private theorem getD_append_left (first second : List Nat) (index : Nat) (hIndex : index < first.length) :
    (first ++ second).getD index 0 = first.getD index 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hIndex]

theorem retained_indices {language : Language} (problem : VerifierTableauProblem language) (index : Nat) (conclusion : Conclusion)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    (allValues problem index conclusion hRegion).getD (newCount conclusion - 1) 0 =
        (BuilderControlLiteralSources.request (conclusionRole conclusion) (ofSource problem index hRegion)).index ∧
      (allValues problem index conclusion hRegion).getD (stateCount conclusion - 1) 0 =
        (BuilderControlCoordinates.stateRequest (ofSource problem index hRegion)).index ∧
      (allValues problem index conclusion hRegion).getD (headCount conclusion - 1) 0 =
        (BuilderControlCoordinates.headRequest (ofSource problem index hRegion)).index ∧
      (allValues problem index conclusion hRegion).getD (allCount conclusion - 1) 0 =
        (BuilderControlCoordinates.readRequest (ofSource problem index hRegion)).index := by
  have hNewEnd : ∃ leadingValues, newValues problem index conclusion hRegion = leadingValues ++
      [(BuilderControlLiteralSources.request (conclusionRole conclusion) (ofSource problem index hRegion)).index] := by
    rcases BuilderControlLiteralSources.literalWrittenValues_end problem index (conclusionRole conclusion) hRegion with ⟨leading, h⟩
    refine ⟨preparedValues problem index hRegion ++ leading, ?_⟩
    simp only [newValues, newScratch, h, List.append_assoc]
  have hStateEnd := appended_literal_end problem index (newExtra conclusion)
    (newScratch problem index conclusion hRegion) .currentState hRegion
  have hHeadEnd := appended_literal_end problem index (stateExtra conclusion)
    (stateScratch problem index conclusion hRegion) .currentHead hRegion
  have hReadEnd := appended_literal_end problem index (headExtra conclusion)
    (headScratch problem index conclusion hRegion) .currentRead hRegion
  have hNew := getD_last _ _ _ (newValues_length problem index conclusion hRegion) hNewEnd
  have hState := getD_last _ _ _ (stateValues_length problem index conclusion hRegion)
    (by simpa only [stateValues, stateScratch, newValues, BuilderControlLiteralSources.kind, newCount, List.append_assoc] using hStateEnd)
  have hHead := getD_last _ _ _ (headValues_length problem index conclusion hRegion)
    (by simpa only [headValues, headScratch, stateValues, BuilderControlLiteralSources.kind, stateCount, List.append_assoc] using hHeadEnd)
  have hRead := getD_last _ _ _ (allValues_length problem index conclusion hRegion)
    (by simpa only [allValues, allScratch, headValues, BuilderControlLiteralSources.kind, headCount, List.append_assoc] using hReadEnd)
  have hBounds : newCount conclusion - 1 < (newValues problem index conclusion hRegion).length ∧
      newCount conclusion - 1 < (stateValues problem index conclusion hRegion).length ∧
      newCount conclusion - 1 < (headValues problem index conclusion hRegion).length ∧
      stateCount conclusion - 1 < (stateValues problem index conclusion hRegion).length ∧
      stateCount conclusion - 1 < (headValues problem index conclusion hRegion).length ∧
      headCount conclusion - 1 < (headValues problem index conclusion hRegion).length := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals
      simp only [newValues_length, stateValues_length, headValues_length, newCount, stateCount, headCount,
        headExtra, stateExtra, newExtra]
      omega
  have hStateLayout : stateValues problem index conclusion hRegion =
      newValues problem index conclusion hRegion ++ writtenValues problem index .control
        (newValues problem index conclusion hRegion) (plan .currentState (newExtra conclusion)) .state := by
    simp only [stateValues, stateScratch, newValues, List.append_assoc]
  have hHeadLayout : headValues problem index conclusion hRegion =
      stateValues problem index conclusion hRegion ++ writtenValues problem index .control
        (stateValues problem index conclusion hRegion) (plan .currentHead (stateExtra conclusion)) .head := by
    simp only [headValues, headScratch, stateValues, List.append_assoc]
  have hAllLayout : allValues problem index conclusion hRegion =
      headValues problem index conclusion hRegion ++ writtenValues problem index .control
        (headValues problem index conclusion hRegion) (plan .currentRead (headExtra conclusion)) .symbol := by
    simp only [allValues, allScratch, headValues, List.append_assoc]
  refine ⟨?_, ?_, ?_, hRead⟩
  · rw [hAllLayout, getD_append_left _ _ _ hBounds.2.2.1,
      hHeadLayout, getD_append_left _ _ _ hBounds.2.1,
      hStateLayout, getD_append_left _ _ _ hBounds.1]
    exact hNew
  · rw [hAllLayout, getD_append_left _ _ _ hBounds.2.2.2.2.1,
      hHeadLayout, getD_append_left _ _ _ hBounds.2.2.2.1]
    exact hState
  · rw [hAllLayout, getD_append_left _ _ _ hBounds.2.2.2.2.2]
    exact hHead

def payloadReferences (conclusion : Conclusion) : List (Reference .control (allCount conclusion)) :=
  [.retained ⟨allCount conclusion - 1, by simp only [allCount]; omega⟩, .constant 1,
   .retained ⟨headCount conclusion - 1, by simp only [allCount, headCount, allExtra]; omega⟩, .constant 1,
   .retained ⟨stateCount conclusion - 1, by simp only [allCount, stateCount, allExtra, headExtra]; omega⟩, .constant 1,
   .retained ⟨newCount conclusion - 1, by simp only [allCount, newCount, allExtra, headExtra, stateExtra]; omega⟩,
   .constant 1, .constant 3, .constant 3]

def payloadFields {language : Language} (verifier : PolynomialTimeVerifier language) (conclusion : Conclusion) :
    List (BuilderRegisterPack.Field (inputCount verifier .control (allCount conclusion))) :=
  (payloadReferences conclusion).map (field verifier .control (allCount conclusion))
def payloadValues {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (conclusion : Conclusion)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : List Nat :=
  BuilderRegisterPack.values (payloadFields problem.verifier conclusion)
    (environment problem index remaining .control (allCount conclusion) (allValues problem index conclusion hRegion))

theorem payloadValues_length {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (conclusion : Conclusion)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    (payloadValues problem index remaining conclusion hRegion).length = 10 := by
  rw [payloadValues, BuilderRegisterPack.values_length]
  rfl

theorem payload_values_eq {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (conclusion : Conclusion)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    payloadValues problem index remaining conclusion hRegion =
      BuilderLocalConstraintPayload.values
        (BuilderControlCoordinates.slot (targetCoordinates conclusion (ofSource problem index hRegion))) := by
  have hRoots := retained_indices problem index conclusion hRegion
  rw [BuilderControlCoordinates.candidate_payload]
  simp only [payloadValues, payloadFields, payloadReferences, BuilderRegisterPack.values,
    List.map_cons, List.map_nil, field_eval, referenceValue,
    hRoots.1, hRoots.2.1, hRoots.2.2.1, hRoots.2.2.2] <;> cases conclusion <;> rfl

theorem payload_decode {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (conclusion : Conclusion)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    BuilderLocalConstraintPayload.decode problem.FormulaWidth (payloadValues problem index remaining conclusion hRegion) =
      some (BuilderControlCoordinates.slot (targetCoordinates conclusion (ofSource problem index hRegion))) := by
  rw [payload_values_eq problem index remaining conclusion hRegion, BuilderLocalConstraintPayload.decode_values]

theorem payload_source_slot {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (conclusion : Conclusion)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control)
    (hSelected : conclusionCode conclusion = (ofSource problem index hRegion).conclusion) :
    BuilderLocalConstraintPayload.decode problem.FormulaWidth (payloadValues problem index remaining conclusion hRegion) =
      some (problem.controlConstraintSlotDirect (BuilderConstraintRegionSource.localCoordinate problem index .control)) := by
  have hTarget : targetCoordinates conclusion (ofSource problem index hRegion) = ofSource problem index hRegion := by
    unfold targetCoordinates
    rw [hSelected]
  rw [payload_decode problem index remaining conclusion hRegion, hTarget]
  exact congrArg some (BuilderControlCoordinates.source_slot problem index hRegion).symm

def stateMachine {language : Language} (verifier : PolynomialTimeVerifier language) (conclusion : Conclusion) : WorkMachine :=
  BuilderLiteralArgumentSource.machine verifier .control (newCount conclusion) (plan .currentState (newExtra conclusion)) .state
def headMachine {language : Language} (verifier : PolynomialTimeVerifier language) (conclusion : Conclusion) : WorkMachine :=
  BuilderLiteralArgumentSource.machine verifier .control (stateCount conclusion) (plan .currentHead (stateExtra conclusion)) .head
def readMachine {language : Language} (verifier : PolynomialTimeVerifier language) (conclusion : Conclusion) : WorkMachine :=
  BuilderLiteralArgumentSource.machine verifier .control (headCount conclusion) (plan .currentRead (headExtra conclusion)) .symbol

def stateSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (conclusion : Conclusion) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : Nat :=
  BuilderLiteralArgumentSource.workSteps problem index remaining .control (newCount conclusion)
    (newValues problem index conclusion hRegion) (plan .currentState (newExtra conclusion)) .state
def headSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (conclusion : Conclusion) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : Nat :=
  BuilderLiteralArgumentSource.workSteps problem index remaining .control (stateCount conclusion)
    (stateValues problem index conclusion hRegion) (plan .currentHead (stateExtra conclusion)) .head
def readSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (conclusion : Conclusion) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : Nat :=
  BuilderLiteralArgumentSource.workSteps problem index remaining .control (headCount conclusion)
    (headValues problem index conclusion hRegion) (plan .currentRead (headExtra conclusion)) .symbol

def prefixMachine {language : Language} (verifier : PolynomialTimeVerifier language) (conclusion : Conclusion) : WorkMachine :=
  WorkMachineChain.machine (BuilderControlLiteralSources.firstLiteralMachine verifier (conclusionRole conclusion))
    (WorkMachineChain.machine (stateMachine verifier conclusion)
      (WorkMachineChain.machine (headMachine verifier conclusion) (readMachine verifier conclusion)))
def prefixSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (conclusion : Conclusion) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : Nat :=
  BuilderControlLiteralSources.firstLiteralSteps problem index remaining (conclusionRole conclusion) hRegion + 1 +
    (stateSteps problem index remaining conclusion hRegion + 1 +
      (headSteps problem index remaining conclusion hRegion + 1 + readSteps problem index remaining conclusion hRegion))

def prefixInitial {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (conclusion : Conclusion) (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration (prefixMachine problem.verifier conclusion)
    (endTape (BuilderControlActionSource.frame problem index remaining) inside outside)
def prefixFinal {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (conclusion : Conclusion) (inside outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : WorkConfiguration :=
  {
    state := (prefixMachine problem.verifier conclusion).acceptState
    tape := endTape (inputValues problem index remaining .control (allValues problem index conclusion hRegion)) inside
      ((BuilderControlLiteralSources.finalOutside problem index outside hRegion).drop
        (registerWord (allScratch problem index conclusion hRegion)).length) }

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

private theorem state_run {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (conclusion : Conclusion) (inside outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    workRunExact? (stateMachine problem.verifier conclusion) (stateSteps problem index remaining conclusion hRegion)
      (workStartConfiguration (stateMachine problem.verifier conclusion)
        (endTape (inputValues problem index remaining .control (newValues problem index conclusion hRegion)) inside
          ((BuilderControlLiteralSources.finalOutside problem index outside hRegion).drop
            (registerWord (newScratch problem index conclusion hRegion)).length))) =
      some {
        state := (stateMachine problem.verifier conclusion).acceptState
        tape := endTape (inputValues problem index remaining .control (stateValues problem index conclusion hRegion)) inside
          ((BuilderControlLiteralSources.finalOutside problem index outside hRegion).drop
            (registerWord (stateScratch problem index conclusion hRegion)).length) } := by
  have h := BuilderLiteralArgumentSource.workRunExact problem index remaining .control (newCount conclusion)
    (newValues problem index conclusion hRegion) (plan .currentState (newExtra conclusion)) .state inside
    ((BuilderControlLiteralSources.finalOutside problem index outside hRegion).drop
      (registerWord (newScratch problem index conclusion hRegion)).length)
    (newValues_length problem index conclusion hRegion)
  simpa only [stateMachine, stateSteps, BuilderLiteralArgumentSource.initialConfiguration,
    BuilderLiteralArgumentSource.finalConfiguration, BuilderLiteralArgumentSource.finalValues,
    inputValues, stateValues, stateScratch, newValues,
    List.append_assoc, List.drop_drop, registerWord_append, List.length_append, newCount] using h

private theorem head_run {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (conclusion : Conclusion) (inside outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    workRunExact? (headMachine problem.verifier conclusion) (headSteps problem index remaining conclusion hRegion)
      (workStartConfiguration (headMachine problem.verifier conclusion)
        (endTape (inputValues problem index remaining .control (stateValues problem index conclusion hRegion)) inside
          ((BuilderControlLiteralSources.finalOutside problem index outside hRegion).drop
            (registerWord (stateScratch problem index conclusion hRegion)).length))) =
      some {
        state := (headMachine problem.verifier conclusion).acceptState
        tape := endTape (inputValues problem index remaining .control (headValues problem index conclusion hRegion)) inside
          ((BuilderControlLiteralSources.finalOutside problem index outside hRegion).drop
            (registerWord (headScratch problem index conclusion hRegion)).length) } := by
  have h := BuilderLiteralArgumentSource.workRunExact problem index remaining .control (stateCount conclusion)
    (stateValues problem index conclusion hRegion) (plan .currentHead (stateExtra conclusion)) .head inside
    ((BuilderControlLiteralSources.finalOutside problem index outside hRegion).drop
      (registerWord (stateScratch problem index conclusion hRegion)).length)
    (stateValues_length problem index conclusion hRegion)
  simpa only [headMachine, headSteps, BuilderLiteralArgumentSource.initialConfiguration,
    BuilderLiteralArgumentSource.finalConfiguration, BuilderLiteralArgumentSource.finalValues,
    inputValues, headValues, headScratch, stateValues,
    List.append_assoc, List.drop_drop, registerWord_append, List.length_append, stateCount] using h

private theorem read_run {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (conclusion : Conclusion) (inside outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    workRunExact? (readMachine problem.verifier conclusion) (readSteps problem index remaining conclusion hRegion)
      (workStartConfiguration (readMachine problem.verifier conclusion)
        (endTape (inputValues problem index remaining .control (headValues problem index conclusion hRegion)) inside
          ((BuilderControlLiteralSources.finalOutside problem index outside hRegion).drop
            (registerWord (headScratch problem index conclusion hRegion)).length))) =
      some {
        state := (readMachine problem.verifier conclusion).acceptState
        tape := endTape (inputValues problem index remaining .control (allValues problem index conclusion hRegion)) inside
          ((BuilderControlLiteralSources.finalOutside problem index outside hRegion).drop
            (registerWord (allScratch problem index conclusion hRegion)).length) } := by
  have h := BuilderLiteralArgumentSource.workRunExact problem index remaining .control (headCount conclusion)
    (headValues problem index conclusion hRegion) (plan .currentRead (headExtra conclusion)) .symbol inside
    ((BuilderControlLiteralSources.finalOutside problem index outside hRegion).drop
      (registerWord (headScratch problem index conclusion hRegion)).length)
    (headValues_length problem index conclusion hRegion)
  simpa only [readMachine, readSteps, BuilderLiteralArgumentSource.initialConfiguration,
    BuilderLiteralArgumentSource.finalConfiguration, BuilderLiteralArgumentSource.finalValues,
    inputValues, allValues, allScratch, headValues,
    List.append_assoc, List.drop_drop, registerWord_append, List.length_append, headCount] using h

theorem prefix_workRunExact {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (conclusion : Conclusion) (inside outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    workRunExact? (prefixMachine problem.verifier conclusion) (prefixSteps problem index remaining conclusion hRegion)
      (prefixInitial problem index remaining conclusion inside outside) =
      some (prefixFinal problem index remaining conclusion inside outside hRegion) := by
  have hNew := BuilderControlLiteralSources.firstLiteral_workRunExact problem index remaining (conclusionRole conclusion)
    inside outside hRegion
  simp only [BuilderControlLiteralSources.firstLiteralInitial, BuilderControlLiteralSources.firstLiteralFinal,
    BuilderControlLiteralSources.firstLiteralValues, BuilderControlLiteralSources.firstLiteralRetained,
    BuilderControlLiteralSources.firstLiteralOutside] at hNew
  have hState := state_run problem index remaining conclusion inside outside hRegion
  have hHead := head_run problem index remaining conclusion inside outside hRegion
  have hRead := read_run problem index remaining conclusion inside outside hRegion
  have hHR := chain_run (headMachine problem.verifier conclusion) (readMachine problem.verifier conclusion)
    (headSteps problem index remaining conclusion hRegion) (readSteps problem index remaining conclusion hRegion)
    _ _ _ hHead hRead
  have hSHR := chain_run (stateMachine problem.verifier conclusion)
    (WorkMachineChain.machine (headMachine problem.verifier conclusion) (readMachine problem.verifier conclusion))
    (stateSteps problem index remaining conclusion hRegion)
    (headSteps problem index remaining conclusion hRegion + 1 + readSteps problem index remaining conclusion hRegion)
    _ _ _ hState hHR
  have h := chain_run (BuilderControlLiteralSources.firstLiteralMachine problem.verifier (conclusionRole conclusion))
    (WorkMachineChain.machine (stateMachine problem.verifier conclusion)
      (WorkMachineChain.machine (headMachine problem.verifier conclusion) (readMachine problem.verifier conclusion)))
    (BuilderControlLiteralSources.firstLiteralSteps problem index remaining (conclusionRole conclusion) hRegion)
    (stateSteps problem index remaining conclusion hRegion + 1 +
      (headSteps problem index remaining conclusion hRegion + 1 + readSteps problem index remaining conclusion hRegion))
    _ _ _ hNew hSHR
  simpa only [prefixMachine, prefixSteps, prefixInitial, prefixFinal, inputValues,
    allValues, allScratch, headValues, headScratch, stateValues, stateScratch, newValues, newScratch,
    List.append_assoc, registerWord_append, List.length_append] using h

def payloadMachine {language : Language} (verifier : PolynomialTimeVerifier language) (conclusion : Conclusion) : WorkMachine :=
  BuilderRegisterPack.machine (payloadFields verifier conclusion) 0
def machine {language : Language} (verifier : PolynomialTimeVerifier language) (conclusion : Conclusion) : WorkMachine :=
  WorkMachineChain.machine (prefixMachine verifier conclusion) (payloadMachine verifier conclusion)

def payloadSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (conclusion : Conclusion) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : Nat :=
  BuilderRegisterPack.workSteps (payloadFields problem.verifier conclusion)
    (environment problem index remaining .control (allCount conclusion) (allValues problem index conclusion hRegion)) []
def workSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (conclusion : Conclusion) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : Nat :=
  prefixSteps problem index remaining conclusion hRegion + 1 + payloadSteps problem index remaining conclusion hRegion

def finalValues {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (conclusion : Conclusion) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : List Nat :=
  inputValues problem index remaining .control (allValues problem index conclusion hRegion) ++
    payloadValues problem index remaining conclusion hRegion
def finalOutside {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (conclusion : Conclusion) (outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : List WorkSymbol :=
  (BuilderControlLiteralSources.finalOutside problem index outside hRegion).drop
    (registerWord (allScratch problem index conclusion hRegion ++ payloadValues problem index remaining conclusion hRegion)).length

def initialConfiguration {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (conclusion : Conclusion) (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration (machine problem.verifier conclusion)
    (endTape (BuilderControlActionSource.frame problem index remaining) inside outside)
def finalConfiguration {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (conclusion : Conclusion) (inside outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : WorkConfiguration :=
  {
    state := (machine problem.verifier conclusion).acceptState
    tape := endTape (finalValues problem index remaining conclusion hRegion) inside
      (finalOutside problem index remaining conclusion outside hRegion) }

theorem workRunExact {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (conclusion : Conclusion) (inside outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    workRunExact? (machine problem.verifier conclusion) (workSteps problem index remaining conclusion hRegion)
      (initialConfiguration problem index remaining conclusion inside outside) =
      some (finalConfiguration problem index remaining conclusion inside outside hRegion) := by
  have hPrefix := prefix_workRunExact problem index remaining conclusion inside outside hRegion
  simp only [prefixInitial, prefixFinal] at hPrefix
  have hPack := BuilderRegisterPack.workRunExact (payloadFields problem.verifier conclusion) 0 []
    (environment problem index remaining .control (allCount conclusion) (allValues problem index conclusion hRegion))
    [] inside ((BuilderControlLiteralSources.finalOutside problem index outside hRegion).drop
      (registerWord (allScratch problem index conclusion hRegion)).length) rfl
  simp only [BuilderRegisterPack.initialConfiguration, BuilderRegisterPack.finalConfiguration,
    environment_values problem index remaining .control (allCount conclusion) (allValues problem index conclusion hRegion)
      (allValues_length problem index conclusion hRegion),
    List.nil_append, List.append_nil] at hPack
  have h := chain_run (prefixMachine problem.verifier conclusion) (payloadMachine problem.verifier conclusion)
    (prefixSteps problem index remaining conclusion hRegion) (payloadSteps problem index remaining conclusion hRegion)
    _ _ _ hPrefix hPack
  simpa only [machine, workSteps, initialConfiguration, finalConfiguration, finalValues, payloadValues,
    finalOutside, List.drop_drop, registerWord_append, List.length_append] using h

theorem run_compile_exact {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (conclusion : Conclusion) (inside outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    run (compileWorkMachine (machine problem.verifier conclusion)) (6 * workSteps problem index remaining conclusion hRegion)
      (encodeWorkConfiguration (initialConfiguration problem index remaining conclusion inside outside)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining conclusion inside outside hRegion) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact problem index remaining conclusion inside outside hRegion)

theorem final_canonical_payload {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (conclusion : Conclusion) (inside outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    (finalConfiguration problem index remaining conclusion inside outside hRegion).tape.right =
      (registerWord (BuilderLocalConstraintPayload.values
        (BuilderControlCoordinates.slot (targetCoordinates conclusion (ofSource problem index hRegion))))).reverse ++
      ((registerWord (inputValues problem index remaining .control (allValues problem index conclusion hRegion))).reverse ++ inside) := by
  simp only [finalConfiguration, endTape, finalValues, registerWord_append, List.reverse_append, List.append_assoc,
    payload_values_eq problem index remaining conclusion hRegion]

theorem final_exterior_accounted {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (conclusion : Conclusion) (inside outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    (finalConfiguration problem index remaining conclusion inside outside hRegion).tape.left =
      finalOutside problem index remaining conclusion outside hRegion := rfl

def newSpanBound {language : Language} (verifier : PolynomialTimeVerifier language) (conclusion : Conclusion) : NatPolynomial :=
  BuilderControlLiteralSources.firstLiteralSpanBound verifier (conclusionRole conclusion)
def stateSpanBound {language : Language} (verifier : PolynomialTimeVerifier language) (conclusion : Conclusion) : NatPolynomial :=
  BuilderLiteralArgumentSource.finalSpanBound verifier .control (newCount conclusion)
    (plan .currentState (newExtra conclusion)) .state (newSpanBound verifier conclusion)
def headSpanBound {language : Language} (verifier : PolynomialTimeVerifier language) (conclusion : Conclusion) : NatPolynomial :=
  BuilderLiteralArgumentSource.finalSpanBound verifier .control (stateCount conclusion)
    (plan .currentHead (stateExtra conclusion)) .head (stateSpanBound verifier conclusion)
def prefixSpanBound {language : Language} (verifier : PolynomialTimeVerifier language) (conclusion : Conclusion) : NatPolynomial :=
  BuilderLiteralArgumentSource.finalSpanBound verifier .control (headCount conclusion)
    (plan .currentRead (headExtra conclusion)) .symbol (headSpanBound verifier conclusion)
def stateRawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) (conclusion : Conclusion) : NatPolynomial :=
  BuilderLiteralArgumentSource.rawTimeBound verifier .control (newCount conclusion)
    (plan .currentState (newExtra conclusion)) .state (newSpanBound verifier conclusion)
def headRawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) (conclusion : Conclusion) : NatPolynomial :=
  BuilderLiteralArgumentSource.rawTimeBound verifier .control (stateCount conclusion)
    (plan .currentHead (stateExtra conclusion)) .head (stateSpanBound verifier conclusion)
def readRawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) (conclusion : Conclusion) : NatPolynomial :=
  BuilderLiteralArgumentSource.rawTimeBound verifier .control (headCount conclusion)
    (plan .currentRead (headExtra conclusion)) .symbol (headSpanBound verifier conclusion)
def prefixRawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) (conclusion : Conclusion) : NatPolynomial :=
  .add (.add (BuilderControlLiteralSources.firstLiteralRawTimeBound verifier (conclusionRole conclusion)) (.constant 6))
    (.add (.add (stateRawTimeBound verifier conclusion) (.constant 6))
      (.add (.add (headRawTimeBound verifier conclusion) (.constant 6)) (readRawTimeBound verifier conclusion)))

private theorem retained_bound {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (after : List Nat) (bound : Nat)
    (h : (registerWord (inputValues problem index remaining .control after)).length ≤ bound) :
    (registerWord after).length ≤ bound := by
  simp only [inputValues, registerWord_append, List.length_append] at h
  omega

theorem prefix_source_polynomial_bounds {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (conclusion : Conclusion)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    (registerWord (inputValues problem index remaining .control (allValues problem index conclusion hRegion))).length ≤
        (prefixSpanBound problem.verifier conclusion).eval problem.input.length ∧
      6 * prefixSteps problem index remaining conclusion hRegion ≤
        (prefixRawTimeBound problem.verifier conclusion).eval problem.input.length := by
  have hNew := BuilderControlLiteralSources.firstLiteral_source_polynomial_bounds problem index remaining
    (conclusionRole conclusion) hBody hBalance hRegion
  have hNewSpan :
      (registerWord (inputValues problem index remaining .control (newValues problem index conclusion hRegion))).length ≤
        (newSpanBound problem.verifier conclusion).eval problem.input.length := by
    simpa only [BuilderControlLiteralSources.firstLiteralValues, BuilderControlLiteralSources.firstLiteralRetained,
      newValues, newScratch, newSpanBound] using hNew.1
  have hState := BuilderLiteralArgumentSource.source_polynomial_bounds problem index remaining .control (newCount conclusion)
    (newValues problem index conclusion hRegion) (plan .currentState (newExtra conclusion)) .state
    (newSpanBound problem.verifier conclusion) (newValues_length problem index conclusion hRegion)
    hBody hBalance hRegion (retained_bound problem index remaining _ _ hNewSpan)
  have hStateSpan :
      (registerWord (inputValues problem index remaining .control (stateValues problem index conclusion hRegion))).length ≤
        (stateSpanBound problem.verifier conclusion).eval problem.input.length := by
    simpa only [BuilderLiteralArgumentSource.finalValues, inputValues, stateValues, stateScratch, newValues,
      List.append_assoc, stateSpanBound, newCount] using hState.1
  have hHead := BuilderLiteralArgumentSource.source_polynomial_bounds problem index remaining .control (stateCount conclusion)
    (stateValues problem index conclusion hRegion) (plan .currentHead (stateExtra conclusion)) .head
    (stateSpanBound problem.verifier conclusion) (stateValues_length problem index conclusion hRegion)
    hBody hBalance hRegion (retained_bound problem index remaining _ _ hStateSpan)
  have hHeadSpan :
      (registerWord (inputValues problem index remaining .control (headValues problem index conclusion hRegion))).length ≤
        (headSpanBound problem.verifier conclusion).eval problem.input.length := by
    simpa only [BuilderLiteralArgumentSource.finalValues, inputValues, headValues, headScratch, stateValues,
      List.append_assoc, headSpanBound, stateCount] using hHead.1
  have hRead := BuilderLiteralArgumentSource.source_polynomial_bounds problem index remaining .control (headCount conclusion)
    (headValues problem index conclusion hRegion) (plan .currentRead (headExtra conclusion)) .symbol
    (headSpanBound problem.verifier conclusion) (headValues_length problem index conclusion hRegion)
    hBody hBalance hRegion (retained_bound problem index remaining _ _ hHeadSpan)
  constructor
  · simpa only [BuilderLiteralArgumentSource.finalValues, inputValues, allValues, allScratch, headValues,
      List.append_assoc, prefixSpanBound, headCount] using hRead.1
  · have hNewTime := hNew.2
    have hStateTime := hState.2
    have hHeadTime := hHead.2
    have hReadTime := hRead.2
    simp only [prefixRawTimeBound, NatPolynomial.eval_add, NatPolynomial.eval_constant,
      prefixSteps, stateSteps, headSteps, readSteps, stateRawTimeBound, headRawTimeBound, readRawTimeBound]
    omega

def spanBound {language : Language} (verifier : PolynomialTimeVerifier language) (conclusion : Conclusion) : NatPolynomial :=
  BuilderRegisterPack.spanPolynomial (payloadFields verifier conclusion) (prefixSpanBound verifier conclusion)
def rawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) (conclusion : Conclusion) : NatPolynomial :=
  .add (.add (prefixRawTimeBound verifier conclusion) (.constant 6))
    (BuilderRegisterPack.rawTimePolynomial (payloadFields verifier conclusion) (prefixSpanBound verifier conclusion))

theorem source_polynomial_bounds {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (conclusion : Conclusion)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    (registerWord (finalValues problem index remaining conclusion hRegion)).length ≤
        (spanBound problem.verifier conclusion).eval problem.input.length ∧
      6 * workSteps problem index remaining conclusion hRegion ≤
        (rawTimeBound problem.verifier conclusion).eval problem.input.length := by
  have hPrefix := prefix_source_polynomial_bounds problem index remaining conclusion hBody hBalance hRegion
  have hEnvironment := environment_values problem index remaining .control (allCount conclusion)
    (allValues problem index conclusion hRegion) (allValues_length problem index conclusion hRegion)
  have hStart :
      (registerWord ([] ++ List.ofFn (environment problem index remaining .control (allCount conclusion)
        (allValues problem index conclusion hRegion)) ++ [])).length ≤
          (prefixSpanBound problem.verifier conclusion).eval problem.input.length := by
    simpa only [List.nil_append, List.append_nil, hEnvironment] using hPrefix.1
  have hPack := BuilderRegisterPack.source_polynomial_bounds (payloadFields problem.verifier conclusion)
    (prefixSpanBound problem.verifier conclusion) problem.input.length []
    (environment problem index remaining .control (allCount conclusion) (allValues problem index conclusion hRegion)) [] hStart
  constructor
  · simpa only [List.nil_append, List.append_nil, hEnvironment, finalValues, payloadValues, spanBound] using hPack.1
  · have hTime := hPack.2
    simp only [rawTimeBound, NatPolynomial.eval_add, NatPolynomial.eval_constant, workSteps, payloadSteps]
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

private theorem literal_good {language : Language} (verifier : PolynomialTimeVerifier language)
    (afterCount : Nat) (literalPlan : Plan .control afterCount) (literalKind : BuilderLiteralIndexExpression.Kind) :
    Good (BuilderLiteralArgumentSource.machine verifier .control afterCount literalPlan literalKind) :=
  ⟨BuilderLiteralArgumentSource.rules_pairwise_query_distinct verifier .control afterCount literalPlan literalKind,
    BuilderLiteralArgumentSource.noRuleAtAccept verifier .control afterCount literalPlan literalKind,
    BuilderLiteralArgumentSource.noRuleAtReject verifier .control afterCount literalPlan literalKind,
    BuilderLiteralArgumentSource.acceptState_ne_rejectState verifier .control afterCount literalPlan literalKind⟩

private theorem prefix_good {language : Language} (verifier : PolynomialTimeVerifier language) (conclusion : Conclusion) :
    Good (prefixMachine verifier conclusion) :=
  chain_good _ _
    ⟨BuilderControlLiteralSources.firstLiteral_rules_pairwise_query_distinct verifier (conclusionRole conclusion),
      BuilderControlLiteralSources.firstLiteral_noRuleAtAccept verifier (conclusionRole conclusion),
      BuilderControlLiteralSources.firstLiteral_noRuleAtReject verifier (conclusionRole conclusion),
      BuilderControlLiteralSources.firstLiteral_acceptState_ne_rejectState verifier (conclusionRole conclusion)⟩
    (chain_good _ _ (literal_good verifier (newCount conclusion) (plan .currentState (newExtra conclusion)) .state)
      (chain_good _ _ (literal_good verifier (stateCount conclusion) (plan .currentHead (stateExtra conclusion)) .head)
        (literal_good verifier (headCount conclusion) (plan .currentRead (headExtra conclusion)) .symbol)))

private theorem machine_good {language : Language} (verifier : PolynomialTimeVerifier language) (conclusion : Conclusion) :
    Good (machine verifier conclusion) :=
  chain_good _ _ (prefix_good verifier conclusion)
    ⟨BuilderRegisterPack.rules_pairwise_query_distinct (payloadFields verifier conclusion) 0,
      BuilderRegisterPack.noRuleAtAccept (payloadFields verifier conclusion) 0,
      BuilderRegisterPack.noRuleAtReject (payloadFields verifier conclusion) 0,
      BuilderRegisterPack.acceptState_ne_rejectState (payloadFields verifier conclusion) 0⟩

theorem rules_pairwise_query_distinct {language : Language} (verifier : PolynomialTimeVerifier language) (conclusion : Conclusion) :
    (machine verifier conclusion).rules.Pairwise WorkMachineProgramGraph.QueryDistinct := (machine_good verifier conclusion).1
theorem noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language) (conclusion : Conclusion) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier conclusion) (machine verifier conclusion).acceptState :=
  (machine_good verifier conclusion).2.1
theorem noRuleAtReject {language : Language} (verifier : PolynomialTimeVerifier language) (conclusion : Conclusion) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier conclusion) (machine verifier conclusion).rejectState :=
  (machine_good verifier conclusion).2.2.1
theorem acceptState_ne_rejectState {language : Language} (verifier : PolynomialTimeVerifier language) (conclusion : Conclusion) :
    (machine verifier conclusion).acceptState ≠ (machine verifier conclusion).rejectState := (machine_good verifier conclusion).2.2.2

end PNP.Concrete.CookLevin.BuilderControlImplicationPayload
