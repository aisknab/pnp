/-
Copyright (c) 2026 PNP Labs.

Runtime selection of every control-implication payload from the source frame.
The verifier fixes one finite graph. A copied source conclusion digit selects
one of three verified branches; the disposable tag is erased before that
branch starts. Neither a conclusion nor a selection certificate is supplied
to the public exact-execution or canonical-payload interface.
-/

import PNP.Concrete.CookLevinBuilderControlImplicationPayload
import PNP.Concrete.CookLevinBuilderRegisterErase
import PNP.Concrete.CookLevinBuilderUnaryTagMatch

namespace PNP.Concrete.CookLevin.BuilderControlPayload

open BuilderUnaryPolynomial (registerWord registerWord_length registerWord_append)
open BuilderDividerOperands (endTape)
open BuilderLiteralArgumentSource
  (Reference field field_eval referenceValue inputCount inputValues environment environment_values)
open BuilderControlImplicationPayload (Conclusion conclusionCode)
open WorkMachineProgramGraph (Node Graph)
open WorkMachineProgramPath (AcceptPath)

def tagReference : Reference .control 0 := .digit ⟨0, by decide⟩
def tagValue {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : Nat :=
  referenceValue problem index .control [] tagReference

theorem tag_canonical {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    tagValue problem index = (BuilderControlCoordinates.ofSource problem index hRegion).conclusion.val := by
  have h := (BuilderControlCoordinates.source_radix_coordinates problem index hRegion).1
  simp only [tagValue, referenceValue, tagReference, h, List.getD_cons_zero]

theorem tag_lt {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    tagValue problem index < 3 := by
  rw [tag_canonical problem index hRegion]
  exact (BuilderControlCoordinates.ofSource problem index hRegion).conclusion.isLt

/-- Execution specification only; the graph below tests the written source tag. -/
def conclusionOfCode (code : Fin 3) : Conclusion :=
  if code.val = 0 then .state else if code.val = 1 then .head else .symbol

theorem conclusionOfCode_code (code : Fin 3) : conclusionCode (conclusionOfCode code) = code := by
  apply Fin.ext
  by_cases hZero : code.val = 0
  · simpa only [conclusionOfCode, if_pos hZero, conclusionCode] using hZero.symm
  · by_cases hOne : code.val = 1
    · simpa only [conclusionOfCode, if_neg hZero, if_pos hOne, conclusionCode] using hOne.symm
    · simp only [conclusionOfCode, if_neg hZero, if_neg hOne, conclusionCode]
      have hLt := code.isLt
      omega

def selectedConclusion {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : Conclusion :=
  conclusionOfCode (BuilderControlCoordinates.ofSource problem index hRegion).conclusion

theorem selected_code {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    conclusionCode (selectedConclusion problem index hRegion) =
      (BuilderControlCoordinates.ofSource problem index hRegion).conclusion :=
  conclusionOfCode_code _

theorem tag_selected {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    tagValue problem index = (conclusionCode (selectedConclusion problem index hRegion)).val := by
  rw [selected_code problem index hRegion]
  exact tag_canonical problem index hRegion

def fields {language : Language} (verifier : PolynomialTimeVerifier language) :
    List (BuilderRegisterPack.Field (inputCount verifier .control 0)) :=
  [field verifier .control 0 tagReference]

theorem fields_values {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    BuilderRegisterPack.values (fields problem.verifier) (environment problem index remaining .control 0 []) =
      [tagValue problem index] := by
  simp only [fields, BuilderRegisterPack.values, List.map_cons, List.map_nil, field_eval, tagValue]

private theorem environment_frame {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) :
    List.ofFn (environment problem index remaining .control 0 []) =
      BuilderControlActionSource.frame problem index remaining := by
  simpa only [inputValues, BuilderControlActionSource.frame, List.append_nil] using
    environment_values problem index remaining .control 0 [] rfl

def copyMachine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  BuilderRegisterPack.machine (fields verifier) 0

def payloadNode {language : Language} (verifier : PolynomialTimeVerifier language) (conclusion : Conclusion) : Node :=
  {name := 7 + (conclusionCode conclusion).val,
   program := BuilderControlImplicationPayload.machine verifier conclusion,
   onAccept := .accept, onReject := .dead}
def eraseNode {language : Language} (verifier : PolynomialTimeVerifier language) (conclusion : Conclusion) : Node :=
  {name := 4 + (conclusionCode conclusion).val, program := BuilderRegisterErase.oneMachine,
   onAccept := .node (payloadNode verifier conclusion).reference, onReject := .dead}
def symbolTestNode {language : Language} (verifier : PolynomialTimeVerifier language) : Node :=
  {name := 3, program := BuilderUnaryTagMatch.machine 2,
   onAccept := .node (eraseNode verifier .symbol).reference, onReject := .reject}
def headTestNode {language : Language} (verifier : PolynomialTimeVerifier language) : Node :=
  {name := 2, program := BuilderUnaryTagMatch.machine 1,
   onAccept := .node (eraseNode verifier .head).reference, onReject := .node (symbolTestNode verifier).reference}
def stateTestNode {language : Language} (verifier : PolynomialTimeVerifier language) : Node :=
  {name := 1, program := BuilderUnaryTagMatch.machine 0,
   onAccept := .node (eraseNode verifier .state).reference, onReject := .node (headTestNode verifier).reference}
def copyNode {language : Language} (verifier : PolynomialTimeVerifier language) : Node :=
  {name := 0, program := copyMachine verifier,
   onAccept := .node (stateTestNode verifier).reference, onReject := .dead}
def graph {language : Language} (verifier : PolynomialTimeVerifier language) : Graph :=
  {nodes := [copyNode verifier, stateTestNode verifier, headTestNode verifier, symbolTestNode verifier,
    eraseNode verifier .state, eraseNode verifier .head, eraseNode verifier .symbol,
    payloadNode verifier .state, payloadNode verifier .head, payloadNode verifier .symbol],
   entry := (copyNode verifier).reference}
def machine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineProgramGraph.machine (graph verifier)

private theorem copy_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    copyNode verifier ∈ (graph verifier).nodes :=
  List.Mem.head _
private theorem stateTest_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    stateTestNode verifier ∈ (graph verifier).nodes :=
  List.Mem.tail _ (List.Mem.head _)
private theorem headTest_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    headTestNode verifier ∈ (graph verifier).nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
private theorem symbolTest_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    symbolTestNode verifier ∈ (graph verifier).nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
private theorem erase_mem {language : Language} (verifier : PolynomialTimeVerifier language) (conclusion : Conclusion) :
    eraseNode verifier conclusion ∈ (graph verifier).nodes := by
  cases conclusion with
  | state => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  | head => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
  | symbol => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
private theorem payload_mem {language : Language} (verifier : PolynomialTimeVerifier language) (conclusion : Conclusion) :
    payloadNode verifier conclusion ∈ (graph verifier).nodes := by
  cases conclusion with
  | state => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
  | head => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
  | symbol => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineProgramGraph.QueryDistinct ∧
    WorkMachineProgramGraph.NoRuleAt program program.acceptState ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧
    program.acceptState ≠ program.rejectState

private theorem copy_good {language : Language} (verifier : PolynomialTimeVerifier language) :
    Good (copyMachine verifier) :=
  ⟨BuilderRegisterPack.rules_pairwise_query_distinct (fields verifier) 0,
    BuilderRegisterPack.noRuleAtAccept (fields verifier) 0,
    BuilderRegisterPack.noRuleAtReject (fields verifier) 0,
    BuilderRegisterPack.acceptState_ne_rejectState (fields verifier) 0⟩
private theorem test_good (tag : Nat) : Good (BuilderUnaryTagMatch.machine tag) :=
  ⟨BuilderUnaryTagMatch.rules_pairwise_query_distinct tag, BuilderUnaryTagMatch.noRuleAtAccept tag,
    BuilderUnaryTagMatch.noRuleAtReject tag, BuilderUnaryTagMatch.acceptState_ne_rejectState tag⟩
private theorem erase_good : Good BuilderRegisterErase.oneMachine :=
  ⟨BuilderRegisterErase.one_rules_pairwise_query_distinct, BuilderRegisterErase.one_noRuleAtAccept,
    BuilderRegisterErase.one_noRuleAtReject, BuilderRegisterErase.one_acceptState_ne_rejectState⟩
private theorem payload_good {language : Language} (verifier : PolynomialTimeVerifier language) (conclusion : Conclusion) :
    Good (BuilderControlImplicationPayload.machine verifier conclusion) :=
  ⟨BuilderControlImplicationPayload.rules_pairwise_query_distinct verifier conclusion,
    BuilderControlImplicationPayload.noRuleAtAccept verifier conclusion,
    BuilderControlImplicationPayload.noRuleAtReject verifier conclusion,
    BuilderControlImplicationPayload.acceptState_ne_rejectState verifier conclusion⟩

theorem graph_wellFormed {language : Language} (verifier : PolynomialTimeVerifier language) :
    (graph verifier).WellFormed := by
  have hNames : ((graph verifier).nodes.map Node.name).Pairwise (fun left right : Nat => left ≠ right) := by
    change ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : List Nat).Pairwise _
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.pairwise_map] using hNames
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact copy_good verifier
    · exact test_good 0
    · exact test_good 1
    · exact test_good 2
    · exact erase_good
    · exact erase_good
    · exact erase_good
    · exact payload_good verifier .state
    · exact payload_good verifier .head
    · exact payload_good verifier .symbol
  · exact ⟨copyNode verifier, copy_mem verifier, rfl, rfl⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨stateTestNode verifier, stateTest_mem verifier, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨eraseNode verifier .state, erase_mem verifier .state, rfl, rfl⟩,
        ⟨headTestNode verifier, headTest_mem verifier, rfl, rfl⟩⟩
    · exact ⟨⟨eraseNode verifier .head, erase_mem verifier .head, rfl, rfl⟩,
        ⟨symbolTestNode verifier, symbolTest_mem verifier, rfl, rfl⟩⟩
    · exact ⟨⟨eraseNode verifier .symbol, erase_mem verifier .symbol, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨payloadNode verifier .state, payload_mem verifier .state, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨payloadNode verifier .head, payload_mem verifier .head, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨payloadNode verifier .symbol, payload_mem verifier .symbol, rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨True.intro, True.intro⟩

def copySteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : Nat :=
  BuilderRegisterPack.workSteps (fields problem.verifier) (environment problem index remaining .control 0 []) []

/-- Includes each visited test's graph bridge. -/
def testSteps : Conclusion → Nat
  | .state => BuilderUnaryTagMatch.workSteps 0 0 + 1
  | .head => BuilderUnaryTagMatch.workSteps 0 1 + 1 + (BuilderUnaryTagMatch.workSteps 1 1 + 1)
  | .symbol => BuilderUnaryTagMatch.workSteps 0 2 + 1 +
      (BuilderUnaryTagMatch.workSteps 1 2 + 1 + (BuilderUnaryTagMatch.workSteps 2 2 + 1))

def branchSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (conclusion : Conclusion) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : Nat :=
  (conclusionCode conclusion).val + 2 + 1 +
    (BuilderControlImplicationPayload.workSteps problem index remaining conclusion hRegion + 1)

def workSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : Nat :=
  copySteps problem index remaining + 1 +
    (testSteps (selectedConclusion problem index hRegion) +
      branchSteps problem index remaining (selectedConclusion problem index hRegion) hRegion)

def restoredOutside (tag : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  List.replicate (tag + 1) WorkSymbol.blank ++ outside.drop (tag + 1)

def payloadValues {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : List Nat :=
  BuilderControlImplicationPayload.payloadValues problem index remaining (selectedConclusion problem index hRegion) hRegion
def finalValues {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : List Nat :=
  BuilderControlImplicationPayload.finalValues problem index remaining (selectedConclusion problem index hRegion) hRegion
def finalOutside {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : List WorkSymbol :=
  BuilderControlImplicationPayload.finalOutside problem index remaining (selectedConclusion problem index hRegion)
    (restoredOutside (tagValue problem index) outside) hRegion

def initialConfiguration {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration (machine problem.verifier)
    (endTape (BuilderControlActionSource.frame problem index remaining) inside outside)
def finalConfiguration {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (inside outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : WorkConfiguration :=
  {
    state := (machine problem.verifier).acceptState
    tape := endTape (finalValues problem index remaining hRegion) inside
      (finalOutside problem index remaining outside hRegion) }

private theorem copy_run {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (inside outside : List WorkSymbol) :
    workRunExact? (copyMachine problem.verifier) (copySteps problem index remaining)
      (workStartConfiguration (copyMachine problem.verifier)
        (endTape (BuilderControlActionSource.frame problem index remaining) inside outside)) =
      some {
        state := (copyMachine problem.verifier).acceptState
        tape := endTape (BuilderControlActionSource.frame problem index remaining ++ [tagValue problem index])
          inside (outside.drop (tagValue problem index + 1)) } := by
  have h := BuilderRegisterPack.workRunExact (fields problem.verifier) 0 []
    (environment problem index remaining .control 0 []) [] inside outside rfl
  have hWord : (registerWord [tagValue problem index]).length = tagValue problem index + 1 := by
    simp only [registerWord_length, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil]
    omega
  simpa only [copyMachine, copySteps, BuilderRegisterPack.initialConfiguration,
    BuilderRegisterPack.finalConfiguration, environment_frame, fields_values,
    List.nil_append, List.append_nil, hWord] using h


private theorem erase_path {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (conclusion : Conclusion) (inside outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    AcceptPath (graph problem.verifier) (.node (eraseNode problem.verifier conclusion).reference) .accept
      (branchSteps problem index remaining conclusion hRegion)
      (endTape (BuilderControlActionSource.frame problem index remaining ++ [(conclusionCode conclusion).val]) inside outside)
      (endTape (BuilderControlImplicationPayload.finalValues problem index remaining conclusion hRegion) inside
        (BuilderControlImplicationPayload.finalOutside problem index remaining conclusion
          (List.replicate ((conclusionCode conclusion).val + 1) WorkSymbol.blank ++ outside) hRegion)) := by
  have hPayload := BuilderControlImplicationPayload.workRunExact problem index remaining conclusion inside
    (List.replicate ((conclusionCode conclusion).val + 1) WorkSymbol.blank ++ outside) hRegion
  simp only [BuilderControlImplicationPayload.initialConfiguration,
    BuilderControlImplicationPayload.finalConfiguration] at hPayload
  have hP := AcceptPath.step (payloadNode problem.verifier conclusion) .accept _ 0 _ _ _
    (payload_mem problem.verifier conclusion) hPayload (.terminal .accept _)
  have hErase := BuilderRegisterErase.one_workRunExact (BuilderControlActionSource.frame problem index remaining)
    (conclusionCode conclusion).val inside outside
  have h := AcceptPath.step (eraseNode problem.verifier conclusion) .accept _ _ _ _ _
    (erase_mem problem.verifier conclusion) hErase hP
  simpa only [branchSteps, Nat.add_zero] using h

private theorem test_path {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (conclusion : Conclusion) (inside outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    AcceptPath (graph problem.verifier) (.node (stateTestNode problem.verifier).reference) .accept
      (testSteps conclusion + branchSteps problem index remaining conclusion hRegion)
      (endTape (BuilderControlActionSource.frame problem index remaining ++ [(conclusionCode conclusion).val]) inside outside)
      (endTape (BuilderControlImplicationPayload.finalValues problem index remaining conclusion hRegion) inside
        (BuilderControlImplicationPayload.finalOutside problem index remaining conclusion
          (List.replicate ((conclusionCode conclusion).val + 1) WorkSymbol.blank ++ outside) hRegion)) := by
  have hErase := erase_path problem index remaining conclusion inside outside hRegion
  cases conclusion with
  | state =>
      have hState := BuilderUnaryTagMatch.accept_workRunExact 0
        (BuilderControlActionSource.frame problem index remaining) inside outside
      exact AcceptPath.step (stateTestNode problem.verifier) .accept _ _ _ _ _
        (stateTest_mem problem.verifier) hState hErase
  | head =>
      have hState := BuilderUnaryTagMatch.reject_workRunExact 0 1
        (BuilderControlActionSource.frame problem index remaining) inside outside (by decide)
      have hHead := BuilderUnaryTagMatch.accept_workRunExact 1
        (BuilderControlActionSource.frame problem index remaining) inside outside
      have hH := AcceptPath.step (headTestNode problem.verifier) .accept _ _ _ _ _
        (headTest_mem problem.verifier) hHead hErase
      have h := AcceptPath.stepReject (stateTestNode problem.verifier) .accept _ _ _ _ _
        (stateTest_mem problem.verifier) hState hH
      simpa only [testSteps, conclusionCode, Nat.add_assoc] using h
  | symbol =>
      have hState := BuilderUnaryTagMatch.reject_workRunExact 0 2
        (BuilderControlActionSource.frame problem index remaining) inside outside (by decide)
      have hHead := BuilderUnaryTagMatch.reject_workRunExact 1 2
        (BuilderControlActionSource.frame problem index remaining) inside outside (by decide)
      have hSymbol := BuilderUnaryTagMatch.accept_workRunExact 2
        (BuilderControlActionSource.frame problem index remaining) inside outside
      have hS := AcceptPath.step (symbolTestNode problem.verifier) .accept _ _ _ _ _
        (symbolTest_mem problem.verifier) hSymbol hErase
      have hH := AcceptPath.stepReject (headTestNode problem.verifier) .accept _ _ _ _ _
        (headTest_mem problem.verifier) hHead hS
      have h := AcceptPath.stepReject (stateTestNode problem.verifier) .accept _ _ _ _ _
        (stateTest_mem problem.verifier) hState hH
      simpa only [testSteps, conclusionCode, Nat.add_assoc] using h

theorem workRunExact {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (inside outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining hRegion)
      (initialConfiguration problem index remaining inside outside) =
      some (finalConfiguration problem index remaining inside outside hRegion) := by
  have hCopy := copy_run problem index remaining inside outside
  have hTest := test_path problem index remaining (selectedConclusion problem index hRegion) inside
    (outside.drop (tagValue problem index + 1)) hRegion
  rw [← tag_selected problem index hRegion] at hTest
  have hPath := AcceptPath.step (copyNode problem.verifier) .accept _ _ _ _ _
    (copy_mem problem.verifier) hCopy hTest
  have h := WorkMachineProgramPath.runExact (graph problem.verifier) _ _ _ _ _
    (graph_wellFormed problem.verifier) hPath
  have hStart (tape : WorkTape) :
      WorkMachineProgramGraph.endpointConfiguration (.node (copyNode problem.verifier).reference) tape =
        workStartConfiguration (machine problem.verifier) tape := rfl
  rw [hStart] at h
  exact h

theorem run_compile_exact {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (inside outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining hRegion)
      (encodeWorkConfiguration (initialConfiguration problem index remaining inside outside)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining inside outside hRegion) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact problem index remaining inside outside hRegion)

def invalidSteps (code : Nat) : Nat :=
  BuilderUnaryTagMatch.workSteps 0 code + 1 +
    (BuilderUnaryTagMatch.workSteps 1 code + 1 + (BuilderUnaryTagMatch.workSteps 2 code + 1))

/-- An invalid written tag rejects at the dispatcher, without executing a payload branch. -/
theorem invalid_tag_workRunExact {language : Language} (verifier : PolynomialTimeVerifier language) (code : Nat)
    (older : List Nat) (inside outside : List WorkSymbol) (hInvalid : code ≠ 0 ∧ code ≠ 1 ∧ code ≠ 2) :
    workRunExact? (machine verifier) (invalidSteps code)
      (WorkMachineProgramGraph.endpointConfiguration (.node (stateTestNode verifier).reference)
        (endTape (older ++ [code]) inside outside)) =
      some {state := (machine verifier).rejectState, tape := endTape (older ++ [code]) inside outside} := by
  have hState := BuilderUnaryTagMatch.reject_workRunExact 0 code older inside outside hInvalid.1
  have hHead := BuilderUnaryTagMatch.reject_workRunExact 1 code older inside outside hInvalid.2.1
  have hSymbol := BuilderUnaryTagMatch.reject_workRunExact 2 code older inside outside hInvalid.2.2
  have hS := AcceptPath.stepReject (symbolTestNode verifier) .reject _ 0 _ _ _
    (symbolTest_mem verifier) hSymbol (.terminal .reject _)
  have hH := AcceptPath.stepReject (headTestNode verifier) .reject _ _ _ _ _
    (headTest_mem verifier) hHead hS
  have hPath := AcceptPath.stepReject (stateTestNode verifier) .reject _ _ _ _ _
    (stateTest_mem verifier) hState hH
  have h := WorkMachineProgramPath.runExact (graph verifier) _ _ _ _ _ (graph_wellFormed verifier) hPath
  have hReject (tape : WorkTape) :
      WorkMachineProgramGraph.endpointConfiguration .reject tape =
        {state := (machine verifier).rejectState, tape := tape} := rfl
  rw [hReject] at h
  simpa only [machine, invalidSteps, Nat.add_zero] using h

theorem payloadValues_length {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    (payloadValues problem index remaining hRegion).length = 10 :=
  BuilderControlImplicationPayload.payloadValues_length problem index remaining _ hRegion

theorem payload_source_values {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    payloadValues problem index remaining hRegion = BuilderLocalConstraintPayload.values
      (problem.controlConstraintSlotDirect (BuilderConstraintRegionSource.localCoordinate problem index .control)) := by
  have hTarget :
      BuilderControlImplicationPayload.targetCoordinates (selectedConclusion problem index hRegion)
        (BuilderControlCoordinates.ofSource problem index hRegion) = BuilderControlCoordinates.ofSource problem index hRegion := by
    unfold BuilderControlImplicationPayload.targetCoordinates
    rw [selected_code problem index hRegion]
  unfold payloadValues
  rw [BuilderControlImplicationPayload.payload_values_eq problem index remaining _ hRegion, hTarget]
  exact congrArg BuilderLocalConstraintPayload.values (BuilderControlCoordinates.source_slot problem index hRegion).symm

theorem payload_source_slot {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    BuilderLocalConstraintPayload.decode problem.FormulaWidth (payloadValues problem index remaining hRegion) =
      some (problem.controlConstraintSlotDirect (BuilderConstraintRegionSource.localCoordinate problem index .control)) :=
  BuilderControlImplicationPayload.payload_source_slot problem index remaining _ hRegion
    (selected_code problem index hRegion)

theorem final_canonical_payload {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (inside outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    (finalConfiguration problem index remaining inside outside hRegion).tape.right =
      (registerWord (BuilderLocalConstraintPayload.values
        (problem.controlConstraintSlotDirect (BuilderConstraintRegionSource.localCoordinate problem index .control)))).reverse ++
      ((registerWord (inputValues problem index remaining .control
        (BuilderControlImplicationPayload.allValues problem index (selectedConclusion problem index hRegion) hRegion))).reverse ++ inside) := by
  have hPayload := payload_source_values problem index remaining hRegion
  simp only [payloadValues] at hPayload
  simp only [finalConfiguration, endTape, finalValues, BuilderControlImplicationPayload.finalValues,
    registerWord_append, List.reverse_append, List.append_assoc, hPayload]

theorem final_exterior_accounted {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (inside outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    (finalConfiguration problem index remaining inside outside hRegion).tape.left =
      BuilderControlImplicationPayload.finalOutside problem index remaining (selectedConclusion problem index hRegion)
        (List.replicate (tagValue problem index + 1) WorkSymbol.blank ++ outside.drop (tagValue problem index + 1)) hRegion := rfl


theorem testSteps_le (conclusion : Conclusion) : testSteps conclusion ≤ 18 := by
  cases conclusion <;> decide

def dispatchOverhead (conclusion : Conclusion) : Nat :=
  1 + testSteps conclusion + ((conclusionCode conclusion).val + 2) + 1 + 1

theorem dispatchOverhead_le (conclusion : Conclusion) : dispatchOverhead conclusion ≤ 25 := by
  cases conclusion <;> decide

theorem workSteps_decomposition {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    workSteps problem index remaining hRegion =
      copySteps problem index remaining +
        BuilderControlImplicationPayload.workSteps problem index remaining (selectedConclusion problem index hRegion) hRegion +
        dispatchOverhead (selectedConclusion problem index hRegion) := by
  simp only [workSteps, branchSteps, dispatchOverhead]
  omega

def copyRawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  BuilderRegisterPack.rawTimePolynomial (fields verifier) (BuilderLiteralArgumentSource.inputBound verifier .control (.constant 0))
def spanBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (.add (BuilderControlImplicationPayload.spanBound verifier .state)
    (BuilderControlImplicationPayload.spanBound verifier .head))
    (BuilderControlImplicationPayload.spanBound verifier .symbol)
def rawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (.add (copyRawTimeBound verifier)
    (.add (.add (BuilderControlImplicationPayload.rawTimeBound verifier .state)
      (BuilderControlImplicationPayload.rawTimeBound verifier .head))
      (BuilderControlImplicationPayload.rawTimeBound verifier .symbol))) (.constant 150)

private theorem copy_source_bound {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    6 * copySteps problem index remaining ≤ (copyRawTimeBound problem.verifier).eval problem.input.length := by
  have hNil : (registerWord ([] : List Nat)).length ≤ (NatPolynomial.constant 0).eval problem.input.length := by
    simp only [registerWord_length, List.sum_nil, List.length_nil, Nat.add_zero, NatPolynomial.eval_constant]
    exact Nat.le_refl 0
  have hInput := BuilderLiteralArgumentSource.input_span_le problem index remaining .control [] (.constant 0)
    hBody hBalance hRegion hNil
  have hEnvironment :
      (registerWord ([] ++ List.ofFn (environment problem index remaining .control 0 []) ++ [])).length ≤
        (BuilderLiteralArgumentSource.inputBound problem.verifier .control (.constant 0)).eval problem.input.length := by
    simpa only [List.nil_append, List.append_nil, environment_values problem index remaining .control 0 [] rfl] using hInput
  have hPack := BuilderRegisterPack.source_polynomial_bounds (fields problem.verifier)
    (BuilderLiteralArgumentSource.inputBound problem.verifier .control (.constant 0)) problem.input.length []
    (environment problem index remaining .control 0 []) [] hEnvironment
  exact hPack.2

private theorem branch_le_sum (bounds : Conclusion → Nat) (conclusion : Conclusion) :
    bounds conclusion ≤ bounds .state + bounds .head + bounds .symbol := by
  cases conclusion <;> omega

theorem source_polynomial_bounds {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    (registerWord (finalValues problem index remaining hRegion)).length ≤
        (spanBound problem.verifier).eval problem.input.length ∧
      6 * workSteps problem index remaining hRegion ≤ (rawTimeBound problem.verifier).eval problem.input.length := by
  have hBranch := BuilderControlImplicationPayload.source_polynomial_bounds problem index remaining
    (selectedConclusion problem index hRegion) hBody hBalance hRegion
  have hSpan := branch_le_sum (fun c => (BuilderControlImplicationPayload.spanBound problem.verifier c).eval problem.input.length)
    (selectedConclusion problem index hRegion)
  have hTime := branch_le_sum (fun c => (BuilderControlImplicationPayload.rawTimeBound problem.verifier c).eval problem.input.length)
    (selectedConclusion problem index hRegion)
  have hCopy := copy_source_bound problem index remaining hBody hBalance hRegion
  have hOverhead := dispatchOverhead_le (selectedConclusion problem index hRegion)
  constructor
  · simp only [finalValues, spanBound, NatPolynomial.eval_add]
    exact Nat.le_trans hBranch.1 hSpan
  · rw [workSteps_decomposition problem index remaining hRegion]
    simp only [rawTimeBound, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

theorem restoredOutside_length_le (tag : Nat) (outside : List WorkSymbol) :
    (restoredOutside tag outside).length ≤ outside.length + tag + 1 := by
  simp only [restoredOutside, List.length_append, List.length_replicate, List.length_drop]
  omega

theorem rules_pairwise_query_distinct {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise (graph verifier) (graph_wellFormed verifier)
theorem noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier) (machine verifier).acceptState :=
  WorkMachineProgramGraph.noRuleAt_globalAccept (graph verifier)
theorem noRuleAtReject {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier) (machine verifier).rejectState :=
  WorkMachineProgramGraph.noRuleAt_globalReject (graph verifier)
theorem acceptState_ne_rejectState {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState := by
  change (0 : Nat) ≠ 1
  decide

end PNP.Concrete.CookLevin.BuilderControlPayload
