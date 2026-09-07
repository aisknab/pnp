/-
Copyright (c) 2026 PNP Labs.

The complete shape-family payload machine from the written source/radix frame.
One fixed graph copies row and tape width, physically compares them, tests the
non-less residual for zero, erases comparison scratch and executes the selected
symbol/head/state payload constructor. No branch verdict or payload is supplied.

The remaining families, clause emission, full loop and packaged reduction are
separate obligations of the complete Cook-Levin builder.
-/
import PNP.Concrete.CookLevinBuilderShapeBranchPayload
import PNP.Concrete.CookLevinBuilderRegisterEquality

namespace PNP.Concrete.CookLevin.BuilderShapePayload

open BuilderUnaryPolynomial (registerWord registerWord_append registerWord_length)
open BuilderDividerOperands (endTape)
open BuilderLiteralArgumentSource (Reference field field_eval inputValues inputCount environment environment_values)
open BuilderShapeCoordinates (Kind Width)
open BuilderShapeBranchPayload (rowValue)
open BuilderArbitrarySlotHeaderRouter
open WorkMachineProgramGraph (Node Graph Endpoint)
open WorkMachineProgramPath (LocalAcceptRun LocalRejectRun AcceptPath)

def rowReference : Reference .shape 0 := .digit ⟨0, by decide⟩
def widthReference : Reference .shape 0 := .source .tapeWidth

def frame {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : List Nat :=
  inputValues problem index remaining .shape []

def pairFields {language : Language} (verifier : PolynomialTimeVerifier language) :
    List (BuilderRegisterPack.Field (inputCount verifier .shape 0)) :=
  [field verifier .shape 0 rowReference, field verifier .shape 0 widthReference]

theorem pairFields_length {language : Language} (verifier : PolynomialTimeVerifier language) :
    (pairFields verifier).length = 2 := rfl

theorem pair_values {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    BuilderRegisterPack.values (pairFields problem.verifier) (environment problem index remaining .shape 0 []) =
      [rowValue problem index, Width problem] := by
  simp only [pairFields, BuilderRegisterPack.values, List.map_cons, List.map_nil, field_eval,
    rowReference, widthReference, BuilderLiteralArgumentSource.referenceValue,
    BuilderLiteralArgumentSource.sourceValue, rowValue, Width]

def resultKind : RawRouter.ComparisonResult → Kind
  | .less _ _ => .symbol
  | .equal _ => .head
  | .greater _ _ => .state

theorem resultKind_compareResult_eq (coordinate boundary : Nat) :
    resultKind (RawRouter.compareResult 0 coordinate boundary) =
      if coordinate < boundary then .symbol else if coordinate = boundary then .head else .state := by
  have h := BuilderSourceRegisterRestore.compareResult_totals 0 coordinate boundary
  cases hResult : RawRouter.compareResult 0 coordinate boundary with
  | less matched rest =>
      simp only [hResult, BuilderSourceRegisterRestore.resultQuotient,
        BuilderSourceRegisterRestore.resultCount, Nat.zero_add] at h
      rw [if_pos (by omega : coordinate < boundary)]
      rfl
  | equal matched =>
      simp only [hResult, BuilderSourceRegisterRestore.resultQuotient,
        BuilderSourceRegisterRestore.resultCount, Nat.zero_add] at h
      rw [if_neg (by omega : ¬ coordinate < boundary), if_pos (by omega : coordinate = boundary)]
      rfl
  | greater matched rest =>
      simp only [hResult, BuilderSourceRegisterRestore.resultQuotient,
        BuilderSourceRegisterRestore.resultCount, Nat.zero_add] at h
      rw [if_neg (by omega : ¬ coordinate < boundary), if_neg (by omega : coordinate ≠ boundary)]
      rfl

def comparisonResult {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    RawRouter.ComparisonResult := RawRouter.compareResult 0 (rowValue problem index) (Width problem)

def selectedKind {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : Kind :=
  resultKind (comparisonResult problem index)

theorem selectedKind_canonical {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape) :
    selectedKind problem index = BuilderShapeCoordinates.kind (BuilderShapeCoordinates.ofSource problem index hRegion) := by
  unfold selectedKind comparisonResult
  rw [resultKind_compareResult_eq, (BuilderShapeBranchPayload.source_coordinates problem index hRegion).2]
  rfl

def pairMachine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  BuilderRegisterPack.machine (pairFields verifier) 0

def pairSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : Nat :=
  BuilderRegisterPack.workSteps (pairFields problem.verifier) (environment problem index remaining .shape 0 []) []

def resultBlanks (result : RawRouter.ComparisonResult) : List WorkSymbol :=
  List.replicate (BuilderRegisterErase.clearedSpan (BuilderRegionResidualSelection.scratchValues result)) .blank

def comparisonBlanks {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : List WorkSymbol :=
  resultBlanks (comparisonResult problem index)

private def resultTape {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (result : RawRouter.ComparisonResult) (inside : List WorkSymbol) : WorkTape :=
  endTape (frame problem index remaining ++ BuilderRegionResidualSelection.scratchValues result) inside []

private def resultFinalTape {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (result : RawRouter.ComparisonResult) (inside : List WorkSymbol) : WorkTape :=
  endTape (BuilderShapeBranchPayload.finalValues problem index remaining 0 [] (resultKind result)) inside
    (BuilderShapeBranchPayload.exteriorWithOutside problem index remaining 0 [] (resultKind result) (resultBlanks result))

def payloadValues {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : List Nat :=
  BuilderRegisterExactlyOnePayload.payloadValues
    (BuilderShapeBranchPayload.countValue problem (selectedKind problem index))
    (BuilderShapeBranchPayload.upperValue problem index (selectedKind problem index))

def finalValues {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : List Nat :=
  BuilderShapeBranchPayload.finalValues problem index remaining 0 [] (selectedKind problem index)

def finalTape {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) : WorkTape :=
  resultFinalTape problem index remaining (comparisonResult problem index) inside

private def branchCode : Kind → Nat
  | .symbol => 0
  | .head => 1
  | .state => 2

def payloadNode {language : Language} (verifier : PolynomialTimeVerifier language) (branch : Kind) : Node :=
  { name := 6 + branchCode branch
    program := BuilderShapeBranchPayload.machine verifier 0 branch
    onAccept := .accept
    onReject := .dead }

def eraseNode {language : Language} (verifier : PolynomialTimeVerifier language) (branch : Kind) : Node :=
  { name := 3 + branchCode branch
    program := BuilderRegisterErase.machine 4
    onAccept := .node (payloadNode verifier branch).reference
    onReject := .dead }

def zeroNode {language : Language} (verifier : PolynomialTimeVerifier language) : Node :=
  { name := 2
    program := BuilderUnaryTagMatch.machine 0
    onAccept := .node (eraseNode verifier .head).reference
    onReject := .node (eraseNode verifier .state).reference }

def comparisonNode {language : Language} (verifier : PolynomialTimeVerifier language) : Node :=
  { name := 1
    program := BuilderRegionResidualSelection.machine
    onAccept := .node (eraseNode verifier .symbol).reference
    onReject := .node (zeroNode verifier).reference }

def pairNode {language : Language} (verifier : PolynomialTimeVerifier language) : Node :=
  { name := 0
    program := pairMachine verifier
    onAccept := .node (comparisonNode verifier).reference
    onReject := .dead }

def graph {language : Language} (verifier : PolynomialTimeVerifier language) : Graph :=
  { nodes := [pairNode verifier, comparisonNode verifier, zeroNode verifier,
      eraseNode verifier .symbol, eraseNode verifier .head, eraseNode verifier .state,
      payloadNode verifier .symbol, payloadNode verifier .head, payloadNode verifier .state]
    entry := (pairNode verifier).reference }

def machine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineProgramGraph.machine (graph verifier)

private theorem pair_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    pairNode verifier ∈ (graph verifier).nodes := List.Mem.head _
private theorem comparison_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    comparisonNode verifier ∈ (graph verifier).nodes := List.Mem.tail _ (List.Mem.head _)
private theorem zero_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    zeroNode verifier ∈ (graph verifier).nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

private theorem erase_mem {language : Language} (verifier : PolynomialTimeVerifier language) (branch : Kind) :
    eraseNode verifier branch ∈ (graph verifier).nodes := by
  cases branch
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

private theorem payload_mem {language : Language} (verifier : PolynomialTimeVerifier language) (branch : Kind) :
    payloadNode verifier branch ∈ (graph verifier).nodes := by
  cases branch
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.head _))))))
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineProgramGraph.QueryDistinct ∧
    WorkMachineProgramGraph.NoRuleAt program program.acceptState ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧
    program.acceptState ≠ program.rejectState

private theorem pair_good {language : Language} (verifier : PolynomialTimeVerifier language) : Good (pairMachine verifier) :=
  ⟨BuilderRegisterPack.rules_pairwise_query_distinct (pairFields verifier) 0,
    BuilderRegisterPack.noRuleAtAccept (pairFields verifier) 0,
    BuilderRegisterPack.noRuleAtReject (pairFields verifier) 0,
    BuilderRegisterPack.acceptState_ne_rejectState (pairFields verifier) 0⟩
private theorem comparison_good : Good BuilderRegionResidualSelection.machine :=
  ⟨BuilderRegionResidualSelection.rules_pairwise_query_distinct,
    BuilderRegionResidualSelection.noRuleAtAccept, BuilderRegionResidualSelection.noRuleAtReject,
    BuilderRegionResidualSelection.acceptState_ne_rejectState⟩
private theorem zero_good : Good (BuilderUnaryTagMatch.machine 0) :=
  ⟨BuilderUnaryTagMatch.rules_pairwise_query_distinct 0,
    BuilderUnaryTagMatch.noRuleAtAccept 0, BuilderUnaryTagMatch.noRuleAtReject 0,
    BuilderUnaryTagMatch.acceptState_ne_rejectState 0⟩
private theorem erase_good : Good (BuilderRegisterErase.machine 4) :=
  ⟨BuilderRegisterErase.rules_pairwise_query_distinct 4,
    BuilderRegisterErase.noRuleAtAccept 4, BuilderRegisterErase.noRuleAtReject 4,
    BuilderRegisterErase.acceptState_ne_rejectState 4⟩
private theorem payload_good {language : Language} (verifier : PolynomialTimeVerifier language) (branch : Kind) :
    Good (BuilderShapeBranchPayload.machine verifier 0 branch) :=
  ⟨BuilderShapeBranchPayload.rules_pairwise_query_distinct verifier 0 branch,
    BuilderShapeBranchPayload.noRuleAtAccept verifier 0 branch,
    BuilderShapeBranchPayload.noRuleAtReject verifier 0 branch,
    BuilderShapeBranchPayload.acceptState_ne_rejectState verifier 0 branch⟩

theorem graph_wellFormed {language : Language} (verifier : PolynomialTimeVerifier language) :
    (graph verifier).WellFormed := by
  have hNames : ((graph verifier).nodes.map Node.name).Pairwise (fun left right : Nat => left ≠ right) := by
    change ([0, 1, 2, 3, 4, 5, 6, 7, 8] : List Nat).Pairwise (fun left right => left ≠ right)
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.pairwise_map] using hNames
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact pair_good verifier
    · exact comparison_good
    · exact zero_good
    · exact erase_good
    · exact erase_good
    · exact erase_good
    · exact payload_good verifier .symbol
    · exact payload_good verifier .head
    · exact payload_good verifier .state
  · exact ⟨pairNode verifier, pair_mem verifier, rfl, rfl⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨comparisonNode verifier, comparison_mem verifier, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨eraseNode verifier .symbol, erase_mem verifier .symbol, rfl, rfl⟩,
        ⟨zeroNode verifier, zero_mem verifier, rfl, rfl⟩⟩
    · exact ⟨⟨eraseNode verifier .head, erase_mem verifier .head, rfl, rfl⟩,
        ⟨eraseNode verifier .state, erase_mem verifier .state, rfl, rfl⟩⟩
    · exact ⟨⟨payloadNode verifier .symbol, payload_mem verifier .symbol, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨payloadNode verifier .head, payload_mem verifier .head, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨payloadNode verifier .state, payload_mem verifier .state, rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨True.intro, True.intro⟩

private def continuationEntry {language : Language} (verifier : PolynomialTimeVerifier language) :
    RawRouter.ComparisonResult → Endpoint
  | .less _ _ => .node (eraseNode verifier .symbol).reference
  | .equal _ | .greater _ _ => .node (zeroNode verifier).reference

def continuationSteps {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (result : RawRouter.ComparisonResult) : Nat :=
  BuilderRegisterEquality.continuationSteps result +
    (BuilderShapeBranchPayload.workSteps problem index remaining 0 [] (resultKind result) + 1)

def workSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : Nat :=
  pairSteps problem index remaining + 1 +
    (BuilderRegisterEquality.workSteps (rowValue problem index) (Width problem) +
      (BuilderShapeBranchPayload.workSteps problem index remaining 0 [] (selectedKind problem index) + 1))

def initialConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration (machine problem.verifier) (endTape (frame problem index remaining) inside [])

def finalConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) : WorkConfiguration :=
  { state := (machine problem.verifier).acceptState
    tape := finalTape problem index remaining inside }

theorem pair_workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) :
    workRunExact? (pairMachine problem.verifier) (pairSteps problem index remaining)
      (workStartConfiguration (pairMachine problem.verifier) (endTape (frame problem index remaining) inside [])) =
      some {
        state := (pairMachine problem.verifier).acceptState
        tape := endTape (frame problem index remaining ++ [rowValue problem index, Width problem]) inside [] } := by
  have h := BuilderRegisterPack.workRunExact (pairFields problem.verifier) 0 []
    (environment problem index remaining .shape 0 []) [] inside [] rfl
  simpa only [BuilderRegisterPack.initialConfiguration, BuilderRegisterPack.finalConfiguration,
    pairMachine, pairSteps, frame, environment_values problem index remaining .shape 0 [] rfl,
    pair_values, List.nil_append, List.append_nil, List.drop_nil] using h

private theorem payload_path {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (result : RawRouter.ComparisonResult) (inside : List WorkSymbol) :
    AcceptPath (graph problem.verifier) (.node (payloadNode problem.verifier (resultKind result)).reference) .accept
      (BuilderShapeBranchPayload.workSteps problem index remaining 0 [] (resultKind result) + 1)
      (endTape (frame problem index remaining) inside (resultBlanks result))
      (resultFinalTape problem index remaining result inside) := by
  have hRun := BuilderShapeBranchPayload.workRunExactWithOutside problem index remaining 0 [] (resultKind result)
    inside (resultBlanks result) rfl
  have hLocal : LocalAcceptRun (payloadNode problem.verifier (resultKind result))
      (BuilderShapeBranchPayload.workSteps problem index remaining 0 [] (resultKind result))
      (endTape (frame problem index remaining) inside (resultBlanks result))
      (resultFinalTape problem index remaining result inside) := by
    simpa only [LocalAcceptRun, payloadNode, workStartConfiguration,
      BuilderShapeBranchPayload.initialConfigurationWithOutside,
      BuilderShapeBranchPayload.finalConfigurationWithOutside, resultFinalTape, frame] using hRun
  simpa only [Nat.add_zero] using
    AcceptPath.step (payloadNode problem.verifier (resultKind result)) .accept _ 0 _ _ _
      (payload_mem problem.verifier (resultKind result)) hLocal
      (AcceptPath.terminal .accept (resultFinalTape problem index remaining result inside))

private theorem erase_path {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (result : RawRouter.ComparisonResult) (inside : List WorkSymbol) :
    AcceptPath (graph problem.verifier) (.node (eraseNode problem.verifier (resultKind result)).reference) .accept
      (BuilderRegisterErase.workSteps (BuilderRegionResidualSelection.scratchValues result) + 1 +
        (BuilderShapeBranchPayload.workSteps problem index remaining 0 [] (resultKind result) + 1))
      (resultTape problem index remaining result inside) (resultFinalTape problem index remaining result inside) := by
  have hRun := BuilderRegisterErase.workRunExact 4 (frame problem index remaining)
    (BuilderRegionResidualSelection.scratchValues result) inside []
    (BuilderRegionResidualSelection.scratchValues_length result)
  have hLocal : LocalAcceptRun (eraseNode problem.verifier (resultKind result))
      (BuilderRegisterErase.workSteps (BuilderRegionResidualSelection.scratchValues result))
      (resultTape problem index remaining result inside)
      (endTape (frame problem index remaining) inside (resultBlanks result)) := by
    simpa only [LocalAcceptRun, eraseNode, workStartConfiguration,
      BuilderRegisterErase.initialConfiguration, BuilderRegisterErase.finalConfiguration,
      resultTape, resultBlanks, List.append_nil] using hRun
  exact AcceptPath.step (eraseNode problem.verifier (resultKind result)) .accept _ _ _ _ _
    (erase_mem problem.verifier (resultKind result)) hLocal (payload_path problem index remaining result inside)

private theorem continuation_path {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (result : RawRouter.ComparisonResult) (inside : List WorkSymbol) :
    AcceptPath (graph problem.verifier) (continuationEntry problem.verifier result) .accept
      (continuationSteps problem index remaining result)
      (resultTape problem index remaining result inside) (resultFinalTape problem index remaining result inside) := by
  cases result with
  | less matched rest => exact erase_path problem index remaining (.less matched rest) inside
  | equal matched =>
      have hZero := BuilderUnaryTagMatch.accept_workRunExact 0
        (frame problem index remaining ++
          BuilderRegionResidualRegisters.restoredValues (BuilderRegionResidualRegisters.ofComparison (.equal matched)))
        inside []
      have hLocal : LocalAcceptRun (zeroNode problem.verifier) (BuilderUnaryTagMatch.workSteps 0 0)
          (resultTape problem index remaining (.equal matched) inside)
          (resultTape problem index remaining (.equal matched) inside) := by
        simpa only [LocalAcceptRun, zeroNode, workStartConfiguration, resultTape,
          BuilderRegionResidualSelection.scratchValues, BuilderRegionResidualSelection.resultCoordinate,
          List.append_assoc] using hZero
      simpa only [continuationSteps, BuilderRegisterEquality.continuationSteps, resultKind,
        continuationEntry, BuilderRegionResidualSelection.resultCoordinate, Nat.add_assoc] using
        AcceptPath.step (zeroNode problem.verifier) .accept _ _ _ _ _ (zero_mem problem.verifier) hLocal
          (erase_path problem index remaining (.equal matched) inside)
  | greater matched rest =>
      have hZero := BuilderUnaryTagMatch.reject_workRunExact 0 (rest + 1)
        (frame problem index remaining ++
          BuilderRegionResidualRegisters.restoredValues (BuilderRegionResidualRegisters.ofComparison (.greater matched rest)))
        inside [] (by omega)
      have hLocal : LocalRejectRun (zeroNode problem.verifier) (BuilderUnaryTagMatch.workSteps 0 (rest + 1))
          (resultTape problem index remaining (.greater matched rest) inside)
          (resultTape problem index remaining (.greater matched rest) inside) := by
        simpa only [LocalRejectRun, zeroNode, workStartConfiguration, resultTape,
          BuilderRegionResidualSelection.scratchValues, BuilderRegionResidualSelection.resultCoordinate,
          List.append_assoc] using hZero
      simpa only [continuationSteps, BuilderRegisterEquality.continuationSteps, resultKind,
        continuationEntry, BuilderRegionResidualSelection.resultCoordinate, Nat.add_assoc] using
        AcceptPath.stepReject (zeroNode problem.verifier) .accept _ _ _ _ _ (zero_mem problem.verifier) hLocal
          (erase_path problem index remaining (.greater matched rest) inside)

private theorem comparison_path {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) :
    AcceptPath (graph problem.verifier) (.node (comparisonNode problem.verifier).reference) .accept
      (BuilderRegionResidualSelection.workSteps (rowValue problem index) (Width problem) + 1 +
        continuationSteps problem index remaining (comparisonResult problem index))
      (endTape (frame problem index remaining ++ [rowValue problem index, Width problem]) inside [])
      (finalTape problem index remaining inside) := by
  have hCompare := BuilderRegionResidualSelection.workRunExact (rowValue problem index) (Width problem)
    (frame problem index remaining) inside
  simp only [BuilderRegionResidualSelection.initialConfiguration, BuilderRegionResidualSelection.finalConfiguration] at hCompare
  have hTail := continuation_path problem index remaining (comparisonResult problem index) inside
  unfold comparisonResult at hTail ⊢
  unfold finalTape
  cases hResult : RawRouter.compareResult 0 (rowValue problem index) (Width problem) with
  | less matched rest =>
      simp only [hResult, comparisonResult] at hCompare hTail ⊢
      exact AcceptPath.step (comparisonNode problem.verifier) .accept _ _ _ _ _
        (comparison_mem problem.verifier) hCompare hTail
  | equal matched =>
      simp only [hResult, comparisonResult] at hCompare hTail ⊢
      exact AcceptPath.stepReject (comparisonNode problem.verifier) .accept _ _ _ _ _
        (comparison_mem problem.verifier) hCompare hTail
  | greater matched rest =>
      simp only [hResult, comparisonResult] at hCompare hTail ⊢
      exact AcceptPath.stepReject (comparisonNode problem.verifier) .accept _ _ _ _ _
        (comparison_mem problem.verifier) hCompare hTail

/-- One fixed machine performs the comparison, cleanup and entire selected payload. -/
theorem workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
      (initialConfiguration problem index remaining inside) = some (finalConfiguration problem index remaining inside) := by
  have hPair : LocalAcceptRun (pairNode problem.verifier) (pairSteps problem index remaining)
      (endTape (frame problem index remaining) inside [])
      (endTape (frame problem index remaining ++ [rowValue problem index, Width problem]) inside []) := by
    simpa only [LocalAcceptRun, pairNode, workStartConfiguration] using pair_workRunExact problem index remaining inside
  have hPath := AcceptPath.step (pairNode problem.verifier) .accept _ _ _ _ _
    (pair_mem problem.verifier) hPair (comparison_path problem index remaining inside)
  have hRun := WorkMachineProgramPath.runExact (graph problem.verifier) _ _ _ _ _ (graph_wellFormed problem.verifier) hPath
  have hInitial (tape : WorkTape) :
      WorkMachineProgramGraph.endpointConfiguration (.node (pairNode problem.verifier).reference) tape =
        workStartConfiguration (machine problem.verifier) tape := rfl
  have hFinal (tape : WorkTape) :
      WorkMachineProgramGraph.endpointConfiguration .accept tape =
        { state := (machine problem.verifier).acceptState, tape := tape } := rfl
  rw [hInitial, hFinal] at hRun
  simpa only [machine, workSteps, initialConfiguration, finalConfiguration,
    BuilderRegisterEquality.workSteps, continuationSteps, selectedKind, comparisonResult, Nat.add_assoc] using hRun

theorem run_compile_exact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining)
      (encodeWorkConfiguration (initialConfiguration problem index remaining inside)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining inside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact problem index remaining inside)

theorem payload_canonical {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape) :
    payloadValues problem index = BuilderLocalConstraintPayload.values
      (problem.shapeConstraintSlotDirect (BuilderConstraintRegionSource.localCoordinate problem index .shape)) :=
  BuilderShapeBranchPayload.source_payload problem index hRegion (selectedKind problem index)
    (selectedKind_canonical problem index hRegion).symm

theorem payload_decode {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape) :
    BuilderLocalConstraintPayload.decode problem.FormulaWidth (payloadValues problem index) =
      some (problem.shapeConstraintSlotDirect (BuilderConstraintRegionSource.localCoordinate problem index .shape)) := by
  rw [payload_canonical problem index hRegion, BuilderLocalConstraintPayload.decode_values]

theorem final_canonical_payload {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape) :
    finalValues problem index remaining =
      BuilderShapeBranchPayload.scratchValues problem index remaining 0 [] (selectedKind problem index) ++
        [BuilderShapeBranchPayload.countValue problem (selectedKind problem index)] ++
        BuilderLocalConstraintPayload.values
          (problem.shapeConstraintSlotDirect (BuilderConstraintRegionSource.localCoordinate problem index .shape)) :=
  BuilderShapeBranchPayload.canonical_final_values problem index remaining 0 [] hRegion
    (selectedKind problem index) (selectedKind_canonical problem index hRegion).symm

/-- Canonical payload execution has no caller-supplied classification premise. -/
theorem canonical_workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
      (initialConfiguration problem index remaining inside) =
      some {
        state := (machine problem.verifier).acceptState
        tape := endTape
          (BuilderShapeBranchPayload.scratchValues problem index remaining 0 [] (selectedKind problem index) ++
            [BuilderShapeBranchPayload.countValue problem (selectedKind problem index)] ++
            BuilderLocalConstraintPayload.values
              (problem.shapeConstraintSlotDirect (BuilderConstraintRegionSource.localCoordinate problem index .shape)))
          inside (BuilderShapeBranchPayload.exteriorWithOutside problem index remaining 0 []
            (selectedKind problem index) (comparisonBlanks problem index)) } := by
  have h := workRunExact problem index remaining inside
  change workRunExact? _ _ _ = some {
    state := (machine problem.verifier).acceptState
    tape := endTape (finalValues problem index remaining) inside
      (BuilderShapeBranchPayload.exteriorWithOutside problem index remaining 0 []
        (selectedKind problem index) (comparisonBlanks problem index)) } at h
  rw [final_canonical_payload problem index remaining hRegion] at h
  exact h

theorem final_inside_preserved {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) :
    (finalConfiguration problem index remaining inside).tape.right =
      (registerWord (finalValues problem index remaining)).reverse ++ inside := rfl

theorem final_exterior {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) :
    (finalConfiguration problem index remaining inside).tape.left =
      BuilderShapeBranchPayload.exteriorWithOutside problem index remaining 0 []
        (selectedKind problem index) (comparisonBlanks problem index) := rfl

def inputSpanBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  BuilderLiteralArgumentSource.inputBound verifier .shape (.constant 0)
def pairSpanBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  BuilderRegisterPack.spanPolynomial (pairFields verifier) (inputSpanBound verifier)
def pairRawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  BuilderRegisterPack.rawTimePolynomial (pairFields verifier) (inputSpanBound verifier)
def comparisonSpanBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (.constant 4) (.mul (.constant 4) (pairSpanBound verifier))
def branchSpanBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderShapeBranchPayload.spanPolynomial verifier 0 .symbol (.constant 0))
    (.add (BuilderShapeBranchPayload.spanPolynomial verifier 0 .head (.constant 0))
      (BuilderShapeBranchPayload.spanPolynomial verifier 0 .state (.constant 0)))
def branchRawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderShapeBranchPayload.rawTimePolynomial verifier 0 .symbol (.constant 0))
    (.add (BuilderShapeBranchPayload.rawTimePolynomial verifier 0 .head (.constant 0))
      (BuilderShapeBranchPayload.rawTimePolynomial verifier 0 .state (.constant 0)))
def spanBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (branchSpanBound verifier) (comparisonSpanBound verifier)
def rawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (pairRawTimeBound verifier)
    (.add (BuilderRegisterEquality.rawTimePolynomial (pairSpanBound verifier))
      (.add (branchRawTimeBound verifier) (.constant 12)))

theorem pair_source_polynomial_bounds {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape) :
    (registerWord (frame problem index remaining ++ [rowValue problem index, Width problem])).length ≤
      (pairSpanBound problem.verifier).eval problem.input.length ∧
    6 * pairSteps problem index remaining ≤ (pairRawTimeBound problem.verifier).eval problem.input.length := by
  have hInput := BuilderLiteralArgumentSource.input_span_le problem index remaining .shape [] (.constant 0)
    hBody hBalance hRegion (Nat.le_refl 0)
  have hEnvironment :
      (registerWord ([] ++ List.ofFn (environment problem index remaining .shape 0 []) ++ [])).length ≤
        (inputSpanBound problem.verifier).eval problem.input.length := by
    simpa only [List.nil_append, List.append_nil, environment_values problem index remaining .shape 0 [] rfl,
      inputSpanBound] using hInput
  have hPack := BuilderRegisterPack.source_polynomial_bounds (pairFields problem.verifier) (inputSpanBound problem.verifier)
    problem.input.length [] (environment problem index remaining .shape 0 []) [] hEnvironment
  simpa only [pairSpanBound, pairRawTimeBound, pairSteps, frame, pair_values,
    environment_values problem index remaining .shape 0 [] rfl, List.nil_append, List.append_nil] using hPack

theorem comparison_source_polynomial_bounds {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape) :
    (comparisonBlanks problem index).length ≤ (comparisonSpanBound problem.verifier).eval problem.input.length ∧
    6 * BuilderRegisterEquality.workSteps (rowValue problem index) (Width problem) ≤
      (BuilderRegisterEquality.rawTimePolynomial (pairSpanBound problem.verifier)).eval problem.input.length := by
  have hPair := (pair_source_polynomial_bounds problem index remaining hBody hBalance hRegion).1
  have hFields : rowValue problem index ≤ (pairSpanBound problem.verifier).eval problem.input.length ∧
      Width problem ≤ (pairSpanBound problem.verifier).eval problem.input.length := by
    simp only [registerWord_append, List.length_append, registerWord_length, List.length_cons, List.length_nil,
      List.sum_cons, List.sum_nil] at hPair
    constructor <;> omega
  have hComparison := BuilderRegisterEquality.source_polynomial_bounds (rowValue problem index) (Width problem)
    problem.input.length (pairSpanBound problem.verifier) hFields.1 hFields.2
  simpa only [comparisonBlanks, resultBlanks, comparisonResult, BuilderRegisterEquality.clearedSpan,
    List.length_replicate, comparisonSpanBound, NatPolynomial.eval_add,
    NatPolynomial.eval_mul, NatPolynomial.eval_constant] using hComparison

private theorem branch_bounds {language : Language} (verifier : PolynomialTimeVerifier language)
    (branch : Kind) (inputLength : Nat) :
    (BuilderShapeBranchPayload.spanPolynomial verifier 0 branch (.constant 0)).eval inputLength ≤
      (branchSpanBound verifier).eval inputLength ∧
    (BuilderShapeBranchPayload.rawTimePolynomial verifier 0 branch (.constant 0)).eval inputLength ≤
      (branchRawTimeBound verifier).eval inputLength := by
  cases branch <;> simp only [branchSpanBound, branchRawTimeBound, NatPolynomial.eval_add] <;>
    constructor <;> omega

/-- All field preparation, compare/zero/erase work, payload work and exterior are charged. -/
theorem source_polynomial_bounds {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape) :
    (registerWord (finalValues problem index remaining)).length +
        (finalConfiguration problem index remaining inside).tape.left.length ≤
      (spanBound problem.verifier).eval problem.input.length ∧
    6 * workSteps problem index remaining ≤ (rawTimeBound problem.verifier).eval problem.input.length := by
  have hPair := pair_source_polynomial_bounds problem index remaining hBody hBalance hRegion
  have hComparison := comparison_source_polynomial_bounds problem index remaining hBody hBalance hRegion
  have hPayload := BuilderShapeBranchPayload.source_polynomial_boundsWithOutside problem index remaining 0 []
    (selectedKind problem index) (.constant 0) (comparisonSpanBound problem.verifier) (comparisonBlanks problem index)
    rfl hBody hBalance hRegion (Nat.le_refl 0) hComparison.1
  have hBranch := branch_bounds problem.verifier (selectedKind problem index) problem.input.length
  have hSpace : (registerWord (finalValues problem index remaining)).length +
      (finalConfiguration problem index remaining inside).tape.left.length ≤
        (BuilderShapeBranchPayload.spanPolynomial problem.verifier 0 (selectedKind problem index) (.constant 0)).eval
          problem.input.length + (comparisonSpanBound problem.verifier).eval problem.input.length := by
    simpa only [finalValues, finalConfiguration, finalTape, resultFinalTape, selectedKind, comparisonBlanks,
      BuilderShapeBranchPayload.finalConfigurationWithOutside, endTape, NatPolynomial.eval_add] using hPayload.1
  constructor
  · simp only [spanBound, NatPolynomial.eval_add]
    omega
  · have hTime := hPayload.2
    simp only [workSteps, rawTimeBound, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

theorem rules_pairwise_query_distinct {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise (graph verifier) (graph_wellFormed verifier)

theorem noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (machine verifier) :=
  WorkMachineProgramGraph.noRuleAt_globalAccept (graph verifier)

theorem noRuleAtReject {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier) (machine verifier).rejectState :=
  WorkMachineProgramGraph.noRuleAt_globalReject (graph verifier)

theorem acceptState_ne_rejectState {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState := by
  change (0 : Nat) ≠ 1
  decide

end PNP.Concrete.CookLevin.BuilderShapePayload
