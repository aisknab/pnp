/-
Copyright (c) 2026 PNP Labs.

One source-driven program constructs all five canonical constraint payload
families. It derives and tests the physical region tag, performs the matching
radix preparation and executes the complete family writer. No family choice,
payload or local correctness certificate is supplied to the source theorem.
Clause occupancy/emission, scratch recovery and the full builder remain open.
-/
import PNP.Concrete.CookLevinBuilderFamilyPayload

namespace PNP.Concrete.CookLevin.BuilderSourcePayload

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape inside)
open BuilderConstraintRegionRegisters (Region)
open BuilderConstraintRegionDispatch (regionTag)
open WorkMachineProgramGraph (Node Graph Endpoint)
open WorkMachineProgramPath (AcceptPath)

def selected {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : Region :=
  (BuilderConstraintRegionSource.selectedRegion problem index).getD .shape

theorem selected_valid {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem) :
    BuilderConstraintRegionSource.selectedRegion problem index = some (selected problem index) := by
  obtain ⟨region, h⟩ := BuilderConstraintRegionSource.selectedRegion_some_of_body problem index hBody
  simp only [selected, h, Option.getD_some]

def tagPrefix {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) (region : Region) : List Nat :=
  BuilderConstraintRegionAssembly.finalValues problem index remaining ++
    BuilderConstraintRegionDispatch.prefixScratch (BuilderConstraintRegionSource.lengths problem)
      (BuilderClauseDividerExecution.constraintIndex problem index) region ++
    BuilderConstraintRegionDispatch.restored (BuilderConstraintRegionSource.localCoordinate problem index region)
      (BuilderConstraintRegionRegisters.regionLength problem region) ++
    [BuilderConstraintRegionSource.localCoordinate problem index region]

theorem selected_suffix {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) (region : Region) :
    BuilderRegionRadixSource.selectedValues problem index remaining region =
      tagPrefix problem index remaining region ++ [regionTag region] := by
  simp only [BuilderRegionRadixSource.selectedValues, BuilderConstraintRegionSource.selectedScratch, tagPrefix,
    List.append_assoc, List.cons_append, List.nil_append]

def testSteps : Region → Nat
  | .shape => BuilderUnaryTagMatch.workSteps 0 0 + 1
  | .initial => BuilderUnaryTagMatch.workSteps 0 1 + 1 + (BuilderUnaryTagMatch.workSteps 1 1 + 1)
  | .control => BuilderUnaryTagMatch.workSteps 0 2 + 1 + (BuilderUnaryTagMatch.workSteps 1 2 + 1 +
      (BuilderUnaryTagMatch.workSteps 2 2 + 1))
  | .preservation => BuilderUnaryTagMatch.workSteps 0 3 + 1 + (BuilderUnaryTagMatch.workSteps 1 3 + 1 +
      (BuilderUnaryTagMatch.workSteps 2 3 + 1 + (BuilderUnaryTagMatch.workSteps 3 3 + 1)))
  | .accepting => BuilderUnaryTagMatch.workSteps 0 4 + 1 + (BuilderUnaryTagMatch.workSteps 1 4 + 1 +
      (BuilderUnaryTagMatch.workSteps 2 4 + 1 + (BuilderUnaryTagMatch.workSteps 3 4 + 1 +
        (BuilderUnaryTagMatch.workSteps 4 4 + 1))))

theorem testSteps_le (region : Region) : testSteps region ≤ 40 := by cases region <;> decide

def familyNode {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) : Node :=
  {name := 6 + regionTag region, program := BuilderFamilyPayload.machine verifier region,
   onAccept := .accept, onReject := .reject}
def nextTest {language : Language} (verifier : PolynomialTimeVerifier language) : Region → Endpoint
  | .shape => .node {name := 2, startState := (BuilderUnaryTagMatch.machine 1).startState}
  | .initial => .node {name := 3, startState := (BuilderUnaryTagMatch.machine 2).startState}
  | .control => .node {name := 4, startState := (BuilderUnaryTagMatch.machine 3).startState}
  | .preservation => .node {name := 5, startState := (BuilderUnaryTagMatch.machine 4).startState}
  | .accepting => .reject
def testNode {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) : Node :=
  {name := 1 + regionTag region, program := BuilderUnaryTagMatch.machine (regionTag region),
   onAccept := .node (familyNode verifier region).reference, onReject := nextTest verifier region}
def sourceNode {language : Language} (verifier : PolynomialTimeVerifier language) : Node :=
  {name := 0, program := BuilderConstraintRegionSource.machine verifier,
   onAccept := .node (testNode verifier .shape).reference, onReject := .reject}
def graph {language : Language} (verifier : PolynomialTimeVerifier language) : Graph :=
  {nodes := [sourceNode verifier, testNode verifier .shape, testNode verifier .initial, testNode verifier .control,
    testNode verifier .preservation, testNode verifier .accepting, familyNode verifier .shape, familyNode verifier .initial,
    familyNode verifier .control, familyNode verifier .preservation, familyNode verifier .accepting],
   entry := (sourceNode verifier).reference}
def machine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineProgramGraph.machine (graph verifier)

def workSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem) : Nat :=
  BuilderConstraintRegionSource.workSteps problem index remaining + 1 +
    (testSteps (selected problem index) +
      (BuilderFamilyPayload.workSteps problem index remaining (selected problem index) (selected_valid problem index hBody) + 1))
def finalValues {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem) : List Nat :=
  BuilderFamilyPayload.finalValues problem index remaining (selected problem index) (selected_valid problem index hBody)
def payloadValues {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem) : List Nat :=
  BuilderFamilyPayload.payloadValues problem index remaining (selected problem index) (selected_valid problem index hBody)
def history {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem) : List Nat :=
  BuilderFamilyPayload.history problem index remaining (selected problem index) (selected_valid problem index hBody)
def exterior {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem) : List WorkSymbol :=
  BuilderFamilyPayload.exterior problem index remaining (selected problem index) (selected_valid problem index hBody)

def initialConfiguration {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) : WorkConfiguration :=
  workStartConfiguration (machine problem.verifier) (BuilderCursorSource.cursorTape problem index remaining output)
def finalConfiguration {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem) :
    WorkConfiguration :=
  {state := (machine problem.verifier).acceptState,
   tape := endTape (finalValues problem index remaining hBody) (inside problem.input output) (exterior problem index remaining hBody)}

theorem graph_nodes_length {language : Language} (verifier : PolynomialTimeVerifier language) :
    (graph verifier).nodes.length = 11 := rfl

private theorem source_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    sourceNode verifier ∈ (graph verifier).nodes := List.Mem.head _

private theorem test_mem {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) :
    testNode verifier region ∈ (graph verifier).nodes := by
  cases region with
  | shape => exact List.Mem.tail _ (List.Mem.head _)
  | initial => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  | control => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  | preservation => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  | accepting => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

private theorem family_mem {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) :
    familyNode verifier region ∈ (graph verifier).nodes := by
  cases region with
  | shape => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
  | initial => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
  | control => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
  | preservation => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))
  | accepting => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineProgramGraph.QueryDistinct ∧
    WorkMachineProgramGraph.NoRuleAt program program.acceptState ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧ program.acceptState ≠ program.rejectState
private theorem source_good {language : Language} (verifier : PolynomialTimeVerifier language) :
    Good (BuilderConstraintRegionSource.machine verifier) :=
  ⟨BuilderConstraintRegionSource.rules_pairwise_query_distinct verifier, BuilderConstraintRegionSource.noRuleAtAccept verifier,
   BuilderConstraintRegionSource.noRuleAtReject verifier, BuilderConstraintRegionSource.acceptState_ne_rejectState verifier⟩
private theorem tag_good (tag : Nat) : Good (BuilderUnaryTagMatch.machine tag) :=
  ⟨BuilderUnaryTagMatch.rules_pairwise_query_distinct tag, BuilderUnaryTagMatch.noRuleAtAccept tag,
   BuilderUnaryTagMatch.noRuleAtReject tag, BuilderUnaryTagMatch.acceptState_ne_rejectState tag⟩
private theorem family_good {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) :
    Good (BuilderFamilyPayload.machine verifier region) :=
  ⟨BuilderFamilyPayload.rules_pairwise_query_distinct verifier region, BuilderFamilyPayload.noRuleAtAccept verifier region,
   BuilderFamilyPayload.noRuleAtReject verifier region, BuilderFamilyPayload.acceptState_ne_rejectState verifier region⟩

theorem graph_wellFormed {language : Language} (verifier : PolynomialTimeVerifier language) : (graph verifier).WellFormed := by
  have hNames : ((graph verifier).nodes.map Node.name).Pairwise (fun a b : Nat => a ≠ b) := by
    change ([0,1,2,3,4,5,6,7,8,9,10] : List Nat).Pairwise _
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.pairwise_map] using hNames
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact source_good verifier
    · exact tag_good 0
    · exact tag_good 1
    · exact tag_good 2
    · exact tag_good 3
    · exact tag_good 4
    · exact family_good verifier .shape
    · exact family_good verifier .initial
    · exact family_good verifier .control
    · exact family_good verifier .preservation
    · exact family_good verifier .accepting
  · exact ⟨sourceNode verifier, source_mem verifier, rfl, rfl⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨testNode verifier .shape, test_mem verifier .shape, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨familyNode verifier .shape, family_mem verifier .shape, rfl, rfl⟩, ⟨testNode verifier .initial, test_mem verifier .initial, rfl, rfl⟩⟩
    · exact ⟨⟨familyNode verifier .initial, family_mem verifier .initial, rfl, rfl⟩, ⟨testNode verifier .control, test_mem verifier .control, rfl, rfl⟩⟩
    · exact ⟨⟨familyNode verifier .control, family_mem verifier .control, rfl, rfl⟩, ⟨testNode verifier .preservation, test_mem verifier .preservation, rfl, rfl⟩⟩
    · exact ⟨⟨familyNode verifier .preservation, family_mem verifier .preservation, rfl, rfl⟩, ⟨testNode verifier .accepting, test_mem verifier .accepting, rfl, rfl⟩⟩
    · exact ⟨⟨familyNode verifier .accepting, family_mem verifier .accepting, rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨True.intro, True.intro⟩

private theorem dispatch_path {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (region : Region)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some region) :
    AcceptPath (graph problem.verifier) (.node (testNode problem.verifier .shape).reference) .accept
      (testSteps region + (BuilderFamilyPayload.workSteps problem index remaining region hRegion + 1))
      (endTape (BuilderRegionRadixSource.selectedValues problem index remaining region) (inside problem.input output) [])
      (endTape (BuilderFamilyPayload.finalValues problem index remaining region hRegion) (inside problem.input output)
        (BuilderFamilyPayload.exterior problem index remaining region hRegion)) := by
  cases region with
  | shape =>
      have hFamily := BuilderFamilyPayload.workRunExact problem index remaining output .shape hRegion
      simp only [BuilderFamilyPayload.initialConfiguration, BuilderFamilyPayload.finalConfiguration] at hFamily
      have hTail := AcceptPath.step (familyNode problem.verifier .shape) .accept _ 0 _ _ _
        (family_mem problem.verifier .shape) hFamily (.terminal .accept _)
      have hYes := BuilderUnaryTagMatch.accept_workRunExact (regionTag .shape) (tagPrefix problem index remaining .shape)
        (inside problem.input output) []
      rw [← selected_suffix problem index remaining .shape] at hYes
      have hPath0 := AcceptPath.step (testNode problem.verifier .shape) .accept _ _ _ _ _
        (test_mem problem.verifier .shape) hYes hTail
      simpa only [testSteps, regionTag, Nat.add_zero, Nat.add_assoc] using hPath0
  | initial =>
      have hFamily := BuilderFamilyPayload.workRunExact problem index remaining output .initial hRegion
      simp only [BuilderFamilyPayload.initialConfiguration, BuilderFamilyPayload.finalConfiguration] at hFamily
      have hTail := AcceptPath.step (familyNode problem.verifier .initial) .accept _ 0 _ _ _
        (family_mem problem.verifier .initial) hFamily (.terminal .accept _)
      have hYes := BuilderUnaryTagMatch.accept_workRunExact (regionTag .initial) (tagPrefix problem index remaining .initial)
        (inside problem.input output) []
      rw [← selected_suffix problem index remaining .initial] at hYes
      have hPath1 := AcceptPath.step (testNode problem.verifier .initial) .accept _ _ _ _ _
        (test_mem problem.verifier .initial) hYes hTail
      have hNo0 := BuilderUnaryTagMatch.reject_workRunExact (regionTag .shape) (regionTag .initial)
        (tagPrefix problem index remaining .initial) (inside problem.input output) [] (by decide)
      rw [← selected_suffix problem index remaining .initial] at hNo0
      have hPath0 := AcceptPath.stepReject (testNode problem.verifier .shape) .accept _ _ _ _ _
        (test_mem problem.verifier .shape) hNo0 hPath1
      simpa only [testSteps, regionTag, Nat.add_zero, Nat.add_assoc] using hPath0
  | control =>
      have hFamily := BuilderFamilyPayload.workRunExact problem index remaining output .control hRegion
      simp only [BuilderFamilyPayload.initialConfiguration, BuilderFamilyPayload.finalConfiguration] at hFamily
      have hTail := AcceptPath.step (familyNode problem.verifier .control) .accept _ 0 _ _ _
        (family_mem problem.verifier .control) hFamily (.terminal .accept _)
      have hYes := BuilderUnaryTagMatch.accept_workRunExact (regionTag .control) (tagPrefix problem index remaining .control)
        (inside problem.input output) []
      rw [← selected_suffix problem index remaining .control] at hYes
      have hPath2 := AcceptPath.step (testNode problem.verifier .control) .accept _ _ _ _ _
        (test_mem problem.verifier .control) hYes hTail
      have hNo1 := BuilderUnaryTagMatch.reject_workRunExact (regionTag .initial) (regionTag .control)
        (tagPrefix problem index remaining .control) (inside problem.input output) [] (by decide)
      rw [← selected_suffix problem index remaining .control] at hNo1
      have hPath1 := AcceptPath.stepReject (testNode problem.verifier .initial) .accept _ _ _ _ _
        (test_mem problem.verifier .initial) hNo1 hPath2
      have hNo0 := BuilderUnaryTagMatch.reject_workRunExact (regionTag .shape) (regionTag .control)
        (tagPrefix problem index remaining .control) (inside problem.input output) [] (by decide)
      rw [← selected_suffix problem index remaining .control] at hNo0
      have hPath0 := AcceptPath.stepReject (testNode problem.verifier .shape) .accept _ _ _ _ _
        (test_mem problem.verifier .shape) hNo0 hPath1
      simpa only [testSteps, regionTag, Nat.add_zero, Nat.add_assoc] using hPath0
  | preservation =>
      have hFamily := BuilderFamilyPayload.workRunExact problem index remaining output .preservation hRegion
      simp only [BuilderFamilyPayload.initialConfiguration, BuilderFamilyPayload.finalConfiguration] at hFamily
      have hTail := AcceptPath.step (familyNode problem.verifier .preservation) .accept _ 0 _ _ _
        (family_mem problem.verifier .preservation) hFamily (.terminal .accept _)
      have hYes := BuilderUnaryTagMatch.accept_workRunExact (regionTag .preservation) (tagPrefix problem index remaining .preservation)
        (inside problem.input output) []
      rw [← selected_suffix problem index remaining .preservation] at hYes
      have hPath3 := AcceptPath.step (testNode problem.verifier .preservation) .accept _ _ _ _ _
        (test_mem problem.verifier .preservation) hYes hTail
      have hNo2 := BuilderUnaryTagMatch.reject_workRunExact (regionTag .control) (regionTag .preservation)
        (tagPrefix problem index remaining .preservation) (inside problem.input output) [] (by decide)
      rw [← selected_suffix problem index remaining .preservation] at hNo2
      have hPath2 := AcceptPath.stepReject (testNode problem.verifier .control) .accept _ _ _ _ _
        (test_mem problem.verifier .control) hNo2 hPath3
      have hNo1 := BuilderUnaryTagMatch.reject_workRunExact (regionTag .initial) (regionTag .preservation)
        (tagPrefix problem index remaining .preservation) (inside problem.input output) [] (by decide)
      rw [← selected_suffix problem index remaining .preservation] at hNo1
      have hPath1 := AcceptPath.stepReject (testNode problem.verifier .initial) .accept _ _ _ _ _
        (test_mem problem.verifier .initial) hNo1 hPath2
      have hNo0 := BuilderUnaryTagMatch.reject_workRunExact (regionTag .shape) (regionTag .preservation)
        (tagPrefix problem index remaining .preservation) (inside problem.input output) [] (by decide)
      rw [← selected_suffix problem index remaining .preservation] at hNo0
      have hPath0 := AcceptPath.stepReject (testNode problem.verifier .shape) .accept _ _ _ _ _
        (test_mem problem.verifier .shape) hNo0 hPath1
      simpa only [testSteps, regionTag, Nat.add_zero, Nat.add_assoc] using hPath0
  | accepting =>
      have hFamily := BuilderFamilyPayload.workRunExact problem index remaining output .accepting hRegion
      simp only [BuilderFamilyPayload.initialConfiguration, BuilderFamilyPayload.finalConfiguration] at hFamily
      have hTail := AcceptPath.step (familyNode problem.verifier .accepting) .accept _ 0 _ _ _
        (family_mem problem.verifier .accepting) hFamily (.terminal .accept _)
      have hYes := BuilderUnaryTagMatch.accept_workRunExact (regionTag .accepting) (tagPrefix problem index remaining .accepting)
        (inside problem.input output) []
      rw [← selected_suffix problem index remaining .accepting] at hYes
      have hPath4 := AcceptPath.step (testNode problem.verifier .accepting) .accept _ _ _ _ _
        (test_mem problem.verifier .accepting) hYes hTail
      have hNo3 := BuilderUnaryTagMatch.reject_workRunExact (regionTag .preservation) (regionTag .accepting)
        (tagPrefix problem index remaining .accepting) (inside problem.input output) [] (by decide)
      rw [← selected_suffix problem index remaining .accepting] at hNo3
      have hPath3 := AcceptPath.stepReject (testNode problem.verifier .preservation) .accept _ _ _ _ _
        (test_mem problem.verifier .preservation) hNo3 hPath4
      have hNo2 := BuilderUnaryTagMatch.reject_workRunExact (regionTag .control) (regionTag .accepting)
        (tagPrefix problem index remaining .accepting) (inside problem.input output) [] (by decide)
      rw [← selected_suffix problem index remaining .accepting] at hNo2
      have hPath2 := AcceptPath.stepReject (testNode problem.verifier .control) .accept _ _ _ _ _
        (test_mem problem.verifier .control) hNo2 hPath3
      have hNo1 := BuilderUnaryTagMatch.reject_workRunExact (regionTag .initial) (regionTag .accepting)
        (tagPrefix problem index remaining .accepting) (inside problem.input output) [] (by decide)
      rw [← selected_suffix problem index remaining .accepting] at hNo1
      have hPath1 := AcceptPath.stepReject (testNode problem.verifier .initial) .accept _ _ _ _ _
        (test_mem problem.verifier .initial) hNo1 hPath2
      have hNo0 := BuilderUnaryTagMatch.reject_workRunExact (regionTag .shape) (regionTag .accepting)
        (tagPrefix problem index remaining .accepting) (inside problem.input output) [] (by decide)
      rw [← selected_suffix problem index remaining .accepting] at hNo0
      have hPath0 := AcceptPath.stepReject (testNode problem.verifier .shape) .accept _ _ _ _ _
        (test_mem problem.verifier .shape) hNo0 hPath1
      simpa only [testSteps, regionTag, Nat.add_zero, Nat.add_assoc] using hPath0

private theorem configuration_eq (config : WorkConfiguration) (state : Nat) (tape : WorkTape)
    (hState : config.state = state) (hTape : config.tape = tape) :
    config = {state := state, tape := tape} := by
  cases config with
  | mk currentState currentTape =>
      change currentState = state at hState
      change currentTape = tape at hTape
      cases hState
      cases hTape
      rfl

/-- The actual cursor selects the region; no region or local branch premise is supplied. -/
theorem workRunExact {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining hBody)
      (initialConfiguration problem index remaining output) =
      some (finalConfiguration problem index remaining output hBody) := by
  have hRegion := selected_valid problem index hBody
  have hSource := BuilderConstraintRegionSource.workRunExact problem index remaining output hBody
  have hSourceFinal := configuration_eq (BuilderConstraintRegionSource.finalConfiguration problem index remaining output)
    (BuilderConstraintRegionSource.machine problem.verifier).acceptState
    (endTape (BuilderRegionRadixSource.selectedValues problem index remaining (selected problem index)) (inside problem.input output) [])
    (BuilderConstraintRegionSource.final_accept_of_body problem index remaining output hBody)
    (BuilderRegionRadixSource.selected_source_handoff problem index remaining output (selected problem index) hRegion)
  rw [hSourceFinal] at hSource
  simp only [BuilderConstraintRegionSource.initialConfiguration] at hSource
  have hTail := dispatch_path problem index remaining output (selected problem index) hRegion
  have hPath := AcceptPath.step (sourceNode problem.verifier) .accept _ _ _ _ _
    (source_mem problem.verifier) hSource hTail
  have h := WorkMachineProgramPath.runExact (graph problem.verifier) _ _ _ _ _ (graph_wellFormed problem.verifier) hPath
  have hStart (tape : WorkTape) :
      WorkMachineProgramGraph.endpointConfiguration (.node (sourceNode problem.verifier).reference) tape =
        workStartConfiguration (machine problem.verifier) tape := rfl
  have hMachine : WorkMachineProgramGraph.machine (graph problem.verifier) = machine problem.verifier := rfl
  have hAccept (tape : WorkTape) :
      WorkMachineProgramGraph.endpointConfiguration .accept tape = {state := (machine problem.verifier).acceptState, tape := tape} := rfl
  rw [hStart, hMachine, hAccept] at h
  simpa only [initialConfiguration, finalConfiguration, workSteps, finalValues, exterior] using h

theorem run_compile_exact {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining hBody)
      (encodeWorkConfiguration (initialConfiguration problem index remaining output)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining output hBody) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact problem index remaining output hBody)

theorem final_suffix {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem) :
    finalValues problem index remaining hBody = history problem index remaining hBody ++ payloadValues problem index remaining hBody :=
  BuilderFamilyPayload.final_suffix problem index remaining (selected problem index) (selected_valid problem index hBody)

theorem payload_canonical {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem) :
    payloadValues problem index remaining hBody = BuilderLocalConstraintPayload.values
      (problem.formulaConstraintSlotDirect (BuilderClauseDividerExecution.constraintIndex problem index)) :=
  BuilderFamilyPayload.payload_canonical problem index remaining (selected problem index) (selected_valid problem index hBody)

theorem payload_decode {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem) :
    BuilderLocalConstraintPayload.decode problem.FormulaWidth (payloadValues problem index remaining hBody) =
      some (problem.formulaConstraintSlotDirect (BuilderClauseDividerExecution.constraintIndex problem index)) := by
  rw [payload_canonical, BuilderLocalConstraintPayload.decode_values]

theorem canonical_workRunExact {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining hBody)
      (initialConfiguration problem index remaining output) =
      some
        {state := (machine problem.verifier).acceptState,
         tape := endTape (history problem index remaining hBody ++ BuilderLocalConstraintPayload.values
           (problem.formulaConstraintSlotDirect (BuilderClauseDividerExecution.constraintIndex problem index)))
           (inside problem.input output) (exterior problem index remaining hBody)} := by
  have h := workRunExact problem index remaining output hBody
  rw [finalConfiguration, final_suffix, payload_canonical] at h
  exact h

theorem final_tape {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem) :
    (finalConfiguration problem index remaining output hBody).tape =
      endTape (finalValues problem index remaining hBody) (inside problem.input output) (exterior problem index remaining hBody) := rfl
theorem final_accept {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem) :
    (finalConfiguration problem index remaining output hBody).state = (machine problem.verifier).acceptState := rfl
theorem final_exterior {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem) :
    (finalConfiguration problem index remaining output hBody).tape.left = exterior problem index remaining hBody := rfl

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

def invalidSteps (code : Nat) : Nat :=
  BuilderUnaryTagMatch.workSteps 0 code + 1 + (BuilderUnaryTagMatch.workSteps 1 code + 1 +
    (BuilderUnaryTagMatch.workSteps 2 code + 1 + (BuilderUnaryTagMatch.workSteps 3 code + 1 +
      (BuilderUnaryTagMatch.workSteps 4 code + 1))))

/-- Corrupted dispatcher tags reject without entering any radix or payload writer. -/
theorem invalid_tag_workRunExact {language : Language} (verifier : PolynomialTimeVerifier language) (code : Nat)
    (older : List Nat) (workspace outside : List WorkSymbol) (hInvalid : 4 < code) :
    workRunExact? (machine verifier) (invalidSteps code)
      (WorkMachineProgramGraph.endpointConfiguration (.node (testNode verifier .shape).reference)
        (endTape (older ++ [code]) workspace outside)) =
      some {state := (machine verifier).rejectState, tape := endTape (older ++ [code]) workspace outside} := by
  have hNo4 := BuilderUnaryTagMatch.reject_workRunExact 4 code older workspace outside (by omega)
  have hPath4 := AcceptPath.stepReject (testNode verifier .accepting) .reject _ 0 _ _ _
    (test_mem verifier .accepting) hNo4 (.terminal .reject _)
  have hNo3 := BuilderUnaryTagMatch.reject_workRunExact 3 code older workspace outside (by omega)
  have hPath3 := AcceptPath.stepReject (testNode verifier .preservation) .reject _ _ _ _ _
    (test_mem verifier .preservation) hNo3 hPath4
  have hNo2 := BuilderUnaryTagMatch.reject_workRunExact 2 code older workspace outside (by omega)
  have hPath2 := AcceptPath.stepReject (testNode verifier .control) .reject _ _ _ _ _
    (test_mem verifier .control) hNo2 hPath3
  have hNo1 := BuilderUnaryTagMatch.reject_workRunExact 1 code older workspace outside (by omega)
  have hPath1 := AcceptPath.stepReject (testNode verifier .initial) .reject _ _ _ _ _
    (test_mem verifier .initial) hNo1 hPath2
  have hNo0 := BuilderUnaryTagMatch.reject_workRunExact 0 code older workspace outside (by omega)
  have hPath0 := AcceptPath.stepReject (testNode verifier .shape) .reject _ _ _ _ _
    (test_mem verifier .shape) hNo0 hPath1
  have h := WorkMachineProgramPath.runExact (graph verifier) _ _ _ _ _ (graph_wellFormed verifier) hPath0
  have hMachine : WorkMachineProgramGraph.machine (graph verifier) = machine verifier := rfl
  have hReject (tape : WorkTape) :
      WorkMachineProgramGraph.endpointConfiguration .reject tape = {state := (machine verifier).rejectState, tape := tape} := rfl
  rw [hMachine, hReject] at h
  simpa only [invalidSteps, Nat.add_zero] using h

private def sumRegions (f : Region → NatPolynomial) : NatPolynomial :=
  .add (f .shape) (.add (f .initial) (.add (f .control) (.add (f .preservation) (f .accepting))))
private theorem region_eval_le (f : Region → NatPolynomial) (region : Region) (input : Nat) :
    (f region).eval input ≤ (sumRegions f).eval input := by
  cases region <;> simp only [sumRegions, NatPolynomial.eval_add] <;> omega

def spanBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  sumRegions (BuilderFamilyPayload.spanBound verifier)
def rawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderConstraintRegionSource.rawTimeBound verifier)
    (.add (.constant 252) (sumRegions (BuilderFamilyPayload.rawTimeBound verifier)))

/-- Source construction, all tag tests, radix/payload work and bridges are charged.
The register/exterior result is bounded without assuming scratch was erased. -/
theorem source_polynomial_bounds {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    (registerWord (finalValues problem index remaining hBody)).length + (exterior problem index remaining hBody).length ≤
        (spanBound problem.verifier).eval problem.input.length ∧
      6 * workSteps problem index remaining hBody ≤ (rawTimeBound problem.verifier).eval problem.input.length := by
  have hRegion := selected_valid problem index hBody
  have hFamily := BuilderFamilyPayload.source_polynomial_bounds problem index remaining (selected problem index) hRegion hBody hBalance
  have hSpan := region_eval_le (BuilderFamilyPayload.spanBound problem.verifier) (selected problem index) problem.input.length
  have hTime := region_eval_le (BuilderFamilyPayload.rawTimeBound problem.verifier) (selected problem index) problem.input.length
  have hSource := BuilderConstraintRegionSource.rawTimeBound_le problem index remaining hBalance
  have hTests := testSteps_le (selected problem index)
  constructor
  · exact Nat.le_trans hFamily.1 hSpan
  · simp only [workSteps, rawTimeBound, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

end PNP.Concrete.CookLevin.BuilderSourcePayload
