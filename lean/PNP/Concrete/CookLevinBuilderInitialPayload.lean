/-
Copyright (c) 2026 PNP Labs.

Complete source-driven initial-family payload dispatch for both input modes.
Direct coordinate tests preserve the existing packet; verified leaf writers
construct state, head, length and cell payloads. Paired exhaustion is padding,
and the length writer's remaining blank exterior is retained explicitly.
Full five-region dispatch, emission and the packaged reduction remain open.
-/

import PNP.Concrete.CookLevinBuilderBoundaryPayload
import PNP.Concrete.CookLevinBuilderInitialLengthPayload
import PNP.Concrete.CookLevinBuilderInitialInputOnlySource
import PNP.Concrete.CookLevinBuilderInitialPairedCellPayload
import PNP.Concrete.CookLevinBuilderUnaryTagMatch

namespace PNP.Concrete.CookLevin.BuilderInitialPayload

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape inside)
open BuilderInitialPairedCellSource (selection)
open WorkMachineProgramGraph (Node Endpoint Graph)
open WorkMachineProgramPath (AcceptPath)

inductive Role where
  | state | head | length | pairedCells | inputCells
  deriving DecidableEq, Repr

def select (mode : InputMode) (coordinate : Nat) : Role :=
  if coordinate = 0 then .state
  else if coordinate = 1 then .head
  else if mode = .paired then
    if coordinate = 2 then .length else .pairedCells
  else .inputCells

def coordinate {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : Nat :=
  BuilderConstraintRegionSource.localCoordinate problem index .initial
def selectedRole {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : Role :=
  select problem.tableauInputMode (coordinate problem index)
def sourceFrame {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : List Nat :=
  BuilderLiteralArgumentSource.inputValues problem index remaining .initial []
def sourcePrefix {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : List Nat :=
  BuilderRegionRadixSource.selectedValues problem index remaining .initial

theorem source_suffix {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    sourceFrame problem index remaining = sourcePrefix problem index remaining ++ [coordinate problem index] := by
  have hRadices : BuilderRegionRadixSource.radices problem .initial = [] := rfl
  simp only [sourceFrame, BuilderLiteralArgumentSource.inputValues, BuilderRegionRadixSource.finalValues,
    hRadices, BuilderRegionRadixDecoder.finalValues, List.append_nil, sourcePrefix, coordinate]

theorem select_state (mode : InputMode) : select mode 0 = .state := rfl
theorem select_head (mode : InputMode) : select mode 1 = .head := rfl
theorem select_paired_length : select .paired 2 = .length := rfl
theorem select_input_cell (coordinate : Nat) (hCell : 2 ≤ coordinate) :
    select .inputOnly coordinate = .inputCells := by
  simp only [select, if_neg (by omega : coordinate ≠ 0), if_neg (by omega : coordinate ≠ 1)]
  rfl
theorem select_paired_cell (coordinate : Nat) (hCell : 3 ≤ coordinate) :
    select .paired coordinate = .pairedCells := by
  simp only [select, if_neg (by omega : coordinate ≠ 0), if_neg (by omega : coordinate ≠ 1),
    if_neg (by omega : coordinate ≠ 2), ite_true]

def pairedValues {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : List Nat :=
  match selection problem index with
  | none => BuilderInitialPairedCellPayload.finalValues problem index remaining ++ [1]
  | some _ => BuilderInitialPairedCellPayload.finalValues problem index remaining

def pairedPayload {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : List Nat :=
  match selection problem index with
  | none => [1]
  | some found => BuilderInitialPairedCellPayload.payloadValues problem found.1 found.2

theorem paired_suffix {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hPrefix : ¬ coordinate problem index < 3) :
    ∃ history : List Nat, pairedValues problem index remaining = history ++ pairedPayload problem index := by
  cases hFound : selection problem index with
  | none => exact ⟨BuilderInitialPairedCellPayload.finalValues problem index remaining,
      by simp only [pairedValues, pairedPayload, hFound]⟩
  | some found =>
      obtain ⟨history, h⟩ := BuilderInitialPairedCellPayload.found_suffix problem index remaining found.1 found.2 hPrefix hFound
      exact ⟨history, by simpa only [pairedValues, pairedPayload, hFound] using h⟩

private theorem initial_cells_values {language : Language} (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired) (cellCoordinate : Nat)
    (hCapacity : cellCoordinate + 1 < BuilderInitialConstraintPayload.symbolCapacity problem) :
    BuilderInitialConstraintPayload.values problem (cellCoordinate + 3) =
      ((BuilderInitialCellSelection.selectedInitialCell problem hMode cellCoordinate).bind
        (fun found => BuilderInitialConstraintPayload.pairedCellValues problem hMode found.1 found.2.1 found.2.2)).getD [1] := by
  change BuilderInitialConstraintPayload.values problem ((cellCoordinate + 1) + 2) = _
  simp only [BuilderInitialConstraintPayload.values, if_pos hCapacity, dif_pos hMode,
    BuilderInitialConstraintPayload.pairedSymbolsValues]

/-- The actual selected row and cell, including exhaustion, determine the canonical slot. -/
theorem paired_payload_canonical {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hMode : problem.tableauInputMode = .paired)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .initial)
    (hPrefix : ¬ coordinate problem index < 3) :
    pairedPayload problem index = BuilderInitialConstraintPayload.values problem (coordinate problem index) := by
  have hCapacity := BuilderInitialInputOnlySource.source_capacity problem index hRegion
  change coordinate problem index - 2 < BuilderInitialConstraintPayload.symbolCapacity problem at hCapacity
  have hCapacity' : (coordinate problem index - 3) + 1 < BuilderInitialConstraintPayload.symbolCapacity problem := by omega
  have hCoordinate : coordinate problem index = (coordinate problem index - 3) + 3 := by omega
  have hInitial : BuilderInitialConstraintPayload.values problem (coordinate problem index) =
      ((BuilderInitialCellSelection.selectedInitialCell problem hMode (coordinate problem index - 3)).bind
        (fun found => BuilderInitialConstraintPayload.pairedCellValues problem hMode found.1 found.2.1 found.2.2)).getD [1] :=
    (congrArg (BuilderInitialConstraintPayload.values problem) hCoordinate).trans
      (initial_cells_values problem hMode _ hCapacity')
  cases hFound : selection problem index with
  | none =>
      have hRow : BuilderInitialLengthSelection.selectedLength problem (coordinate problem index - 3) = none := hFound
      simpa only [pairedPayload, hFound, BuilderInitialCellSelection.selectedInitialCell,
        hRow, Option.bind_none, Option.getD_none] using hInitial.symm
  | some found =>
      rcases found with ⟨length, offset⟩
      have hRow : BuilderInitialLengthSelection.selectedLength problem (coordinate problem index - 3) =
          some (length, offset) := hFound
      obtain ⟨position, hPosition, hPayload⟩ :=
        BuilderInitialPairedCellPayload.selected_payload_canonical problem index hMode length offset hFound
      have hInside := (BuilderInitialLengthSelection.selectedLength_bounds problem (coordinate problem index - 3)
        length offset hRow).1
      have hCell : BuilderInitialCellSelection.selectedCell problem hMode length offset =
          some (position, (BuilderInitialPairedCellResolution.cell problem length offset).2) := by
        unfold BuilderInitialCellSelection.selectedCell BuilderInitialCellSelection.locate
        rw [dif_pos hInside]
        apply congrArg some
        apply Prod.ext
        · apply Fin.ext
          exact hPosition.symm
        · rfl
      have hSelected : BuilderInitialCellSelection.selectedInitialCell problem hMode (coordinate problem index - 3) =
          some (length, position, (BuilderInitialPairedCellResolution.cell problem length offset).2) := by
        simp only [BuilderInitialCellSelection.selectedInitialCell, hRow, Option.bind_some, hCell, Option.map_some]
      simpa only [pairedPayload, hFound, hSelected, Option.bind_some, hPayload, Option.getD_some] using hInitial.symm

def branchValues {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : Role → List Nat
  | .state => BuilderBoundaryPayload.finalValues problem index remaining .initialState
  | .head => BuilderBoundaryPayload.finalValues problem index remaining .initialHead
  | .length => BuilderInitialLengthPayload.finalValues problem index remaining
  | .pairedCells => pairedValues problem index remaining
  | .inputCells => BuilderInitialInputOnlySource.finalValues problem index remaining
def branchExterior {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : Role → List WorkSymbol
  | .length => BuilderInitialLengthPayload.exterior problem index
  | _ => []
def finalValues {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : List Nat :=
  branchValues problem index remaining (selectedRole problem index)
def exterior {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : List WorkSymbol :=
  branchExterior problem index (selectedRole problem index)

def paddingFields : List (BuilderRegisterPack.Field 0) := [.constant 1]
def paddingEnvironment : Fin 0 → Nat := Fin.elim0
def paddingSteps : Nat := BuilderRegisterPack.workSteps paddingFields paddingEnvironment []
def pairedSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : Nat :=
  BuilderInitialPairedCellPayload.workSteps problem index remaining + 1 +
    match selection problem index with | none => paddingSteps + 1 | some _ => 0
def branchSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : Role → Nat
  | .state => BuilderBoundaryPayload.workSteps problem index remaining .initialState + 1
  | .head => BuilderBoundaryPayload.workSteps problem index remaining .initialHead + 1
  | .length => BuilderInitialLengthPayload.workSteps problem index remaining + 1
  | .pairedCells => pairedSteps problem index remaining
  | .inputCells => BuilderInitialInputOnlySource.workSteps problem index remaining + 1
def afterHeadSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : Nat :=
  if problem.tableauInputMode = .paired then
    BuilderUnaryTagMatch.workSteps 2 (coordinate problem index) + 1 +
      if coordinate problem index = 2 then branchSteps problem index remaining .length
      else branchSteps problem index remaining .pairedCells
  else branchSteps problem index remaining .inputCells
def afterZeroSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : Nat :=
  BuilderUnaryTagMatch.workSteps 1 (coordinate problem index) + 1 +
    if coordinate problem index = 1 then branchSteps problem index remaining .head else afterHeadSteps problem index remaining
def testSteps (mode : InputMode) (coordinate : Nat) : Nat :=
  BuilderUnaryTagMatch.workSteps 0 coordinate + 1 +
    if coordinate = 0 then 0 else BuilderUnaryTagMatch.workSteps 1 coordinate + 1 +
      if coordinate = 1 then 0 else if mode = .paired then BuilderUnaryTagMatch.workSteps 2 coordinate + 1 else 0
def workSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : Nat :=
  BuilderUnaryTagMatch.workSteps 0 (coordinate problem index) + 1 +
    if coordinate problem index = 0 then branchSteps problem index remaining .state else afterZeroSteps problem index remaining

theorem workSteps_decomposition {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    workSteps problem index remaining = testSteps problem.tableauInputMode (coordinate problem index) +
      branchSteps problem index remaining (selectedRole problem index) := by
  by_cases h0 : coordinate problem index = 0
  · simp only [workSteps, testSteps, selectedRole, select, if_pos h0, Nat.add_zero]
  · by_cases h1 : coordinate problem index = 1
    · simp only [workSteps, testSteps, afterZeroSteps, selectedRole, select, if_neg h0, if_pos h1, Nat.add_zero, Nat.add_assoc]
    · by_cases hMode : problem.tableauInputMode = .paired
      · by_cases h2 : coordinate problem index = 2
        · simp only [workSteps, testSteps, afterZeroSteps, afterHeadSteps, selectedRole, select,
            if_neg h0, if_neg h1, if_pos hMode, if_pos h2, Nat.add_assoc]
        · simp only [workSteps, testSteps, afterZeroSteps, afterHeadSteps, selectedRole, select,
            if_neg h0, if_neg h1, if_pos hMode, if_neg h2, Nat.add_assoc]
      · simp only [workSteps, testSteps, afterZeroSteps, afterHeadSteps, selectedRole, select,
          if_neg h0, if_neg h1, if_neg hMode, Nat.add_zero, Nat.add_assoc]

theorem testSteps_le (mode : InputMode) (coordinate : Nat) : testSteps mode coordinate ≤ 18 := by
  have h0 := BuilderUnaryTagMatch.workSteps_le 0 coordinate
  have h1 := BuilderUnaryTagMatch.workSteps_le 1 coordinate
  have h2 := BuilderUnaryTagMatch.workSteps_le 2 coordinate
  simp only [testSteps]
  split
  · omega
  · split
    · omega
    · split <;> omega

def paddingNode : Node :=
  {name := 8, program := BuilderRegisterPack.machine paddingFields 0, onAccept := .accept, onReject := .dead}
def inputNode {language : Language} (verifier : PolynomialTimeVerifier language) : Node :=
  {name := 7, program := BuilderInitialInputOnlySource.machine verifier, onAccept := .accept, onReject := .dead}
def pairedNode {language : Language} (verifier : PolynomialTimeVerifier language) : Node :=
  {name := 6, program := BuilderInitialPairedCellPayload.machine verifier, onAccept := .accept,
   onReject := .node paddingNode.reference}
def lengthNode {language : Language} (verifier : PolynomialTimeVerifier language) : Node :=
  {name := 5, program := BuilderInitialLengthPayload.machine verifier, onAccept := .accept, onReject := .dead}
def headNode {language : Language} (verifier : PolynomialTimeVerifier language) : Node :=
  {name := 4, program := BuilderBoundaryPayload.machine verifier .initialHead, onAccept := .accept, onReject := .dead}
def stateNode {language : Language} (verifier : PolynomialTimeVerifier language) : Node :=
  {name := 3, program := BuilderBoundaryPayload.machine verifier .initialState, onAccept := .accept, onReject := .dead}
def twoNode {language : Language} (verifier : PolynomialTimeVerifier language) : Node :=
  {name := 2, program := BuilderUnaryTagMatch.machine 2, onAccept := .node (lengthNode verifier).reference,
   onReject := .node (pairedNode verifier).reference}
def afterHead {language : Language} (verifier : PolynomialTimeVerifier language) : Endpoint :=
  if inputModeOfVerifier verifier.program.inputMode = .paired then .node (twoNode verifier).reference else .node (inputNode verifier).reference
def oneNode {language : Language} (verifier : PolynomialTimeVerifier language) : Node :=
  {name := 1, program := BuilderUnaryTagMatch.machine 1, onAccept := .node (headNode verifier).reference,
   onReject := afterHead verifier}
def zeroNode {language : Language} (verifier : PolynomialTimeVerifier language) : Node :=
  {name := 0, program := BuilderUnaryTagMatch.machine 0, onAccept := .node (stateNode verifier).reference,
   onReject := .node (oneNode verifier).reference}
def graph {language : Language} (verifier : PolynomialTimeVerifier language) : Graph :=
  {nodes := [zeroNode verifier, oneNode verifier, twoNode verifier, stateNode verifier, headNode verifier,
    lengthNode verifier, pairedNode verifier, inputNode verifier, paddingNode],
   entry := (zeroNode verifier).reference}
def machine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineProgramGraph.machine (graph verifier)

theorem graph_nodes_length {language : Language} (verifier : PolynomialTimeVerifier language) :
    (graph verifier).nodes.length = 9 := rfl

private theorem zero_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    zeroNode verifier ∈ (graph verifier).nodes := List.Mem.head _

private theorem one_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    oneNode verifier ∈ (graph verifier).nodes := List.Mem.tail _ (List.Mem.head _)

private theorem two_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    twoNode verifier ∈ (graph verifier).nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

private theorem state_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    stateNode verifier ∈ (graph verifier).nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

private theorem head_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    headNode verifier ∈ (graph verifier).nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

private theorem length_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    lengthNode verifier ∈ (graph verifier).nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

private theorem paired_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    pairedNode verifier ∈ (graph verifier).nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))

private theorem input_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    inputNode verifier ∈ (graph verifier).nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))

private theorem padding_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    paddingNode ∈ (graph verifier).nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineProgramGraph.QueryDistinct ∧
    WorkMachineProgramGraph.NoRuleAt program program.acceptState ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧
    program.acceptState ≠ program.rejectState

private theorem tag_good (tag : Nat) : Good (BuilderUnaryTagMatch.machine tag) :=
  ⟨BuilderUnaryTagMatch.rules_pairwise_query_distinct tag, BuilderUnaryTagMatch.noRuleAtAccept tag,
    BuilderUnaryTagMatch.noRuleAtReject tag, BuilderUnaryTagMatch.acceptState_ne_rejectState tag⟩
private theorem boundary_good {language : Language} (verifier : PolynomialTimeVerifier language) (role : BuilderBoundaryPayload.Role) :
    Good (BuilderBoundaryPayload.machine verifier role) :=
  ⟨BuilderBoundaryPayload.rules_pairwise_query_distinct verifier role, BuilderBoundaryPayload.noRuleAtAccept verifier role,
    BuilderBoundaryPayload.noRuleAtReject verifier role, BuilderBoundaryPayload.acceptState_ne_rejectState verifier role⟩
private theorem length_good {language : Language} (verifier : PolynomialTimeVerifier language) :
    Good (BuilderInitialLengthPayload.machine verifier) :=
  ⟨BuilderInitialLengthPayload.rules_pairwise_query_distinct verifier, BuilderInitialLengthPayload.noRuleAtAccept verifier,
    BuilderInitialLengthPayload.noRuleAtReject verifier, BuilderInitialLengthPayload.acceptState_ne_rejectState verifier⟩
private theorem paired_good {language : Language} (verifier : PolynomialTimeVerifier language) :
    Good (BuilderInitialPairedCellPayload.machine verifier) :=
  ⟨BuilderInitialPairedCellPayload.rules_pairwise_query_distinct verifier, BuilderInitialPairedCellPayload.noRuleAtAccept verifier,
    BuilderInitialPairedCellPayload.noRuleAtReject verifier, BuilderInitialPairedCellPayload.acceptState_ne_rejectState verifier⟩
private theorem input_good {language : Language} (verifier : PolynomialTimeVerifier language) :
    Good (BuilderInitialInputOnlySource.machine verifier) :=
  ⟨BuilderInitialInputOnlySource.rules_pairwise_query_distinct verifier, BuilderInitialInputOnlySource.noRuleAtAccept verifier,
    BuilderInitialInputOnlySource.noRuleAtReject verifier, BuilderInitialInputOnlySource.acceptState_ne_rejectState verifier⟩
private theorem padding_good : Good (BuilderRegisterPack.machine paddingFields 0) :=
  ⟨BuilderRegisterPack.rules_pairwise_query_distinct paddingFields 0, BuilderRegisterPack.noRuleAtAccept paddingFields 0,
    BuilderRegisterPack.noRuleAtReject paddingFields 0, BuilderRegisterPack.acceptState_ne_rejectState paddingFields 0⟩

theorem graph_wellFormed {language : Language} (verifier : PolynomialTimeVerifier language) : (graph verifier).WellFormed := by
  have hNames : ((graph verifier).nodes.map Node.name).Pairwise (fun a b : Nat => a ≠ b) := by
    change ([0,1,2,3,4,5,6,7,8] : List Nat).Pairwise _
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.pairwise_map] using hNames
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact tag_good 0
    · exact tag_good 1
    · exact tag_good 2
    · exact boundary_good verifier .initialState
    · exact boundary_good verifier .initialHead
    · exact length_good verifier
    · exact paired_good verifier
    · exact input_good verifier
    · exact padding_good
  · exact ⟨zeroNode verifier, zero_mem verifier, rfl, rfl⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨stateNode verifier, state_mem verifier, rfl, rfl⟩, ⟨oneNode verifier, one_mem verifier, rfl, rfl⟩⟩
    · refine ⟨⟨headNode verifier, head_mem verifier, rfl, rfl⟩, ?_⟩
      by_cases hMode : inputModeOfVerifier verifier.program.inputMode = .paired
      · simp only [oneNode, afterHead, if_pos hMode]
        exact ⟨twoNode verifier, two_mem verifier, rfl, rfl⟩
      · simp only [oneNode, afterHead, if_neg hMode]
        exact ⟨inputNode verifier, input_mem verifier, rfl, rfl⟩
    · exact ⟨⟨lengthNode verifier, length_mem verifier, rfl, rfl⟩, ⟨pairedNode verifier, paired_mem verifier, rfl, rfl⟩⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨True.intro, ⟨paddingNode, padding_mem verifier, rfl, rfl⟩⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨True.intro, True.intro⟩

def initialConfiguration {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) : WorkConfiguration :=
  workStartConfiguration (machine problem.verifier) (endTape (sourceFrame problem index remaining) (inside problem.input output) [])
def finalConfiguration {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) : WorkConfiguration :=
  {state := (machine problem.verifier).acceptState,
   tape := endTape (finalValues problem index remaining) (inside problem.input output) (exterior problem index)}

/-- The existing coordinate is tested in place; there is no disposable copy. -/
theorem tag_accept {language : Language} (problem : VerifierTableauProblem language) (index remaining expected : Nat)
    (workspace outside : List WorkSymbol) (hValue : coordinate problem index = expected) :
    workRunExact? (BuilderUnaryTagMatch.machine expected) (BuilderUnaryTagMatch.workSteps expected (coordinate problem index))
      (workStartConfiguration (BuilderUnaryTagMatch.machine expected) (endTape (sourceFrame problem index remaining) workspace outside)) =
      some {state := (BuilderUnaryTagMatch.machine expected).acceptState, tape := endTape (sourceFrame problem index remaining) workspace outside} := by
  rw [source_suffix, hValue]
  exact BuilderUnaryTagMatch.accept_workRunExact expected (sourcePrefix problem index remaining) workspace outside

theorem tag_reject {language : Language} (problem : VerifierTableauProblem language) (index remaining expected : Nat)
    (workspace outside : List WorkSymbol) (hValue : coordinate problem index ≠ expected) :
    workRunExact? (BuilderUnaryTagMatch.machine expected) (BuilderUnaryTagMatch.workSteps expected (coordinate problem index))
      (workStartConfiguration (BuilderUnaryTagMatch.machine expected) (endTape (sourceFrame problem index remaining) workspace outside)) =
      some {state := (BuilderUnaryTagMatch.machine expected).rejectState, tape := endTape (sourceFrame problem index remaining) workspace outside} := by
  rw [source_suffix]
  exact BuilderUnaryTagMatch.reject_workRunExact expected (coordinate problem index) (sourcePrefix problem index remaining) workspace outside hValue

private theorem padding_run (older : List Nat) (workspace : List WorkSymbol) :
    workRunExact? (BuilderRegisterPack.machine paddingFields 0) paddingSteps
      (workStartConfiguration (BuilderRegisterPack.machine paddingFields 0) (endTape older workspace [])) =
      some {state := (BuilderRegisterPack.machine paddingFields 0).acceptState, tape := endTape (older ++ [1]) workspace []} := by
  have hEnv : List.ofFn paddingEnvironment = [] := rfl
  have hFields : BuilderRegisterPack.values paddingFields paddingEnvironment = [1] := rfl
  have h := BuilderRegisterPack.workRunExact paddingFields 0 older paddingEnvironment [] workspace [] rfl
  simpa only [BuilderRegisterPack.initialConfiguration, BuilderRegisterPack.finalConfiguration, hEnv, hFields,
    List.append_nil, List.drop_nil, paddingSteps] using h

private theorem state_path {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) :
    AcceptPath (graph problem.verifier) (.node (stateNode problem.verifier).reference) .accept
      (branchSteps problem index remaining .state)
      (endTape (sourceFrame problem index remaining) (inside problem.input output) [])
      (endTape (branchValues problem index remaining .state) (inside problem.input output) (branchExterior problem index .state)) := by
  have hRun := BuilderBoundaryPayload.workRunExact problem index remaining .initialState (inside problem.input output) []
  simp only [BuilderBoundaryPayload.initialConfiguration, BuilderBoundaryPayload.finalConfiguration,
    BuilderBoundaryPayload.finalOutside_nil] at hRun
  have h := AcceptPath.step (stateNode problem.verifier) .accept _ 0 _ _ _ (state_mem problem.verifier) hRun (.terminal .accept _)
  simpa only [branchSteps, branchValues, branchExterior, sourceFrame, BuilderBoundaryPayload.region, Nat.add_zero] using h

private theorem head_path {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) :
    AcceptPath (graph problem.verifier) (.node (headNode problem.verifier).reference) .accept
      (branchSteps problem index remaining .head)
      (endTape (sourceFrame problem index remaining) (inside problem.input output) [])
      (endTape (branchValues problem index remaining .head) (inside problem.input output) (branchExterior problem index .head)) := by
  have hRun := BuilderBoundaryPayload.workRunExact problem index remaining .initialHead (inside problem.input output) []
  simp only [BuilderBoundaryPayload.initialConfiguration, BuilderBoundaryPayload.finalConfiguration,
    BuilderBoundaryPayload.finalOutside_nil] at hRun
  have h := AcceptPath.step (headNode problem.verifier) .accept _ 0 _ _ _ (head_mem problem.verifier) hRun (.terminal .accept _)
  simpa only [branchSteps, branchValues, branchExterior, sourceFrame, BuilderBoundaryPayload.region, Nat.add_zero] using h

private theorem length_path {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) :
    AcceptPath (graph problem.verifier) (.node (lengthNode problem.verifier).reference) .accept
      (branchSteps problem index remaining .length)
      (endTape (sourceFrame problem index remaining) (inside problem.input output) [])
      (endTape (branchValues problem index remaining .length) (inside problem.input output) (branchExterior problem index .length)) := by
  have hRun := BuilderInitialLengthPayload.workRunExact problem index remaining (inside problem.input output)
  simp only [BuilderInitialLengthPayload.initialConfiguration, BuilderInitialLengthPayload.finalConfiguration] at hRun
  have h := AcceptPath.step (lengthNode problem.verifier) .accept _ 0 _ _ _ (length_mem problem.verifier) hRun (.terminal .accept _)
  simpa only [branchSteps, branchValues, branchExterior, sourceFrame, Nat.add_zero] using h

private theorem input_path {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hPrefix : ¬ coordinate problem index < 2) :
    AcceptPath (graph problem.verifier) (.node (inputNode problem.verifier).reference) .accept
      (branchSteps problem index remaining .inputCells)
      (endTape (sourceFrame problem index remaining) (inside problem.input output) [])
      (endTape (branchValues problem index remaining .inputCells) (inside problem.input output) (branchExterior problem index .inputCells)) := by
  have hData : ¬ (BuilderInitialInputOnlySource.data problem index).coordinate < 2 := hPrefix
  have hRun := BuilderInitialInputOnlySource.workRunExact problem index remaining output
  simp only [BuilderInitialInputOnlySource.initialConfiguration, BuilderInitialInputOnlySource.finalConfiguration,
    BuilderInitialInputOnlyPayload.endpoint, if_neg hData] at hRun
  have h := AcceptPath.step (inputNode problem.verifier) .accept _ 0 _ _ _ (input_mem problem.verifier) hRun (.terminal .accept _)
  simpa only [branchSteps, branchValues, branchExterior, sourceFrame, BuilderInitialInputOnlySource.sourceFrame, Nat.add_zero] using h

private theorem paired_path {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hMode : problem.tableauInputMode = .paired) (hPrefix : ¬ coordinate problem index < 3) :
    AcceptPath (graph problem.verifier) (.node (pairedNode problem.verifier).reference) .accept
      (branchSteps problem index remaining .pairedCells)
      (endTape (sourceFrame problem index remaining) (inside problem.input output) [])
      (endTape (branchValues problem index remaining .pairedCells) (inside problem.input output) (branchExterior problem index .pairedCells)) := by
  have hPrefix' : ¬ BuilderInitialPairedCellSource.coordinate problem index < 3 := hPrefix
  have hRun := BuilderInitialPairedCellPayload.workRunExact problem index remaining output hMode
  simp only [BuilderInitialPairedCellPayload.initialConfiguration, BuilderInitialPairedCellPayload.finalConfiguration,
    BuilderInitialPairedCellPayload.endpoint_selection, if_neg hPrefix'] at hRun
  cases hFound : selection problem index with
  | none =>
      simp only [hFound] at hRun
      have hPadding := padding_run (BuilderInitialPairedCellPayload.finalValues problem index remaining) (inside problem.input output)
      have hP := AcceptPath.step paddingNode .accept _ 0 _ _ _ (padding_mem problem.verifier) hPadding (.terminal .accept _)
      have h := AcceptPath.stepReject (pairedNode problem.verifier) .accept _ _ _ _ _ (paired_mem problem.verifier) hRun hP
      simpa only [branchSteps, pairedSteps, pairedValues, branchValues, branchExterior, hFound,
        sourceFrame, BuilderInitialPairedCellSource.sourceFrame, Nat.add_zero] using h
  | some found =>
      simp only [hFound] at hRun
      have h := AcceptPath.step (pairedNode problem.verifier) .accept _ 0 _ _ _ (paired_mem problem.verifier) hRun (.terminal .accept _)
      simpa only [branchSteps, pairedSteps, pairedValues, branchValues, branchExterior, hFound,
        sourceFrame, BuilderInitialPairedCellSource.sourceFrame, Nat.add_zero] using h

private theorem after_head_path {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (h0 : coordinate problem index ≠ 0) (h1 : coordinate problem index ≠ 1) :
    AcceptPath (graph problem.verifier) (afterHead problem.verifier) .accept (afterHeadSteps problem index remaining)
      (endTape (sourceFrame problem index remaining) (inside problem.input output) [])
      (endTape (finalValues problem index remaining) (inside problem.input output) (exterior problem index)) := by
  by_cases hMode : problem.tableauInputMode = .paired
  · have hStatic : inputModeOfVerifier problem.verifier.program.inputMode = .paired := hMode
    by_cases h2 : coordinate problem index = 2
    · have hTag := tag_accept problem index remaining 2 (inside problem.input output) [] h2
      have hTail := length_path problem index remaining output
      have h := AcceptPath.step (twoNode problem.verifier) .accept _ _ _ _ _ (two_mem problem.verifier) hTag hTail
      simpa only [afterHead, if_pos hStatic, afterHeadSteps, finalValues, exterior, selectedRole, select,
        if_neg h0, if_neg h1, if_pos hMode, if_pos h2] using h
    · have hTag := tag_reject problem index remaining 2 (inside problem.input output) [] h2
      have hTail := paired_path problem index remaining output hMode (by omega)
      have h := AcceptPath.stepReject (twoNode problem.verifier) .accept _ _ _ _ _ (two_mem problem.verifier) hTag hTail
      simpa only [afterHead, if_pos hStatic, afterHeadSteps, finalValues, exterior, selectedRole, select,
        if_neg h0, if_neg h1, if_pos hMode, if_neg h2] using h
  · have hStatic : inputModeOfVerifier problem.verifier.program.inputMode ≠ .paired := hMode
    have h := input_path problem index remaining output (by omega)
    simpa only [afterHead, if_neg hStatic, afterHeadSteps, finalValues, exterior, selectedRole, select,
      if_neg h0, if_neg h1, if_neg hMode] using h

private theorem after_zero_path {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (h0 : coordinate problem index ≠ 0) :
    AcceptPath (graph problem.verifier) (.node (oneNode problem.verifier).reference) .accept (afterZeroSteps problem index remaining)
      (endTape (sourceFrame problem index remaining) (inside problem.input output) [])
      (endTape (finalValues problem index remaining) (inside problem.input output) (exterior problem index)) := by
  by_cases h1 : coordinate problem index = 1
  · have hTag := tag_accept problem index remaining 1 (inside problem.input output) [] h1
    have hTail := head_path problem index remaining output
    have h := AcceptPath.step (oneNode problem.verifier) .accept _ _ _ _ _ (one_mem problem.verifier) hTag hTail
    simpa only [afterZeroSteps, finalValues, exterior, selectedRole, select, if_neg h0, if_pos h1] using h
  · have hTag := tag_reject problem index remaining 1 (inside problem.input output) [] h1
    have hTail := after_head_path problem index remaining output h0 h1
    have h := AcceptPath.stepReject (oneNode problem.verifier) .accept _ _ _ _ _ (one_mem problem.verifier) hTag hTail
    simpa only [afterZeroSteps, if_neg h1] using h

theorem workRunExact {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
      (initialConfiguration problem index remaining output) = some (finalConfiguration problem index remaining output) := by
  have hPath : AcceptPath (graph problem.verifier) (.node (zeroNode problem.verifier).reference) .accept
      (workSteps problem index remaining)
      (endTape (sourceFrame problem index remaining) (inside problem.input output) [])
      (endTape (finalValues problem index remaining) (inside problem.input output) (exterior problem index)) := by
    by_cases h0 : coordinate problem index = 0
    · have hTag := tag_accept problem index remaining 0 (inside problem.input output) [] h0
      have hTail := state_path problem index remaining output
      have h := AcceptPath.step (zeroNode problem.verifier) .accept _ _ _ _ _ (zero_mem problem.verifier) hTag hTail
      simpa only [workSteps, finalValues, exterior, selectedRole, select, if_pos h0] using h
    · have hTag := tag_reject problem index remaining 0 (inside problem.input output) [] h0
      have hTail := after_zero_path problem index remaining output h0
      have h := AcceptPath.stepReject (zeroNode problem.verifier) .accept _ _ _ _ _ (zero_mem problem.verifier) hTag hTail
      simpa only [workSteps, if_neg h0] using h
  have h := WorkMachineProgramPath.runExact (graph problem.verifier) _ _ _ _ _ (graph_wellFormed problem.verifier) hPath
  have hStart (tape : WorkTape) :
      WorkMachineProgramGraph.endpointConfiguration (.node (zeroNode problem.verifier).reference) tape =
        workStartConfiguration (machine problem.verifier) tape := rfl
  have hMachine : WorkMachineProgramGraph.machine (graph problem.verifier) = machine problem.verifier := rfl
  have hAccept (tape : WorkTape) :
      WorkMachineProgramGraph.endpointConfiguration .accept tape = {state := (machine problem.verifier).acceptState, tape := tape} := rfl
  rw [hStart, hMachine, hAccept] at h
  simpa only [initialConfiguration, finalConfiguration] using h

theorem run_compile_exact {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining)
      (encodeWorkConfiguration (initialConfiguration problem index remaining output)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining output) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact problem index remaining output)

theorem final_tape {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) :
    (finalConfiguration problem index remaining output).tape =
      endTape (finalValues problem index remaining) (inside problem.input output) (exterior problem index) := rfl
theorem final_accept {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) : (finalConfiguration problem index remaining output).state = (machine problem.verifier).acceptState := rfl
theorem final_exterior {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) : (finalConfiguration problem index remaining output).tape.left = exterior problem index := rfl
theorem length_exterior {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hMode : problem.tableauInputMode = .paired) (hCoordinate : coordinate problem index = 2) :
    exterior problem index = BuilderInitialLengthPayload.exterior problem index := by
  simp only [exterior, selectedRole, hCoordinate, select_paired_length, hMode, branchExterior]
theorem nonlength_exterior {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRole : selectedRole problem index ≠ .length) : exterior problem index = [] := by
  cases h : selectedRole problem index <;> simp only [exterior, h, branchExterior]
  exact (hRole h).elim

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

def branchPayload {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : Role → List Nat
  | .state => BuilderBoundaryPayload.payloadValues problem index .initialState
  | .head => BuilderBoundaryPayload.payloadValues problem index .initialHead
  | .length => BuilderInitialLengthPayload.payloadValues problem index
  | .pairedCells => pairedPayload problem index
  | .inputCells => BuilderInitialInputOnlySource.payloadValues problem index
def payloadValues {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : List Nat :=
  branchPayload problem index (selectedRole problem index)

/-- Every runtime-selected branch ends in its computed payload, without a supplied history. -/
theorem final_has_suffix {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    ∃ older : List Nat, finalValues problem index remaining = older ++ payloadValues problem index := by
  by_cases h0 : coordinate problem index = 0
  · simp only [finalValues, payloadValues, selectedRole, select, if_pos h0, branchValues, branchPayload]
    exact ⟨_, rfl⟩
  · by_cases h1 : coordinate problem index = 1
    · simp only [finalValues, payloadValues, selectedRole, select, if_neg h0, if_pos h1, branchValues, branchPayload]
      exact ⟨_, rfl⟩
    · by_cases hMode : problem.tableauInputMode = .paired
      · by_cases h2 : coordinate problem index = 2
        · simp only [finalValues, payloadValues, selectedRole, select, if_neg h0, if_neg h1, if_pos hMode,
            if_pos h2, branchValues, branchPayload]
          exact ⟨_, BuilderInitialLengthPayload.final_suffix problem index remaining⟩
        · simp only [finalValues, payloadValues, selectedRole, select, if_neg h0, if_neg h1, if_pos hMode,
            if_neg h2, branchValues, branchPayload]
          exact paired_suffix problem index remaining (by omega)
      · simp only [finalValues, payloadValues, selectedRole, select, if_neg h0, if_neg h1, if_neg hMode,
          branchValues, branchPayload]
        exact ⟨_, BuilderInitialInputOnlySource.final_suffix problem index remaining (by
          change ¬ coordinate problem index < 2
          omega)⟩

def history {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : List Nat :=
  (finalValues problem index remaining).take
    ((finalValues problem index remaining).length - (payloadValues problem index).length)

theorem final_suffix {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    finalValues problem index remaining = history problem index remaining ++ payloadValues problem index := by
  obtain ⟨older, h⟩ := final_has_suffix problem index remaining
  have hHistory : history problem index remaining = older := by
    simp only [history, h, List.length_append, Nat.add_sub_cancel, List.take_left]
  rw [hHistory]
  exact h

theorem payload_canonical {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .initial) :
    payloadValues problem index = BuilderInitialConstraintPayload.values problem (coordinate problem index) := by
  by_cases h0 : coordinate problem index = 0
  · simp only [payloadValues, selectedRole, select, if_pos h0, branchPayload, h0]
    exact BuilderBoundaryPayload.initial_state_payload problem index
  · by_cases h1 : coordinate problem index = 1
    · simp only [payloadValues, selectedRole, select, if_neg h0, if_pos h1, branchPayload, h1]
      exact BuilderBoundaryPayload.initial_head_payload problem index
    · by_cases hMode : problem.tableauInputMode = .paired
      · by_cases h2 : coordinate problem index = 2
        · simp only [payloadValues, selectedRole, select, if_neg h0, if_neg h1, if_pos hMode, if_pos h2,
            branchPayload, h2]
          exact BuilderInitialLengthPayload.payload_initial_slot problem index hMode
        · simp only [payloadValues, selectedRole, select, if_neg h0, if_neg h1, if_pos hMode, if_neg h2, branchPayload]
          exact paired_payload_canonical problem index hMode hRegion (by omega)
      · simp only [payloadValues, selectedRole, select, if_neg h0, if_neg h1, if_neg hMode, branchPayload]
        exact BuilderInitialInputOnlySource.payload_canonical problem index hMode hRegion (by
          change ¬ coordinate problem index < 2
          omega)

theorem payload_decode {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .initial) :
    BuilderLocalConstraintPayload.decode problem.FormulaWidth (payloadValues problem index) =
      some (problem.initialConstraintSlotDirect (coordinate problem index)) := by
  rw [payload_canonical problem index hRegion, BuilderInitialConstraintPayload.decode_values]

theorem whole_formula_payload {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .initial) :
    payloadValues problem index = BuilderLocalConstraintPayload.values
      (problem.formulaConstraintSlotDirect (BuilderClauseDividerExecution.constraintIndex problem index)) := by
  rw [payload_canonical problem index hRegion, BuilderInitialConstraintPayload.values_canonical,
    ← BuilderConstraintRegionSource.regionSlot_eq problem index .initial hRegion]
  rfl

/-- Complete initial-family construction from the actual source packet and input. -/
theorem source_canonical_payload {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .initial) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
      (initialConfiguration problem index remaining output) =
      some
        {state := (machine problem.verifier).acceptState,
         tape := endTape (history problem index remaining ++ BuilderLocalConstraintPayload.values
           (problem.formulaConstraintSlotDirect (BuilderClauseDividerExecution.constraintIndex problem index)))
           (inside problem.input output) (exterior problem index)} := by
  have h := workRunExact problem index remaining output
  rw [finalConfiguration, final_suffix problem index remaining, whole_formula_payload problem index hRegion] at h
  exact h

def pairedSourceSpan {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  BuilderInitialPairedCellPayload.spanPolynomial verifier (BuilderInitialPairedCellSource.sourceBound verifier)
def pairedSourceTime {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  BuilderInitialPairedCellPayload.rawTimePolynomial verifier (BuilderInitialPairedCellSource.sourceBound verifier)
def pairedSpan {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (pairedSourceSpan verifier) (BuilderRegisterPack.spanPolynomial paddingFields (pairedSourceSpan verifier))
def pairedTime {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (pairedSourceTime verifier)
    (.add (BuilderRegisterPack.rawTimePolynomial paddingFields (pairedSourceSpan verifier)) (.constant 12))

theorem paired_polynomial_bounds {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hMode : problem.tableauInputMode = .paired)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .initial) :
    (registerWord (pairedValues problem index remaining)).length ≤ (pairedSpan problem.verifier).eval problem.input.length ∧
      6 * pairedSteps problem index remaining ≤ (pairedTime problem.verifier).eval problem.input.length := by
  have hSource := BuilderInitialPairedCellPayload.source_polynomial_bounds problem index remaining hMode hBody hBalance hRegion
  have hSpan : (registerWord (BuilderInitialPairedCellPayload.finalValues problem index remaining)).length ≤
      (pairedSourceSpan problem.verifier).eval problem.input.length := hSource.1
  have hTime : 6 * BuilderInitialPairedCellPayload.workSteps problem index remaining ≤
      (pairedSourceTime problem.verifier).eval problem.input.length := hSource.2
  cases hFound : selection problem index with
  | none =>
      have hEnv : List.ofFn paddingEnvironment = [] := rfl
      have hFields : BuilderRegisterPack.values paddingFields paddingEnvironment = [1] := rfl
      have hPack := BuilderRegisterPack.source_polynomial_bounds paddingFields (pairedSourceSpan problem.verifier)
        problem.input.length (BuilderInitialPairedCellPayload.finalValues problem index remaining) paddingEnvironment [] (by
          simpa only [hEnv, List.append_nil] using hSpan)
      simp only [hEnv, hFields, List.append_nil] at hPack
      have hPaddingTime : 6 * paddingSteps ≤
          (BuilderRegisterPack.rawTimePolynomial paddingFields (pairedSourceSpan problem.verifier)).eval problem.input.length := hPack.2
      constructor
      · simp only [pairedValues, hFound, pairedSpan, NatPolynomial.eval_add]
        omega
      · simp only [pairedSteps, hFound, pairedTime, NatPolynomial.eval_add, NatPolynomial.eval_constant, Nat.mul_add, Nat.mul_one]
        omega
  | some found =>
      constructor
      · simp only [pairedValues, hFound, pairedSpan, NatPolynomial.eval_add]
        omega
      · simp only [pairedSteps, hFound, pairedTime, NatPolynomial.eval_add, NatPolynomial.eval_constant]
        omega

def branchSpan {language : Language} (verifier : PolynomialTimeVerifier language) : Role → NatPolynomial
  | .state => BuilderBoundaryPayload.spanPolynomial verifier .initialState
  | .head => BuilderBoundaryPayload.spanPolynomial verifier .initialHead
  | .length => BuilderInitialLengthPayload.spanPolynomial verifier
  | .pairedCells => pairedSpan verifier
  | .inputCells => BuilderInitialInputOnlySource.spanPolynomial verifier
def branchTime {language : Language} (verifier : PolynomialTimeVerifier language) : Role → NatPolynomial
  | .state => .add (BuilderBoundaryPayload.rawTimePolynomial verifier .initialState) (.constant 6)
  | .head => .add (BuilderBoundaryPayload.rawTimePolynomial verifier .initialHead) (.constant 6)
  | .length => .add (BuilderInitialLengthPayload.rawTimePolynomial verifier) (.constant 6)
  | .pairedCells => pairedTime verifier
  | .inputCells => .add (BuilderInitialInputOnlySource.rawTimePolynomial verifier) (.constant 6)

theorem branch_polynomial_bounds {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (role : Role) (hMode : role = .pairedCells → problem.tableauInputMode = .paired)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .initial) :
    (registerWord (branchValues problem index remaining role)).length + (branchExterior problem index role).length ≤
        (branchSpan problem.verifier role).eval problem.input.length ∧
      6 * branchSteps problem index remaining role ≤ (branchTime problem.verifier role).eval problem.input.length := by
  cases role with
  | state =>
      have h := BuilderBoundaryPayload.source_polynomial_bounds problem index remaining .initialState hBody hBalance hRegion
      simp only [branchValues, branchExterior, branchSpan, branchSteps, branchTime, List.length_nil, Nat.add_zero,
        NatPolynomial.eval_add, NatPolynomial.eval_constant]
      constructor
      · exact h.1
      · omega
  | head =>
      have h := BuilderBoundaryPayload.source_polynomial_bounds problem index remaining .initialHead hBody hBalance hRegion
      simp only [branchValues, branchExterior, branchSpan, branchSteps, branchTime, List.length_nil, Nat.add_zero,
        NatPolynomial.eval_add, NatPolynomial.eval_constant]
      constructor
      · exact h.1
      · omega
  | length =>
      have h := BuilderInitialLengthPayload.source_polynomial_bounds problem index remaining hBody hBalance hRegion
      simp only [branchValues, branchExterior, branchSpan, branchSteps, branchTime,
        NatPolynomial.eval_add, NatPolynomial.eval_constant]
      constructor
      · exact h.1
      · omega
  | pairedCells =>
      simpa only [branchValues, branchExterior, branchSpan, branchSteps, branchTime, List.length_nil, Nat.add_zero] using
        paired_polynomial_bounds problem index remaining (hMode rfl) hBody hBalance hRegion
  | inputCells =>
      have h := BuilderInitialInputOnlySource.source_polynomial_bounds problem index remaining hBody hBalance hRegion
      simp only [branchValues, branchExterior, branchSpan, branchSteps, branchTime, List.length_nil, Nat.add_zero,
        NatPolynomial.eval_add, NatPolynomial.eval_constant]
      constructor
      · exact h.1
      · omega

private def sumBranches (f : Role → NatPolynomial) : NatPolynomial :=
  .add (f .state) (.add (f .head) (.add (f .length) (.add (f .pairedCells) (f .inputCells))))
private theorem branch_eval_le (f : Role → NatPolynomial) (role : Role) (n : Nat) :
    (f role).eval n ≤ (sumBranches f).eval n := by
  cases role <;> simp only [sumBranches, NatPolynomial.eval_add] <;> omega

def spanPolynomial {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  sumBranches (branchSpan verifier)
def rawTimePolynomial {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (.constant 108) (sumBranches (branchTime verifier))

private theorem selected_paired_mode {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRole : selectedRole problem index = .pairedCells) : problem.tableauInputMode = .paired := by
  by_cases hMode : problem.tableauInputMode = .paired
  · exact hMode
  · have hImpossible : selectedRole problem index ≠ .pairedCells := by
      unfold selectedRole select
      simp only [if_neg hMode]
      split
      · decide
      · split <;> decide
    exact (hImpossible hRole).elim

/-- All source-selected branches, retained scratch, remaining exterior, tests,
padding and graph bridges have uniform encoded-source-size polynomial bounds. -/
theorem source_polynomial_bounds {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .initial) :
    (registerWord (finalValues problem index remaining)).length + (exterior problem index).length ≤
        (spanPolynomial problem.verifier).eval problem.input.length ∧
      6 * workSteps problem index remaining ≤ (rawTimePolynomial problem.verifier).eval problem.input.length := by
  have hBranch := branch_polynomial_bounds problem index remaining (selectedRole problem index)
    (selected_paired_mode problem index) hBody hBalance hRegion
  have hSpan := branch_eval_le (branchSpan problem.verifier) (selectedRole problem index) problem.input.length
  have hTime := branch_eval_le (branchTime problem.verifier) (selectedRole problem index) problem.input.length
  have hTests := testSteps_le problem.tableauInputMode (coordinate problem index)
  constructor
  · change _ ≤ (sumBranches (branchSpan problem.verifier)).eval problem.input.length
    exact Nat.le_trans hBranch.1 hSpan
  · rw [workSteps_decomposition, rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

end PNP.Concrete.CookLevin.BuilderInitialPayload
