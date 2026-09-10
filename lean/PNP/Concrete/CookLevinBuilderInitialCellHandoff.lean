/-
Copyright (c) 2026 PNP Labs.

A fixed branch-aware wrapper retains actual source/row metadata through the
complete initial-cell decoder. Every return path leaves the same seven-register
suffix. Routing, copies, the unchanged decoder and bridges are charged.
Actual source-packet preparation and payload writing remain separate integration
obligations; no complete formula-builder or global-runtime claim is made here.
-/
import PNP.Concrete.CookLevinBuilderInitialCellDecoder

namespace PNP.Concrete.CookLevin.BuilderInitialCellHandoff

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderArbitrarySlotHeaderRouter
open BuilderInitialCellDecoder (comparisonValues residual recovery)
open WorkMachineProgramGraph (Node Endpoint Graph)
open WorkMachineProgramPath (AcceptPath)

structure Metadata where
  inputLength : Nat
  fuel : Nat
  length : Nat
  rowWidth : Nat
  remaining : Nat
  deriving DecidableEq, Repr

def Metadata.values (metadata : Metadata) : List Nat :=
  [metadata.inputLength, metadata.fuel, metadata.length, metadata.rowWidth, metadata.remaining]

inductive Branch where
  | before | middle | after
  deriving DecidableEq, Repr

def upper (metadata : Metadata) (start : Nat) : Nat := start + (metadata.length + metadata.length)
def selectedBranch (metadata : Metadata) (start coordinate : Nat) : Branch :=
  if coordinate < start then .before else if coordinate < upper metadata start then .middle else .after

def frame (metadata : Metadata) (start coordinate : Nat) : List Nat :=
  metadata.values ++ [start, coordinate]
def firstValues (metadata : Metadata) (start coordinate : Nat) : List Nat :=
  frame metadata start coordinate ++ comparisonValues coordinate start
def upperValues (metadata : Metadata) (start : Nat) : List Nat :=
  [start, metadata.length, metadata.length, metadata.length + metadata.length, upper metadata start]
def secondValues (metadata : Metadata) (start coordinate : Nat) : List Nat :=
  firstValues metadata start coordinate ++ upperValues metadata start ++
    comparisonValues coordinate (upper metadata start)
def baseCount : Branch → Nat | .before => 12 | .middle => 22 | .after => 22
def baseValues (branch : Branch) (metadata : Metadata) (start coordinate : Nat) : List Nat :=
  match branch with | .before => firstValues metadata start coordinate | _ => secondValues metadata start coordinate
def decodedValues (branch : Branch) (metadata : Metadata) (start coordinate : Nat) : List Nat :=
  match branch with
  | .before => BuilderInitialCellDecoder.beforeOutput start metadata.length coordinate
  | .middle => BuilderInitialCellDecoder.middleOutput start metadata.length coordinate
  | .after => BuilderInitialCellDecoder.afterOutput start metadata.length coordinate
def resultCount : Branch → Nat | .before => 22 | .middle => 51 | .after => 45
def resultFrame (branch : Branch) (metadata : Metadata) (start coordinate : Nat) : List Nat :=
  baseValues branch metadata start coordinate ++ decodedValues branch metadata start coordinate
def branchPair (branch : Branch) (metadata : Metadata) (start coordinate : Nat) : List Nat :=
  match branch with
  | .before => [residual coordinate start, 0]
  | .middle => [start + BuilderInitialCellDecoder.secondResidual start metadata.length coordinate / 2,
      BuilderInitialCellDecoder.secondResidual start metadata.length coordinate % 2]
  | .after => [start + metadata.length + BuilderInitialCellDecoder.secondResidual start metadata.length coordinate, 0]
def branchResult (branch : Branch) (metadata : Metadata) (start coordinate : Nat) : List Nat :=
  metadata.values ++ branchPair branch metadata start coordinate
def carriedValues (metadata : Metadata) (start coordinate : Nat) : List Nat :=
  metadata.values ++ [(BuilderInitialCellSelection.cellCoordinate start metadata.length coordinate).1,
    (BuilderInitialCellSelection.cellCoordinate start metadata.length coordinate).2]
def outputValues (metadata : Metadata) (start coordinate : Nat) : List Nat :=
  let branch := selectedBranch metadata start coordinate
  resultFrame branch metadata start coordinate ++ carriedValues metadata start coordinate

def firstFields : List (BuilderRegisterPack.Field 7) :=
  [.argument ⟨6, by decide⟩, .argument ⟨5, by decide⟩]
def upperExpression : BuilderRegisterExpression.Expr 12 :=
  .binary .add (.argument ⟨5, by decide⟩)
    (.binary .add (.argument ⟨2, by decide⟩) (.argument ⟨2, by decide⟩))
def secondFields : List (BuilderRegisterPack.Field 17) :=
  [.argument ⟨6, by decide⟩, .argument ⟨16, by decide⟩]
def decoderFields (branch : Branch) : List (BuilderRegisterPack.Field (baseCount branch)) :=
  [.argument ⟨5, by cases branch <;> decide⟩, .argument ⟨2, by cases branch <;> decide⟩,
    .argument ⟨6, by cases branch <;> decide⟩]
def carryFields (branch : Branch) : List (BuilderRegisterPack.Field (resultCount branch)) :=
  [.argument ⟨0, by cases branch <;> decide⟩, .argument ⟨1, by cases branch <;> decide⟩,
   .argument ⟨2, by cases branch <;> decide⟩, .argument ⟨3, by cases branch <;> decide⟩,
   .argument ⟨4, by cases branch <;> decide⟩,
   .argument ⟨resultCount branch - 2, by cases branch <;> decide⟩,
   .argument ⟨resultCount branch - 1, by cases branch <;> decide⟩]

theorem frame_length (metadata : Metadata) (start coordinate : Nat) : (frame metadata start coordinate).length = 7 := rfl
theorem carriedValues_length (metadata : Metadata) (start coordinate : Nat) :
    (carriedValues metadata start coordinate).length = 7 := rfl
theorem baseValues_length (branch : Branch) (metadata : Metadata) (start coordinate : Nat) :
    (baseValues branch metadata start coordinate).length = baseCount branch := by cases branch <;> rfl
theorem resultFrame_length (branch : Branch) (metadata : Metadata) (start coordinate : Nat) :
    (resultFrame branch metadata start coordinate).length = resultCount branch := by cases branch <;> rfl

private def environment {arity : Nat} (data : List Nat) (index : Fin arity) : Nat :=
  data[index.val]?.getD 0

private theorem environment_ofFn {arity : Nat} (data : List Nat) (hLength : data.length = arity) :
    List.ofFn (environment data : Fin arity → Nat) = data := by
  subst arity
  have h : (environment data : Fin data.length → Nat) = fun index => data[index.val] := by
    funext index
    simp only [environment, List.getElem?_eq_getElem index.isLt, Option.getD_some]
  rw [h]
  exact List.ofFn_getElem

private theorem first_values (metadata : Metadata) (start coordinate : Nat) :
    BuilderRegisterPack.values firstFields (environment (frame metadata start coordinate)) = [coordinate, start] := rfl
private theorem upper_values (metadata : Metadata) (start coordinate : Nat) :
    BuilderRegisterExpression.values upperExpression (environment (firstValues metadata start coordinate)) =
      upperValues metadata start := rfl
private theorem second_values (metadata : Metadata) (start coordinate : Nat) :
    BuilderRegisterPack.values secondFields
      (environment (firstValues metadata start coordinate ++ upperValues metadata start)) =
        [coordinate, upper metadata start] := rfl
theorem decoder_values (branch : Branch) (metadata : Metadata) (start coordinate : Nat) :
    BuilderRegisterPack.values (decoderFields branch) (environment (baseValues branch metadata start coordinate)) =
      BuilderInitialCellDecoder.inputValues start metadata.length coordinate := by cases branch <;> rfl
theorem carry_values (branch : Branch) (metadata : Metadata) (start coordinate : Nat) :
    BuilderRegisterPack.values (carryFields branch) (environment (resultFrame branch metadata start coordinate)) =
      branchResult branch metadata start coordinate := by cases branch <;> rfl

theorem selected_decoder_values (metadata : Metadata) (start coordinate : Nat) :
    decodedValues (selectedBranch metadata start coordinate) metadata start coordinate =
      BuilderInitialCellDecoder.outputValues start metadata.length coordinate := by
  by_cases hBefore : coordinate < start
  · simp only [selectedBranch, BuilderInitialCellDecoder.outputValues, if_pos hBefore, decodedValues]
  · have hResidual : residual coordinate start = coordinate - start := if_neg hBefore
    by_cases hMiddle : coordinate < upper metadata start
    · have hComparison : residual coordinate start < metadata.length + metadata.length := by
        rw [hResidual]; unfold upper at hMiddle; omega
      simp only [selectedBranch, BuilderInitialCellDecoder.outputValues, if_neg hBefore, if_pos hMiddle,
        if_pos hComparison, decodedValues]
    · have hComparison : ¬ residual coordinate start < metadata.length + metadata.length := by
        rw [hResidual]; unfold upper at hMiddle; omega
      simp only [selectedBranch, BuilderInitialCellDecoder.outputValues, if_neg hBefore, if_neg hMiddle,
        if_neg hComparison, decodedValues]

theorem selected_carried_values (metadata : Metadata) (start coordinate : Nat) :
    branchResult (selectedBranch metadata start coordinate) metadata start coordinate =
      carriedValues metadata start coordinate := by
  by_cases hBefore : coordinate < start
  · simp only [selectedBranch, if_pos hBefore, branchResult, branchPair, carriedValues,
      BuilderInitialCellSelection.cellCoordinate, residual]
  · by_cases hMiddle : coordinate < upper metadata start
    · have hCompare : coordinate - start < metadata.length + metadata.length := by
        unfold upper at hMiddle; omega
      have hCell : coordinate < start + 2 * metadata.length := by unfold upper at hMiddle; omega
      simp only [selectedBranch, if_neg hBefore, if_pos hMiddle, branchResult, branchPair, carriedValues,
        BuilderInitialCellSelection.cellCoordinate, if_pos hCell, BuilderInitialCellDecoder.secondResidual,
        residual, if_neg hBefore, if_pos hCompare]
    · have hCompare : ¬ coordinate - start < metadata.length + metadata.length := by
        unfold upper at hMiddle; omega
      have hCell : ¬ coordinate < start + 2 * metadata.length := by unfold upper at hMiddle; omega
      have hPosition : start + metadata.length + (coordinate - start - (metadata.length + metadata.length)) =
          coordinate - metadata.length := by unfold upper at hMiddle; omega
      simp only [selectedBranch, if_neg hBefore, if_neg hMiddle, branchResult, branchPair, carriedValues,
        BuilderInitialCellSelection.cellCoordinate, if_neg hCell, BuilderInitialCellDecoder.secondResidual,
        residual, if_neg hBefore, if_neg hCompare, hPosition]

def carryNode (branch : Branch) : Node :=
  {name := match branch with | .before => 4 | .middle => 10 | .after => 13,
   program := BuilderRegisterPack.machine (carryFields branch) 0, onAccept := .accept, onReject := .dead}
def decoderNode (branch : Branch) : Node :=
  {name := match branch with | .before => 3 | .middle => 9 | .after => 12,
   program := BuilderInitialCellDecoder.machine, onAccept := .node (carryNode branch).reference, onReject := .dead}
def decoderPackNode (branch : Branch) : Node :=
  {name := match branch with | .before => 2 | .middle => 8 | .after => 11,
   program := BuilderRegisterPack.machine (decoderFields branch) 0,
   onAccept := .node (decoderNode branch).reference, onReject := .dead}
def secondCompareNode : Node :=
  {name := 7, program := BuilderRegisterCompareResidual.machine,
   onAccept := .node (decoderPackNode .middle).reference, onReject := .node (decoderPackNode .after).reference}
def secondPackNode : Node :=
  {name := 6, program := BuilderRegisterPack.machine secondFields 0,
   onAccept := .node secondCompareNode.reference, onReject := .dead}
def upperNode : Node :=
  {name := 5, program := BuilderRegisterExpression.machine upperExpression 0,
   onAccept := .node secondPackNode.reference, onReject := .dead}
def firstCompareNode : Node :=
  {name := 1, program := BuilderRegisterCompareResidual.machine,
   onAccept := .node (decoderPackNode .before).reference, onReject := .node upperNode.reference}
def firstPackNode : Node :=
  {name := 0, program := BuilderRegisterPack.machine firstFields 0,
   onAccept := .node firstCompareNode.reference, onReject := .dead}
def graph : Graph :=
  {nodes := [firstPackNode, firstCompareNode, decoderPackNode .before, decoderNode .before, carryNode .before,
    upperNode, secondPackNode, secondCompareNode, decoderPackNode .middle, decoderNode .middle, carryNode .middle,
    decoderPackNode .after, decoderNode .after, carryNode .after], entry := firstPackNode.reference}
def machine : WorkMachine := WorkMachineProgramGraph.machine graph
theorem graph_nodes_length : graph.nodes.length = 14 := rfl

private theorem node0_mem : (firstPackNode) ∈ graph.nodes := List.Mem.head _
private theorem node1_mem : (firstCompareNode) ∈ graph.nodes := List.Mem.tail _ (List.Mem.head _)
private theorem node2_mem : (decoderPackNode .before) ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
private theorem node3_mem : (decoderNode .before) ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
private theorem node4_mem : (carryNode .before) ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
private theorem node5_mem : (upperNode) ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
private theorem node6_mem : (secondPackNode) ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
private theorem node7_mem : (secondCompareNode) ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
private theorem node8_mem : (decoderPackNode .middle) ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
private theorem node9_mem : (decoderNode .middle) ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))
private theorem node10_mem : (carryNode .middle) ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))
private theorem node11_mem : (decoderPackNode .after) ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))
private theorem node12_mem : (decoderNode .after) ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))
private theorem node13_mem : (carryNode .after) ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))

private theorem decoderPackNode_mem (branch : Branch) : decoderPackNode branch ∈ graph.nodes := by
  cases branch
  · exact node2_mem
  · exact node8_mem
  · exact node11_mem
private theorem decoderNode_mem (branch : Branch) : decoderNode branch ∈ graph.nodes := by
  cases branch
  · exact node3_mem
  · exact node9_mem
  · exact node12_mem
private theorem carryNode_mem (branch : Branch) : carryNode branch ∈ graph.nodes := by
  cases branch
  · exact node4_mem
  · exact node10_mem
  · exact node13_mem

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineProgramGraph.QueryDistinct ∧
    WorkMachineProgramGraph.NoRuleAt program program.acceptState ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧
    program.acceptState ≠ program.rejectState
private theorem pack_good {arity : Nat} (fields : List (BuilderRegisterPack.Field arity)) :
    Good (BuilderRegisterPack.machine fields 0) :=
  ⟨BuilderRegisterPack.rules_pairwise_query_distinct fields 0,
    BuilderRegisterPack.noRuleAtAccept fields 0, BuilderRegisterPack.noRuleAtReject fields 0,
    BuilderRegisterPack.acceptState_ne_rejectState fields 0⟩
private theorem expression_good {arity : Nat} (expression : BuilderRegisterExpression.Expr arity) :
    Good (BuilderRegisterExpression.machine expression 0) :=
  ⟨BuilderRegisterExpression.rules_pairwise_query_distinct expression 0,
    BuilderRegisterExpression.noRuleAtAccept expression 0, BuilderRegisterExpression.noRuleAtReject expression 0,
    BuilderRegisterExpression.acceptState_ne_rejectState expression 0⟩
private theorem comparison_good : Good BuilderRegisterCompareResidual.machine :=
  ⟨BuilderRegisterCompareResidual.rules_pairwise_query_distinct,
    BuilderRegisterCompareResidual.noRuleAtAccept, BuilderRegisterCompareResidual.noRuleAtReject,
    BuilderRegisterCompareResidual.acceptState_ne_rejectState⟩

private theorem decoder_good : Good BuilderInitialCellDecoder.machine :=
  ⟨BuilderInitialCellDecoder.rules_pairwise_query_distinct, BuilderInitialCellDecoder.noRuleAtAccept,
    BuilderInitialCellDecoder.noRuleAtReject, BuilderInitialCellDecoder.acceptState_ne_rejectState⟩

theorem graph_wellFormed : graph.WellFormed := by
  have hNames : (graph.nodes.map Node.name).Pairwise (fun a b : Nat => a ≠ b) := by
    change ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] : List Nat).Pairwise _
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.pairwise_map] using hNames
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact pack_good firstFields
    · exact comparison_good
    · exact pack_good (decoderFields .before)
    · exact decoder_good
    · exact pack_good (carryFields .before)
    · exact expression_good upperExpression
    · exact pack_good secondFields
    · exact comparison_good
    · exact pack_good (decoderFields .middle)
    · exact decoder_good
    · exact pack_good (carryFields .middle)
    · exact pack_good (decoderFields .after)
    · exact decoder_good
    · exact pack_good (carryFields .after)
  · exact ⟨firstPackNode, node0_mem, rfl, rfl⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨firstCompareNode, node1_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨decoderPackNode .before, node2_mem, rfl, rfl⟩, ⟨upperNode, node5_mem, rfl, rfl⟩⟩
    · exact ⟨⟨decoderNode .before, node3_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨carryNode .before, node4_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨⟨secondPackNode, node6_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨secondCompareNode, node7_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨decoderPackNode .middle, node8_mem, rfl, rfl⟩, ⟨decoderPackNode .after, node11_mem, rfl, rfl⟩⟩
    · exact ⟨⟨decoderNode .middle, node9_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨carryNode .middle, node10_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨⟨decoderNode .after, node12_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨carryNode .after, node13_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, True.intro⟩

private theorem recovery_eq (coordinate boundary : Nat) :
    recovery coordinate boundary =
      BuilderRegisterLessThan.resultValues (RawRouter.compareResult 0 coordinate boundary) :=
  BuilderRegisterCompareResidual.environment_ofFn (RawRouter.compareResult 0 coordinate boundary)
private theorem pack_run {arity : Nat} (fields : List (BuilderRegisterPack.Field arity))
    (data older : List Nat) (inside : List WorkSymbol) (hLength : data.length = arity) :
    workRunExact? (BuilderRegisterPack.machine fields 0)
      (BuilderRegisterPack.workSteps fields (environment data) [])
      (workStartConfiguration (BuilderRegisterPack.machine fields 0) (endTape (older ++ data) inside [])) =
      some {
        state := (BuilderRegisterPack.machine fields 0).acceptState
        tape := endTape (older ++ data ++ BuilderRegisterPack.values fields (environment data)) inside [] } := by
  have h := BuilderRegisterPack.workRunExact fields 0 older (environment data) [] inside [] rfl
  simpa only [BuilderRegisterPack.initialConfiguration, BuilderRegisterPack.finalConfiguration,
    environment_ofFn data hLength, List.append_nil, List.drop_nil] using h

private theorem expression_run {arity : Nat} (expression : BuilderRegisterExpression.Expr arity)
    (data older : List Nat) (inside : List WorkSymbol) (hLength : data.length = arity) :
    workRunExact? (BuilderRegisterExpression.machine expression 0)
      (BuilderRegisterExpression.workSteps expression (environment data) [])
      (workStartConfiguration (BuilderRegisterExpression.machine expression 0) (endTape (older ++ data) inside [])) =
      some {
        state := (BuilderRegisterExpression.machine expression 0).acceptState
        tape := endTape (older ++ data ++ BuilderRegisterExpression.values expression (environment data)) inside [] } := by
  have h := BuilderRegisterExpression.workRunExact expression 0 older (environment data) [] inside [] rfl
  simpa only [BuilderRegisterExpression.initialConfiguration, BuilderRegisterExpression.finalConfiguration,
    environment_ofFn data hLength, List.append_nil, List.drop_nil] using h

private theorem configuration_eq_of_fields (config : WorkConfiguration) (state : Nat) (tape : WorkTape)
    (hState : config.state = state) (hTape : config.tape = tape) :
    config = {state := state, tape := tape} := by
  cases config with
  | mk currentState currentTape =>
      change currentState = state at hState
      change currentTape = tape at hTape
      subst currentState
      subst currentTape
      rfl

private theorem comparison_run (coordinate boundary : Nat) (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? BuilderRegisterCompareResidual.machine
      (BuilderRegisterCompareResidual.workSteps coordinate boundary)
      (workStartConfiguration BuilderRegisterCompareResidual.machine (endTape (older ++ [coordinate, boundary]) inside [])) =
      some {
        state := if coordinate < boundary then BuilderRegisterCompareResidual.machine.acceptState
          else BuilderRegisterCompareResidual.machine.rejectState
        tape := endTape (older ++ comparisonValues coordinate boundary) inside [] } := by
  have hState : (BuilderRegisterCompareResidual.finalConfiguration coordinate boundary older inside []).state =
      if coordinate < boundary then BuilderRegisterCompareResidual.machine.acceptState
      else BuilderRegisterCompareResidual.machine.rejectState := by
    by_cases hLess : coordinate < boundary
    · rw [if_pos hLess]
      exact (BuilderRegisterCompareResidual.final_accept_iff coordinate boundary older inside []).mpr hLess
    · rw [if_neg hLess]
      exact (BuilderRegisterCompareResidual.final_reject_iff coordinate boundary older inside []).mpr (by omega)
  have hTape : (BuilderRegisterCompareResidual.finalConfiguration coordinate boundary older inside []).tape =
      endTape (older ++ comparisonValues coordinate boundary) inside [] := by
    rw [BuilderRegisterCompareResidual.final_tape]
    simp only [comparisonValues, recovery_eq, residual, List.drop_nil, List.append_assoc]
  have h := BuilderRegisterCompareResidual.workRunExact coordinate boundary older inside []
  rw [configuration_eq_of_fields _ _ _ hState hTape] at h
  exact h

def firstPackSteps (metadata : Metadata) (start coordinate : Nat) : Nat :=
  BuilderRegisterPack.workSteps firstFields (environment (frame metadata start coordinate)) []
def upperSteps (metadata : Metadata) (start coordinate : Nat) : Nat :=
  BuilderRegisterExpression.workSteps upperExpression (environment (firstValues metadata start coordinate)) []
def secondPackSteps (metadata : Metadata) (start coordinate : Nat) : Nat :=
  BuilderRegisterPack.workSteps secondFields
    (environment (firstValues metadata start coordinate ++ upperValues metadata start)) []
def decoderPackSteps (branch : Branch) (metadata : Metadata) (start coordinate : Nat) : Nat :=
  BuilderRegisterPack.workSteps (decoderFields branch) (environment (baseValues branch metadata start coordinate)) []
def carrySteps (branch : Branch) (metadata : Metadata) (start coordinate : Nat) : Nat :=
  BuilderRegisterPack.workSteps (carryFields branch) (environment (resultFrame branch metadata start coordinate)) []
def branchSteps (branch : Branch) (metadata : Metadata) (start coordinate : Nat) : Nat :=
  decoderPackSteps branch metadata start coordinate + 1 +
    (BuilderInitialCellDecoder.workSteps start metadata.length coordinate + 1 +
      (carrySteps branch metadata start coordinate + 1))
def laterSteps (metadata : Metadata) (start coordinate : Nat) : Nat :=
  upperSteps metadata start coordinate + 1 + (secondPackSteps metadata start coordinate + 1 +
    (BuilderRegisterCompareResidual.workSteps coordinate (upper metadata start) + 1 +
      (if coordinate < upper metadata start then branchSteps .middle metadata start coordinate
       else branchSteps .after metadata start coordinate)))
def workSteps (metadata : Metadata) (start coordinate : Nat) : Nat :=
  firstPackSteps metadata start coordinate + 1 +
    (BuilderRegisterCompareResidual.workSteps coordinate start + 1 +
      (if coordinate < start then branchSteps .before metadata start coordinate
       else laterSteps metadata start coordinate))
def initialConfiguration (metadata : Metadata) (start coordinate : Nat) (older : List Nat)
    (inside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration machine (endTape (older ++ frame metadata start coordinate) inside [])
def finalConfiguration (metadata : Metadata) (start coordinate : Nat) (older : List Nat)
    (inside : List WorkSymbol) : WorkConfiguration :=
  {state := machine.acceptState, tape := endTape (older ++ outputValues metadata start coordinate) inside []}

private theorem branch_path (branch : Branch) (metadata : Metadata) (start coordinate : Nat)
    (older : List Nat) (inside : List WorkSymbol)
    (hBranch : selectedBranch metadata start coordinate = branch) :
    AcceptPath graph (.node (decoderPackNode branch).reference) .accept
      (branchSteps branch metadata start coordinate)
      (endTape (older ++ baseValues branch metadata start coordinate) inside [])
      (endTape (older ++ resultFrame branch metadata start coordinate ++ carriedValues metadata start coordinate) inside []) := by
  have hOutput : BuilderInitialCellDecoder.outputValues start metadata.length coordinate =
      decodedValues branch metadata start coordinate := by
    rw [← selected_decoder_values, hBranch]
  have hCarried : branchResult branch metadata start coordinate = carriedValues metadata start coordinate := by
    rw [← hBranch]
    exact selected_carried_values metadata start coordinate
  have hResult := pack_run (carryFields branch) (resultFrame branch metadata start coordinate)
    older inside (resultFrame_length branch metadata start coordinate)
  rw [carry_values, hCarried] at hResult
  simp only [List.append_assoc] at hResult
  have hP := AcceptPath.step (carryNode branch) .accept _ 0 _ _ _
    (carryNode_mem branch) hResult (.terminal .accept _)
  have hD : WorkMachineProgramPath.LocalAcceptRun (decoderNode branch)
      (BuilderInitialCellDecoder.workSteps start metadata.length coordinate)
      (endTape (older ++ baseValues branch metadata start coordinate ++
        BuilderInitialCellDecoder.inputValues start metadata.length coordinate) inside [])
      (endTape (older ++ resultFrame branch metadata start coordinate) inside []) := by
    have h := BuilderInitialCellDecoder.workRunExact start metadata.length coordinate
      (older ++ baseValues branch metadata start coordinate) inside
    simpa only [WorkMachineProgramPath.LocalAcceptRun, decoderNode, BuilderInitialCellDecoder.initialConfiguration,
      BuilderInitialCellDecoder.finalConfiguration, workStartConfiguration, hOutput, resultFrame,
      List.append_assoc] using h
  have hDP := AcceptPath.step (decoderNode branch) .accept _ _ _ _ _
    (decoderNode_mem branch) hD hP
  simp only [List.append_assoc] at hDP
  have hPack := pack_run (decoderFields branch) (baseValues branch metadata start coordinate)
    older inside (baseValues_length branch metadata start coordinate)
  rw [decoder_values] at hPack
  simp only [List.append_assoc] at hPack
  have hPath := AcceptPath.step (decoderPackNode branch) .accept _ _ _ _ _
    (decoderPackNode_mem branch) hPack hDP
  simpa only [branchSteps, decoderPackSteps, carrySteps, Nat.add_zero, List.append_assoc] using hPath

private theorem later_path (metadata : Metadata) (start coordinate : Nat)
    (older : List Nat) (inside : List WorkSymbol) (hBefore : ¬ coordinate < start) :
    AcceptPath graph (.node upperNode.reference) .accept (laterSteps metadata start coordinate)
      (endTape (older ++ firstValues metadata start coordinate) inside [])
      (endTape (older ++ outputValues metadata start coordinate) inside []) := by
  have hCompare := comparison_run coordinate (upper metadata start)
    (older ++ firstValues metadata start coordinate ++ upperValues metadata start) inside
  simp only [List.append_assoc] at hCompare
  have hC : AcceptPath graph (.node secondCompareNode.reference) .accept
      (BuilderRegisterCompareResidual.workSteps coordinate (upper metadata start) + 1 +
        (if coordinate < upper metadata start then branchSteps .middle metadata start coordinate
         else branchSteps .after metadata start coordinate))
      (endTape (older ++ firstValues metadata start coordinate ++ upperValues metadata start ++
        [coordinate, upper metadata start]) inside [])
      (endTape (older ++ outputValues metadata start coordinate) inside []) := by
    by_cases hMiddle : coordinate < upper metadata start
    · have hBranch : selectedBranch metadata start coordinate = .middle := by
        simp only [selectedBranch, if_neg hBefore, if_pos hMiddle]
      rw [if_pos hMiddle] at hCompare ⊢
      have h := AcceptPath.step secondCompareNode .accept _ _ _ _ _ node7_mem hCompare
        (branch_path .middle metadata start coordinate older inside hBranch)
      simpa only [outputValues, hBranch, baseValues, secondValues, List.append_assoc] using h
    · have hBranch : selectedBranch metadata start coordinate = .after := by
        simp only [selectedBranch, if_neg hBefore, if_neg hMiddle]
      rw [if_neg hMiddle] at hCompare ⊢
      have h := AcceptPath.stepReject secondCompareNode .accept _ _ _ _ _ node7_mem hCompare
        (branch_path .after metadata start coordinate older inside hBranch)
      simpa only [outputValues, hBranch, baseValues, secondValues, List.append_assoc] using h
  simp only [List.append_assoc] at hC
  have hPack := pack_run secondFields
    (firstValues metadata start coordinate ++ upperValues metadata start) older inside rfl
  rw [second_values] at hPack
  simp only [List.append_assoc] at hPack
  have hP := AcceptPath.step secondPackNode .accept _ _ _ _ _ node6_mem hPack hC
  have hUpper := expression_run upperExpression (firstValues metadata start coordinate) older inside rfl
  rw [upper_values] at hUpper
  simp only [List.append_assoc] at hUpper
  have hU := AcceptPath.step upperNode .accept _ _ _ _ _ node5_mem hUpper hP
  simpa only [laterSteps, upperSteps, secondPackSteps, List.append_assoc] using hU

theorem workRunExact (metadata : Metadata) (start coordinate : Nat) (older : List Nat)
    (inside : List WorkSymbol) :
    workRunExact? machine (workSteps metadata start coordinate)
      (initialConfiguration metadata start coordinate older inside) =
        some (finalConfiguration metadata start coordinate older inside) := by
  have hCompare := comparison_run coordinate start (older ++ frame metadata start coordinate) inside
  simp only [List.append_assoc] at hCompare
  have hC : AcceptPath graph (.node firstCompareNode.reference) .accept
      (BuilderRegisterCompareResidual.workSteps coordinate start + 1 +
        (if coordinate < start then branchSteps .before metadata start coordinate
         else laterSteps metadata start coordinate))
      (endTape (older ++ frame metadata start coordinate ++ [coordinate, start]) inside [])
      (endTape (older ++ outputValues metadata start coordinate) inside []) := by
    by_cases hBefore : coordinate < start
    · have hBranch : selectedBranch metadata start coordinate = .before := by
        simp only [selectedBranch, if_pos hBefore]
      rw [if_pos hBefore] at hCompare ⊢
      have h := AcceptPath.step firstCompareNode .accept _ _ _ _ _ node1_mem hCompare
        (branch_path .before metadata start coordinate older inside hBranch)
      simpa only [outputValues, hBranch, baseValues, firstValues, List.append_assoc] using h
    · rw [if_neg hBefore] at hCompare ⊢
      have h := AcceptPath.stepReject firstCompareNode .accept _ _ _ _ _ node1_mem hCompare
        (later_path metadata start coordinate older inside hBefore)
      simpa only [firstValues, List.append_assoc] using h
  simp only [List.append_assoc] at hC
  have hFirst := pack_run firstFields (frame metadata start coordinate) older inside rfl
  rw [first_values] at hFirst
  simp only [List.append_assoc] at hFirst
  have hP := AcceptPath.step firstPackNode .accept _ _ _ _ _ node0_mem hFirst hC
  have h := WorkMachineProgramPath.runExact graph _ _ _ _ _ graph_wellFormed hP
  have hStart (tape : WorkTape) :
      WorkMachineProgramGraph.endpointConfiguration (.node firstPackNode.reference) tape =
        workStartConfiguration machine tape := rfl
  have hMachine : WorkMachineProgramGraph.machine graph = machine := rfl
  have hFinish (tape : WorkTape) :
      WorkMachineProgramGraph.endpointConfiguration .accept tape =
        {state := machine.acceptState, tape := tape} := rfl
  rw [hStart, hMachine, hFinish] at h
  simpa only [workSteps, firstPackSteps, initialConfiguration, finalConfiguration] using h

theorem run_compile_exact (metadata : Metadata) (start coordinate : Nat) (older : List Nat)
    (inside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps metadata start coordinate)
      (encodeWorkConfiguration (initialConfiguration metadata start coordinate older inside)) =
      encodeWorkConfiguration (finalConfiguration metadata start coordinate older inside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact metadata start coordinate older inside)

theorem final_tape (metadata : Metadata) (start coordinate : Nat) (older : List Nat)
    (inside : List WorkSymbol) :
    (finalConfiguration metadata start coordinate older inside).tape =
      endTape (older ++ resultFrame (selectedBranch metadata start coordinate) metadata start coordinate ++
        metadata.values ++ [(BuilderInitialCellSelection.cellCoordinate start metadata.length coordinate).1,
          (BuilderInitialCellSelection.cellCoordinate start metadata.length coordinate).2]) inside [] := by
  simp only [finalConfiguration, outputValues, carriedValues, List.append_assoc]

theorem final_frontier (metadata : Metadata) (start coordinate : Nat) (older : List Nat)
    (inside : List WorkSymbol) :
    (finalConfiguration metadata start coordinate older inside).tape.left = [] := rfl

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise graph graph_wellFormed
theorem noRuleAtAccept : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState :=
  WorkMachineProgramGraph.noRuleAt_globalAccept graph
theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  WorkMachineProgramGraph.noRuleAt_globalReject graph
theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := by
  change (0 : Nat) ≠ 1
  decide

private theorem pack_bounds {arity : Nat} (fields : List (BuilderRegisterPack.Field arity))
    (data older : List Nat) (bound : NatPolynomial) (inputLength : Nat)
    (hLength : data.length = arity)
    (hSpan : (registerWord (older ++ data)).length ≤ bound.eval inputLength) :
    (registerWord (older ++ data ++ BuilderRegisterPack.values fields (environment data))).length ≤
        (BuilderRegisterPack.spanPolynomial fields bound).eval inputLength ∧
      6 * BuilderRegisterPack.workSteps fields (environment data) [] ≤
        (BuilderRegisterPack.rawTimePolynomial fields bound).eval inputLength := by
  have h := BuilderRegisterPack.source_polynomial_bounds fields bound inputLength older (environment data) [] (by
    simpa only [environment_ofFn data hLength, List.append_nil] using hSpan)
  simpa only [environment_ofFn data hLength, List.append_nil] using h

private theorem expression_bounds {arity : Nat} (expression : BuilderRegisterExpression.Expr arity)
    (data older : List Nat) (bound : NatPolynomial) (inputLength : Nat)
    (hLength : data.length = arity)
    (hSpan : (registerWord (older ++ data)).length ≤ bound.eval inputLength) :
    (registerWord (older ++ data ++ BuilderRegisterExpression.values expression (environment data))).length ≤
        (BuilderRegisterExpression.spanPolynomial expression bound).eval inputLength ∧
      6 * BuilderRegisterExpression.workSteps expression (environment data) [] ≤
        (BuilderRegisterExpression.rawTimePolynomial expression bound).eval inputLength := by
  have h := BuilderRegisterExpression.source_polynomial_bounds expression bound inputLength older (environment data) [] (by
    simpa only [environment_ofFn data hLength, List.append_nil] using hSpan)
  simpa only [environment_ofFn data hLength, List.append_nil] using h

def preparedSpan (bound : NatPolynomial) : NatPolynomial := BuilderRegisterPack.spanPolynomial firstFields bound
def firstSpan (bound : NatPolynomial) : NatPolynomial := BuilderRegisterCompareResidual.spanPolynomial (preparedSpan bound)
def upperSpan (bound : NatPolynomial) : NatPolynomial := BuilderRegisterExpression.spanPolynomial upperExpression (firstSpan bound)
def secondPreparedSpan (bound : NatPolynomial) : NatPolynomial := BuilderRegisterPack.spanPolynomial secondFields (upperSpan bound)
def secondSpan (bound : NatPolynomial) : NatPolynomial := BuilderRegisterCompareResidual.spanPolynomial (secondPreparedSpan bound)
def baseSpan (branch : Branch) (bound : NatPolynomial) : NatPolynomial :=
  match branch with | .before => firstSpan bound | _ => secondSpan bound
def decoderPreparedSpan (branch : Branch) (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterPack.spanPolynomial (decoderFields branch) (baseSpan branch bound)
def decodedSpan (branch : Branch) (bound : NatPolynomial) : NatPolynomial :=
  BuilderInitialCellDecoder.spanPolynomial (decoderPreparedSpan branch bound)
def returnSpan (branch : Branch) (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterPack.spanPolynomial (carryFields branch) (decodedSpan branch bound)
def branchRawTimePolynomial (branch : Branch) (bound : NatPolynomial) : NatPolynomial :=
  .add (BuilderRegisterPack.rawTimePolynomial (decoderFields branch) (baseSpan branch bound))
    (.add (BuilderInitialCellDecoder.rawTimePolynomial (decoderPreparedSpan branch bound))
      (BuilderRegisterPack.rawTimePolynomial (carryFields branch) (decodedSpan branch bound)))
def spanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (returnSpan .before bound) (.add (returnSpan .middle bound) (returnSpan .after bound))
/-- All actual routing/decoder/copy stages, and at most eight outer bridges. -/
def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (BuilderRegisterPack.rawTimePolynomial firstFields bound)
    (.add (BuilderRegisterCompareResidual.rawTimePolynomial (preparedSpan bound))
      (.add (BuilderRegisterExpression.rawTimePolynomial upperExpression (firstSpan bound))
        (.add (BuilderRegisterPack.rawTimePolynomial secondFields (upperSpan bound))
          (.add (BuilderRegisterCompareResidual.rawTimePolynomial (secondPreparedSpan bound))
            (.add (branchRawTimePolynomial .before bound)
              (.add (branchRawTimePolynomial .middle bound)
                (.add (branchRawTimePolynomial .after bound) (.constant 48))))))))

private theorem branch_bounds (branch : Branch) (metadata : Metadata) (start coordinate : Nat)
    (older : List Nat) (bound : NatPolynomial) (inputLength : Nat)
    (hBranch : selectedBranch metadata start coordinate = branch)
    (hSpan : (registerWord (older ++ baseValues branch metadata start coordinate)).length ≤
      (baseSpan branch bound).eval inputLength) :
    (registerWord (older ++ resultFrame branch metadata start coordinate ++ carriedValues metadata start coordinate)).length ≤
        (returnSpan branch bound).eval inputLength ∧
      6 * branchSteps branch metadata start coordinate ≤ (branchRawTimePolynomial branch bound).eval inputLength + 18 := by
  have hOutput : BuilderInitialCellDecoder.outputValues start metadata.length coordinate =
      decodedValues branch metadata start coordinate := by rw [← selected_decoder_values, hBranch]
  have hCarried : branchResult branch metadata start coordinate = carriedValues metadata start coordinate := by
    rw [← hBranch]
    exact selected_carried_values metadata start coordinate
  have hPack := pack_bounds (decoderFields branch) (baseValues branch metadata start coordinate)
    older (baseSpan branch bound) inputLength (baseValues_length branch metadata start coordinate) hSpan
  rw [decoder_values] at hPack
  have hDecoder := BuilderInitialCellDecoder.source_polynomial_bounds start metadata.length coordinate
    (older ++ baseValues branch metadata start coordinate) (decoderPreparedSpan branch bound) inputLength hPack.1
  have hResult : (registerWord (older ++ resultFrame branch metadata start coordinate)).length ≤
      (decodedSpan branch bound).eval inputLength := by
    simpa only [resultFrame, List.append_assoc, hOutput, decodedSpan] using hDecoder.1
  have hCarry := pack_bounds (carryFields branch) (resultFrame branch metadata start coordinate)
    older (decodedSpan branch bound) inputLength (resultFrame_length branch metadata start coordinate) hResult
  rw [carry_values, hCarried] at hCarry
  constructor
  · exact hCarry.1
  · simp only [branchRawTimePolynomial, NatPolynomial.eval_add, branchSteps, decoderPackSteps, carrySteps]
    omega

/-- Whole-wrapper runtime and retained workspace are polynomial in the actual encoded input span. -/
theorem source_polynomial_bounds (metadata : Metadata) (start coordinate : Nat)
    (older : List Nat) (bound : NatPolynomial) (inputLength : Nat)
    (hSpan : (registerWord (older ++ frame metadata start coordinate)).length ≤ bound.eval inputLength) :
    (registerWord (older ++ outputValues metadata start coordinate)).length ≤ (spanPolynomial bound).eval inputLength ∧
      6 * workSteps metadata start coordinate ≤ (rawTimePolynomial bound).eval inputLength := by
  have h0 := pack_bounds firstFields (frame metadata start coordinate) older bound inputLength rfl hSpan
  rw [first_values] at h0
  have h1 := BuilderRegisterCompareResidual.source_polynomial_bounds coordinate start
    (older ++ frame metadata start coordinate) (preparedSpan bound) inputLength h0.1
  have hFirst : (registerWord (older ++ firstValues metadata start coordinate)).length ≤
      (firstSpan bound).eval inputLength := by
    rw [firstValues, BuilderInitialCellDecoder.comparisonValues_eq]
    simpa only [firstSpan, List.append_assoc] using h1.1
  have h2 := expression_bounds upperExpression (firstValues metadata start coordinate) older
    (firstSpan bound) inputLength rfl hFirst
  rw [upper_values] at h2
  have hUpper : (registerWord (older ++ firstValues metadata start coordinate ++ upperValues metadata start)).length ≤
      (upperSpan bound).eval inputLength := h2.1
  have h3 := pack_bounds secondFields (firstValues metadata start coordinate ++ upperValues metadata start)
    older (upperSpan bound) inputLength rfl (by simpa only [List.append_assoc] using hUpper)
  rw [second_values] at h3
  have h4 := BuilderRegisterCompareResidual.source_polynomial_bounds coordinate (upper metadata start)
    (older ++ firstValues metadata start coordinate ++ upperValues metadata start)
    (secondPreparedSpan bound) inputLength (by simpa only [secondPreparedSpan, List.append_assoc] using h3.1)
  have hSecond : (registerWord (older ++ secondValues metadata start coordinate)).length ≤
      (secondSpan bound).eval inputLength := by
    rw [secondValues, BuilderInitialCellDecoder.comparisonValues_eq]
    simpa only [secondSpan, List.append_assoc] using h4.1
  by_cases hBefore : coordinate < start
  · have hBranch : selectedBranch metadata start coordinate = .before := by
      simp only [selectedBranch, if_pos hBefore]
    have hB := branch_bounds .before metadata start coordinate older bound inputLength hBranch hFirst
    constructor
    · simp only [outputValues, hBranch, spanPolynomial, NatPolynomial.eval_add, List.append_assoc]
      have hOut := hB.1
      simp only [List.append_assoc] at hOut
      omega
    · simp only [rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant,
        workSteps, if_pos hBefore, firstPackSteps]
      omega
  · by_cases hMiddle : coordinate < upper metadata start
    · have hBranch : selectedBranch metadata start coordinate = .middle := by
        simp only [selectedBranch, if_neg hBefore, if_pos hMiddle]
      have hB := branch_bounds .middle metadata start coordinate older bound inputLength hBranch hSecond
      constructor
      · simp only [outputValues, hBranch, spanPolynomial, NatPolynomial.eval_add, List.append_assoc]
        have hOut := hB.1
        simp only [List.append_assoc] at hOut
        omega
      · simp only [rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant,
          workSteps, laterSteps, if_neg hBefore, if_pos hMiddle, firstPackSteps, upperSteps, secondPackSteps]
        omega
    · have hBranch : selectedBranch metadata start coordinate = .after := by
        simp only [selectedBranch, if_neg hBefore, if_neg hMiddle]
      have hB := branch_bounds .after metadata start coordinate older bound inputLength hBranch hSecond
      constructor
      · simp only [outputValues, hBranch, spanPolynomial, NatPolynomial.eval_add, List.append_assoc]
        have hOut := hB.1
        simp only [List.append_assoc] at hOut
        omega
      · simp only [rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant,
          workSteps, laterSteps, if_neg hBefore, if_neg hMiddle, firstPackSteps, upperSteps, secondPackSteps]
        omega

theorem final_accept (metadata : Metadata) (start coordinate : Nat) (older : List Nat)
    (inside : List WorkSymbol) :
    (finalConfiguration metadata start coordinate older inside).state = machine.acceptState := rfl

theorem decoded_bounds (metadata : Metadata) (width start coordinate : Nat)
    (hInterval : start + metadata.length ≤ width) (hInside : coordinate < width + metadata.length) :
    (BuilderInitialCellSelection.cellCoordinate start metadata.length coordinate).1 < width ∧
      (BuilderInitialCellSelection.cellCoordinate start metadata.length coordinate).2 <
        BuilderInitialCellCoordinates.intervalWidth start metadata.length
          (BuilderInitialCellSelection.cellCoordinate start metadata.length coordinate).1 ∧
      coordinate = (BuilderInitialCellSelection.cellCoordinate start metadata.length coordinate).1 +
        min metadata.length ((BuilderInitialCellSelection.cellCoordinate start metadata.length coordinate).1 - start) +
        (BuilderInitialCellSelection.cellCoordinate start metadata.length coordinate).2 :=
  BuilderInitialCellDecoder.decoded_bounds width start metadata.length coordinate hInterval hInside

end PNP.Concrete.CookLevin.BuilderInitialCellHandoff
