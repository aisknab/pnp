/-
Copyright (c) 2026 PNP Labs.

One fixed graph decodes all three parts of the compressed initial-cell row.
Actual registers determine both comparisons, division and arithmetic.
Retained scratch and all graph bridges are part of the execution and bounds.
Source metadata/history recovery remains a separate integration obligation.
-/

import PNP.Concrete.CookLevinBuilderRegisterHalve
import PNP.Concrete.CookLevinBuilderInitialCellSelection

namespace PNP.Concrete.CookLevin.BuilderInitialCellDecoder

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderArbitrarySlotHeaderRouter
open WorkMachineProgramGraph (Node Endpoint Graph)
open WorkMachineProgramPath (AcceptPath)

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

def residual (coordinate boundary : Nat) : Nat :=
  if coordinate < boundary then coordinate else coordinate - boundary
def recovery (coordinate boundary : Nat) : List Nat :=
  let e := BuilderRegisterCompareResidual.environment (RawRouter.compareResult 0 coordinate boundary)
  [e ⟨0, by decide⟩, e ⟨1, by decide⟩, e ⟨2, by decide⟩]
def comparisonValues (coordinate boundary : Nat) : List Nat :=
  recovery coordinate boundary ++ [boundary, residual coordinate boundary]

private theorem recovery_eq (coordinate boundary : Nat) :
    recovery coordinate boundary =
      BuilderRegisterLessThan.resultValues (RawRouter.compareResult 0 coordinate boundary) :=
  BuilderRegisterCompareResidual.environment_ofFn (RawRouter.compareResult 0 coordinate boundary)

theorem comparisonValues_eq (coordinate boundary : Nat) :
    comparisonValues coordinate boundary =
      BuilderRegisterCompareResidual.outputValues (RawRouter.compareResult 0 coordinate boundary) := by
  rw [comparisonValues, recovery_eq]
  simp only [BuilderRegisterCompareResidual.outputValues,
    BuilderRegisterCompareResidual.resultBoundary_eq,
    BuilderRegisterCompareResidual.resultCoordinate_eq, residual]

def inputValues (start length coordinate : Nat) : List Nat := [start, length, coordinate]
def firstValues (start length coordinate : Nat) : List Nat :=
  inputValues start length coordinate ++ comparisonValues coordinate start
def doubledValues (start length coordinate : Nat) : List Nat :=
  firstValues start length coordinate ++ [length, length, length + length]
def secondBase (start length coordinate : Nat) : List Nat :=
  doubledValues start length coordinate ++ recovery (residual coordinate start) (length + length) ++ [length + length]
def secondResidual (start length coordinate : Nat) : Nat :=
  residual (residual coordinate start) (length + length)
def secondValues (start length coordinate : Nat) : List Nat :=
  secondBase start length coordinate ++ [secondResidual start length coordinate]
def halvedValues (start length coordinate : Nat) : List Nat :=
  secondBase start length coordinate ++ BuilderRegisterHalve.outputValues (secondResidual start length coordinate)
def middleAddedValues (start length coordinate : Nat) : List Nat :=
  halvedValues start length coordinate ++
    [start, secondResidual start length coordinate / 2, start + secondResidual start length coordinate / 2]
def afterAddedValues (start length coordinate : Nat) : List Nat :=
  secondValues start length coordinate ++
    [start, length, start + length, secondResidual start length coordinate,
      start + length + secondResidual start length coordinate]

def beforeFields : List (BuilderRegisterPack.Field 3) :=
  [.argument ⟨2, by decide⟩, .argument ⟨0, by decide⟩]
def beforeResultFields : List (BuilderRegisterPack.Field 8) :=
  [.argument ⟨7, by decide⟩, .constant 0]
def doubleExpression : BuilderRegisterExpression.Expr 8 :=
  .binary .add (.argument ⟨1, by decide⟩) (.argument ⟨1, by decide⟩)
def middleFields : List (BuilderRegisterPack.Field 11) :=
  [.argument ⟨7, by decide⟩, .argument ⟨10, by decide⟩]
def middleExpression : BuilderRegisterExpression.Expr 24 :=
  .binary .add (.argument ⟨0, by decide⟩) (.argument ⟨22, by decide⟩)
def middleResultFields : List (BuilderRegisterPack.Field 27) :=
  [.argument ⟨26, by decide⟩, .argument ⟨23, by decide⟩]
def afterExpression : BuilderRegisterExpression.Expr 16 :=
  .binary .add (.binary .add (.argument ⟨0, by decide⟩) (.argument ⟨1, by decide⟩))
    (.argument ⟨15, by decide⟩)
def afterResultFields : List (BuilderRegisterPack.Field 21) :=
  [.argument ⟨20, by decide⟩, .constant 0]

def beforeOutput (start length coordinate : Nat) : List Nat :=
  firstValues start length coordinate ++ [residual coordinate start, 0]
def middleOutput (start length coordinate : Nat) : List Nat :=
  middleAddedValues start length coordinate ++
    [start + secondResidual start length coordinate / 2, secondResidual start length coordinate % 2]
def afterOutput (start length coordinate : Nat) : List Nat :=
  afterAddedValues start length coordinate ++ [start + length + secondResidual start length coordinate, 0]
def outputValues (start length coordinate : Nat) : List Nat :=
  if coordinate < start then beforeOutput start length coordinate
  else if residual coordinate start < length + length then middleOutput start length coordinate
  else afterOutput start length coordinate
def outputPrefix (start length coordinate : Nat) : List Nat :=
  if coordinate < start then firstValues start length coordinate
  else if residual coordinate start < length + length then middleAddedValues start length coordinate
  else afterAddedValues start length coordinate

theorem beforeOutput_length (start length coordinate : Nat) : (beforeOutput start length coordinate).length = 10 := rfl
theorem middleOutput_length (start length coordinate : Nat) : (middleOutput start length coordinate).length = 29 := rfl
theorem afterOutput_length (start length coordinate : Nat) : (afterOutput start length coordinate).length = 23 := rfl

theorem canonical_output (start length coordinate : Nat) :
    outputValues start length coordinate = outputPrefix start length coordinate ++
      [(BuilderInitialCellSelection.cellCoordinate start length coordinate).1,
       (BuilderInitialCellSelection.cellCoordinate start length coordinate).2] := by
  by_cases hBefore : coordinate < start
  · simp only [outputValues, outputPrefix, beforeOutput,
      BuilderInitialCellSelection.cellCoordinate, residual, if_pos hBefore]
  · have hFirst : residual coordinate start = coordinate - start := if_neg hBefore
    by_cases hMiddle : residual coordinate start < length + length
    · have hCoordinate : coordinate < start + 2 * length := by rw [hFirst] at hMiddle; omega
      have hSecond : secondResidual start length coordinate = coordinate - start := by
        simp only [secondResidual, residual, if_neg hBefore, if_pos (by simpa only [hFirst] using hMiddle)]
      simp only [outputValues, outputPrefix, if_neg hBefore, if_pos hMiddle, middleOutput,
        BuilderInitialCellSelection.cellCoordinate, if_pos hCoordinate, hSecond]
    · have hCoordinate : ¬ coordinate < start + 2 * length := by rw [hFirst] at hMiddle; omega
      have hSecond : start + length + secondResidual start length coordinate = coordinate - length := by
        simp only [secondResidual, residual, if_neg hBefore,
          if_neg (by simpa only [hFirst] using hMiddle)]
        omega
      simp only [outputValues, outputPrefix, if_neg hBefore, if_neg hMiddle, afterOutput,
        BuilderInitialCellSelection.cellCoordinate, if_neg hCoordinate, hSecond]

private theorem secondValues_eq (start length coordinate : Nat) :
    secondValues start length coordinate =
      doubledValues start length coordinate ++ comparisonValues (residual coordinate start) (length + length) := by
  simp only [secondValues, secondBase, comparisonValues, secondResidual, List.append_assoc, List.cons_append, List.nil_append]

private theorem before_values (start length coordinate : Nat) :
    BuilderRegisterPack.values beforeFields (environment (inputValues start length coordinate)) = [coordinate, start] := rfl
private theorem before_result_values (start length coordinate : Nat) :
    BuilderRegisterPack.values beforeResultFields (environment (firstValues start length coordinate)) =
      [residual coordinate start, 0] := rfl
private theorem double_values (start length coordinate : Nat) :
    BuilderRegisterExpression.values doubleExpression (environment (firstValues start length coordinate)) =
      [length, length, length + length] := rfl
private theorem middle_values (start length coordinate : Nat) :
    BuilderRegisterPack.values middleFields (environment (doubledValues start length coordinate)) =
      [residual coordinate start, length + length] := rfl
private theorem middle_added_values (start length coordinate : Nat) :
    BuilderRegisterExpression.values middleExpression (environment (halvedValues start length coordinate)) =
      [start, secondResidual start length coordinate / 2, start + secondResidual start length coordinate / 2] := rfl
private theorem middle_result_values (start length coordinate : Nat) :
    BuilderRegisterPack.values middleResultFields (environment (middleAddedValues start length coordinate)) =
      [start + secondResidual start length coordinate / 2, secondResidual start length coordinate % 2] := rfl
private theorem after_added_values (start length coordinate : Nat) :
    BuilderRegisterExpression.values afterExpression (environment (secondValues start length coordinate)) =
      [start, length, start + length, secondResidual start length coordinate,
        start + length + secondResidual start length coordinate] := rfl
private theorem after_result_values (start length coordinate : Nat) :
    BuilderRegisterPack.values afterResultFields (environment (afterAddedValues start length coordinate)) =
      [start + length + secondResidual start length coordinate, 0] := rfl

def beforeResultNode : Node :=
  {name := 2, program := BuilderRegisterPack.machine beforeResultFields 0, onAccept := .accept, onReject := .dead}
def middleResultNode : Node :=
  {name := 8, program := BuilderRegisterPack.machine middleResultFields 0, onAccept := .accept, onReject := .dead}
def middleAddNode : Node :=
  {name := 7, program := BuilderRegisterExpression.machine middleExpression 0,
   onAccept := .node middleResultNode.reference, onReject := .dead}
def halveNode : Node :=
  {name := 6, program := BuilderRegisterHalve.machine, onAccept := .node middleAddNode.reference, onReject := .dead}
def afterResultNode : Node :=
  {name := 10, program := BuilderRegisterPack.machine afterResultFields 0, onAccept := .accept, onReject := .dead}
def afterAddNode : Node :=
  {name := 9, program := BuilderRegisterExpression.machine afterExpression 0,
   onAccept := .node afterResultNode.reference, onReject := .dead}
def middleCompareNode : Node :=
  {name := 5, program := BuilderRegisterCompareResidual.machine,
   onAccept := .node halveNode.reference, onReject := .node afterAddNode.reference}
def middlePrepareNode : Node :=
  {name := 4, program := BuilderRegisterPack.machine middleFields 0,
   onAccept := .node middleCompareNode.reference, onReject := .dead}
def doubleNode : Node :=
  {name := 3, program := BuilderRegisterExpression.machine doubleExpression 0,
   onAccept := .node middlePrepareNode.reference, onReject := .dead}
def beforeCompareNode : Node :=
  {name := 1, program := BuilderRegisterCompareResidual.machine,
   onAccept := .node beforeResultNode.reference, onReject := .node doubleNode.reference}
def prepareNode : Node :=
  {name := 0, program := BuilderRegisterPack.machine beforeFields 0,
   onAccept := .node beforeCompareNode.reference, onReject := .dead}
def graph : Graph :=
  {nodes := [prepareNode, beforeCompareNode, beforeResultNode, doubleNode, middlePrepareNode,
    middleCompareNode, halveNode, middleAddNode, middleResultNode, afterAddNode, afterResultNode],
   entry := prepareNode.reference}
/-- The entire all-coordinate decoder is one fixed finite machine. -/
def machine : WorkMachine := WorkMachineProgramGraph.machine graph
theorem graph_nodes_length : graph.nodes.length = 11 := rfl

private theorem prepareNode_mem : prepareNode ∈ graph.nodes := List.Mem.head _

private theorem beforeCompareNode_mem : beforeCompareNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.head _)

private theorem beforeResultNode_mem : beforeResultNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

private theorem doubleNode_mem : doubleNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

private theorem middlePrepareNode_mem : middlePrepareNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

private theorem middleCompareNode_mem : middleCompareNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

private theorem halveNode_mem : halveNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))

private theorem middleAddNode_mem : middleAddNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))

private theorem middleResultNode_mem : middleResultNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))

private theorem afterAddNode_mem : afterAddNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

private theorem afterResultNode_mem : afterResultNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))

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
private theorem halve_good : Good BuilderRegisterHalve.machine :=
  ⟨BuilderRegisterHalve.rules_pairwise_query_distinct,
    BuilderRegisterHalve.noRuleAtAccept, BuilderRegisterHalve.noRuleAtReject,
    BuilderRegisterHalve.acceptState_ne_rejectState⟩

theorem graph_wellFormed : graph.WellFormed := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact pack_good beforeFields
    · exact comparison_good
    · exact pack_good beforeResultFields
    · exact expression_good doubleExpression
    · exact pack_good middleFields
    · exact comparison_good
    · exact halve_good
    · exact expression_good middleExpression
    · exact pack_good middleResultFields
    · exact expression_good afterExpression
    · exact pack_good afterResultFields
  · exact ⟨prepareNode, prepareNode_mem, rfl, rfl⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨beforeCompareNode, beforeCompareNode_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨beforeResultNode, beforeResultNode_mem, rfl, rfl⟩,
        ⟨doubleNode, doubleNode_mem, rfl, rfl⟩⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨⟨middlePrepareNode, middlePrepareNode_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨middleCompareNode, middleCompareNode_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨halveNode, halveNode_mem, rfl, rfl⟩, ⟨afterAddNode, afterAddNode_mem, rfl, rfl⟩⟩
    · exact ⟨⟨middleAddNode, middleAddNode_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨middleResultNode, middleResultNode_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨⟨afterResultNode, afterResultNode_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, True.intro⟩

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

def prepareSteps (start length coordinate : Nat) : Nat :=
  BuilderRegisterPack.workSteps beforeFields (environment (inputValues start length coordinate)) []
def beforeSteps (start length coordinate : Nat) : Nat :=
  BuilderRegisterPack.workSteps beforeResultFields (environment (firstValues start length coordinate)) []
def doubleSteps (start length coordinate : Nat) : Nat :=
  BuilderRegisterExpression.workSteps doubleExpression (environment (firstValues start length coordinate)) []
def middlePrepareSteps (start length coordinate : Nat) : Nat :=
  BuilderRegisterPack.workSteps middleFields (environment (doubledValues start length coordinate)) []
def middleAddSteps (start length coordinate : Nat) : Nat :=
  BuilderRegisterExpression.workSteps middleExpression (environment (halvedValues start length coordinate)) []
def middleResultSteps (start length coordinate : Nat) : Nat :=
  BuilderRegisterPack.workSteps middleResultFields (environment (middleAddedValues start length coordinate)) []
def afterAddSteps (start length coordinate : Nat) : Nat :=
  BuilderRegisterExpression.workSteps afterExpression (environment (secondValues start length coordinate)) []
def afterResultSteps (start length coordinate : Nat) : Nat :=
  BuilderRegisterPack.workSteps afterResultFields (environment (afterAddedValues start length coordinate)) []
def middleTailSteps (start length coordinate : Nat) : Nat :=
  BuilderRegisterHalve.workSteps (secondResidual start length coordinate) + 1 +
    (middleAddSteps start length coordinate + 1 + (middleResultSteps start length coordinate + 1))
def afterTailSteps (start length coordinate : Nat) : Nat :=
  afterAddSteps start length coordinate + 1 + (afterResultSteps start length coordinate + 1)
def continuationSteps (start length coordinate : Nat) : Nat :=
  doubleSteps start length coordinate + 1 +
    (middlePrepareSteps start length coordinate + 1 +
      (BuilderRegisterCompareResidual.workSteps (residual coordinate start) (length + length) + 1 +
        (if residual coordinate start < length + length then middleTailSteps start length coordinate
         else afterTailSteps start length coordinate)))
def workSteps (start length coordinate : Nat) : Nat :=
  prepareSteps start length coordinate + 1 +
    (BuilderRegisterCompareResidual.workSteps coordinate start + 1 +
      (if coordinate < start then beforeSteps start length coordinate + 1
       else continuationSteps start length coordinate))

def initialConfiguration (start length coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration machine (endTape (older ++ inputValues start length coordinate) inside [])
def finalConfiguration (start length coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) : WorkConfiguration :=
  {state := machine.acceptState, tape := endTape (older ++ outputValues start length coordinate) inside []}

private theorem middle_path (start length coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    AcceptPath graph (.node halveNode.reference) .accept (middleTailSteps start length coordinate)
      (endTape (older ++ secondValues start length coordinate) inside [])
      (endTape (older ++ middleOutput start length coordinate) inside []) := by
  have hResult := pack_run middleResultFields (middleAddedValues start length coordinate) older inside rfl
  rw [middle_result_values] at hResult
  simp only [List.append_assoc] at hResult
  have hP := AcceptPath.step middleResultNode .accept _ 0 _ _ _ middleResultNode_mem hResult (.terminal .accept _)
  have hAdd := expression_run middleExpression (halvedValues start length coordinate) older inside rfl
  rw [middle_added_values] at hAdd
  simp only [List.append_assoc] at hAdd
  have hA := AcceptPath.step middleAddNode .accept _ _ _ _ _ middleAddNode_mem hAdd hP
  have hHalf := BuilderRegisterHalve.workRunExact (secondResidual start length coordinate)
    (older ++ secondBase start length coordinate) inside
  simp only [BuilderRegisterHalve.initialConfiguration, BuilderRegisterHalve.finalConfiguration,
    List.append_assoc] at hHalf
  have hH := AcceptPath.step halveNode .accept _ _ _ _ _ halveNode_mem hHalf hA
  simpa only [middleTailSteps, middleAddSteps, middleResultSteps, secondValues, halvedValues,
    middleAddedValues, middleOutput, List.append_assoc, Nat.add_zero] using hH

private theorem after_path (start length coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    AcceptPath graph (.node afterAddNode.reference) .accept (afterTailSteps start length coordinate)
      (endTape (older ++ secondValues start length coordinate) inside [])
      (endTape (older ++ afterOutput start length coordinate) inside []) := by
  have hResult := pack_run afterResultFields (afterAddedValues start length coordinate) older inside rfl
  rw [after_result_values] at hResult
  simp only [List.append_assoc] at hResult
  have hP := AcceptPath.step afterResultNode .accept _ 0 _ _ _ afterResultNode_mem hResult (.terminal .accept _)
  have hAdd := expression_run afterExpression (secondValues start length coordinate) older inside rfl
  rw [after_added_values] at hAdd
  simp only [List.append_assoc] at hAdd
  have hA := AcceptPath.step afterAddNode .accept _ _ _ _ _ afterAddNode_mem hAdd hP
  simpa only [afterTailSteps, afterAddSteps, afterResultSteps, afterAddedValues, afterOutput,
    List.append_assoc, Nat.add_zero] using hA

private theorem continuation_path (start length coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    AcceptPath graph (.node doubleNode.reference) .accept (continuationSteps start length coordinate)
      (endTape (older ++ firstValues start length coordinate) inside [])
      (endTape (older ++ (if residual coordinate start < length + length then middleOutput start length coordinate
        else afterOutput start length coordinate)) inside []) := by
  have hCompare := comparison_run (residual coordinate start) (length + length)
    (older ++ doubledValues start length coordinate) inside
  simp only [List.append_assoc] at hCompare
  rw [← secondValues_eq] at hCompare
  have hC : AcceptPath graph (.node middleCompareNode.reference) .accept
      (BuilderRegisterCompareResidual.workSteps (residual coordinate start) (length + length) + 1 +
        (if residual coordinate start < length + length then middleTailSteps start length coordinate
         else afterTailSteps start length coordinate))
      (endTape (older ++ (doubledValues start length coordinate ++ [residual coordinate start, length + length])) inside [])
      (endTape (older ++ (if residual coordinate start < length + length then middleOutput start length coordinate
         else afterOutput start length coordinate)) inside []) := by
    by_cases hMiddle : residual coordinate start < length + length
    · simp only [if_pos hMiddle] at hCompare ⊢
      exact AcceptPath.step middleCompareNode .accept _ _ _ _ _ middleCompareNode_mem hCompare
        (middle_path start length coordinate older inside)
    · simp only [if_neg hMiddle] at hCompare ⊢
      exact AcceptPath.stepReject middleCompareNode .accept _ _ _ _ _ middleCompareNode_mem hCompare
        (after_path start length coordinate older inside)
  have hPrepare := pack_run middleFields (doubledValues start length coordinate) older inside rfl
  rw [middle_values] at hPrepare
  simp only [List.append_assoc] at hPrepare
  have hP := AcceptPath.step middlePrepareNode .accept _ _ _ _ _ middlePrepareNode_mem hPrepare hC
  have hDouble := expression_run doubleExpression (firstValues start length coordinate) older inside rfl
  rw [double_values] at hDouble
  simp only [List.append_assoc] at hDouble
  have hD := AcceptPath.step doubleNode .accept _ _ _ _ _ doubleNode_mem hDouble hP
  simpa only [continuationSteps, doubleSteps, middlePrepareSteps, doubledValues, List.append_assoc] using hD

/-- Both comparisons are executed by the fixed program; no branch answer is an input. -/
theorem workRunExact (start length coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? machine (workSteps start length coordinate)
      (initialConfiguration start length coordinate older inside) =
      some (finalConfiguration start length coordinate older inside) := by
  have hCompare := comparison_run coordinate start (older ++ inputValues start length coordinate) inside
  simp only [List.append_assoc] at hCompare
  have hC : AcceptPath graph (.node beforeCompareNode.reference) .accept
      (BuilderRegisterCompareResidual.workSteps coordinate start + 1 +
        (if coordinate < start then beforeSteps start length coordinate + 1
         else continuationSteps start length coordinate))
      (endTape (older ++ (inputValues start length coordinate ++ [coordinate, start])) inside [])
      (endTape (older ++ outputValues start length coordinate) inside []) := by
    by_cases hBefore : coordinate < start
    · simp only [if_pos hBefore] at hCompare ⊢
      have hBeforeRun := pack_run beforeResultFields (firstValues start length coordinate) older inside rfl
      rw [before_result_values] at hBeforeRun
      simp only [List.append_assoc] at hBeforeRun
      have hP := AcceptPath.step beforeResultNode .accept _ 0 _ _ _ beforeResultNode_mem hBeforeRun (.terminal .accept _)
      have hB := AcceptPath.step beforeCompareNode .accept _ _ _ _ _ beforeCompareNode_mem hCompare hP
      simpa only [outputValues, if_pos hBefore, beforeOutput, beforeSteps, firstValues,
        List.append_assoc, Nat.add_zero] using hB
    · simp only [if_neg hBefore] at hCompare ⊢
      have hB := AcceptPath.stepReject beforeCompareNode .accept _ _ _ _ _ beforeCompareNode_mem hCompare
        (continuation_path start length coordinate older inside)
      simpa only [outputValues, if_neg hBefore, firstValues, List.append_assoc] using hB
  have hPrepare := pack_run beforeFields (inputValues start length coordinate) older inside rfl
  rw [before_values] at hPrepare
  simp only [List.append_assoc] at hPrepare
  have hP := AcceptPath.step prepareNode .accept _ _ _ _ _ prepareNode_mem hPrepare hC
  have h := WorkMachineProgramPath.runExact graph _ _ _ _ _ graph_wellFormed hP
  have hStart (tape : WorkTape) :
      WorkMachineProgramGraph.endpointConfiguration (.node prepareNode.reference) tape =
        workStartConfiguration machine tape := rfl
  rw [hStart] at h
  have hMachine : WorkMachineProgramGraph.machine graph = machine := rfl
  have hFinish (tape : WorkTape) :
      WorkMachineProgramGraph.endpointConfiguration .accept tape =
        {state := machine.acceptState, tape := tape} := rfl
  rw [hMachine, hFinish] at h
  simpa only [workSteps, prepareSteps, initialConfiguration, finalConfiguration] using h

theorem run_compile_exact (start length coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps start length coordinate)
      (encodeWorkConfiguration (initialConfiguration start length coordinate older inside)) =
      encodeWorkConfiguration (finalConfiguration start length coordinate older inside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact start length coordinate older inside)

theorem final_frontier (start length coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration start length coordinate older inside).tape.left = [] := rfl

theorem final_tape (start length coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration start length coordinate older inside).tape =
      endTape (older ++ outputPrefix start length coordinate ++
        [(BuilderInitialCellSelection.cellCoordinate start length coordinate).1,
         (BuilderInitialCellSelection.cellCoordinate start length coordinate).2]) inside [] := by
  rw [finalConfiguration, canonical_output]
  simp only [List.append_assoc]

theorem decoded_bounds (width start length coordinate : Nat)
    (hInterval : start + length ≤ width) (hInside : coordinate < width + length) :
    (BuilderInitialCellSelection.cellCoordinate start length coordinate).1 < width ∧
      (BuilderInitialCellSelection.cellCoordinate start length coordinate).2 <
        BuilderInitialCellCoordinates.intervalWidth start length
          (BuilderInitialCellSelection.cellCoordinate start length coordinate).1 ∧
      coordinate = (BuilderInitialCellSelection.cellCoordinate start length coordinate).1 +
        min length ((BuilderInitialCellSelection.cellCoordinate start length coordinate).1 - start) +
        (BuilderInitialCellSelection.cellCoordinate start length coordinate).2 :=
  BuilderInitialCellSelection.cellCoordinate_spec width start length coordinate hInterval hInside

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

def preparedSpan (bound : NatPolynomial) : NatPolynomial := BuilderRegisterPack.spanPolynomial beforeFields bound
def firstSpan (bound : NatPolynomial) : NatPolynomial := BuilderRegisterCompareResidual.spanPolynomial (preparedSpan bound)
def beforeSpan (bound : NatPolynomial) : NatPolynomial := BuilderRegisterPack.spanPolynomial beforeResultFields (firstSpan bound)
def doubledSpan (bound : NatPolynomial) : NatPolynomial := BuilderRegisterExpression.spanPolynomial doubleExpression (firstSpan bound)
def middlePreparedSpan (bound : NatPolynomial) : NatPolynomial := BuilderRegisterPack.spanPolynomial middleFields (doubledSpan bound)
def secondSpan (bound : NatPolynomial) : NatPolynomial := BuilderRegisterCompareResidual.spanPolynomial (middlePreparedSpan bound)
def halvedSpan (bound : NatPolynomial) : NatPolynomial := BuilderRegisterHalve.spanPolynomial (secondSpan bound)
def middleAddedSpan (bound : NatPolynomial) : NatPolynomial := BuilderRegisterExpression.spanPolynomial middleExpression (halvedSpan bound)
def middleSpan (bound : NatPolynomial) : NatPolynomial := BuilderRegisterPack.spanPolynomial middleResultFields (middleAddedSpan bound)
def afterAddedSpan (bound : NatPolynomial) : NatPolynomial := BuilderRegisterExpression.spanPolynomial afterExpression (secondSpan bound)
def afterSpan (bound : NatPolynomial) : NatPolynomial := BuilderRegisterPack.spanPolynomial afterResultFields (afterAddedSpan bound)
def spanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (beforeSpan bound) (.add (middleSpan bound) (afterSpan bound))

/-- A bound for all possible visited nodes and at most eight graph bridges. -/
def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (BuilderRegisterPack.rawTimePolynomial beforeFields bound) (.add (BuilderRegisterCompareResidual.rawTimePolynomial (preparedSpan bound)) (.add (BuilderRegisterPack.rawTimePolynomial beforeResultFields (firstSpan bound)) (.add (BuilderRegisterExpression.rawTimePolynomial doubleExpression (firstSpan bound)) (.add (BuilderRegisterPack.rawTimePolynomial middleFields (doubledSpan bound)) (.add (BuilderRegisterCompareResidual.rawTimePolynomial (middlePreparedSpan bound)) (.add (BuilderRegisterHalve.rawTimePolynomial (secondSpan bound)) (.add (BuilderRegisterExpression.rawTimePolynomial middleExpression (halvedSpan bound)) (.add (BuilderRegisterPack.rawTimePolynomial middleResultFields (middleAddedSpan bound)) (.add (BuilderRegisterExpression.rawTimePolynomial afterExpression (secondSpan bound)) (.add (BuilderRegisterPack.rawTimePolynomial afterResultFields (afterAddedSpan bound)) (.constant 48)))))))))))

/-- Whole-decoder bounds from the actual incoming encoded register span. -/
theorem source_polynomial_bounds (start length coordinate : Nat) (older : List Nat)
    (bound : NatPolynomial) (inputLength : Nat)
    (hSpan : (registerWord (older ++ inputValues start length coordinate)).length ≤ bound.eval inputLength) :
    (registerWord (older ++ outputValues start length coordinate)).length ≤ (spanPolynomial bound).eval inputLength ∧
      6 * workSteps start length coordinate ≤ (rawTimePolynomial bound).eval inputLength := by
  have h0 := pack_bounds beforeFields (inputValues start length coordinate) older bound inputLength rfl hSpan
  rw [before_values] at h0
  have h1 := BuilderRegisterCompareResidual.source_polynomial_bounds coordinate start
    (older ++ inputValues start length coordinate) (preparedSpan bound) inputLength h0.1
  have hFirst : (registerWord (older ++ firstValues start length coordinate)).length ≤
      (firstSpan bound).eval inputLength := by
    rw [firstValues, comparisonValues_eq]
    simpa only [firstSpan, List.append_assoc] using h1.1
  have h2 := pack_bounds beforeResultFields (firstValues start length coordinate) older
    (firstSpan bound) inputLength rfl hFirst
  rw [before_result_values] at h2
  have h3 := expression_bounds doubleExpression (firstValues start length coordinate) older
    (firstSpan bound) inputLength rfl hFirst
  rw [double_values] at h3
  have hDoubled : (registerWord (older ++ doubledValues start length coordinate)).length ≤
      (doubledSpan bound).eval inputLength := by
    simpa only [doubledSpan, doubledValues, List.append_assoc] using h3.1
  have h4 := pack_bounds middleFields (doubledValues start length coordinate) older
    (doubledSpan bound) inputLength rfl hDoubled
  rw [middle_values] at h4
  have h5 := BuilderRegisterCompareResidual.source_polynomial_bounds (residual coordinate start) (length + length)
    (older ++ doubledValues start length coordinate) (middlePreparedSpan bound) inputLength h4.1
  have hSecond : (registerWord (older ++ secondValues start length coordinate)).length ≤
      (secondSpan bound).eval inputLength := by
    rw [secondValues_eq, comparisonValues_eq]
    simpa only [secondSpan, List.append_assoc] using h5.1
  have h6 := BuilderRegisterHalve.source_polynomial_bounds (secondResidual start length coordinate)
    (older ++ secondBase start length coordinate) (secondSpan bound) inputLength (by
      simpa only [secondValues, List.append_assoc] using hSecond)
  have hHalved : (registerWord (older ++ halvedValues start length coordinate)).length ≤
      (halvedSpan bound).eval inputLength := by
    simpa only [halvedSpan, halvedValues, List.append_assoc] using h6.1
  have h7 := expression_bounds middleExpression (halvedValues start length coordinate) older
    (halvedSpan bound) inputLength rfl hHalved
  rw [middle_added_values] at h7
  have hMiddleAdded : (registerWord (older ++ middleAddedValues start length coordinate)).length ≤
      (middleAddedSpan bound).eval inputLength := by
    simpa only [middleAddedSpan, middleAddedValues, List.append_assoc] using h7.1
  have h8 := pack_bounds middleResultFields (middleAddedValues start length coordinate) older
    (middleAddedSpan bound) inputLength rfl hMiddleAdded
  rw [middle_result_values] at h8
  have h9 := expression_bounds afterExpression (secondValues start length coordinate) older
    (secondSpan bound) inputLength rfl hSecond
  rw [after_added_values] at h9
  have hAfterAdded : (registerWord (older ++ afterAddedValues start length coordinate)).length ≤
      (afterAddedSpan bound).eval inputLength := by
    simpa only [afterAddedSpan, afterAddedValues, List.append_assoc] using h9.1
  have h10 := pack_bounds afterResultFields (afterAddedValues start length coordinate) older
    (afterAddedSpan bound) inputLength rfl hAfterAdded
  rw [after_result_values] at h10
  simp only [List.append_assoc] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  constructor
  · simp only [spanPolynomial, NatPolynomial.eval_add]
    by_cases hBefore : coordinate < start
    · simp only [outputValues, if_pos hBefore, beforeOutput]
      have hBeforeSpan := h2.1
      change _ ≤ (beforeSpan bound).eval inputLength at hBeforeSpan
      omega
    · by_cases hMiddle : residual coordinate start < length + length
      · simp only [outputValues, if_neg hBefore, if_pos hMiddle, middleOutput]
        have hMiddleSpan := h8.1
        change _ ≤ (middleSpan bound).eval inputLength at hMiddleSpan
        omega
      · simp only [outputValues, if_neg hBefore, if_neg hMiddle, afterOutput]
        have hAfterSpan := h10.1
        change _ ≤ (afterSpan bound).eval inputLength at hAfterSpan
        omega
  · simp only [rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant,
      workSteps, continuationSteps, middleTailSteps, afterTailSteps, prepareSteps, beforeSteps,
      doubleSteps, middlePrepareSteps, middleAddSteps, middleResultSteps, afterAddSteps, afterResultSteps]
    split
    · omega
    · split <;> omega

end PNP.Concrete.CookLevin.BuilderInitialCellDecoder
