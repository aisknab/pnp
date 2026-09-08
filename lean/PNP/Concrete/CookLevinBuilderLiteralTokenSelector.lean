/-
Copyright (c) 2026 PNP Labs.

One fixed finite program reads a physical sign, variable value and token
position. It observes the exact sign/unary literal token or padding, preserving
the original registers and arbitrary tape interior. Positive positions are
copied and decremented; the actual comparator residual distinguishes the
terminator from padding. There is no caller-supplied token verdict.
General clause/list selection and the source-bound request remain downstream.
-/
import PNP.Concrete.CookLevinBuilderRegisterCompareResidual
import PNP.Concrete.CookLevinBuilderRegisterCountdownControl
import PNP.Concrete.CookLevinBuilderUnaryTagMatch
import PNP.Concrete.CookLevinBuilderLocalConstraintPayload

namespace PNP.Concrete.CookLevin.BuilderLiteralTokenSelector

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderLocalConstraintPayload (signValue)
open BuilderArbitrarySlotHeaderRouter
open WorkMachineProgramGraph (Node Graph Endpoint endpointConfiguration)
open WorkMachineProgramPath (AcceptPath LocalAcceptRun LocalRejectRun)

def residualNode : Node :=
  {name := 9, program := BuilderUnaryTagMatch.machine 0, onAccept := .reject, onReject := .dead}
def compareNode : Node :=
  {name := 8, program := BuilderRegisterCompareResidual.machine, onAccept := .accept, onReject := .node residualNode.reference}
def copyValueNode : Node :=
  {name := 7, program := RegisterCopy.machine 2, onAccept := .node compareNode.reference, onReject := .dead}
def decrementNode : Node :=
  {name := 6, program := BuilderRegisterCountdownControl.decrement, onAccept := .node copyValueNode.reference, onReject := .dead}
def copyPositionNode : Node :=
  {name := 5, program := RegisterCopy.machine 0, onAccept := .node decrementNode.reference, onReject := .dead}
def eraseTrueNode : Node :=
  {name := 4, program := BuilderRegisterErase.oneMachine, onAccept := .accept, onReject := .dead}
def eraseFalseNode : Node :=
  {name := 3, program := BuilderRegisterErase.oneMachine, onAccept := .reject, onReject := .dead}
def signNode : Node :=
  {name := 2, program := BuilderUnaryTagMatch.machine 0, onAccept := .node eraseFalseNode.reference, onReject := .node eraseTrueNode.reference}
def copySignNode : Node :=
  {name := 1, program := RegisterCopy.machine 2, onAccept := .node signNode.reference, onReject := .dead}
def positionNode : Node :=
  {name := 0, program := BuilderUnaryTagMatch.machine 0, onAccept := .node copySignNode.reference, onReject := .node copyPositionNode.reference}
def graph : Graph := {nodes := [positionNode, copySignNode, signNode, eraseFalseNode, eraseTrueNode, copyPositionNode, decrementNode, copyValueNode, compareNode, residualNode], entry := positionNode.reference}
def machine : WorkMachine := WorkMachineProgramGraph.machine graph

theorem graph_nodes_length : graph.nodes.length = 10 := rfl

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineProgramGraph.QueryDistinct ∧
    WorkMachineProgramGraph.NoRuleAt program program.acceptState ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧ program.acceptState ≠ program.rejectState
private theorem copy_good (offset : Nat) : Good (RegisterCopy.machine offset) := by
  refine ⟨RegisterCopy.rules_pairwise_query_distinct offset, ?_, ?_,
    RegisterCopy.machine_acceptState_ne_rejectState offset⟩
  · intro item h
    exact Nat.ne_of_lt (RegisterCopy.rule_source_lt_acceptState offset item h)
  · intro item h
    have hBound := RegisterCopy.rule_source_lt_acceptState offset item h
    rw [RegisterCopy.machine_acceptState] at hBound
    rw [RegisterCopy.machine_rejectState]
    omega
private theorem tag_good (code : Nat) : Good (BuilderUnaryTagMatch.machine code) :=
  ⟨BuilderUnaryTagMatch.rules_pairwise_query_distinct code, BuilderUnaryTagMatch.noRuleAtAccept code,
   BuilderUnaryTagMatch.noRuleAtReject code, BuilderUnaryTagMatch.acceptState_ne_rejectState code⟩
private theorem erase_good : Good BuilderRegisterErase.oneMachine :=
  ⟨BuilderRegisterErase.one_rules_pairwise_query_distinct, BuilderRegisterErase.one_noRuleAtAccept,
   BuilderRegisterErase.one_noRuleAtReject, BuilderRegisterErase.one_acceptState_ne_rejectState⟩
private theorem decrement_good : Good BuilderRegisterCountdownControl.decrement :=
  BuilderRegisterCountdownControl.decrement_control
private theorem compare_good : Good BuilderRegisterCompareResidual.machine :=
  ⟨BuilderRegisterCompareResidual.rules_pairwise_query_distinct, BuilderRegisterCompareResidual.noRuleAtAccept,
   BuilderRegisterCompareResidual.noRuleAtReject, BuilderRegisterCompareResidual.acceptState_ne_rejectState⟩

private theorem node_mem_0 : positionNode ∈ graph.nodes := List.Mem.head _
private theorem node_mem_1 : copySignNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.head _)
private theorem node_mem_2 : signNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
private theorem node_mem_3 : eraseFalseNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
private theorem node_mem_4 : eraseTrueNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
private theorem node_mem_5 : copyPositionNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
private theorem node_mem_6 : decrementNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
private theorem node_mem_7 : copyValueNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
private theorem node_mem_8 : compareNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
private theorem node_mem_9 : residualNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

theorem graph_wellFormed : graph.WellFormed := by
  have hNames : (graph.nodes.map Node.name).Pairwise (fun a b : Nat => a ≠ b) := by
    change ([0,1,2,3,4,5,6,7,8,9] : List Nat).Pairwise _
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.pairwise_map] using hNames
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact tag_good 0
    · exact copy_good 2
    · exact tag_good 0
    · exact erase_good
    · exact erase_good
    · exact copy_good 0
    · exact decrement_good
    · exact copy_good 2
    · exact compare_good
    · exact tag_good 0
  · exact ⟨positionNode, node_mem_0, rfl, rfl⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨copySignNode, node_mem_1, rfl, rfl⟩, ⟨copyPositionNode, node_mem_5, rfl, rfl⟩⟩
    · exact ⟨⟨signNode, node_mem_2, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨eraseFalseNode, node_mem_3, rfl, rfl⟩, ⟨eraseTrueNode, node_mem_4, rfl, rfl⟩⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨⟨decrementNode, node_mem_6, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨copyValueNode, node_mem_7, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨compareNode, node_mem_8, rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, ⟨residualNode, node_mem_9, rfl, rfl⟩⟩
    · exact ⟨True.intro, True.intro⟩

def literal (positive : Bool) (value : Nat) : CNFLiteral := {positive := positive, variableIndex := value}
def observe (configuration : WorkConfiguration) : Option CNFToken :=
  if configuration.state = 0 then some .t else if configuration.state = 1 then some .f else none
def unaryEndpoint (position value : Nat) : Endpoint :=
  if position < value then .accept else if position = value then .reject else .dead
def endpoint (positive : Bool) (value position : Nat) : Endpoint :=
  if position = 0 then (if positive then .accept else .reject) else unaryEndpoint (position - 1) value
def frame (positive : Bool) (value position : Nat) : List Nat := [signValue positive, value, position]
def comparisonResult (value position : Nat) : RawRouter.ComparisonResult :=
  RawRouter.compareResult 0 (position - 1) value
def finalValues (positive : Bool) (value position : Nat) (older : List Nat) : List Nat :=
  older ++ frame positive value position ++
    if position = 0 then [] else BuilderRegisterCompareResidual.outputValues (comparisonResult value position)
def signOutside (positive : Bool) (outside : List WorkSymbol) : List WorkSymbol :=
  List.replicate (signValue positive + 1) WorkSymbol.blank ++ outside.drop (signValue positive + 1)
def preparedOutside (value position : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  (WorkSymbol.blank :: outside.drop (position + 1)).drop (value + 1)
def comparisonOutside (value position : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  (preparedOutside value position outside).drop
    (BuilderRegisterCompareResidual.allocatedCells (comparisonResult value position))
def finalOutside (positive : Bool) (value position : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  if position = 0 then signOutside positive outside else comparisonOutside value position outside

def signSteps (positive : Bool) (value : Nat) : Nat :=
  RegisterCopy.steps [value, 0] (signValue positive) + 1 +
    (BuilderUnaryTagMatch.workSteps 0 (signValue positive) + 1 + (signValue positive + 2 + 1))
def residualSteps (position value : Nat) : Nat :=
  if position < value then 0 else BuilderUnaryTagMatch.workSteps 0 (position - value) + 1
def comparisonSteps (position value : Nat) : Nat :=
  BuilderRegisterCompareResidual.workSteps position value + 1 + residualSteps position value
def unarySteps (value position : Nat) : Nat :=
  RegisterCopy.steps [] position + 1 + (2 + 1 +
    (RegisterCopy.steps [position, position - 1] value + 1 + comparisonSteps (position - 1) value))
def workSteps (positive : Bool) (value position : Nat) : Nat :=
  BuilderUnaryTagMatch.workSteps 0 position + 1 +
    if position = 0 then signSteps positive value else unarySteps value position
def initialConfiguration (positive : Bool) (value position : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration machine (endTape (older ++ frame positive value position) inside outside)
def finalConfiguration (positive : Bool) (value position : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  endpointConfiguration (endpoint positive value position)
    (endTape (finalValues positive value position older) inside (finalOutside positive value position outside))

private theorem copy_run (offset : Nat) (older : List Nat) (value : Nat) (newer : List Nat)
    (inside outside : List WorkSymbol) (hLength : newer.length = offset) :
    workRunExact? (RegisterCopy.machine offset) (RegisterCopy.steps newer value)
      (workStartConfiguration (RegisterCopy.machine offset) (endTape (older ++ [value] ++ newer) inside outside)) =
      some {state := (RegisterCopy.machine offset).acceptState,
            tape := endTape (older ++ [value] ++ newer ++ [value]) inside (outside.drop (value + 1))} := by
  subst offset
  have h := RegisterCopy.workRunExact (registerWord older) inside outside value newer
  have hInitial : RegisterCopy.initialConfiguration (registerWord older) inside outside value newer =
      workStartConfiguration (RegisterCopy.machine newer.length)
        (endTape (older ++ [value] ++ newer) inside outside) := by
    simp only [RegisterCopy.initialConfiguration, endTape, workStartConfiguration,
      RegisterCopy.machine_startState, registerWord_append, List.append_assoc]
    rfl
  have hFinal : RegisterCopy.finalConfiguration (registerWord older) inside outside value newer =
      {state := (RegisterCopy.machine newer.length).acceptState,
       tape := endTape (older ++ [value] ++ newer ++ [value]) inside (outside.drop (value + 1))} := by
    simp only [RegisterCopy.finalConfiguration, endTape, RegisterCopy.machine_acceptState,
      registerWord_append, List.append_assoc]
    rfl
  rw [hInitial, hFinal] at h
  exact h

private theorem configuration_eq (configuration : WorkConfiguration) (state : Nat) (tape : WorkTape)
    (hState : configuration.state = state) (hTape : configuration.tape = tape) :
    configuration = {state := state, tape := tape} := by
  cases configuration
  cases hState
  cases hTape
  rfl

private theorem sign_path (positive : Bool) (value : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    AcceptPath graph (.node copySignNode.reference) (if positive then .accept else .reject)
      (signSteps positive value) (endTape (older ++ frame positive value 0) inside outside)
      (endTape (older ++ frame positive value 0) inside (signOutside positive outside)) := by
  have hCopy := copy_run 2 older (signValue positive) [value, 0] inside outside rfl
  have hErase := BuilderRegisterErase.one_workRunExact (older ++ frame positive value 0)
    (signValue positive) inside (outside.drop (signValue positive + 1))
  cases positive with
  | false =>
      have hTag := BuilderUnaryTagMatch.accept_workRunExact 0 (older ++ frame false value 0) inside (outside.drop 1)
      have hTail := AcceptPath.step eraseFalseNode .reject 2 0 _ _ _ node_mem_3 hErase (.terminal .reject _)
      have hTest := AcceptPath.step signNode .reject _ _ _ _ _ node_mem_2 hTag hTail
      have hCopy' : LocalAcceptRun copySignNode (RegisterCopy.steps [value, 0] (signValue false))
          (endTape (older ++ frame false value 0) inside outside)
          (endTape (older ++ frame false value 0 ++ [signValue false]) inside (outside.drop 1)) := by
        simpa only [LocalAcceptRun, copySignNode, workStartConfiguration, frame, signValue, Bool.false_eq_true, ite_false,
          List.append_assoc, List.cons_append, List.nil_append] using hCopy
      have h := AcceptPath.step copySignNode .reject _ _ _ _ _ node_mem_1 hCopy' hTest
      simpa only [signSteps, signOutside, signValue, Bool.false_eq_true, ite_false, Nat.add_zero] using h
  | true =>
      have hTag := BuilderUnaryTagMatch.reject_workRunExact 0 1 (older ++ frame true value 0)
        inside (outside.drop 2) (by decide)
      have hTail := AcceptPath.step eraseTrueNode .accept 3 0 _ _ _ node_mem_4 hErase (.terminal .accept _)
      have hTest := AcceptPath.stepReject signNode .accept _ _ _ _ _ node_mem_2 hTag hTail
      have hCopy' : LocalAcceptRun copySignNode (RegisterCopy.steps [value, 0] (signValue true))
          (endTape (older ++ frame true value 0) inside outside)
          (endTape (older ++ frame true value 0 ++ [signValue true]) inside (outside.drop 2)) := by
        simpa only [LocalAcceptRun, copySignNode, workStartConfiguration, frame, signValue, ite_true,
          List.append_assoc, List.cons_append, List.nil_append] using hCopy
      have h := AcceptPath.step copySignNode .accept _ _ _ _ _ node_mem_1 hCopy' hTest
      simpa only [signSteps, signOutside, signValue, ite_true, Nat.add_zero] using h

private theorem comparison_path (position value : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    AcceptPath graph (.node compareNode.reference) (unaryEndpoint position value) (comparisonSteps position value)
      (endTape (older ++ [position, value]) inside outside)
      (endTape (older ++ BuilderRegisterCompareResidual.outputValues (RawRouter.compareResult 0 position value))
        inside (outside.drop (BuilderRegisterCompareResidual.allocatedCells (RawRouter.compareResult 0 position value)))) := by
  have hRun := BuilderRegisterCompareResidual.workRunExact position value older inside outside
  simp only [BuilderRegisterCompareResidual.initialConfiguration] at hRun
  have hTape : (BuilderRegisterCompareResidual.finalConfiguration position value older inside outside).tape =
      endTape (older ++ BuilderRegisterCompareResidual.outputValues (RawRouter.compareResult 0 position value))
        inside (outside.drop (BuilderRegisterCompareResidual.allocatedCells (RawRouter.compareResult 0 position value))) := rfl
  by_cases hLess : position < value
  · have hState := (BuilderRegisterCompareResidual.final_accept_iff position value older inside outside).mpr hLess
    rw [configuration_eq _ _ _ hState hTape] at hRun
    have h := AcceptPath.step compareNode .accept _ 0 _ _ _ node_mem_8 hRun (.terminal .accept _)
    simpa only [unaryEndpoint, comparisonSteps, residualSteps, if_pos hLess, Nat.add_zero] using h
  · have hState := (BuilderRegisterCompareResidual.final_reject_iff position value older inside outside).mpr
      (Nat.le_of_not_gt hLess)
    rw [configuration_eq _ _ _ hState hTape] at hRun
    have hSuffix : older ++ BuilderRegisterCompareResidual.outputValues (RawRouter.compareResult 0 position value) =
        (older ++ BuilderRegisterLessThan.resultValues (RawRouter.compareResult 0 position value) ++ [value]) ++
          [position - value] := by
      simp only [BuilderRegisterCompareResidual.outputValues, BuilderRegisterCompareResidual.resultBoundary_eq,
        BuilderRegisterCompareResidual.resultCoordinate_eq, if_neg hLess,
        List.append_assoc, List.cons_append, List.nil_append]
    by_cases hEqual : position = value
    · have hZero : position - value = 0 := by omega
      have hTag := BuilderUnaryTagMatch.accept_workRunExact 0
        (older ++ BuilderRegisterLessThan.resultValues (RawRouter.compareResult 0 position value) ++ [value])
        inside (outside.drop (BuilderRegisterCompareResidual.allocatedCells (RawRouter.compareResult 0 position value)))
      have hTail : AcceptPath graph (.node residualNode.reference) .reject
          (BuilderUnaryTagMatch.workSteps 0 (position - value) + 1)
          (endTape (older ++ BuilderRegisterCompareResidual.outputValues (RawRouter.compareResult 0 position value))
            inside (outside.drop (BuilderRegisterCompareResidual.allocatedCells (RawRouter.compareResult 0 position value))))
          (endTape (older ++ BuilderRegisterCompareResidual.outputValues (RawRouter.compareResult 0 position value))
            inside (outside.drop (BuilderRegisterCompareResidual.allocatedCells (RawRouter.compareResult 0 position value)))) := by
        rw [hSuffix, hZero]
        simpa only [Nat.add_zero] using
          AcceptPath.step residualNode .reject _ 0 _ _ _ node_mem_9 hTag (.terminal .reject _)
      have h := AcceptPath.stepReject compareNode .reject _ _ _ _ _ node_mem_8 hRun hTail
      simpa only [unaryEndpoint, comparisonSteps, residualSteps, if_neg hLess, if_pos hEqual] using h
    · have hNonzero : position - value ≠ 0 := by omega
      have hTag := BuilderUnaryTagMatch.reject_workRunExact 0 (position - value)
        (older ++ BuilderRegisterLessThan.resultValues (RawRouter.compareResult 0 position value) ++ [value])
        inside (outside.drop (BuilderRegisterCompareResidual.allocatedCells (RawRouter.compareResult 0 position value)))
        hNonzero
      have hTail : AcceptPath graph (.node residualNode.reference) .dead
          (BuilderUnaryTagMatch.workSteps 0 (position - value) + 1)
          (endTape (older ++ BuilderRegisterCompareResidual.outputValues (RawRouter.compareResult 0 position value))
            inside (outside.drop (BuilderRegisterCompareResidual.allocatedCells (RawRouter.compareResult 0 position value))))
          (endTape (older ++ BuilderRegisterCompareResidual.outputValues (RawRouter.compareResult 0 position value))
            inside (outside.drop (BuilderRegisterCompareResidual.allocatedCells (RawRouter.compareResult 0 position value)))) := by
        rw [hSuffix]
        simpa only [Nat.add_zero] using
          AcceptPath.stepReject residualNode .dead _ 0 _ _ _ node_mem_9 hTag (.terminal .dead _)
      have h := AcceptPath.stepReject compareNode .dead _ _ _ _ _ node_mem_8 hRun hTail
      simpa only [unaryEndpoint, comparisonSteps, residualSteps, if_neg hLess, if_neg hEqual] using h

private theorem unary_path (positive : Bool) (value position : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    AcceptPath graph (.node copyPositionNode.reference) (unaryEndpoint position value)
      (unarySteps value (position + 1))
      (endTape (older ++ frame positive value (position + 1)) inside outside)
      (endTape (finalValues positive value (position + 1) older) inside
        (finalOutside positive value (position + 1) outside)) := by
  have hCopy := copy_run 0 (older ++ [signValue positive, value]) (position + 1) [] inside outside rfl
  have hDecrement : LocalAcceptRun decrementNode 2
      (endTape (older ++ frame positive value (position + 1) ++ [position + 1]) inside (outside.drop (position + 1 + 1)))
      (endTape (older ++ frame positive value (position + 1) ++ [position]) inside
        (WorkSymbol.blank :: outside.drop (position + 1 + 1))) := by
    have h := BuilderRegisterCountdownControl.decrement_workRunExact position
      (registerWord (older ++ frame positive value (position + 1))) inside (outside.drop (position + 1 + 1))
    simpa only [LocalAcceptRun, decrementNode, workStartConfiguration, endTape,
      registerWord_append, registerWord, List.append_nil, List.reverse_append, List.reverse_cons,
      List.reverse_replicate, List.nil_append, List.cons_append, List.append_assoc] using h
  have hValue := copy_run 2 (older ++ [signValue positive]) value [position + 1, position] inside
    (WorkSymbol.blank :: outside.drop (position + 1 + 1)) rfl
  have hValue' : LocalAcceptRun copyValueNode (RegisterCopy.steps [position + 1, position] value)
      (endTape (older ++ frame positive value (position + 1) ++ [position]) inside
        (WorkSymbol.blank :: outside.drop (position + 1 + 1)))
      (endTape (older ++ frame positive value (position + 1) ++ [position, value]) inside
        (preparedOutside value (position + 1) outside)) := by
    simpa only [LocalAcceptRun, copyValueNode, workStartConfiguration, frame, preparedOutside,
      List.append_assoc, List.cons_append, List.nil_append] using hValue
  have hCompare := comparison_path position value (older ++ frame positive value (position + 1))
    inside (preparedOutside value (position + 1) outside)
  have hValuePath := AcceptPath.step copyValueNode (unaryEndpoint position value) _ _ _ _ _ node_mem_7 hValue' hCompare
  have hDecrementPath := AcceptPath.step decrementNode (unaryEndpoint position value) _ _ _ _ _ node_mem_6 hDecrement hValuePath
  have hCopy' : LocalAcceptRun copyPositionNode (RegisterCopy.steps [] (position + 1))
      (endTape (older ++ frame positive value (position + 1)) inside outside)
      (endTape (older ++ frame positive value (position + 1) ++ [position + 1]) inside (outside.drop (position + 1 + 1))) := by
    simpa only [LocalAcceptRun, copyPositionNode, workStartConfiguration, frame, List.append_assoc, List.cons_append,
      List.nil_append, List.append_nil] using hCopy
  have h := AcceptPath.step copyPositionNode (unaryEndpoint position value) _ _ _ _ _ node_mem_5 hCopy' hDecrementPath
  simpa only [unarySteps, finalValues, finalOutside, comparisonOutside, comparisonResult,
    Nat.add_sub_cancel, Nat.add_one_ne_zero, ite_false] using h

theorem workRunExact (positive : Bool) (value position : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps positive value position) (initialConfiguration positive value position older inside outside) =
      some (finalConfiguration positive value position older inside outside) := by
  have hPath : AcceptPath graph (.node positionNode.reference) (endpoint positive value position)
      (workSteps positive value position) (endTape (older ++ frame positive value position) inside outside)
      (endTape (finalValues positive value position older) inside (finalOutside positive value position outside)) := by
    cases position with
    | zero =>
        have hTag := BuilderUnaryTagMatch.accept_workRunExact 0 (older ++ [signValue positive, value]) inside outside
        have hTag' : LocalAcceptRun positionNode (BuilderUnaryTagMatch.workSteps 0 0)
            (endTape (older ++ frame positive value 0) inside outside)
            (endTape (older ++ frame positive value 0) inside outside) := by
          simpa only [LocalAcceptRun, positionNode, workStartConfiguration, frame,
            List.append_assoc, List.cons_append, List.nil_append] using hTag
        have h := AcceptPath.step positionNode (if positive then .accept else .reject) _ _ _ _ _ node_mem_0 hTag'
          (sign_path positive value older inside outside)
        simpa only [workSteps, endpoint, finalValues, finalOutside, frame, ite_true, List.append_nil,
          List.append_assoc, List.cons_append, List.nil_append] using h
    | succ position =>
        have hTag := BuilderUnaryTagMatch.reject_workRunExact 0 (position + 1)
          (older ++ [signValue positive, value]) inside outside (by omega)
        have hTag' : LocalRejectRun positionNode (BuilderUnaryTagMatch.workSteps 0 (position + 1))
            (endTape (older ++ frame positive value (position + 1)) inside outside)
            (endTape (older ++ frame positive value (position + 1)) inside outside) := by
          simpa only [LocalRejectRun, positionNode, workStartConfiguration, frame,
            List.append_assoc, List.cons_append, List.nil_append] using hTag
        have h := AcceptPath.stepReject positionNode (unaryEndpoint position value) _ _ _ _ _ node_mem_0 hTag'
          (unary_path positive value position older inside outside)
        simpa only [workSteps, endpoint, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel,
          frame, List.append_assoc, List.cons_append, List.nil_append] using h
  have hRun := WorkMachineProgramPath.runExact graph _ _ _ _ _ graph_wellFormed hPath
  have hInitial (tape : WorkTape) :
      endpointConfiguration (.node positionNode.reference) tape = workStartConfiguration machine tape := rfl
  rw [hInitial] at hRun
  exact hRun

theorem run_compile_exact (positive : Bool) (value position : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps positive value position)
      (encodeWorkConfiguration (initialConfiguration positive value position older inside outside)) =
      encodeWorkConfiguration (finalConfiguration positive value position older inside outside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact positive value position older inside outside)

theorem unarySlot_cases (value position : Nat) :
    DirectToken.unarySlot value position =
      if position < value then some .t else if position = value then some .f else none := by
  induction value generalizing position with
  | zero =>
      cases position with
      | zero => rfl
      | succ position =>
          simp only [DirectToken.unarySlot, Nat.not_lt_zero, Nat.succ_ne_zero, ite_false]
  | succ value ih =>
      cases position with
      | zero => simp only [DirectToken.unarySlot, Nat.zero_lt_succ, ite_true]
      | succ position =>
          simpa only [DirectToken.unarySlot, Nat.succ_lt_succ_iff, Nat.succ.injEq] using ih position

private theorem unary_observe (position value : Nat) (tape : WorkTape) :
    observe (endpointConfiguration (unaryEndpoint position value) tape) =
      DirectToken.unarySlot value position := by
  rw [unarySlot_cases]
  by_cases hLess : position < value
  · simp only [unaryEndpoint, if_pos hLess] <;> rfl
  · by_cases hEqual : position = value
    · simp only [unaryEndpoint, if_neg hLess, if_pos hEqual] <;> rfl
    · simp only [unaryEndpoint, if_neg hLess, if_neg hEqual] <;> rfl

theorem canonical_result (positive : Bool) (value position : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    observe (finalConfiguration positive value position older inside outside) =
      DirectToken.literalSlot (literal positive value) position := by
  cases position with
  | zero => cases positive <;> rfl
  | succ position =>
      simp only [finalConfiguration, endpoint, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel,
        DirectToken.literalSlot, literal]
      exact unary_observe position value _

theorem workRun_observes_literal (positive : Bool) (value position : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    observe (workRun machine (workSteps positive value position)
      (initialConfiguration positive value position older inside outside)) =
      DirectToken.literalSlot (literal positive value) position := by
  rw [workRun_eq_of_workRunExact _ _ _ _ (workRunExact positive value position older inside outside)]
  exact canonical_result positive value position older inside outside

theorem final_tape (positive : Bool) (value position : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration positive value position older inside outside).tape =
      endTape (finalValues positive value position older) inside (finalOutside positive value position outside) := rfl
theorem original_frame_preserved (positive : Bool) (value position : Nat) (older : List Nat) :
    ∃ history, finalValues positive value position older = older ++ frame positive value position ++ history :=
  ⟨_, rfl⟩
theorem comparison_history_length (value position : Nat) :
    (BuilderRegisterCompareResidual.outputValues (comparisonResult value position)).length = 5 :=
  BuilderRegisterCompareResidual.outputValues_length _
theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise graph graph_wellFormed
theorem noRuleAtAccept : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState :=
  WorkMachineProgramGraph.noRuleAt_globalAccept graph
theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  WorkMachineProgramGraph.noRuleAt_globalReject graph
theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := by
  change (0 : Nat) ≠ 1
  decide

def copyWorkBound (bound : Nat) : Nat :=
  4 * (2 * bound + 5) * (2 * bound + 5) + 9 * (2 * bound + 5) + 5
def copyWorkPolynomial (bound : NatPolynomial) : NatPolynomial :=
  let next := NatPolynomial.add (.mul (.constant 2) bound) (.constant 5)
  .add (.add (.mul (.mul (.constant 4) next) next) (.mul (.constant 9) next)) (.constant 5)
def comparisonInputBound (bound : NatPolynomial) : NatPolynomial := .add (.mul (.constant 3) bound) (.constant 3)
def spanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.add (BuilderRegisterCompareResidual.spanPolynomial (comparisonInputBound bound)) bound) (.constant 2)
def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.add (.mul (.constant 12) (copyWorkPolynomial bound)) (.constant 120))
    (BuilderRegisterCompareResidual.rawTimePolynomial (comparisonInputBound bound))

private theorem copy_polynomial_eval (bound : NatPolynomial) (input : Nat) :
    (copyWorkPolynomial bound).eval input = copyWorkBound (bound.eval input) := rfl
private theorem copy_steps_le (value : Nat) (newer : List Nat) (bound : Nat)
    (hValue : value ≤ 2 * bound + 4) (hNewer : newer.length + newer.sum ≤ 2 * bound + 4) :
    RegisterCopy.steps newer value ≤ copyWorkBound bound := by
  have h := RegisterCopy.steps_le newer value (2 * bound + 4) hValue hNewer
  have hNext : 2 * bound + 4 + 1 = 2 * bound + 5 := by omega
  simpa only [hNext, copyWorkBound] using h

theorem final_outside_length_le (positive : Bool) (value position : Nat) (outside : List WorkSymbol) :
    (finalOutside positive value position outside).length ≤ outside.length + 2 := by
  have hSign : signValue positive ≤ 1 := by cases positive <;> change _ ≤ 1 <;> decide
  by_cases hZero : position = 0
  · simp only [finalOutside, if_pos hZero, signOutside, List.length_append, List.length_replicate, List.length_drop]
    omega
  · simp only [finalOutside, if_neg hZero, comparisonOutside, preparedOutside, List.length_drop, List.length_cons]
    omega

theorem source_polynomial_bounds (positive : Bool) (value position : Nat) (older : List Nat)
    (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (older ++ frame positive value position)).length + outside.length ≤ bound.eval input) :
    (registerWord (finalValues positive value position older)).length + (finalOutside positive value position outside).length ≤
        (spanPolynomial bound).eval input ∧
      6 * workSteps positive value position ≤ (rawTimePolynomial bound).eval input := by
  have hScalars := hSpan
  simp only [frame, registerWord_append, List.length_append, registerWord, List.length_append,
    List.length_cons, List.length_nil, List.length_replicate] at hScalars
  have hValue : value ≤ bound.eval input := by omega
  have hPosition : position ≤ bound.eval input := by omega
  have hSign : signValue positive ≤ 1 := by cases positive <;> change _ ≤ 1 <;> decide
  have hCopySign := copy_steps_le (signValue positive) [value, 0] (bound.eval input) (by omega) (by
    simp only [List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
    omega)
  have hCopyPosition := copy_steps_le position [] (bound.eval input) (by omega) (by
    simp only [List.length_nil, List.sum_nil]
    omega)
  have hCopyValue := copy_steps_le value [position, position - 1] (bound.eval input) (by omega) (by
    simp only [List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
    omega)
  have hPositionTest := BuilderUnaryTagMatch.workSteps_le 0 position
  have hSignTest := BuilderUnaryTagMatch.workSteps_le 0 (signValue positive)
  have hResidualTest := BuilderUnaryTagMatch.workSteps_le 0 (position - 1 - value)
  have hOutside := final_outside_length_le positive value position outside
  have hInput : (registerWord ((older ++ frame positive value position) ++ [position - 1, value])).length ≤
      (comparisonInputBound bound).eval input := by
    simp only [frame, registerWord_append, List.length_append, registerWord, List.length_append,
      List.length_cons, List.length_nil, List.length_replicate, comparisonInputBound,
      NatPolynomial.eval_add, NatPolynomial.eval_mul, NatPolynomial.eval_constant]
    omega
  have hCompare := BuilderRegisterCompareResidual.source_polynomial_bounds (position - 1) value
    (older ++ frame positive value position) (comparisonInputBound bound) input hInput
  have hTail : residualSteps (position - 1) value ≤ 4 := by
    unfold residualSteps
    split <;> omega
  by_cases hZero : position = 0
  · constructor
    · simp only [finalValues, if_pos hZero, List.append_nil, spanPolynomial,
        NatPolynomial.eval_add, NatPolynomial.eval_constant]
      omega
    · simp only [workSteps, if_pos hZero, signSteps, rawTimePolynomial, NatPolynomial.eval_add,
        NatPolynomial.eval_mul, NatPolynomial.eval_constant, copy_polynomial_eval]
      omega
  · constructor
    · simp only [finalValues, if_neg hZero, comparisonResult, spanPolynomial,
        NatPolynomial.eval_add, NatPolynomial.eval_constant]
      omega
    · simp only [workSteps, if_neg hZero, unarySteps, comparisonSteps, rawTimePolynomial,
        NatPolynomial.eval_add, NatPolynomial.eval_mul, NatPolynomial.eval_constant, copy_polynomial_eval]
      omega

end PNP.Concrete.CookLevin.BuilderLiteralTokenSelector
