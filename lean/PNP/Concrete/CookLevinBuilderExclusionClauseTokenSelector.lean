/-
Copyright (c) 2026 PNP Labs.

One fixed finite program selects every token of the exact canonical exclusion
clause. The separator and finish are separate stable control outcomes; body
positions enter the verified literal selector after exact scratch erasure and
decrement. Source values and the position are physically read from the frame.

Whole-source position binding, root recovery and final formula construction
remain separate obligations. No caller-supplied token or route certificate is
an input to this machine.
-/

import PNP.Concrete.CookLevinBuilderExclusionClauseBoundary
import PNP.Concrete.CookLevinBuilderRegisterErase

namespace PNP.Concrete.CookLevin.BuilderExclusionClauseTokenSelector

open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderExclusionPairLiteralTokens (frame initialValues)
open BuilderExclusionClauseBoundary (boundary)
open WorkMachineProgramGraph (Node Graph Endpoint endpointConfiguration endpointState)
open WorkMachineProgramPath (AcceptPath LocalAcceptRun LocalRejectRun)
open PipelineStateNamespace (renameConfiguration)

/-- A stable local entry, distinct from both automatically bridged endpoints. -/
def stopMachine : WorkMachine := {rules := [], startState := 0, acceptState := 1, rejectState := 2}
def finishNode : Node :=
  {name := 7, program := stopMachine, onAccept := .dead, onReject := .dead}
def separatorNode : Node :=
  {name := 6, program := stopMachine, onAccept := .dead, onReject := .dead}
def bodyNode : Node :=
  {name := 5, program := BuilderExclusionPairLiteralTokens.machine, onAccept := .accept, onReject := .reject}
def decrementNode : Node :=
  {name := 4, program := BuilderRegisterCountdownControl.decrement, onAccept := .node bodyNode.reference, onReject := .dead}
def eraseNode : Node :=
  {name := 3, program := BuilderRegisterErase.machine 9, onAccept := .node decrementNode.reference, onReject := .dead}
def residualNode : Node :=
  {name := 2, program := BuilderUnaryTagMatch.machine 0, onAccept := .node finishNode.reference, onReject := .node eraseNode.reference}
def boundaryNode : Node :=
  {name := 1, program := BuilderExclusionClauseBoundary.machine, onAccept := .dead, onReject := .node residualNode.reference}
def positionNode : Node :=
  {name := 0, program := BuilderUnaryTagMatch.machine 0, onAccept := .node separatorNode.reference, onReject := .node boundaryNode.reference}
def graph : Graph :=
  {nodes := [positionNode, boundaryNode, residualNode, eraseNode, decrementNode, bodyNode, separatorNode, finishNode],
   entry := positionNode.reference}
def machine : WorkMachine := WorkMachineProgramGraph.machine graph
def separatorState : Nat := endpointState (.node separatorNode.reference)
def finishState : Nat := endpointState (.node finishNode.reference)

theorem graph_nodes_length : graph.nodes.length = 8 := rfl
theorem terminal_states_distinct :
    ([0,1,2,separatorState,finishState] : List Nat).Pairwise (fun left right => left ≠ right) := by decide

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineProgramGraph.QueryDistinct ∧
    WorkMachineProgramGraph.NoRuleAt program program.acceptState ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧ program.acceptState ≠ program.rejectState
private theorem tag_good : Good (BuilderUnaryTagMatch.machine 0) :=
  ⟨BuilderUnaryTagMatch.rules_pairwise_query_distinct 0, BuilderUnaryTagMatch.noRuleAtAccept 0,
   BuilderUnaryTagMatch.noRuleAtReject 0, BuilderUnaryTagMatch.acceptState_ne_rejectState 0⟩
private theorem boundary_good : Good BuilderExclusionClauseBoundary.machine :=
  ⟨BuilderExclusionClauseBoundary.rules_pairwise_query_distinct, BuilderExclusionClauseBoundary.noRuleAtAccept,
   BuilderExclusionClauseBoundary.noRuleAtReject, BuilderExclusionClauseBoundary.acceptState_ne_rejectState⟩
private theorem erase_good : Good (BuilderRegisterErase.machine 9) :=
  ⟨BuilderRegisterErase.rules_pairwise_query_distinct 9, BuilderRegisterErase.noRuleAtAccept 9,
   BuilderRegisterErase.noRuleAtReject 9, BuilderRegisterErase.acceptState_ne_rejectState 9⟩
private theorem decrement_good : Good BuilderRegisterCountdownControl.decrement :=
  BuilderRegisterCountdownControl.decrement_control
private theorem body_good : Good BuilderExclusionPairLiteralTokens.machine :=
  ⟨BuilderExclusionPairLiteralTokens.rules_pairwise_query_distinct, BuilderExclusionPairLiteralTokens.noRuleAtAccept,
   BuilderExclusionPairLiteralTokens.noRuleAtReject, BuilderExclusionPairLiteralTokens.acceptState_ne_rejectState⟩
private theorem stop_good : Good stopMachine :=
  ⟨List.Pairwise.nil, (by intro rule h; cases h), (by intro rule h; cases h), (by decide)⟩

private theorem member_0 : positionNode ∈ graph.nodes := List.Mem.head _
private theorem member_1 : boundaryNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.head _)
private theorem member_2 : residualNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
private theorem member_3 : eraseNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
private theorem member_4 : decrementNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
private theorem member_5 : bodyNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
private theorem member_6 : separatorNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
private theorem member_7 : finishNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))

theorem graph_wellFormed : graph.WellFormed := by
  have hNames : (graph.nodes.map Node.name).Pairwise (fun left right : Nat => left ≠ right) := by
    change ([0,1,2,3,4,5,6,7] : List Nat).Pairwise _
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.pairwise_map] using hNames
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact tag_good
    · exact boundary_good
    · exact tag_good
    · exact erase_good
    · exact decrement_good
    · exact body_good
    · exact stop_good
    · exact stop_good
  · exact ⟨positionNode, member_0, rfl, rfl⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨separatorNode, member_6, rfl, rfl⟩, ⟨boundaryNode, member_1, rfl, rfl⟩⟩
    · exact ⟨True.intro, ⟨residualNode, member_2, rfl, rfl⟩⟩
    · exact ⟨⟨finishNode, member_7, rfl, rfl⟩, ⟨eraseNode, member_3, rfl, rfl⟩⟩
    · exact ⟨⟨decrementNode, member_4, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨bodyNode, member_5, rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨True.intro, True.intro⟩

def bodyEndpoint {width : Nat} (first second : Fin width) (position : Nat) : Endpoint :=
  BuilderLiteralListSearch.endpoint (excludeBoundedPairClause first second) (position - 1)
def endpoint {width : Nat} (first second : Fin width) (position : Nat) : Endpoint :=
  if position = 0 then .node separatorNode.reference
  else if boundary first.val second.val < position then .dead
  else if position = boundary first.val second.val then .node finishNode.reference
  else bodyEndpoint first second position
def eraseOutside (first second position : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  List.replicate (BuilderRegisterErase.clearedSpan (BuilderExclusionClauseBoundary.scratch first second position)) WorkSymbol.blank ++
    BuilderExclusionClauseBoundary.finalOutside first second position outside
def bodyOutside (first second position : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  WorkSymbol.blank :: eraseOutside first second position outside
def bodySteps {width : Nat} (first second : Fin width) (position : Nat) (retained : List Nat)
    (hRetained : retained.length = 11) : Nat :=
  BuilderRegisterErase.workSteps (BuilderExclusionClauseBoundary.scratch first.val second.val position) + 1 +
    (2 + 1 + (BuilderExclusionPairLiteralTokens.workSteps first second (position - 1) retained hRetained + 1))
def afterComparisonSteps {width : Nat} (first second : Fin width) (position : Nat)
    (retained : List Nat) (hRetained : retained.length = 11) : Nat :=
  if boundary first.val second.val < position then 0
  else BuilderUnaryTagMatch.workSteps 0 (boundary first.val second.val - position) + 1 +
    if position = boundary first.val second.val then 0 else bodySteps first second position retained hRetained
def workSteps {width : Nat} (first second : Fin width) (position : Nat) (retained : List Nat)
    (hRetained : retained.length = 11) : Nat :=
  BuilderUnaryTagMatch.workSteps 0 position + 1 +
    if position = 0 then 0 else BuilderExclusionClauseBoundary.workSteps first.val second.val position retained hRetained + 1 +
      afterComparisonSteps first second position retained hRetained
def finalValues {width : Nat} (first second : Fin width) (position : Nat) (retained older : List Nat) : List Nat :=
  if position = 0 then initialValues first.val second.val position retained older
  else if boundary first.val second.val < position ∨ position = boundary first.val second.val then
    BuilderExclusionClauseBoundary.finalValues first.val second.val position retained older
  else BuilderExclusionPairLiteralTokens.finalValues first second (position - 1) retained older
def finalOutside {width : Nat} (first second : Fin width) (position : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  if position = 0 then outside
  else if boundary first.val second.val < position ∨ position = boundary first.val second.val then
    BuilderExclusionClauseBoundary.finalOutside first.val second.val position outside
  else BuilderExclusionPairLiteralTokens.finalOutside first second (position - 1) (bodyOutside first.val second.val position outside)
def initialConfiguration (first second position : Nat) (retained older : List Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration machine (endTape (initialValues first second position retained older) inside outside)
def finalConfiguration {width : Nat} (first second : Fin width) (position : Nat) (retained older : List Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  endpointConfiguration (endpoint first second position)
    (endTape (finalValues first second position retained older) inside (finalOutside first second position outside))
def observe (configuration : WorkConfiguration) : Option CNFToken :=
  if configuration.state = 0 then some .t else if configuration.state = 1 then some .f
  else if configuration.state = separatorState then some .sep else if configuration.state = finishState then some .finish else none

theorem zero_test_steps (position : Nat) : BuilderUnaryTagMatch.workSteps 0 position = 3 := by
  simp only [BuilderUnaryTagMatch.workSteps, Nat.min_zero, Nat.zero_min, Nat.mul_zero, Nat.zero_add]

theorem body_width {width : Nat} (first second : Fin width) :
    DirectToken.boundedLiteralListWidth (excludeBoundedPairClause first second) = first.val + second.val + 4 := by
  simp only [excludeBoundedPairClause, DirectToken.boundedLiteralListWidth, DirectToken.boundedLiteralWidth, falseLiteral]
  omega

theorem clause_cases {width : Nat} (first second : Fin width) (position : Nat) :
    DirectToken.clauseSlot (excludeBoundedPairClause first second) position =
      if position = 0 then some .sep
      else if boundary first.val second.val < position then none
      else if position = boundary first.val second.val then some .finish
      else DirectToken.boundedLiteralListSlot (excludeBoundedPairClause first second) (position - 1) := by
  cases position with
  | zero => rfl
  | succ position =>
      have hZero : ¬ position + 1 = 0 := by omega
      have hFirst : ¬ position + 1 < 1 := by omega
      simp only [DirectToken.clauseSlot, DirectSlot.append, if_neg hFirst, Nat.add_sub_cancel, body_width, if_neg hZero]
      by_cases hBody : position < first.val + second.val + 4
      · have hNotPast : ¬ boundary first.val second.val < position + 1 := by unfold boundary; omega
        have hNotFinish : ¬ position + 1 = boundary first.val second.val := by unfold boundary; omega
        rw [if_pos hBody, if_neg hNotPast, if_neg hNotFinish]
      · rw [if_neg hBody]
        by_cases hFinish : position + 1 = boundary first.val second.val
        · have hNotPast : ¬ boundary first.val second.val < position + 1 := by omega
          have hRest : position - (first.val + second.val + 4) = 0 := by unfold boundary at hFinish; omega
          rw [if_neg hNotPast, if_pos hFinish, hRest]
          rfl
        · have hPast : boundary first.val second.val < position + 1 := by unfold boundary at *; omega
          have hRest : ¬ position - (first.val + second.val + 4) = 0 := by unfold boundary at hPast; omega
          rw [if_pos hPast]
          cases hIndex : position - (first.val + second.val + 4) with
          | zero => exact False.elim (hRest hIndex)
          | succ rest => rfl

private theorem configuration_eq (configuration : WorkConfiguration) (state : Nat) (tape : WorkTape)
    (hState : configuration.state = state) (hTape : configuration.tape = tape) :
    configuration = {state := state, tape := tape} := by
  cases configuration
  cases hState
  cases hTape
  rfl

private theorem literal_endpoint_terminal (positive : Bool) (value position : Nat) (hHit : position < value + 2) :
    BuilderLiteralTokenSelector.endpoint positive value position = .accept ∨
      BuilderLiteralTokenSelector.endpoint positive value position = .reject := by
  unfold BuilderLiteralTokenSelector.endpoint BuilderLiteralTokenSelector.unaryEndpoint
  by_cases hZero : position = 0
  · rw [if_pos hZero]
    cases positive
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rw [if_neg hZero]
    by_cases hLess : position - 1 < value
    · rw [if_pos hLess]
      exact Or.inl rfl
    · have hEqual : position - 1 = value := by omega
      rw [if_neg hLess, if_pos hEqual]
      exact Or.inr rfl

theorem body_endpoint_terminal {width : Nat} (first second : Fin width) (position : Nat)
    (hPositive : 0 < position) (hBody : position < boundary first.val second.val) :
    bodyEndpoint first second position = .accept ∨ bodyEndpoint first second position = .reject := by
  unfold bodyEndpoint
  simp only [excludeBoundedPairClause, BuilderLiteralListSearch.endpoint, falseLiteral]
  by_cases hFirst : position - 1 < first.val + 2
  · rw [if_pos hFirst]
    exact literal_endpoint_terminal false first.val (position - 1) hFirst
  · rw [if_neg hFirst]
    have hSecond : BuilderLiteralSearchFrame.residual (position - 1) first.val < second.val + 2 := by
      simp only [BuilderLiteralSearchFrame.residual, if_neg hFirst]
      unfold boundary at hBody
      omega
    rw [if_pos hSecond]
    exact literal_endpoint_terminal false second.val _ hSecond

private theorem frame_suffix (first second position : Nat) (retained older : List Nat) :
    initialValues first second position retained older =
      (older ++ [first] ++ retained ++ [second]) ++ [position] := by
  simp only [initialValues, BuilderExclusionPairLiteralTokens.frame, List.append_assoc, List.cons_append, List.nil_append]

private theorem body_accept_projection :
    bodyNode.program.acceptState = WorkMachineChain.secondState 0 := rfl
private theorem body_reject_projection :
    bodyNode.program.rejectState = WorkMachineChain.secondState 1 := rfl
private theorem body_final_state {width : Nat} (first second : Fin width) (position : Nat)
    (retained older : List Nat) (inside outside : List WorkSymbol) :
    (BuilderExclusionPairLiteralTokens.finalConfiguration first second (position - 1) retained older inside outside).state =
      WorkMachineChain.secondState (endpointState (bodyEndpoint first second position)) := rfl

private theorem body_path {width : Nat} (first second : Fin width) (position : Nat)
    (retained older : List Nat) (hRetained : retained.length = 11) (inside outside : List WorkSymbol)
    (hPositive : 0 < position) (hBody : position < boundary first.val second.val) :
    AcceptPath graph (.node eraseNode.reference) (bodyEndpoint first second position)
      (bodySteps first second position retained hRetained)
      (endTape (BuilderExclusionClauseBoundary.finalValues first.val second.val position retained older) inside
        (BuilderExclusionClauseBoundary.finalOutside first.val second.val position outside))
      (endTape (BuilderExclusionPairLiteralTokens.finalValues first second (position - 1) retained older) inside
        (BuilderExclusionPairLiteralTokens.finalOutside first second (position - 1)
          (bodyOutside first.val second.val position outside))) := by
  have hErase : LocalAcceptRun eraseNode
      (BuilderRegisterErase.workSteps (BuilderExclusionClauseBoundary.scratch first.val second.val position))
      (endTape (BuilderExclusionClauseBoundary.finalValues first.val second.val position retained older) inside
        (BuilderExclusionClauseBoundary.finalOutside first.val second.val position outside))
      (endTape (initialValues first.val second.val position retained older) inside
        (eraseOutside first.val second.val position outside)) := by
    rw [BuilderExclusionClauseBoundary.final_values_layout]
    exact BuilderRegisterErase.workRunExact 9 (initialValues first.val second.val position retained older)
      (BuilderExclusionClauseBoundary.scratch first.val second.val position) inside
      (BuilderExclusionClauseBoundary.finalOutside first.val second.val position outside)
      (BuilderExclusionClauseBoundary.scratch_length _ _ _)
  have hSucc : position - 1 + 1 = position := by omega
  have hDecrement : LocalAcceptRun decrementNode 2
      (endTape (initialValues first.val second.val position retained older) inside
        (eraseOutside first.val second.val position outside))
      (endTape (initialValues first.val second.val (position - 1) retained older) inside
        (bodyOutside first.val second.val position outside)) := by
    have h := BuilderRegisterCountdownControl.decrement_workRunExact (position - 1)
      (registerWord (older ++ [first.val] ++ retained ++ [second.val])) inside
      (eraseOutside first.val second.val position outside)
    rw [frame_suffix, frame_suffix]
    simpa only [LocalAcceptRun, decrementNode, workStartConfiguration, bodyOutside, endTape,
      registerWord_append, registerWord, List.append_nil, List.reverse_append, List.reverse_cons,
      List.reverse_replicate, List.nil_append, List.cons_append, List.append_assoc, hSucc] using h
  have hRun := BuilderExclusionPairLiteralTokens.workRunExact first second (position - 1)
    retained older hRetained inside (bodyOutside first.val second.val position outside)
  have hTape := BuilderExclusionPairLiteralTokens.final_tape first second (position - 1)
    retained older inside (bodyOutside first.val second.val position outside)
  have hTail : AcceptPath graph (.node bodyNode.reference) (bodyEndpoint first second position)
      (BuilderExclusionPairLiteralTokens.workSteps first second (position - 1) retained hRetained + 1)
      (endTape (initialValues first.val second.val (position - 1) retained older) inside
        (bodyOutside first.val second.val position outside))
      (endTape (BuilderExclusionPairLiteralTokens.finalValues first second (position - 1) retained older) inside
        (BuilderExclusionPairLiteralTokens.finalOutside first second (position - 1)
          (bodyOutside first.val second.val position outside))) := by
    rcases body_endpoint_terminal first second position hPositive hBody with hAccept | hReject
    · have hState : (BuilderExclusionPairLiteralTokens.finalConfiguration first second (position - 1)
          retained older inside (bodyOutside first.val second.val position outside)).state = bodyNode.program.acceptState := by
        rw [body_final_state, hAccept, body_accept_projection]
        rfl
      rw [configuration_eq _ _ _ hState hTape] at hRun
      rw [hAccept]
      simpa only [Nat.add_zero] using
        AcceptPath.step bodyNode .accept _ 0 _ _ _ member_5 hRun (.terminal .accept _)
    · have hState : (BuilderExclusionPairLiteralTokens.finalConfiguration first second (position - 1)
          retained older inside (bodyOutside first.val second.val position outside)).state = bodyNode.program.rejectState := by
        rw [body_final_state, hReject, body_reject_projection]
        rfl
      rw [configuration_eq _ _ _ hState hTape] at hRun
      rw [hReject]
      simpa only [Nat.add_zero] using
        AcceptPath.stepReject bodyNode .reject _ 0 _ _ _ member_5 hRun (.terminal .reject _)
  exact AcceptPath.step eraseNode _ _ _ _ _ _ member_3 hErase
    (AcceptPath.step decrementNode _ _ _ _ _ _ member_4 hDecrement hTail)


private theorem boundary_path {width : Nat} (first second : Fin width) (position : Nat)
    (retained older : List Nat) (hRetained : retained.length = 11) (inside outside : List WorkSymbol)
    (hPositive : 0 < position) :
    AcceptPath graph (.node boundaryNode.reference) (endpoint first second position)
      (BuilderExclusionClauseBoundary.workSteps first.val second.val position retained hRetained + 1 +
        afterComparisonSteps first second position retained hRetained)
      (endTape (initialValues first.val second.val position retained older) inside outside)
      (endTape (finalValues first second position retained older) inside (finalOutside first second position outside)) := by
  have hZero : position ≠ 0 := by omega
  have hRun := BuilderExclusionClauseBoundary.workRunExact first.val second.val position retained older hRetained inside outside
  have hTape := BuilderExclusionClauseBoundary.final_tape first.val second.val position retained older inside outside
  by_cases hPast : boundary first.val second.val < position
  · have hState := (BuilderExclusionClauseBoundary.final_accept_iff first.val second.val position retained older inside outside).mpr hPast
    rw [configuration_eq _ _ _ hState hTape] at hRun
    have h := AcceptPath.step boundaryNode .dead _ 0 _ _ _ member_1 hRun (.terminal .dead _)
    simpa only [endpoint, finalValues, finalOutside, afterComparisonSteps, if_neg hZero,
      if_pos hPast, if_pos (Or.inl hPast : boundary first.val second.val < position ∨ position = boundary first.val second.val)] using h
  · have hInside : position ≤ boundary first.val second.val := by omega
    have hState := (BuilderExclusionClauseBoundary.final_reject_iff first.val second.val position retained older inside outside).mpr hInside
    rw [configuration_eq _ _ _ hState hTape] at hRun
    have hSuffix := BuilderExclusionClauseBoundary.residual_suffix first.val second.val position retained older hInside
    let residualOlder := initialValues first.val second.val position retained older ++
      BuilderExclusionClauseBoundary.boundaryPrefix first.val second.val ++
      BuilderRegisterLessThan.resultValues (BuilderExclusionClauseBoundary.result first.val second.val position) ++ [position]
    by_cases hFinish : position = boundary first.val second.val
    · have hResidual : boundary first.val second.val - position = 0 := by omega
      have hTag := BuilderUnaryTagMatch.accept_workRunExact 0 residualOlder inside
        (BuilderExclusionClauseBoundary.finalOutside first.val second.val position outside)
      have hTail : AcceptPath graph (.node residualNode.reference) (.node finishNode.reference)
          (BuilderUnaryTagMatch.workSteps 0 (boundary first.val second.val - position) + 1)
          (endTape (BuilderExclusionClauseBoundary.finalValues first.val second.val position retained older) inside
            (BuilderExclusionClauseBoundary.finalOutside first.val second.val position outside))
          (endTape (BuilderExclusionClauseBoundary.finalValues first.val second.val position retained older) inside
            (BuilderExclusionClauseBoundary.finalOutside first.val second.val position outside)) := by
        rw [hSuffix, hResidual]
        simpa only [Nat.add_zero] using
          AcceptPath.step residualNode (.node finishNode.reference) _ 0 _ _ _ member_2 hTag (.terminal _ _)
      have h := AcceptPath.stepReject boundaryNode _ _ _ _ _ _ member_1 hRun hTail
      simpa only [endpoint, finalValues, finalOutside, afterComparisonSteps, if_neg hZero, if_neg hPast,
        if_pos hFinish, if_pos (Or.inr hFinish : boundary first.val second.val < position ∨ position = boundary first.val second.val), Nat.add_zero] using h
    · have hBody : position < boundary first.val second.val := by omega
      have hResidual : boundary first.val second.val - position ≠ 0 := by omega
      have hTag : LocalRejectRun residualNode (BuilderUnaryTagMatch.workSteps 0 (boundary first.val second.val - position))
          (endTape (BuilderExclusionClauseBoundary.finalValues first.val second.val position retained older) inside
            (BuilderExclusionClauseBoundary.finalOutside first.val second.val position outside))
          (endTape (BuilderExclusionClauseBoundary.finalValues first.val second.val position retained older) inside
            (BuilderExclusionClauseBoundary.finalOutside first.val second.val position outside)) := by
        rw [hSuffix]
        exact BuilderUnaryTagMatch.reject_workRunExact 0 (boundary first.val second.val - position)
          residualOlder inside (BuilderExclusionClauseBoundary.finalOutside first.val second.val position outside) hResidual
      have hBodyPath := body_path first second position retained older hRetained inside outside hPositive hBody
      have hTail := AcceptPath.stepReject residualNode _ _ _ _ _ _ member_2 hTag hBodyPath
      have h := AcceptPath.stepReject boundaryNode _ _ _ _ _ _ member_1 hRun hTail
      simpa only [endpoint, finalValues, finalOutside, afterComparisonSteps, if_neg hZero, if_neg hPast,
        if_neg hFinish, if_neg (show ¬ (boundary first.val second.val < position ∨ position = boundary first.val second.val) from fun h => h.elim hPast hFinish)] using h

private theorem execution_path {width : Nat} (first second : Fin width) (position : Nat)
    (retained older : List Nat) (hRetained : retained.length = 11) (inside outside : List WorkSymbol) :
    AcceptPath graph (.node positionNode.reference) (endpoint first second position)
      (workSteps first second position retained hRetained)
      (endTape (initialValues first.val second.val position retained older) inside outside)
      (endTape (finalValues first second position retained older) inside (finalOutside first second position outside)) := by
  by_cases hZero : position = 0
  · subst position
    have hTag : LocalAcceptRun positionNode (BuilderUnaryTagMatch.workSteps 0 0)
        (endTape (initialValues first.val second.val 0 retained older) inside outside)
        (endTape (initialValues first.val second.val 0 retained older) inside outside) := by
      rw [frame_suffix]
      exact BuilderUnaryTagMatch.accept_workRunExact 0 (older ++ [first.val] ++ retained ++ [second.val]) inside outside
    simpa only [workSteps, endpoint, finalValues, finalOutside, if_pos rfl, ite_true] using
      AcceptPath.step positionNode (.node separatorNode.reference) _ 0 _ _ _ member_0 hTag (.terminal _ _)
  · have hTag : LocalRejectRun positionNode (BuilderUnaryTagMatch.workSteps 0 position)
        (endTape (initialValues first.val second.val position retained older) inside outside)
        (endTape (initialValues first.val second.val position retained older) inside outside) := by
      rw [frame_suffix]
      exact BuilderUnaryTagMatch.reject_workRunExact 0 position (older ++ [first.val] ++ retained ++ [second.val]) inside outside hZero
    simpa only [workSteps, if_neg hZero] using
      AcceptPath.stepReject positionNode _ _ _ _ _ _ member_0 hTag
        (boundary_path first second position retained older hRetained inside outside (by omega))

private theorem start_projection (tape : WorkTape) :
    endpointConfiguration (.node positionNode.reference) tape = workStartConfiguration machine tape := rfl

theorem workRunExact {width : Nat} (first second : Fin width) (position : Nat)
    (retained older : List Nat) (hRetained : retained.length = 11) (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps first second position retained hRetained)
      (initialConfiguration first.val second.val position retained older inside outside) =
      some (finalConfiguration first second position retained older inside outside) := by
  have h := WorkMachineProgramPath.runExact graph _ _ _ _ _ graph_wellFormed
    (execution_path first second position retained older hRetained inside outside)
  rw [start_projection] at h
  exact h

theorem run_compile_exact {width : Nat} (first second : Fin width) (position : Nat)
    (retained older : List Nat) (hRetained : retained.length = 11) (inside outside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps first second position retained hRetained)
      (encodeWorkConfiguration (initialConfiguration first.val second.val position retained older inside outside)) =
      encodeWorkConfiguration (finalConfiguration first second position retained older inside outside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact first second position retained older hRetained inside outside)

theorem final_tape {width : Nat} (first second : Fin width) (position : Nat)
    (retained older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration first second position retained older inside outside).tape =
      endTape (finalValues first second position retained older) inside (finalOutside first second position outside) := rfl


private theorem observe_body_endpoint {width : Nat} (first second : Fin width) (position : Nat)
    (tape : WorkTape) (hPositive : 0 < position) (hBody : position < boundary first.val second.val) :
    observe (endpointConfiguration (bodyEndpoint first second position) tape) =
      DirectToken.boundedLiteralListSlot (excludeBoundedPairClause first second) (position - 1) := by
  rw [← BuilderLiteralListSearch.endpoint_observes_list (excludeBoundedPairClause first second) (position - 1) tape]
  change observe (endpointConfiguration (bodyEndpoint first second position) tape) =
    BuilderLiteralListSearch.observe (endpointConfiguration (bodyEndpoint first second position) tape)
  rcases body_endpoint_terminal first second position hPositive hBody with hAccept | hReject
  · rw [hAccept]
    rfl
  · rw [hReject]
    rfl

private theorem observe_separator (tape : WorkTape) :
    observe (endpointConfiguration (.node separatorNode.reference) tape) = some .sep := rfl
private theorem observe_finish (tape : WorkTape) :
    observe (endpointConfiguration (.node finishNode.reference) tape) = some .finish := rfl
private theorem observe_padding (tape : WorkTape) :
    observe (endpointConfiguration .dead tape) = none := rfl

theorem canonical_result {width : Nat} (first second : Fin width) (position : Nat)
    (retained older : List Nat) (inside outside : List WorkSymbol) :
    observe (finalConfiguration first second position retained older inside outside) =
      (encodeClauseTokens (BoundedClause.emit (excludeBoundedPairClause first second)))[position]? := by
  rw [← DirectToken.clauseSlot_eq_encodeClauseTokens_getElem?, clause_cases]
  unfold finalConfiguration endpoint
  by_cases hZero : position = 0
  · rw [if_pos hZero, if_pos hZero, observe_separator]
  · rw [if_neg hZero, if_neg hZero]
    by_cases hPast : boundary first.val second.val < position
    · rw [if_pos hPast, if_pos hPast, observe_padding]
    · rw [if_neg hPast, if_neg hPast]
      by_cases hFinish : position = boundary first.val second.val
      · rw [if_pos hFinish, if_pos hFinish, observe_finish]
      · rw [if_neg hFinish, if_neg hFinish]
        exact observe_body_endpoint first second position _ (by omega) (by omega)

theorem workRun_observes_encoding {width : Nat} (first second : Fin width) (position : Nat)
    (retained older : List Nat) (hRetained : retained.length = 11) (inside outside : List WorkSymbol) :
    observe (workRun machine (workSteps first second position retained hRetained)
      (initialConfiguration first.val second.val position retained older inside outside)) =
      (encodeClauseTokens (BoundedClause.emit (excludeBoundedPairClause first second)))[position]? := by
  rw [workRun_eq_of_workRunExact _ _ _ _ (workRunExact first second position retained older hRetained inside outside)]
  exact canonical_result first second position retained older inside outside

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise graph graph_wellFormed
theorem noRuleAtAccept : WorkMachineChain.NoRuleAtAccept machine :=
  WorkMachineProgramGraph.noRuleAt_globalAccept graph
theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  WorkMachineProgramGraph.noRuleAt_globalReject graph
theorem noRuleAtPadding : WorkMachineProgramGraph.NoRuleAt machine 2 :=
  WorkMachineProgramGraph.noRuleAt_globalDead graph
theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := by decide

private theorem bridge_source {source target : Nat} {rule : WorkRule}
    (hMem : rule ∈ PipelineStageBridges.launchRules source target) : rule.sourceState = source := by
  rcases List.mem_map.mp hMem with ⟨symbol, _, rfl⟩
  rfl
private theorem local_source {node : Node} {rule : WorkRule} (hMem : rule ∈ node.localRules) :
    ∃ localRule ∈ node.program.rules, rule.sourceState = node.encode localRule.sourceState := by
  rcases List.mem_map.mp hMem with ⟨localRule, hLocal, rfl⟩
  exact ⟨localRule, hLocal, rfl⟩
private theorem node_rule_source {node : Node} {rule : WorkRule} (hMem : rule ∈ node.rules) :
    ∃ localState, rule.sourceState = node.encode localState := by
  simp only [Node.rules, List.mem_append] at hMem
  rcases hMem with hAccept | hReject | hLocal
  · exact ⟨node.program.acceptState, bridge_source hAccept⟩
  · exact ⟨node.program.rejectState, bridge_source hReject⟩
  · rcases local_source hLocal with ⟨localRule, _, hSource⟩
    exact ⟨localRule.sourceState, hSource⟩
private theorem node_no_entry (node : Node)
    (hAccept : node.program.startState ≠ node.program.acceptState)
    (hReject : node.program.startState ≠ node.program.rejectState)
    (hNone : WorkMachineProgramGraph.NoRuleAt node.program node.program.startState)
    (rule : WorkRule) (hMem : rule ∈ node.rules) :
    rule.sourceState ≠ node.encode node.program.startState := by
  intro hEq
  simp only [Node.rules, List.mem_append] at hMem
  rcases hMem with hA | hR | hLocal
  · rw [bridge_source hA] at hEq
    exact hAccept (node.encode_injective hEq).symm
  · rw [bridge_source hR] at hEq
    exact hReject (node.encode_injective hEq).symm
  · rcases local_source hLocal with ⟨localRule, hLocal, hSource⟩
    rw [hSource] at hEq
    exact hNone localRule hLocal (node.encode_injective hEq)

theorem noRuleAtSeparator : WorkMachineProgramGraph.NoRuleAt machine separatorState := by
  intro rule hMem hEq
  change rule ∈ graph.nodes.flatMap Node.rules at hMem
  rcases List.mem_flatMap.mp hMem with ⟨node, hNode, hRule⟩
  rcases node_rule_source hRule with ⟨localState, hSource⟩
  have hName : node.name = 6 := (WorkMachineProgramGraph.nodeState_injective (hSource.symm.trans hEq)).1
  simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hNode
  rcases hNode with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change 0 = 6 at hName; omega
  · change 1 = 6 at hName; omega
  · change 2 = 6 at hName; omega
  · change 3 = 6 at hName; omega
  · change 4 = 6 at hName; omega
  · change 5 = 6 at hName; omega
  · exact node_no_entry separatorNode (by decide) (by decide) (by intro r h; cases h) rule hRule hEq
  · change 7 = 6 at hName; omega

theorem noRuleAtFinish : WorkMachineProgramGraph.NoRuleAt machine finishState := by
  intro rule hMem hEq
  change rule ∈ graph.nodes.flatMap Node.rules at hMem
  rcases List.mem_flatMap.mp hMem with ⟨node, hNode, hRule⟩
  rcases node_rule_source hRule with ⟨localState, hSource⟩
  have hName : node.name = 7 := (WorkMachineProgramGraph.nodeState_injective (hSource.symm.trans hEq)).1
  simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hNode
  rcases hNode with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change 0 = 7 at hName; omega
  · change 1 = 7 at hName; omega
  · change 2 = 7 at hName; omega
  · change 3 = 7 at hName; omega
  · change 4 = 7 at hName; omega
  · change 5 = 7 at hName; omega
  · change 6 = 7 at hName; omega
  · exact node_no_entry finishNode (by decide) (by decide) (by intro r h; cases h) rule hRule hEq


def spanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (BuilderExclusionClauseBoundary.spanPolynomial bound)
    (BuilderExclusionPairLiteralTokens.spanPolynomial (BuilderExclusionClauseBoundary.spanPolynomial bound))
def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.add (.add (.constant 84) (BuilderExclusionClauseBoundary.rawTimePolynomial bound))
    (BuilderRegisterErase.rawTimePolynomial (BuilderExclusionClauseBoundary.spanPolynomial bound)))
    (BuilderExclusionPairLiteralTokens.rawTimePolynomial (BuilderExclusionClauseBoundary.spanPolynomial bound))

theorem body_input_span (first second position : Nat) (retained older : List Nat) (outside : List WorkSymbol)
    (hPositive : 0 < position) :
    (registerWord (initialValues first second (position - 1) retained older)).length +
        (bodyOutside first second position outside).length =
      (registerWord (BuilderExclusionClauseBoundary.finalValues first second position retained older)).length +
        (BuilderExclusionClauseBoundary.finalOutside first second position outside).length := by
  simp only [BuilderExclusionClauseBoundary.final_values_layout, bodyOutside, eraseOutside,
    BuilderRegisterErase.clearedSpan, initialValues, BuilderExclusionPairLiteralTokens.frame, registerWord_append, registerWord,
    List.length_append, List.length_cons, List.length_nil, List.length_replicate]
  omega

theorem source_polynomial_bounds {width : Nat} (first second : Fin width) (position : Nat)
    (retained older : List Nat) (hRetained : retained.length = 11) (outside : List WorkSymbol)
    (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues first.val second.val position retained older)).length +
      outside.length ≤ bound.eval input) :
    (registerWord (finalValues first second position retained older)).length +
        (finalOutside first second position outside).length ≤ (spanPolynomial bound).eval input ∧
      6 * workSteps first second position retained hRetained ≤ (rawTimePolynomial bound).eval input := by
  have hBoundary := BuilderExclusionClauseBoundary.source_polynomial_bounds first.val second.val position
    retained older hRetained outside bound input hSpan
  have hDominates : bound.eval input ≤ (BuilderExclusionClauseBoundary.spanPolynomial bound).eval input := by
    simp only [BuilderExclusionClauseBoundary.spanPolynomial, NatPolynomial.eval_add]
    omega
  by_cases hZero : position = 0
  · constructor
    · simpa only [finalValues, finalOutside, if_pos hZero, spanPolynomial, NatPolynomial.eval_add] using
        Nat.le_trans hSpan (Nat.le_trans hDominates (Nat.le_add_right _ _))
    · simp only [workSteps, if_pos hZero, zero_test_steps, rawTimePolynomial,
        NatPolynomial.eval_add, NatPolynomial.eval_constant]
      omega
  · by_cases hPast : boundary first.val second.val < position
    · have hOutsideCase : boundary first.val second.val < position ∨ position = boundary first.val second.val := Or.inl hPast
      constructor
      · simp only [finalValues, finalOutside, if_neg hZero, if_pos hOutsideCase, spanPolynomial, NatPolynomial.eval_add]
        omega
      · have hTime := hBoundary.2
        simp only [workSteps, afterComparisonSteps, if_neg hZero, if_pos hPast, zero_test_steps,
          rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
        omega
    · by_cases hFinish : position = boundary first.val second.val
      · have hOutsideCase : boundary first.val second.val < position ∨ position = boundary first.val second.val := Or.inr hFinish
        constructor
        · simp only [finalValues, finalOutside, if_neg hZero, if_pos hOutsideCase, spanPolynomial, NatPolynomial.eval_add]
          omega
        · have hTime := hBoundary.2
          simp only [workSteps, afterComparisonSteps, if_neg hZero, if_neg hPast, if_pos hFinish, zero_test_steps,
            rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
          omega
      · have hOutsideCase : ¬ (boundary first.val second.val < position ∨ position = boundary first.val second.val) :=
          fun h => h.elim hPast hFinish
        have hBodySpan : (registerWord (initialValues first.val second.val (position - 1) retained older)).length +
            (bodyOutside first.val second.val position outside).length ≤
              (BuilderExclusionClauseBoundary.spanPolynomial bound).eval input := by
          rw [body_input_span _ _ _ _ _ _ (by omega)]
          exact hBoundary.1
        have hBody := BuilderExclusionPairLiteralTokens.source_polynomial_bounds first second (position - 1)
          retained older hRetained (bodyOutside first.val second.val position outside)
          (BuilderExclusionClauseBoundary.spanPolynomial bound) input hBodySpan
        have hScratch : BuilderRegisterErase.clearedSpan (BuilderExclusionClauseBoundary.scratch first.val second.val position) ≤
            (BuilderExclusionClauseBoundary.spanPolynomial bound).eval input := by
          have h := hBoundary.1
          rw [BuilderExclusionClauseBoundary.final_values_layout, registerWord_append, List.length_append] at h
          exact Nat.le_trans (by unfold BuilderRegisterErase.clearedSpan; omega) h
        have hErase := BuilderRegisterErase.source_polynomial_bound
          (BuilderExclusionClauseBoundary.spanPolynomial bound) input
          (BuilderExclusionClauseBoundary.scratch first.val second.val position) hScratch
        constructor
        · have hOutput := hBody.1
          simp only [finalValues, finalOutside, if_neg hZero, if_neg hOutsideCase, spanPolynomial, NatPolynomial.eval_add]
          omega
        · have hBoundaryTime := hBoundary.2
          have hBodyTime := hBody.2
          simp only [workSteps, afterComparisonSteps, bodySteps, if_neg hZero, if_neg hPast, if_neg hFinish, zero_test_steps,
            rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
          omega

theorem uniform_polynomial_lookup {width : Nat} (first second : Fin width) (position : Nat)
    (retained older : List Nat) (hRetained : retained.length = 11) (inside outside : List WorkSymbol)
    (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues first.val second.val position retained older)).length +
      outside.length ≤ bound.eval input) :
    ∃ rawSteps, rawSteps ≤ (rawTimePolynomial bound).eval input ∧
      run (compileWorkMachine machine) rawSteps
        (encodeWorkConfiguration (initialConfiguration first.val second.val position retained older inside outside)) =
        encodeWorkConfiguration (finalConfiguration first second position retained older inside outside) ∧
      observe (finalConfiguration first second position retained older inside outside) =
        (encodeClauseTokens (BoundedClause.emit (excludeBoundedPairClause first second)))[position]? ∧
      (registerWord (finalValues first second position retained older)).length +
        (finalOutside first second position outside).length ≤ (spanPolynomial bound).eval input := by
  have hBounds := source_polynomial_bounds first second position retained older hRetained outside bound input hSpan
  exact ⟨6 * workSteps first second position retained hRetained, hBounds.2,
    run_compile_exact first second position retained older hRetained inside outside,
    canonical_result first second position retained older inside outside, hBounds.1⟩

end PNP.Concrete.CookLevin.BuilderExclusionClauseTokenSelector
