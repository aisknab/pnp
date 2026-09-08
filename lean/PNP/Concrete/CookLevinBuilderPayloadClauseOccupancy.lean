/-
Copyright (c) 2026 PNP Labs.

One finite program derives clause occupancy from a physically written canonical
payload and local coordinate. The temporary tag copy is erased; every original
payload cell and the coordinate survive. Exactly-one counts are copied from
the payload itself, including the empty list. No clause or pair enumeration.
Absent coordinates remain distinct from in-range padded opportunities.
-/
import PNP.Concrete.CookLevinBuilderLocalConstraintPayload
import PNP.Concrete.CookLevinBuilderExactlyOneClauseOccupancy
import PNP.Concrete.CookLevinBuilderRegisterErase
import PNP.Concrete.CookLevinBuilderUnaryTagMatch

namespace PNP.Concrete.CookLevin.BuilderPayloadClauseOccupancy

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderLocalConstraintPayload (Slot values)
open WorkMachineProgramGraph (Node Graph Endpoint endpointConfiguration)
open WorkMachineProgramPath (AcceptPath LocalAcceptRun LocalRejectRun)

def tag {width : Nat} : Slot width → Nat
  | none => 0
  | some none => 1
  | some (some (.require _)) => 2
  | some (some (.implication _ _)) => 3
  | some (some (.exactlyOne _)) => 4
def beforeTag {width : Nat} (slot : Slot width) : List Nat :=
  (BuilderLocalConstraintPayload.front slot).tail.reverse

theorem values_suffix {width : Nat} (slot : Slot width) : values slot = beforeTag slot ++ [tag slot] := by
  cases slot with
  | none => rfl
  | some item =>
      cases item with
      | none => rfl
      | some constraint =>
          cases constraint <;>
            simp only [values, BuilderLocalConstraintPayload.front, beforeTag, tag,
              List.cons_append, List.tail_cons, List.reverse_cons, List.append_assoc]

theorem tag_le {width : Nat} (slot : Slot width) : tag slot ≤ 4 := by
  cases slot with
  | none => change 0 ≤ 4; decide
  | some item =>
      cases item with
      | none => change 1 ≤ 4; decide
      | some constraint => cases constraint <;> simp only [tag] <;> decide

theorem exactly_one_values {width : Nat} (variables : List (Fin width)) :
    values (some (some (.exactlyOne variables))) =
      (BuilderLocalConstraintPayload.variableValues variables).reverse ++ [variables.length, 4] := by
  simp only [values, BuilderLocalConstraintPayload.front, List.reverse_append]
  rfl

def endpoint {width : Nat} : Slot width → Nat → Endpoint
  | none, _ => .dead
  | some none, _ => .reject
  | some (some constraint), index => if index < constraint.clauseCount then .accept else .reject
def result {width : Nat} (slot : Slot width) (index : Nat) : Option Bool :=
  slot.map (fun item => match item with | none => false | some constraint => ClauseOccupancy.localSlot constraint index)
def observe (configuration : WorkConfiguration) : Option Bool :=
  if configuration.state = 0 then some true else if configuration.state = 1 then some false else none

def singleNode : Node :=
  {name := 9, program := BuilderUnaryTagMatch.machine 0, onAccept := .accept, onReject := .reject}
def manyNode : Node :=
  {name := 12, program := BuilderExactlyOneClauseOccupancy.machine, onAccept := .accept, onReject := .reject}
def countNode : Node :=
  {name := 11, program := RegisterCopy.machine 2, onAccept := .node manyNode.reference, onReject := .dead}
def eraseAbsentNode : Node :=
  {name := 6, program := BuilderRegisterErase.oneMachine, onAccept := .dead, onReject := .dead}
def erasePaddingNode : Node :=
  {name := 7, program := BuilderRegisterErase.oneMachine, onAccept := .reject, onReject := .dead}
def eraseSingleNode : Node :=
  {name := 8, program := BuilderRegisterErase.oneMachine, onAccept := .node singleNode.reference, onReject := .dead}
def eraseManyNode : Node :=
  {name := 10, program := BuilderRegisterErase.oneMachine, onAccept := .node countNode.reference, onReject := .dead}
def eraseNode : Nat → Node
  | 0 => eraseAbsentNode
  | 1 => erasePaddingNode
  | 2 | 3 => eraseSingleNode
  | _ => eraseManyNode
def testNode (code : Nat) : Node :=
  {name := code + 1, program := BuilderUnaryTagMatch.machine code,
   onAccept := .node (eraseNode code).reference,
   onReject := if code < 4 then .node {name := code + 2, startState := (BuilderUnaryTagMatch.machine (code + 1)).startState}
               else .dead}
def copyTagNode : Node :=
  {name := 0, program := RegisterCopy.machine 1, onAccept := .node (testNode 0).reference, onReject := .dead}
def graph : Graph :=
  {nodes := [copyTagNode, testNode 0, testNode 1, testNode 2, testNode 3, testNode 4,
    eraseAbsentNode, erasePaddingNode, eraseSingleNode, singleNode, eraseManyNode, countNode, manyNode],
   entry := copyTagNode.reference}
def machine : WorkMachine := WorkMachineProgramGraph.machine graph

theorem graph_nodes_length : graph.nodes.length = 13 := rfl

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
private theorem many_good : Good BuilderExactlyOneClauseOccupancy.machine :=
  ⟨BuilderExactlyOneClauseOccupancy.rules_pairwise_query_distinct, BuilderExactlyOneClauseOccupancy.noRuleAtAccept,
   BuilderExactlyOneClauseOccupancy.noRuleAtReject, BuilderExactlyOneClauseOccupancy.acceptState_ne_rejectState⟩

private theorem node_mem_0 : copyTagNode ∈ graph.nodes := List.Mem.head _
private theorem node_mem_1 : testNode 0 ∈ graph.nodes := List.Mem.tail _ (List.Mem.head _)
private theorem node_mem_2 : testNode 1 ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
private theorem node_mem_3 : testNode 2 ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
private theorem node_mem_4 : testNode 3 ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
private theorem node_mem_5 : testNode 4 ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
private theorem node_mem_6 : eraseAbsentNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
private theorem node_mem_7 : erasePaddingNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
private theorem node_mem_8 : eraseSingleNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
private theorem node_mem_9 : singleNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))
private theorem node_mem_10 : eraseManyNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))
private theorem node_mem_11 : countNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))
private theorem node_mem_12 : manyNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))

private theorem test_mem (code : Nat) (hCode : code ≤ 4) : testNode code ∈ graph.nodes := by
  have h : code = 0 ∨ code = 1 ∨ code = 2 ∨ code = 3 ∨ code = 4 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl
  · exact node_mem_1
  · exact node_mem_2
  · exact node_mem_3
  · exact node_mem_4
  · exact node_mem_5
private theorem erase_mem (code : Nat) : eraseNode code ∈ graph.nodes := by
  cases code with
  | zero => exact node_mem_6
  | succ code =>
      cases code with
      | zero => exact node_mem_7
      | succ code =>
          cases code with
          | zero => exact node_mem_8
          | succ code =>
              cases code with
              | zero => exact node_mem_8
              | succ code => exact node_mem_10

theorem graph_wellFormed : graph.WellFormed := by
  have hNames : (graph.nodes.map Node.name).Pairwise (fun a b : Nat => a ≠ b) := by
    change ([0,1,2,3,4,5,6,7,8,9,10,11,12] : List Nat).Pairwise _
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.pairwise_map] using hNames
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact copy_good 1
    · exact tag_good 0
    · exact tag_good 1
    · exact tag_good 2
    · exact tag_good 3
    · exact tag_good 4
    · exact erase_good
    · exact erase_good
    · exact erase_good
    · exact tag_good 0
    · exact erase_good
    · exact copy_good 2
    · exact many_good
  · exact ⟨copyTagNode, node_mem_0, rfl, rfl⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨testNode 0, node_mem_1, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨eraseAbsentNode, node_mem_6, rfl, rfl⟩, ⟨testNode 1, node_mem_2, rfl, rfl⟩⟩
    · exact ⟨⟨erasePaddingNode, node_mem_7, rfl, rfl⟩, ⟨testNode 2, node_mem_3, rfl, rfl⟩⟩
    · exact ⟨⟨eraseSingleNode, node_mem_8, rfl, rfl⟩, ⟨testNode 3, node_mem_4, rfl, rfl⟩⟩
    · exact ⟨⟨eraseSingleNode, node_mem_8, rfl, rfl⟩, ⟨testNode 4, node_mem_5, rfl, rfl⟩⟩
    · exact ⟨⟨eraseManyNode, node_mem_10, rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨⟨singleNode, node_mem_9, rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨⟨countNode, node_mem_11, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨manyNode, node_mem_12, rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, True.intro⟩

def testSteps : Nat → Nat
  | 0 => 4 | 1 => 10 | 2 => 18 | 3 => 28 | _ => 40
def copiedOutside (code : Nat) (outside : List WorkSymbol) : List WorkSymbol := outside.drop (code + 1)
def restoredOutside (code : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  List.replicate (code + 1) WorkSymbol.blank ++ copiedOutside code outside
def singleEndpoint (index : Nat) : Endpoint := if index = 0 then .accept else .reject
def manyEndpoint (index count : Nat) : Endpoint :=
  if index < 1 + LocalConstraint.pairCount count then .accept else .reject
def branchSteps {width : Nat} : Slot width → Nat → Nat
  | none, _ | some none, _ => 0
  | some (some (.require _)), index | some (some (.implication _ _)), index =>
      BuilderUnaryTagMatch.workSteps 0 index + 1
  | some (some (.exactlyOne variables)), index =>
      RegisterCopy.steps [4, index] variables.length + 1 +
        (BuilderExactlyOneClauseOccupancy.workSteps index variables.length + 1)
def workSteps {width : Nat} (slot : Slot width) (index : Nat) : Nat :=
  RegisterCopy.steps [index] (tag slot) + 1 +
    (testSteps (tag slot) + (tag slot + 2 + 1 + branchSteps slot index))
def finalValues {width : Nat} (slot : Slot width) (index : Nat) (older : List Nat) : List Nat :=
  older ++ values slot ++
    match slot with
    | some (some (.exactlyOne variables)) => BuilderExactlyOneClauseOccupancy.history index variables.length
    | _ => [index]
def finalOutside {width : Nat} (slot : Slot width) (index : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  match slot with
  | some (some (.exactlyOne variables)) =>
      BuilderExactlyOneClauseOccupancy.finalOutside index variables.length
        ((restoredOutside 4 outside).drop (variables.length + 1))
  | _ => restoredOutside (tag slot) outside
def initialConfiguration {width : Nat} (slot : Slot width) (index : Nat)
    (older : List Nat) (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration machine (endTape (older ++ values slot ++ [index]) inside outside)
def finalConfiguration {width : Nat} (slot : Slot width) (index : Nat)
    (older : List Nat) (inside outside : List WorkSymbol) : WorkConfiguration :=
  endpointConfiguration (endpoint slot index) (endTape (finalValues slot index older) inside (finalOutside slot index outside))

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

private theorem tests_path (code : Nat) (hCode : code ≤ 4) (finish : Endpoint) (steps : Nat)
    (older : List Nat) (inside outside : List WorkSymbol) (final : WorkTape)
    (hTail : AcceptPath graph (.node (eraseNode code).reference) finish steps
      (endTape (older ++ [code]) inside outside) final) :
    AcceptPath graph (.node (testNode 0).reference) finish (testSteps code + steps)
      (endTape (older ++ [code]) inside outside) final := by
  have hCases : code = 0 ∨ code = 1 ∨ code = 2 ∨ code = 3 ∨ code = 4 := by omega
  rcases hCases with rfl | rfl | rfl | rfl | rfl
  · have hMatch : LocalAcceptRun (testNode 0) (BuilderUnaryTagMatch.workSteps 0 0)
        (endTape (older ++ [0]) inside outside) (endTape (older ++ [0]) inside outside) :=
      BuilderUnaryTagMatch.accept_workRunExact 0 older inside outside
    have h0 := AcceptPath.step (testNode 0) finish _ _ _ _ _ node_mem_1 hMatch hTail
    have hClock : (BuilderUnaryTagMatch.workSteps 0 0 + 1 + steps) = testSteps 0 + steps := by
      change (3 + 1 + steps) = 4 + steps
      omega
    rw [hClock] at h0
    exact h0
  · have hMatch : LocalAcceptRun (testNode 1) (BuilderUnaryTagMatch.workSteps 1 1)
        (endTape (older ++ [1]) inside outside) (endTape (older ++ [1]) inside outside) :=
      BuilderUnaryTagMatch.accept_workRunExact 1 older inside outside
    have h1 := AcceptPath.step (testNode 1) finish _ _ _ _ _ node_mem_2 hMatch hTail
    have hNo0 : LocalRejectRun (testNode 0) (BuilderUnaryTagMatch.workSteps 0 1)
        (endTape (older ++ [1]) inside outside) (endTape (older ++ [1]) inside outside) :=
      BuilderUnaryTagMatch.reject_workRunExact 0 1 older inside outside (by decide)
    have h0 := AcceptPath.stepReject (testNode 0) finish _ _ _ _ _ node_mem_1 hNo0 h1
    have hClock : (BuilderUnaryTagMatch.workSteps 0 1 + 1 + (BuilderUnaryTagMatch.workSteps 1 1 + 1 + steps)) = testSteps 1 + steps := by
      change (3 + 1 + (5 + 1 + steps)) = 10 + steps
      omega
    rw [hClock] at h0
    exact h0
  · have hMatch : LocalAcceptRun (testNode 2) (BuilderUnaryTagMatch.workSteps 2 2)
        (endTape (older ++ [2]) inside outside) (endTape (older ++ [2]) inside outside) :=
      BuilderUnaryTagMatch.accept_workRunExact 2 older inside outside
    have h2 := AcceptPath.step (testNode 2) finish _ _ _ _ _ node_mem_3 hMatch hTail
    have hNo1 : LocalRejectRun (testNode 1) (BuilderUnaryTagMatch.workSteps 1 2)
        (endTape (older ++ [2]) inside outside) (endTape (older ++ [2]) inside outside) :=
      BuilderUnaryTagMatch.reject_workRunExact 1 2 older inside outside (by decide)
    have h1 := AcceptPath.stepReject (testNode 1) finish _ _ _ _ _ node_mem_2 hNo1 h2
    have hNo0 : LocalRejectRun (testNode 0) (BuilderUnaryTagMatch.workSteps 0 2)
        (endTape (older ++ [2]) inside outside) (endTape (older ++ [2]) inside outside) :=
      BuilderUnaryTagMatch.reject_workRunExact 0 2 older inside outside (by decide)
    have h0 := AcceptPath.stepReject (testNode 0) finish _ _ _ _ _ node_mem_1 hNo0 h1
    have hClock : (BuilderUnaryTagMatch.workSteps 0 2 + 1 + (BuilderUnaryTagMatch.workSteps 1 2 + 1 + (BuilderUnaryTagMatch.workSteps 2 2 + 1 + steps))) = testSteps 2 + steps := by
      change (3 + 1 + (5 + 1 + (7 + 1 + steps))) = 18 + steps
      omega
    rw [hClock] at h0
    exact h0
  · have hMatch : LocalAcceptRun (testNode 3) (BuilderUnaryTagMatch.workSteps 3 3)
        (endTape (older ++ [3]) inside outside) (endTape (older ++ [3]) inside outside) :=
      BuilderUnaryTagMatch.accept_workRunExact 3 older inside outside
    have h3 := AcceptPath.step (testNode 3) finish _ _ _ _ _ node_mem_4 hMatch hTail
    have hNo2 : LocalRejectRun (testNode 2) (BuilderUnaryTagMatch.workSteps 2 3)
        (endTape (older ++ [3]) inside outside) (endTape (older ++ [3]) inside outside) :=
      BuilderUnaryTagMatch.reject_workRunExact 2 3 older inside outside (by decide)
    have h2 := AcceptPath.stepReject (testNode 2) finish _ _ _ _ _ node_mem_3 hNo2 h3
    have hNo1 : LocalRejectRun (testNode 1) (BuilderUnaryTagMatch.workSteps 1 3)
        (endTape (older ++ [3]) inside outside) (endTape (older ++ [3]) inside outside) :=
      BuilderUnaryTagMatch.reject_workRunExact 1 3 older inside outside (by decide)
    have h1 := AcceptPath.stepReject (testNode 1) finish _ _ _ _ _ node_mem_2 hNo1 h2
    have hNo0 : LocalRejectRun (testNode 0) (BuilderUnaryTagMatch.workSteps 0 3)
        (endTape (older ++ [3]) inside outside) (endTape (older ++ [3]) inside outside) :=
      BuilderUnaryTagMatch.reject_workRunExact 0 3 older inside outside (by decide)
    have h0 := AcceptPath.stepReject (testNode 0) finish _ _ _ _ _ node_mem_1 hNo0 h1
    have hClock : (BuilderUnaryTagMatch.workSteps 0 3 + 1 + (BuilderUnaryTagMatch.workSteps 1 3 + 1 + (BuilderUnaryTagMatch.workSteps 2 3 + 1 + (BuilderUnaryTagMatch.workSteps 3 3 + 1 + steps)))) = testSteps 3 + steps := by
      change (3 + 1 + (5 + 1 + (7 + 1 + (9 + 1 + steps)))) = 28 + steps
      omega
    rw [hClock] at h0
    exact h0
  · have hMatch : LocalAcceptRun (testNode 4) (BuilderUnaryTagMatch.workSteps 4 4)
        (endTape (older ++ [4]) inside outside) (endTape (older ++ [4]) inside outside) :=
      BuilderUnaryTagMatch.accept_workRunExact 4 older inside outside
    have h4 := AcceptPath.step (testNode 4) finish _ _ _ _ _ node_mem_5 hMatch hTail
    have hNo3 : LocalRejectRun (testNode 3) (BuilderUnaryTagMatch.workSteps 3 4)
        (endTape (older ++ [4]) inside outside) (endTape (older ++ [4]) inside outside) :=
      BuilderUnaryTagMatch.reject_workRunExact 3 4 older inside outside (by decide)
    have h3 := AcceptPath.stepReject (testNode 3) finish _ _ _ _ _ node_mem_4 hNo3 h4
    have hNo2 : LocalRejectRun (testNode 2) (BuilderUnaryTagMatch.workSteps 2 4)
        (endTape (older ++ [4]) inside outside) (endTape (older ++ [4]) inside outside) :=
      BuilderUnaryTagMatch.reject_workRunExact 2 4 older inside outside (by decide)
    have h2 := AcceptPath.stepReject (testNode 2) finish _ _ _ _ _ node_mem_3 hNo2 h3
    have hNo1 : LocalRejectRun (testNode 1) (BuilderUnaryTagMatch.workSteps 1 4)
        (endTape (older ++ [4]) inside outside) (endTape (older ++ [4]) inside outside) :=
      BuilderUnaryTagMatch.reject_workRunExact 1 4 older inside outside (by decide)
    have h1 := AcceptPath.stepReject (testNode 1) finish _ _ _ _ _ node_mem_2 hNo1 h2
    have hNo0 : LocalRejectRun (testNode 0) (BuilderUnaryTagMatch.workSteps 0 4)
        (endTape (older ++ [4]) inside outside) (endTape (older ++ [4]) inside outside) :=
      BuilderUnaryTagMatch.reject_workRunExact 0 4 older inside outside (by decide)
    have h0 := AcceptPath.stepReject (testNode 0) finish _ _ _ _ _ node_mem_1 hNo0 h1
    have hClock : (BuilderUnaryTagMatch.workSteps 0 4 + 1 + (BuilderUnaryTagMatch.workSteps 1 4 + 1 + (BuilderUnaryTagMatch.workSteps 2 4 + 1 + (BuilderUnaryTagMatch.workSteps 3 4 + 1 + (BuilderUnaryTagMatch.workSteps 4 4 + 1 + steps))))) = testSteps 4 + steps := by
      change (3 + 1 + (5 + 1 + (7 + 1 + (9 + 1 + (11 + 1 + steps))))) = 40 + steps
      omega
    rw [hClock] at h0
    exact h0

private theorem single_path (index : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    AcceptPath graph (.node singleNode.reference) (singleEndpoint index) (BuilderUnaryTagMatch.workSteps 0 index + 1)
      (endTape (older ++ [index]) inside outside) (endTape (older ++ [index]) inside outside) := by
  by_cases hZero : index = 0
  · subst index
    have hRun : LocalAcceptRun singleNode (BuilderUnaryTagMatch.workSteps 0 0)
        (endTape (older ++ [0]) inside outside) (endTape (older ++ [0]) inside outside) :=
      BuilderUnaryTagMatch.accept_workRunExact 0 older inside outside
    have h := AcceptPath.step singleNode .accept _ 0 _ _ _ node_mem_9 hRun (.terminal .accept _)
    simpa only [singleEndpoint, ite_true, Nat.add_zero] using h
  · have hRun : LocalRejectRun singleNode (BuilderUnaryTagMatch.workSteps 0 index)
        (endTape (older ++ [index]) inside outside) (endTape (older ++ [index]) inside outside) :=
      BuilderUnaryTagMatch.reject_workRunExact 0 index older inside outside hZero
    have h := AcceptPath.stepReject singleNode .reject _ 0 _ _ _ node_mem_9 hRun (.terminal .reject _)
    simpa only [singleEndpoint, if_neg hZero, Nat.add_zero] using h

private theorem many_path (index count : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    AcceptPath graph (.node manyNode.reference) (manyEndpoint index count)
      (BuilderExactlyOneClauseOccupancy.workSteps index count + 1)
      (endTape (older ++ [index, count]) inside outside)
      (endTape (older ++ BuilderExactlyOneClauseOccupancy.history index count) inside
        (BuilderExactlyOneClauseOccupancy.finalOutside index count outside)) := by
  have hRun := BuilderExactlyOneClauseOccupancy.workRunExact index count older inside outside
  simp only [BuilderExactlyOneClauseOccupancy.initialConfiguration] at hRun
  have hTape := BuilderExactlyOneClauseOccupancy.final_tape index count older inside outside
  by_cases hOccupied : index < 1 + LocalConstraint.pairCount count
  · have hState := (BuilderExactlyOneClauseOccupancy.final_accept_iff index count older inside outside).mpr hOccupied
    rw [configuration_eq _ _ _ hState hTape] at hRun
    have h := AcceptPath.step manyNode .accept _ 0 _ _ _ node_mem_12 hRun (.terminal .accept _)
    simpa only [manyEndpoint, if_pos hOccupied, Nat.add_zero] using h
  · have hState := (BuilderExactlyOneClauseOccupancy.final_reject_iff index count older inside outside).mpr
      (Nat.le_of_not_gt hOccupied)
    rw [configuration_eq _ _ _ hState hTape] at hRun
    have h := AcceptPath.stepReject manyNode .reject _ 0 _ _ _ node_mem_12 hRun (.terminal .reject _)
    simpa only [manyEndpoint, if_neg hOccupied, Nat.add_zero] using h

private theorem branch_path {width : Nat} (slot : Slot width) (index : Nat)
    (older : List Nat) (inside outside : List WorkSymbol) :
    AcceptPath graph (eraseNode (tag slot)).onAccept (endpoint slot index) (branchSteps slot index)
      (endTape (older ++ values slot ++ [index]) inside (restoredOutside (tag slot) outside))
      (endTape (finalValues slot index older) inside (finalOutside slot index outside)) := by
  cases slot with
  | none => exact .terminal .dead _
  | some item =>
      cases item with
      | none => exact .terminal .reject _
      | some constraint =>
          cases constraint with
          | require literal =>
              simpa only [tag, eraseNode, eraseSingleNode, endpoint, LocalConstraint.clauseCount, Nat.lt_one_iff,
                branchSteps, finalValues, finalOutside, singleEndpoint] using
                single_path index (older ++ values (some (some (.require literal)))) inside (restoredOutside 2 outside)
          | implication premises conclusion =>
              simpa only [tag, eraseNode, eraseSingleNode, endpoint, LocalConstraint.clauseCount, Nat.lt_one_iff,
                branchSteps, finalValues, finalOutside, singleEndpoint] using
                single_path index (older ++ values (some (some (.implication premises conclusion)))) inside (restoredOutside 3 outside)
          | exactlyOne variables =>
              have hCount := copy_run 2 (older ++ (BuilderLocalConstraintPayload.variableValues variables).reverse)
                variables.length [4, index] inside (restoredOutside 4 outside) rfl
              have hCount' : LocalAcceptRun countNode (RegisterCopy.steps [4, index] variables.length)
                  (endTape (older ++ values (some (some (.exactlyOne variables))) ++ [index]) inside (restoredOutside 4 outside))
                  (endTape (older ++ values (some (some (.exactlyOne variables))) ++ [index, variables.length])
                    inside ((restoredOutside 4 outside).drop (variables.length + 1))) := by
                simpa only [LocalAcceptRun, countNode, workStartConfiguration, exactly_one_values,
                  List.append_assoc, List.cons_append, List.nil_append] using hCount
              have hMany := many_path index variables.length (older ++ values (some (some (.exactlyOne variables))))
                inside ((restoredOutside 4 outside).drop (variables.length + 1))
              have h := AcceptPath.step countNode (manyEndpoint index variables.length) _ _ _ _ _ node_mem_11 hCount' hMany
              simp only [tag, eraseNode, eraseManyNode, endpoint, LocalConstraint.clauseCount,
                branchSteps, finalValues, finalOutside, manyEndpoint] at h ⊢
              exact h

private theorem erase_path {width : Nat} (slot : Slot width) (index : Nat)
    (older : List Nat) (inside outside : List WorkSymbol) :
    AcceptPath graph (.node (eraseNode (tag slot)).reference) (endpoint slot index)
      (tag slot + 2 + 1 + branchSteps slot index)
      (endTape (older ++ values slot ++ [index] ++ [tag slot]) inside (copiedOutside (tag slot) outside))
      (endTape (finalValues slot index older) inside (finalOutside slot index outside)) := by
  have hErase : LocalAcceptRun (eraseNode (tag slot)) (tag slot + 2)
      (endTape (older ++ values slot ++ [index] ++ [tag slot]) inside (copiedOutside (tag slot) outside))
      (endTape (older ++ values slot ++ [index]) inside (restoredOutside (tag slot) outside)) := by
    have h := BuilderRegisterErase.one_workRunExact (older ++ values slot ++ [index]) (tag slot)
      inside (copiedOutside (tag slot) outside)
    have hProgram : (eraseNode (tag slot)).program = BuilderRegisterErase.oneMachine := by
      cases slot with
      | none => rfl
      | some item =>
          cases item with
          | none => rfl
          | some constraint => cases constraint <;> rfl
    simpa only [LocalAcceptRun, workStartConfiguration, hProgram, restoredOutside] using h
  exact AcceptPath.step (eraseNode (tag slot)) (endpoint slot index) _ _ _ _ _
    (erase_mem (tag slot)) hErase (branch_path slot index older inside outside)

theorem workRunExact {width : Nat} (slot : Slot width) (index : Nat)
    (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps slot index) (initialConfiguration slot index older inside outside) =
      some (finalConfiguration slot index older inside outside) := by
  have hCopy := copy_run 1 (older ++ beforeTag slot) (tag slot) [index] inside outside rfl
  have hCopy' : LocalAcceptRun copyTagNode (RegisterCopy.steps [index] (tag slot))
      (endTape (older ++ values slot ++ [index]) inside outside)
      (endTape (older ++ values slot ++ [index] ++ [tag slot]) inside (copiedOutside (tag slot) outside)) := by
    simpa only [LocalAcceptRun, copyTagNode, workStartConfiguration, values_suffix,
      List.append_assoc, copiedOutside] using hCopy
  have hErase := erase_path slot index older inside outside
  have hTests := tests_path (tag slot) (tag_le slot) (endpoint slot index) _
    (older ++ values slot ++ [index]) inside (copiedOutside (tag slot) outside) _ hErase
  have hPath := AcceptPath.step copyTagNode (endpoint slot index) _ _ _ _ _ node_mem_0 hCopy' hTests
  have hRun := WorkMachineProgramPath.runExact graph _ _ _ _ _ graph_wellFormed hPath
  have hInitial (tape : WorkTape) :
      endpointConfiguration (.node copyTagNode.reference) tape = workStartConfiguration machine tape := rfl
  rw [hInitial] at hRun
  simpa only [machine, workSteps, initialConfiguration, finalConfiguration] using hRun

theorem run_compile_exact {width : Nat} (slot : Slot width) (index : Nat)
    (older : List Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps slot index)
      (encodeWorkConfiguration (initialConfiguration slot index older inside outside)) =
      encodeWorkConfiguration (finalConfiguration slot index older inside outside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact slot index older inside outside)

theorem final_tape {width : Nat} (slot : Slot width) (index : Nat)
    (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration slot index older inside outside).tape =
      endTape (finalValues slot index older) inside (finalOutside slot index outside) := rfl

theorem canonical_result {width : Nat} (slot : Slot width) (index : Nat)
    (older : List Nat) (inside outside : List WorkSymbol) :
    observe (finalConfiguration slot index older inside outside) = result slot index := by
  cases slot with
  | none => rfl
  | some item =>
      cases item with
      | none => rfl
      | some constraint =>
          by_cases hOccupied : index < constraint.clauseCount
          · simp only [finalConfiguration, endpoint, if_pos hOccupied, endpointConfiguration,
              WorkMachineProgramGraph.endpointState, WorkMachineProgramGraph.globalAcceptState,
              observe, if_pos rfl, result, Option.map_some, ClauseOccupancy.localSlot, hOccupied, ite_true, decide_true]
          · simp only [finalConfiguration, endpoint, if_neg hOccupied, endpointConfiguration,
              WorkMachineProgramGraph.endpointState, WorkMachineProgramGraph.globalRejectState,
              observe, if_neg (by decide : ¬ (1 : Nat) = 0), if_pos rfl, result, Option.map_some,
              ClauseOccupancy.localSlot, hOccupied, ite_false, ite_true, decide_false]

theorem absent_not_padding {width : Nat} (index : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    observe (finalConfiguration (none : Slot width) index older inside outside) = none ∧
      observe (finalConfiguration (some none : Slot width) index older inside outside) = some false := ⟨rfl, rfl⟩
theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise graph graph_wellFormed
theorem noRuleAtAccept : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState :=
  WorkMachineProgramGraph.noRuleAt_globalAccept graph
theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  WorkMachineProgramGraph.noRuleAt_globalReject graph
theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := by
  change (0 : Nat) ≠ 1
  decide

private theorem append_span (registers : List Nat) (value : Nat) :
    (registerWord (registers ++ [value])).length = (registerWord registers).length + value + 1 := by
  rw [registerWord_append, List.length_append]
  simp only [registerWord, List.length_cons, List.length_append, List.length_replicate, List.length_nil]
  omega

private theorem restored_length_le (code : Nat) (outside : List WorkSymbol) :
    (restoredOutside code outside).length ≤ outside.length + code + 1 := by
  simp only [restoredOutside, copiedOutside, List.length_append, List.length_replicate, List.length_drop]
  omega

theorem testSteps_le (code : Nat) : testSteps code ≤ 40 := by
  cases code with
  | zero => decide
  | succ code =>
      cases code with
      | zero => decide
      | succ code =>
          cases code with
          | zero => decide
          | succ code =>
              cases code with
              | zero => decide
              | succ code => exact Nat.le_refl 40

def copyWorkBound (bound : Nat) : Nat := 4 * (bound + 9) * (bound + 9) + 9 * (bound + 9) + 5
def copyWorkPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.add (.mul (.mul (.constant 4) (.add bound (.constant 9))) (.add bound (.constant 9)))
    (.mul (.constant 9) (.add bound (.constant 9)))) (.constant 5)
def arithmeticInputBound (bound : NatPolynomial) : NatPolynomial :=
  .add (.mul (.constant 3) bound) (.constant 20)
def spanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (arithmeticInputBound bound) (BuilderExactlyOneClauseOccupancy.spanPolynomial (arithmeticInputBound bound))
def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.mul (.constant 12) (copyWorkPolynomial bound))
    (.add (.constant 400) (BuilderExactlyOneClauseOccupancy.rawTimePolynomial (arithmeticInputBound bound)))

private theorem copy_polynomial_eval (bound : NatPolynomial) (input : Nat) :
    (copyWorkPolynomial bound).eval input = copyWorkBound (bound.eval input) := rfl
private theorem copy_steps_le (value : Nat) (newer : List Nat) (bound : Nat)
    (hValue : value ≤ bound + 8) (hNewer : newer.length + newer.sum ≤ bound + 8) :
    RegisterCopy.steps newer value ≤ copyWorkBound bound := by
  have h := RegisterCopy.steps_le newer value (bound + 8) hValue hNewer
  have hAdd : bound + 8 + 1 = bound + 9 := by omega
  simpa only [hAdd, copyWorkBound] using h

theorem source_polynomial_bounds {width : Nat} (slot : Slot width) (index : Nat) (older : List Nat)
    (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (older ++ values slot ++ [index])).length + outside.length ≤ bound.eval input) :
    (registerWord (finalValues slot index older)).length + (finalOutside slot index outside).length ≤
        (spanPolynomial bound).eval input ∧
      6 * workSteps slot index ≤ (rawTimePolynomial bound).eval input := by
  have hIndex : index ≤ bound.eval input := by
    rw [append_span] at hSpan
    omega
  have hTag := tag_le slot
  have hCopy := copy_steps_le (tag slot) [index] (bound.eval input) (by omega) (by
    simp only [List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
    omega)
  have hTests := testSteps_le (tag slot)
  have hSimple
      (hValues : finalValues slot index older = older ++ values slot ++ [index])
      (hOutside : finalOutside slot index outside = restoredOutside (tag slot) outside)
      (hBranch : branchSteps slot index ≤ 4) :
      (registerWord (finalValues slot index older)).length + (finalOutside slot index outside).length ≤
          (spanPolynomial bound).eval input ∧
        6 * workSteps slot index ≤ (rawTimePolynomial bound).eval input := by
    have hExterior := restored_length_le (tag slot) outside
    constructor
    · rw [hValues, hOutside]
      simp only [spanPolynomial, arithmeticInputBound, NatPolynomial.eval_add,
        NatPolynomial.eval_mul, NatPolynomial.eval_constant]
      omega
    · simp only [workSteps, rawTimePolynomial, NatPolynomial.eval_add,
        NatPolynomial.eval_mul, NatPolynomial.eval_constant, copy_polynomial_eval]
      omega
  cases slot with
  | none => exact hSimple rfl rfl (by change 0 ≤ 4; decide)
  | some item =>
      cases item with
      | none => exact hSimple rfl rfl (by change 0 ≤ 4; decide)
      | some constraint =>
          cases constraint with
          | require literal => exact hSimple rfl rfl (by
              have h := BuilderUnaryTagMatch.workSteps_le 0 index
              simp only [branchSteps]
              omega)
          | implication premises conclusion => exact hSimple rfl rfl (by
              have h := BuilderUnaryTagMatch.workSteps_le 0 index
              simp only [branchSteps]
              omega)
          | exactlyOne variables =>
              have hCount : variables.length ≤ bound.eval input := by
                have h := hSpan
                rw [exactly_one_values] at h
                simp only [registerWord_append, List.length_append, registerWord, List.length_cons,
                  List.length_nil, List.length_replicate] at h
                omega
              have hCountCopy := copy_steps_le variables.length [4, index] (bound.eval input) (by omega) (by
                simp only [List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
                omega)
              have hInput :
                  (registerWord ((older ++ values (some (some (.exactlyOne variables)))) ++ [index, variables.length])).length +
                    ((restoredOutside 4 outside).drop (variables.length + 1)).length ≤
                      (arithmeticInputBound bound).eval input := by
                have hWord : (registerWord ((older ++ values (some (some (.exactlyOne variables)))) ++ [index, variables.length])).length =
                    (registerWord (older ++ values (some (some (.exactlyOne variables))) ++ [index])).length +
                      variables.length + 1 := by
                  have h := append_span (older ++ values (some (some (.exactlyOne variables))) ++ [index]) variables.length
                  simpa only [List.append_assoc, List.cons_append, List.nil_append] using h
                have hExterior := restored_length_le 4 outside
                rw [hWord]
                simp only [arithmeticInputBound, NatPolynomial.eval_add, NatPolynomial.eval_mul,
                  NatPolynomial.eval_constant, List.length_drop]
                omega
              have hMany := BuilderExactlyOneClauseOccupancy.source_polynomial_bounds index variables.length
                (older ++ values (some (some (.exactlyOne variables))))
                ((restoredOutside 4 outside).drop (variables.length + 1)) (arithmeticInputBound bound) input hInput
              constructor
              · simp only [finalValues, finalOutside, spanPolynomial, NatPolynomial.eval_add]
                omega
              · simp only [workSteps, tag, branchSteps, rawTimePolynomial, NatPolynomial.eval_add,
                  NatPolynomial.eval_mul, NatPolynomial.eval_constant, copy_polynomial_eval]
                simp only [tag] at hCopy hTests
                omega

end PNP.Concrete.CookLevin.BuilderPayloadClauseOccupancy
