/-
Copyright (c) 2026 PNP Labs.

Restoring physical test for the final literal of an implication source search.
The remaining count includes the conclusion. Exactly one selects its header;
all other counts take the other branch. The enclosing zero guard separately
handles exhaustion. Runtime magnitudes do not choose the finite control graph.
-/

import PNP.Concrete.CookLevinBuilderLiteralSearchGuard

namespace PNP.Concrete.CookLevin.BuilderPayloadConclusionGuard

open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open WorkMachineProgramGraph (Node Graph Endpoint endpointConfiguration)
open WorkMachineProgramPath (AcceptPath LocalAcceptRun LocalRejectRun)

def eraseEqualNode : Node :=
  {name := 2, program := BuilderRegisterErase.oneMachine, onAccept := .accept, onReject := .dead}
def eraseUnequalNode : Node :=
  {name := 3, program := BuilderRegisterErase.oneMachine, onAccept := .reject, onReject := .dead}
def testNode : Node :=
  {name := 1, program := BuilderUnaryTagMatch.machine 1,
   onAccept := .node eraseEqualNode.reference, onReject := .node eraseUnequalNode.reference}
def copyNode : Node :=
  {name := 0, program := RegisterCopy.machine 1, onAccept := .node testNode.reference, onReject := .dead}
def graph : Graph := {nodes := [copyNode, testNode, eraseEqualNode, eraseUnequalNode], entry := copyNode.reference}
def machine : WorkMachine := WorkMachineProgramGraph.machine graph

theorem graph_nodes_length : graph.nodes.length = 4 := rfl

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineProgramGraph.QueryDistinct ∧
    WorkMachineProgramGraph.NoRuleAt program program.acceptState ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧ program.acceptState ≠ program.rejectState
private theorem copy_good : Good (RegisterCopy.machine 1) := by
  refine ⟨RegisterCopy.rules_pairwise_query_distinct 1, ?_, ?_,
    RegisterCopy.machine_acceptState_ne_rejectState 1⟩
  · intro item h
    exact Nat.ne_of_lt (RegisterCopy.rule_source_lt_acceptState 1 item h)
  · intro item h
    have hBound := RegisterCopy.rule_source_lt_acceptState 1 item h
    rw [RegisterCopy.machine_acceptState] at hBound
    rw [RegisterCopy.machine_rejectState]
    omega
private theorem tag_good : Good (BuilderUnaryTagMatch.machine 1) :=
  ⟨BuilderUnaryTagMatch.rules_pairwise_query_distinct 1, BuilderUnaryTagMatch.noRuleAtAccept 1,
   BuilderUnaryTagMatch.noRuleAtReject 1, BuilderUnaryTagMatch.acceptState_ne_rejectState 1⟩
private theorem erase_good : Good BuilderRegisterErase.oneMachine :=
  ⟨BuilderRegisterErase.one_rules_pairwise_query_distinct, BuilderRegisterErase.one_noRuleAtAccept,
   BuilderRegisterErase.one_noRuleAtReject, BuilderRegisterErase.one_acceptState_ne_rejectState⟩
private theorem copy_mem : copyNode ∈ graph.nodes := List.Mem.head _
private theorem test_mem : testNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.head _)
private theorem eraseEqual_mem : eraseEqualNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
private theorem eraseUnequal_mem : eraseUnequalNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem graph_wellFormed : graph.WellFormed := by
  have hNames : (graph.nodes.map Node.name).Pairwise (fun a b : Nat => a ≠ b) := by
    change ([0,1,2,3] : List Nat).Pairwise _
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.pairwise_map] using hNames
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl
    · exact copy_good
    · exact tag_good
    · exact erase_good
    · exact erase_good
  · exact ⟨copyNode, copy_mem, rfl, rfl⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl
    · exact ⟨⟨testNode, test_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨eraseEqualNode, eraseEqual_mem, rfl, rfl⟩, ⟨eraseUnequalNode, eraseUnequal_mem, rfl, rfl⟩⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨True.intro, True.intro⟩

def frame (ordinal count position : Nat) : List Nat := [ordinal, count, position]
def workSteps (count position : Nat) : Nat :=
  RegisterCopy.steps [position] count + 1 +
    (BuilderUnaryTagMatch.workSteps 1 count + 1 + (count + 2 + 1))
def endpoint (count : Nat) : Endpoint := if count = 1 then .accept else .reject
def finalOutside (count : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  List.replicate (count + 1) .blank ++ outside.drop (count + 1)
def initialConfiguration (older : List Nat) (ordinal count position : Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration machine (endTape (older ++ frame ordinal count position) inside outside)
def finalConfiguration (older : List Nat) (ordinal count position : Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  endpointConfiguration (endpoint count)
    (endTape (older ++ frame ordinal count position) inside (finalOutside count outside))

private theorem execution_path (older : List Nat) (ordinal count position : Nat)
    (inside outside : List WorkSymbol) :
    AcceptPath graph (.node copyNode.reference) (endpoint count) (workSteps count position)
      (endTape (older ++ frame ordinal count position) inside outside)
      (endTape (older ++ frame ordinal count position) inside (finalOutside count outside)) := by
  let values := older ++ frame ordinal count position
  let copied := endTape (values ++ [count]) inside (outside.drop (count + 1))
  let final := endTape values inside (finalOutside count outside)
  have hCopy := BuilderRegionComparisonOperands.copy_workRunExact 1 (older ++ [ordinal]) [position]
    count inside outside rfl
  have hCopyLocal : LocalAcceptRun copyNode (RegisterCopy.steps [position] count)
      (endTape values inside outside) copied := by
    simpa only [LocalAcceptRun, copyNode, workStartConfiguration, values, copied, frame,
      List.append_assoc, List.cons_append, List.nil_append] using hCopy
  have hErase := BuilderRegisterErase.one_workRunExact values count inside (outside.drop (count + 1))
  have hEraseEqual : LocalAcceptRun eraseEqualNode (count + 2) copied final := hErase
  have hEraseUnequal : LocalAcceptRun eraseUnequalNode (count + 2) copied final := hErase
  by_cases hOne : count = 1
  · have hTag := BuilderUnaryTagMatch.accept_workRunExact 1 values inside (outside.drop (count + 1))
    have hTest : LocalAcceptRun testNode (BuilderUnaryTagMatch.workSteps 1 count) copied copied := by
      simpa only [LocalAcceptRun, testNode, workStartConfiguration, copied, hOne] using hTag
    have hEnd := AcceptPath.step eraseEqualNode .accept (count + 2) 0 copied final final
      eraseEqual_mem hEraseEqual (.terminal .accept final)
    have hMiddle := AcceptPath.step testNode .accept (BuilderUnaryTagMatch.workSteps 1 count)
      (count + 2 + 1 + 0) copied copied final test_mem hTest hEnd
    have h := AcceptPath.step copyNode .accept (RegisterCopy.steps [position] count)
      (BuilderUnaryTagMatch.workSteps 1 count + 1 + (count + 2 + 1 + 0))
      _ copied final copy_mem hCopyLocal hMiddle
    simpa only [endpoint, if_pos hOne, workSteps, Nat.add_zero] using h
  · have hTag := BuilderUnaryTagMatch.reject_workRunExact 1 count values inside (outside.drop (count + 1)) hOne
    have hTest : LocalRejectRun testNode (BuilderUnaryTagMatch.workSteps 1 count) copied copied := hTag
    have hEnd := AcceptPath.step eraseUnequalNode .reject (count + 2) 0 copied final final
      eraseUnequal_mem hEraseUnequal (.terminal .reject final)
    have hMiddle := AcceptPath.stepReject testNode .reject (BuilderUnaryTagMatch.workSteps 1 count)
      (count + 2 + 1 + 0) copied copied final test_mem hTest hEnd
    have h := AcceptPath.step copyNode .reject (RegisterCopy.steps [position] count)
      (BuilderUnaryTagMatch.workSteps 1 count + 1 + (count + 2 + 1 + 0))
      _ copied final copy_mem hCopyLocal hMiddle
    simpa only [endpoint, if_neg hOne, workSteps, Nat.add_zero] using h

theorem workRunExact (older : List Nat) (ordinal count position : Nat)
    (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps count position)
      (initialConfiguration older ordinal count position inside outside) =
      some (finalConfiguration older ordinal count position inside outside) := by
  have h := WorkMachineProgramPath.runExact graph (.node copyNode.reference) (endpoint count)
    (workSteps count position) _ _ graph_wellFormed (execution_path older ordinal count position inside outside)
  exact h

theorem run_compile_exact (older : List Nat) (ordinal count position : Nat)
    (inside outside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps count position)
      (encodeWorkConfiguration (initialConfiguration older ordinal count position inside outside)) =
      encodeWorkConfiguration (finalConfiguration older ordinal count position inside outside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact older ordinal count position inside outside)

theorem final_accept_iff (older : List Nat) (ordinal count position : Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration older ordinal count position inside outside).state = machine.acceptState ↔ count = 1 := by
  by_cases hOne : count = 1
  · simp only [finalConfiguration, endpoint, if_pos hOne, endpointConfiguration, WorkMachineProgramGraph.endpointState, hOne] <;> decide
  · simp only [finalConfiguration, endpoint, if_neg hOne, endpointConfiguration, WorkMachineProgramGraph.endpointState, hOne] <;> decide

theorem final_reject_iff (older : List Nat) (ordinal count position : Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration older ordinal count position inside outside).state = machine.rejectState ↔ count ≠ 1 := by
  unfold finalConfiguration endpoint
  by_cases hOne : count = 1
  · rw [if_pos hOne]
    constructor
    · intro h
      change (0 : Nat) = 1 at h
      exfalso
      omega
    · intro h
      exact False.elim (h hOne)
  · rw [if_neg hOne]
    exact ⟨fun _ => hOne, fun _ => rfl⟩

theorem final_tape (older : List Nat) (ordinal count position : Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration older ordinal count position inside outside).tape =
      endTape (older ++ frame ordinal count position) inside (finalOutside count outside) := by
  unfold finalConfiguration endpoint
  split <;> rfl

theorem finalOutside_length_le (count : Nat) (outside : List WorkSymbol) :
    (finalOutside count outside).length ≤ outside.length + count + 1 := by
  simp only [finalOutside, List.length_append, List.length_replicate, List.length_drop]
  omega
theorem final_span_le (older : List Nat) (ordinal count position : Nat) (outside : List WorkSymbol) :
    (registerWord (older ++ frame ordinal count position)).length + (finalOutside count outside).length ≤
      (registerWord (older ++ frame ordinal count position)).length + outside.length + count + 1 := by
  have h := finalOutside_length_le count outside
  omega
theorem workSteps_eq (count position : Nat) :
    workSteps count position = RegisterCopy.steps [position] count + count + 8 + 2 * min 1 count := by
  simp only [workSteps, BuilderUnaryTagMatch.workSteps]
  omega

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise graph graph_wellFormed
theorem noRuleAtAccept : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState :=
  WorkMachineProgramGraph.noRuleAt_globalAccept graph
theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  WorkMachineProgramGraph.noRuleAt_globalReject graph
theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := by
  change (0 : Nat) ≠ 1
  decide

def workBound (bound : Nat) : Nat := BuilderLiteralSearchAdvance.copyBound bound + bound + 10
def spanBound (bound : Nat) : Nat := 2 * bound + 1
def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .mul (.constant 6) (.add (.add (BuilderLiteralSearchAdvance.copyBoundPolynomial bound) bound) (.constant 10))
def spanPolynomial (bound : NatPolynomial) : NatPolynomial := .add (.mul (.constant 2) bound) (.constant 1)

theorem space_time_bounds (older : List Nat) (ordinal count position bound : Nat) (outside : List WorkSymbol)
    (hSpan : (registerWord (older ++ frame ordinal count position)).length + outside.length ≤ bound) :
    (registerWord (older ++ frame ordinal count position)).length + (finalOutside count outside).length ≤ spanBound bound ∧
    workSteps count position ≤ workBound bound := by
  have hScalar := hSpan
  simp only [registerWord_length, frame, List.length_append, List.sum_append,
    List.length_cons, List.length_nil, List.sum_cons, List.sum_nil] at hScalar
  have hCount : count ≤ bound := by omega
  have hTail : [position].length + [position].sum ≤ bound := by
    simp only [List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
    omega
  have hCopy := RegisterCopy.steps_le [position] count bound hCount hTail
  have hMin := Nat.min_le_left 1 count
  constructor
  · have hOutput := final_span_le older ordinal count position outside
    unfold spanBound
    omega
  · rw [workSteps_eq]
    unfold workBound BuilderLiteralSearchAdvance.copyBound
    omega

theorem source_polynomial_bounds (older : List Nat) (ordinal count position : Nat) (outside : List WorkSymbol)
    (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (older ++ frame ordinal count position)).length + outside.length ≤ bound.eval input) :
    (registerWord (older ++ frame ordinal count position)).length + (finalOutside count outside).length ≤ (spanPolynomial bound).eval input ∧
    6 * workSteps count position ≤ (rawTimePolynomial bound).eval input := by
  have h := space_time_bounds older ordinal count position (bound.eval input) outside hSpan
  have hSpace : (spanPolynomial bound).eval input = spanBound (bound.eval input) := rfl
  have hTime : (rawTimePolynomial bound).eval input = 6 * workBound (bound.eval input) := rfl
  rw [hSpace, hTime]
  exact ⟨h.1, Nat.mul_le_mul_left 6 h.2⟩

end PNP.Concrete.CookLevin.BuilderPayloadConclusionGuard
