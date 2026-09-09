/-
Copyright (c) 2026 PNP Labs.

A fixed cyclic literal-list token locator. The physical guard, comparison,
advancement and selection branches derive the selected literal from the actual
canonical list and overall token position. Empty and exhausted lists reach a
distinct padding endpoint. The induction below constructs the execution proof;
no selected literal, route certificate or precomputed path is a machine input.

This is the all-list lookup dependency, not the complete Cook–Levin builder.
-/

import PNP.Concrete.CookLevinBuilderLiteralSearchGuard
import PNP.Concrete.CookLevinBuilderLiteralSearchComparison

namespace PNP.Concrete.CookLevin.BuilderLiteralListSearch

open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderLocalConstraintPayload (literalListValues)
open BuilderLiteralSearchFrame (chunk residual historyStride)
open WorkMachineProgramGraph (Node NodeRef Graph Endpoint endpointConfiguration)
open WorkMachineProgramPath (AcceptPath LocalAcceptRun LocalRejectRun)

def guardReference : NodeRef := {name := 0, startState := BuilderLiteralSearchGuard.machine.startState}
def selectNode : Node :=
  {name := 3, program := BuilderLiteralSearchSelect.machine, onAccept := .accept, onReject := .reject}
def advanceNode : Node :=
  {name := 2, program := BuilderLiteralSearchAdvance.machine, onAccept := .node guardReference, onReject := .dead}
def compareNode : Node :=
  {name := 1, program := BuilderLiteralSearchComparison.machine,
   onAccept := .node selectNode.reference, onReject := .node advanceNode.reference}
def guardNode : Node :=
  {name := 0, program := BuilderLiteralSearchGuard.machine,
   onAccept := .dead, onReject := .node compareNode.reference}
def graph : Graph := {nodes := [guardNode, compareNode, advanceNode, selectNode], entry := guardReference}
def machine : WorkMachine := WorkMachineProgramGraph.machine graph

theorem graph_nodes_length : graph.nodes.length = 4 := rfl
theorem guard_reference : guardNode.reference = guardReference := rfl
private theorem advance_program : advanceNode.program = BuilderLiteralSearchAdvance.machine := rfl

private theorem guard_mem : guardNode ∈ graph.nodes := List.Mem.head _
private theorem compare_mem : compareNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.head _)
private theorem advance_mem : advanceNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
private theorem select_mem : selectNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem graph_wellFormed : graph.WellFormed := by
  have hNames : (graph.nodes.map Node.name).Pairwise (fun a b : Nat => a ≠ b) := by
    change ([0,1,2,3] : List Nat).Pairwise _
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.pairwise_map] using hNames
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl
    · exact ⟨BuilderLiteralSearchGuard.rules_pairwise_query_distinct, BuilderLiteralSearchGuard.noRuleAtAccept,
        BuilderLiteralSearchGuard.noRuleAtReject, BuilderLiteralSearchGuard.acceptState_ne_rejectState⟩
    · exact ⟨BuilderLiteralSearchComparison.rules_pairwise_query_distinct, BuilderLiteralSearchComparison.noRuleAtAccept,
        BuilderLiteralSearchComparison.noRuleAtReject, BuilderLiteralSearchComparison.acceptState_ne_rejectState⟩
    · exact ⟨BuilderLiteralSearchAdvance.rules_pairwise_query_distinct, BuilderLiteralSearchAdvance.noRuleAtAccept,
        BuilderLiteralSearchAdvance.noRuleAtReject, BuilderLiteralSearchAdvance.acceptState_ne_rejectState⟩
    · exact ⟨BuilderLiteralSearchSelect.rules_pairwise_query_distinct, BuilderLiteralSearchSelect.noRuleAtAccept,
        BuilderLiteralSearchSelect.noRuleAtReject, BuilderLiteralSearchSelect.acceptState_ne_rejectState⟩
  · exact ⟨guardNode, guard_mem, rfl, rfl⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl
    · exact ⟨True.intro, ⟨compareNode, compare_mem, rfl, rfl⟩⟩
    · exact ⟨⟨selectNode, select_mem, rfl, rfl⟩, ⟨advanceNode, advance_mem, rfl, rfl⟩⟩
    · exact ⟨⟨guardNode, guard_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, True.intro⟩

def endpoint {width : Nat} : List (BoundedLiteral width) → Nat → Endpoint
  | [], _ => .dead
  | item :: rest, position =>
      if position < item.index.val + 2 then BuilderLiteralTokenSelector.endpoint item.positive item.index.val position
      else endpoint rest (residual position item.index.val)

def searchSteps {width : Nat} (payload : List Nat) :
    List (BoundedLiteral width) → Nat → List Nat → Nat → Nat
  | [], _, _, position => BuilderLiteralSearchGuard.workSteps 0 position + 1
  | item :: rest, ordinal, prior, position =>
      BuilderLiteralSearchGuard.workSteps (rest.length + 1) position + 1 +
        (BuilderLiteralSearchComparison.workSteps payload prior ordinal (rest.length + 1) position item.index.val + 1 +
          if position < item.index.val + 2 then
            BuilderLiteralSearchSelect.workSteps payload prior ordinal (rest.length + 1) position item.index.val item.positive + 1
          else BuilderLiteralSearchAdvance.workSteps ordinal rest.length position item.index.val + 1 +
            searchSteps payload rest (ordinal + 1)
              (prior ++ chunk ordinal (rest.length + 1) position item.index.val) (residual position item.index.val))

def finishValues {width : Nat} (payload older : List Nat) :
    List (BoundedLiteral width) → Nat → List Nat → Nat → List Nat
  | [], ordinal, prior, position =>
      BuilderLiteralSearchComparison.initialValues payload older prior ordinal 0 position
  | item :: rest, ordinal, prior, position =>
      if position < item.index.val + 2 then
        BuilderLiteralTokenSelector.finalValues item.positive item.index.val position
          (BuilderLiteralSearchSelect.prepareOlder payload older prior ordinal (rest.length + 1) position item.index.val item.positive)
      else finishValues payload older rest (ordinal + 1)
        (prior ++ chunk ordinal (rest.length + 1) position item.index.val) (residual position item.index.val)

def comparedOutside (ordinal count position value : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  BuilderLiteralSearchComparison.finalOutside ordinal position value (BuilderLiteralSearchGuard.finalOutside count outside)

def finishOutside {width : Nat} :
    List (BoundedLiteral width) → Nat → Nat → List WorkSymbol → List WorkSymbol
  | [], _, _, outside => BuilderLiteralSearchGuard.finalOutside 0 outside
  | item :: rest, ordinal, position, outside =>
      if position < item.index.val + 2 then
        BuilderLiteralTokenSelector.finalOutside item.positive item.index.val position
          (BuilderLiteralSearchSelect.prepareOutside ordinal position item.index.val item.positive
            (comparedOutside ordinal (rest.length + 1) position item.index.val outside))
      else finishOutside rest (ordinal + 1) (residual position item.index.val)
        (BuilderLiteralSearchAdvance.finalOutside ordinal rest.length position item.index.val
          (comparedOutside ordinal (rest.length + 1) position item.index.val outside))

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

private theorem selection_path {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (prior : List Nat) (hPrior : prior.length = historyStride * index.val) (count position : Nat)
    (older : List Nat) (inside outside : List WorkSymbol) (hHit : position < literals[index.val].index.val + 2) :
    AcceptPath graph (.node selectNode.reference)
      (BuilderLiteralTokenSelector.endpoint literals[index.val].positive literals[index.val].index.val position)
      (BuilderLiteralSearchSelect.workSteps (literalListValues literals) prior index.val count position
        literals[index.val].index.val literals[index.val].positive + 1)
      (endTape (BuilderLiteralSearchSelect.initialValues (literalListValues literals) older prior index.val count position
        literals[index.val].index.val) inside outside)
      (BuilderLiteralSearchSelect.finalConfiguration (literalListValues literals) older prior index.val count position
        literals[index.val].index.val literals[index.val].positive inside outside).tape := by
  have hRun := BuilderLiteralSearchSelect.workRunExact literals index prior hPrior count position older inside outside
  rcases literal_endpoint_terminal literals[index.val].positive literals[index.val].index.val position hHit with hAccept | hReject
  · have hState :
        (BuilderLiteralSearchSelect.finalConfiguration (literalListValues literals) older prior index.val count position
          literals[index.val].index.val literals[index.val].positive inside outside).state =
            BuilderLiteralSearchSelect.machine.acceptState := by
      change WorkMachineChain.secondState (endpointConfiguration
        (BuilderLiteralTokenSelector.endpoint literals[index.val].positive literals[index.val].index.val position) _).state =
          WorkMachineChain.secondState 0
      rw [hAccept]
      rfl
    rw [configuration_eq_of_fields _ _ _ hState rfl] at hRun
    rw [hAccept]
    exact AcceptPath.step selectNode .accept _ 0 _ _ _ select_mem hRun (.terminal .accept _)
  · have hState :
        (BuilderLiteralSearchSelect.finalConfiguration (literalListValues literals) older prior index.val count position
          literals[index.val].index.val literals[index.val].positive inside outside).state =
            BuilderLiteralSearchSelect.machine.rejectState := by
      change WorkMachineChain.secondState (endpointConfiguration
        (BuilderLiteralTokenSelector.endpoint literals[index.val].positive literals[index.val].index.val position) _).state =
          WorkMachineChain.secondState 1
      rw [hReject]
      rfl
    rw [configuration_eq_of_fields _ _ _ hState rfl] at hRun
    rw [hReject]
    exact AcceptPath.stepReject selectNode .reject _ 0 _ _ _ select_mem hRun (.terminal .reject _)

private theorem advance_path (next : Endpoint) (steps tailSteps : Nat) (initial middle final : WorkTape)
    (hRun : LocalAcceptRun advanceNode steps initial middle)
    (hTail : AcceptPath graph (.node guardReference) next tailSteps middle final) :
    AcceptPath graph (.node advanceNode.reference) next (steps + 1 + tailSteps) initial final := by
  have hBack : advanceNode.onAccept = .node guardReference := rfl
  apply AcceptPath.step advanceNode next steps tailSteps initial middle final advance_mem hRun
  rw [hBack]
  exact hTail

private theorem append_index {width : Nat} (completed : List (BoundedLiteral width))
    (item : BoundedLiteral width) (rest : List (BoundedLiteral width)) :
    (completed ++ item :: rest)[completed.length]'(by simp only [List.length_append, List.length_cons]; omega) = item := by
  rw [List.getElem_append_right (show completed.length ≤ completed.length from Nat.le_refl _)]
  simp only [Nat.sub_self, List.getElem_cons_zero]

/-- The invariant is derived from a prefix of the actual list, not supplied route data. -/
private theorem loop_path {width : Nat} (remaining : List (BoundedLiteral width)) (literals completed : List (BoundedLiteral width))
    (hList : literals = completed ++ remaining) (prior : List Nat) (hPrior : prior.length = historyStride * completed.length)
    (position : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    AcceptPath graph (.node guardNode.reference) (endpoint remaining position)
      (searchSteps (literalListValues literals) remaining completed.length prior position)
      (endTape (BuilderLiteralSearchComparison.initialValues (literalListValues literals) older prior
        completed.length remaining.length position) inside outside)
      (endTape (finishValues (literalListValues literals) older remaining completed.length prior position) inside
        (finishOutside remaining completed.length position outside)) := by
  induction remaining generalizing completed prior position outside with
  | nil =>
      have hGuard := BuilderLiteralSearchGuard.workRunExact
        (BuilderLiteralSearchComparison.baseValues (literalListValues literals) older prior) completed.length 0 position inside outside
      have hState := (BuilderLiteralSearchGuard.final_accept_iff
        (BuilderLiteralSearchComparison.baseValues (literalListValues literals) older prior) completed.length 0 position inside outside).2 rfl
      have hTape := BuilderLiteralSearchGuard.final_tape
        (BuilderLiteralSearchComparison.baseValues (literalListValues literals) older prior) completed.length 0 position inside outside
      rw [configuration_eq_of_fields _ _ _ hState hTape] at hGuard
      exact AcceptPath.step guardNode .dead _ 0 _ _ _ guard_mem hGuard (.terminal .dead _)
  | cons item rest ih =>
      have hIndex : completed.length < literals.length := by
        rw [hList, List.length_append, List.length_cons]
        omega
      let index : Fin literals.length := ⟨completed.length, hIndex⟩
      have hLiteral : literals[index.val] = item := by
        change literals[completed.length] = item
        subst literals
        exact append_index completed item rest
      let guarded := BuilderLiteralSearchGuard.finalOutside (rest.length + 1) outside
      let compared := comparedOutside completed.length (rest.length + 1) position item.index.val outside
      have hGuard := BuilderLiteralSearchGuard.workRunExact
        (BuilderLiteralSearchComparison.baseValues (literalListValues literals) older prior)
        completed.length (rest.length + 1) position inside outside
      have hGuardState := (BuilderLiteralSearchGuard.final_reject_iff
        (BuilderLiteralSearchComparison.baseValues (literalListValues literals) older prior) completed.length (rest.length + 1) position inside outside).2
        (by omega)
      have hGuardTape := BuilderLiteralSearchGuard.final_tape
        (BuilderLiteralSearchComparison.baseValues (literalListValues literals) older prior)
        completed.length (rest.length + 1) position inside outside
      rw [configuration_eq_of_fields _ _ _ hGuardState hGuardTape] at hGuard
      have hCompare := BuilderLiteralSearchComparison.workRunExact literals index prior hPrior
        (rest.length + 1) position older inside guarded
      rw [hLiteral] at hCompare
      by_cases hHit : position < item.index.val + 2
      · have hState := (BuilderLiteralSearchComparison.final_accept_iff (literalListValues literals) older prior
          completed.length (rest.length + 1) position item.index.val inside guarded).2 hHit
        have hTape := BuilderLiteralSearchComparison.final_tape (literalListValues literals) older prior
          completed.length (rest.length + 1) position item.index.val inside guarded
        rw [configuration_eq_of_fields _ _ _ hState hTape] at hCompare
        have hSelect := selection_path literals index prior hPrior (rest.length + 1) position older inside compared
          (by simpa only [hLiteral] using hHit)
        rw [hLiteral, BuilderLiteralSearchSelect.final_tape] at hSelect
        have hC := AcceptPath.step compareNode _ _ _ _ _ _ compare_mem hCompare hSelect
        have hG := AcceptPath.stepReject guardNode _ _ _ _ _ _ guard_mem hGuard hC
        simpa only [endpoint, searchSteps, finishValues, finishOutside, if_pos hHit, List.length_cons,
          guarded, compared, comparedOutside, index, BuilderLiteralSearchComparison.initialValues,
          BuilderLiteralSearchGuard.frame] using hG
      · have hState := (BuilderLiteralSearchComparison.final_reject_iff (literalListValues literals) older prior
          completed.length (rest.length + 1) position item.index.val inside guarded).2 (by omega)
        have hTape := BuilderLiteralSearchComparison.final_tape (literalListValues literals) older prior
          completed.length (rest.length + 1) position item.index.val inside guarded
        rw [configuration_eq_of_fields _ _ _ hState hTape] at hCompare
        have hNextList : literals = (completed ++ [item]) ++ rest := by
          simpa only [List.append_assoc, List.cons_append, List.nil_append] using hList
        have hNextPrior : (prior ++ chunk completed.length (rest.length + 1) position item.index.val).length =
            historyStride * (completed ++ [item]).length := by
          simpa only [List.length_append, List.length_cons, List.length_nil] using
            BuilderLiteralSearchFrame.history_step prior completed.length (rest.length + 1) position item.index.val hPrior
        have hTail := ih (completed ++ [item]) hNextList
          (prior ++ chunk completed.length (rest.length + 1) position item.index.val) hNextPrior
          (residual position item.index.val)
          (BuilderLiteralSearchAdvance.finalOutside completed.length rest.length position item.index.val compared)
        simp only [List.length_append, List.length_cons, List.length_nil, guard_reference] at hTail
        have hNextInput :
            BuilderLiteralSearchAdvance.finalValues
              (BuilderLiteralSearchComparison.baseValues (literalListValues literals) older prior)
              completed.length rest.length position item.index.val =
            BuilderLiteralSearchComparison.initialValues (literalListValues literals) older
              (prior ++ chunk completed.length (rest.length + 1) position item.index.val)
              (completed.length + 1) rest.length (residual position item.index.val) := by
          simp only [BuilderLiteralSearchAdvance.finalValues, BuilderLiteralSearchAdvance.initialValues,
            BuilderLiteralSearchComparison.initialValues, BuilderLiteralSearchComparison.baseValues, List.append_assoc]
        have hAdvanceLocal : LocalAcceptRun advanceNode
            (BuilderLiteralSearchAdvance.workSteps completed.length rest.length position item.index.val)
            (endTape (BuilderLiteralSearchComparison.finalValues (literalListValues literals) older prior
              completed.length (rest.length + 1) position item.index.val) inside compared)
            (endTape (BuilderLiteralSearchComparison.initialValues (literalListValues literals) older
              (prior ++ chunk completed.length (rest.length + 1) position item.index.val)
              (completed.length + 1) rest.length (residual position item.index.val)) inside
              (BuilderLiteralSearchAdvance.finalOutside completed.length rest.length position item.index.val compared)) := by
          unfold LocalAcceptRun
          rw [advance_program]
          simpa only [BuilderLiteralSearchAdvance.initialConfiguration, BuilderLiteralSearchAdvance.finalConfiguration,
            workStartConfiguration, hNextInput, BuilderLiteralSearchAdvance.initialValues,
            BuilderLiteralSearchComparison.finalValues] using
            BuilderLiteralSearchAdvance.workRunExact
              (BuilderLiteralSearchComparison.baseValues (literalListValues literals) older prior)
              completed.length rest.length position item.index.val inside compared
        have hA := advance_path _ _ _ _ _ _ hAdvanceLocal hTail
        have hC := AcceptPath.stepReject compareNode _ _ _ _ _ _ compare_mem hCompare hA
        have hG := AcceptPath.stepReject guardNode _ _ _ _ _ _ guard_mem hGuard hC
        simpa only [endpoint, searchSteps, finishValues, finishOutside, if_neg hHit, List.length_cons,
          guarded, compared, comparedOutside, index, BuilderLiteralSearchComparison.initialValues,
          BuilderLiteralSearchGuard.frame] using hG

def workSteps {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat) : Nat :=
  searchSteps (literalListValues literals) literals 0 [] position
def initialValues {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat) (older : List Nat) : List Nat :=
  older ++ (literalListValues literals).reverse ++ [0, literals.length, position]
def finalValues {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat) (older : List Nat) : List Nat :=
  finishValues (literalListValues literals) older literals 0 [] position
def finalOutside {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  finishOutside literals 0 position outside
def initialConfiguration {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration machine (endTape (initialValues literals position older) inside outside)
def finalConfiguration {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  endpointConfiguration (endpoint literals position)
    (endTape (finalValues literals position older) inside (finalOutside literals position outside))

theorem workRunExact {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps literals position) (initialConfiguration literals position older inside outside) =
      some (finalConfiguration literals position older inside outside) := by
  have hPath := loop_path literals literals [] rfl [] rfl position older inside outside
  have h := WorkMachineProgramPath.runExact graph _ _ _ _ _ graph_wellFormed hPath
  have hStart (tape : WorkTape) :
      endpointConfiguration (.node guardNode.reference) tape = workStartConfiguration machine tape := rfl
  rw [hStart] at h
  simpa only [initialConfiguration, finalConfiguration, initialValues, finalValues, finalOutside, workSteps,
    BuilderLiteralSearchComparison.initialValues, BuilderLiteralSearchComparison.baseValues,
    List.append_nil, List.length_nil, machine] using h

theorem run_compile_exact {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps literals position)
      (encodeWorkConfiguration (initialConfiguration literals position older inside outside)) =
      encodeWorkConfiguration (finalConfiguration literals position older inside outside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact literals position older inside outside)

def observe (configuration : WorkConfiguration) : Option CNFToken := BuilderLiteralTokenSelector.observe configuration

private theorem observe_tape (target : Endpoint) (first second : WorkTape) :
    observe (endpointConfiguration target first) = observe (endpointConfiguration target second) := by
  cases target <;> rfl

theorem endpoint_observes_list {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat) (tape : WorkTape) :
    observe (endpointConfiguration (endpoint literals position) tape) = DirectToken.boundedLiteralListSlot literals position := by
  induction literals generalizing position with
  | nil => rfl
  | cons item rest ih =>
      by_cases hHit : position < item.index.val + 2
      · simp only [endpoint, if_pos hHit]
        have hLiteral := BuilderLiteralTokenSelector.canonical_result item.positive item.index.val position [] [] []
        have hObserve := observe_tape (BuilderLiteralTokenSelector.endpoint item.positive item.index.val position)
          tape (BuilderLiteralTokenSelector.finalConfiguration item.positive item.index.val position [] [] []).tape
        rw [hObserve]
        change BuilderLiteralTokenSelector.observe
          (BuilderLiteralTokenSelector.finalConfiguration item.positive item.index.val position [] [] []) = _
        rw [hLiteral]
        simp only [DirectToken.boundedLiteralListSlot, DirectSlot.append, DirectToken.boundedLiteralWidth, if_pos hHit]
        rfl
      · simp only [endpoint, if_neg hHit]
        rw [ih]
        simp only [DirectToken.boundedLiteralListSlot, DirectSlot.append, DirectToken.boundedLiteralWidth,
          if_neg hHit, residual]

theorem canonical_result {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    observe (finalConfiguration literals position older inside outside) = DirectToken.boundedLiteralListSlot literals position :=
  endpoint_observes_list literals position _

theorem workRun_observes_list {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    observe (workRun machine (workSteps literals position) (initialConfiguration literals position older inside outside)) =
      DirectToken.boundedLiteralListSlot literals position := by
  rw [workRun_eq_of_workRunExact _ _ _ _ (workRunExact literals position older inside outside)]
  exact canonical_result literals position older inside outside

theorem workRun_observes_encoding {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    observe (workRun machine (workSteps literals position) (initialConfiguration literals position older inside outside)) =
      (encodeLiteralListTokens (BoundedClause.emit literals))[position]? := by
  rw [workRun_observes_list, DirectToken.boundedLiteralListSlot_eq_getElem?]

theorem final_tape {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration literals position older inside outside).tape =
      endTape (finalValues literals position older) inside (finalOutside literals position outside) := by
  unfold finalConfiguration
  cases endpoint literals position <;> rfl

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise graph graph_wellFormed
theorem noRuleAtAccept : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState :=
  WorkMachineProgramGraph.noRuleAt_globalAccept graph
theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  WorkMachineProgramGraph.noRuleAt_globalReject graph
theorem noRuleAtPadding : WorkMachineProgramGraph.NoRuleAt machine 2 :=
  WorkMachineProgramGraph.noRuleAt_globalDead graph
theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := by
  change (0 : Nat) ≠ 1
  decide

end PNP.Concrete.CookLevin.BuilderLiteralListSearch
