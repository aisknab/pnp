/-
Copyright (c) 2026 PNP Labs.

A fixed finite machine selects every token of an arbitrary canonical clause.
The initial position test handles the separator. The complete literal-list
search reads the actual literal fields, and its actual exhausted residual
distinguishes finish from padding. No total-width verdict or token is supplied
to the executable machine.

Source-payload adapters, outcome-preserving recovery and the complete formula
builder remain downstream obligations.
-/

import PNP.Concrete.CookLevinBuilderLiteralListSearchBounds

namespace PNP.Concrete.CookLevin.BuilderLiteralClauseTokenSelector

open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderLocalConstraintPayload (literalListValues)
open WorkMachineProgramGraph (Node Graph Endpoint endpointConfiguration endpointState)
open WorkMachineProgramPath (AcceptPath LocalAcceptRun LocalRejectRun)
open PipelineStateNamespace (renameConfiguration)

/-- Expose exhaustion as the local continuation; keep the true-bit state stable. -/
def searchMachine : WorkMachine := {BuilderLiteralListSearch.machine with acceptState := 2}
def stopMachine : WorkMachine := {rules := [], startState := 0, acceptState := 1, rejectState := 2}
def finishNode : Node :=
  {name := 5, program := stopMachine, onAccept := .dead, onReject := .dead}
def separatorNode : Node :=
  {name := 4, program := stopMachine, onAccept := .dead, onReject := .dead}
def residualNode : Node :=
  {name := 3, program := BuilderUnaryTagMatch.machine 0,
   onAccept := .node finishNode.reference, onReject := .dead}
def bodyNode : Node :=
  {name := 2, program := searchMachine, onAccept := .node residualNode.reference, onReject := .reject}
def decrementNode : Node :=
  {name := 1, program := BuilderRegisterCountdownControl.decrement,
   onAccept := .node bodyNode.reference, onReject := .dead}
def positionNode : Node :=
  {name := 0, program := BuilderUnaryTagMatch.machine 0,
   onAccept := .node separatorNode.reference, onReject := .node decrementNode.reference}
def graph : Graph :=
  {nodes := [positionNode, decrementNode, bodyNode, residualNode, separatorNode, finishNode],
   entry := positionNode.reference}
def trueReference : WorkMachineProgramGraph.NodeRef := {name := bodyNode.name, startState := 0}
def trueState : Nat := endpointState (.node trueReference)
def separatorState : Nat := endpointState (.node separatorNode.reference)
def finishState : Nat := endpointState (.node finishNode.reference)
def machine : WorkMachine := {WorkMachineProgramGraph.machine graph with acceptState := trueState}

theorem graph_nodes_length : graph.nodes.length = 6 := rfl
theorem terminal_states_distinct :
    ([trueState,1,2,separatorState,finishState] : List Nat).Pairwise (fun left right => left ≠ right) := by decide

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineProgramGraph.QueryDistinct ∧
    WorkMachineProgramGraph.NoRuleAt program program.acceptState ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧ program.acceptState ≠ program.rejectState
private theorem tag_good : Good (BuilderUnaryTagMatch.machine 0) :=
  ⟨BuilderUnaryTagMatch.rules_pairwise_query_distinct 0, BuilderUnaryTagMatch.noRuleAtAccept 0,
   BuilderUnaryTagMatch.noRuleAtReject 0, BuilderUnaryTagMatch.acceptState_ne_rejectState 0⟩
private theorem search_good : Good searchMachine :=
  ⟨BuilderLiteralListSearch.rules_pairwise_query_distinct, BuilderLiteralListSearch.noRuleAtPadding,
   BuilderLiteralListSearch.noRuleAtReject, (by decide)⟩
private theorem stop_good : Good stopMachine :=
  ⟨List.Pairwise.nil, (by intro rule h; cases h), (by intro rule h; cases h), (by decide)⟩
private theorem member_0 : positionNode ∈ graph.nodes := List.Mem.head _
private theorem member_1 : decrementNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.head _)
private theorem member_2 : bodyNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
private theorem member_3 : residualNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
private theorem member_4 : separatorNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
private theorem member_5 : finishNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem graph_wellFormed : graph.WellFormed := by
  have hNames : (graph.nodes.map Node.name).Pairwise (fun left right : Nat => left ≠ right) := by
    change ([0,1,2,3,4,5] : List Nat).Pairwise _
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.pairwise_map] using hNames
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl
    · exact tag_good
    · exact BuilderRegisterCountdownControl.decrement_control
    · exact search_good
    · exact tag_good
    · exact stop_good
    · exact stop_good
  · exact ⟨positionNode, member_0, rfl, rfl⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨separatorNode, member_4, rfl, rfl⟩, ⟨decrementNode, member_1, rfl, rfl⟩⟩
    · exact ⟨⟨bodyNode, member_2, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨residualNode, member_3, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨finishNode, member_5, rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨True.intro, True.intro⟩

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
private theorem node_no_local (node : Node) (state : Nat)
    (hAccept : state ≠ node.program.acceptState) (hReject : state ≠ node.program.rejectState)
    (hNone : WorkMachineProgramGraph.NoRuleAt node.program state)
    (rule : WorkRule) (hMem : rule ∈ node.rules) : rule.sourceState ≠ node.encode state := by
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

theorem noRuleAtAccept : WorkMachineChain.NoRuleAtAccept machine := by
  intro rule hMem hEq
  change rule ∈ graph.nodes.flatMap Node.rules at hMem
  rcases List.mem_flatMap.mp hMem with ⟨node, hNode, hRule⟩
  rcases node_rule_source hRule with ⟨localState, hSource⟩
  have hName : node.name = 2 := (WorkMachineProgramGraph.nodeState_injective (hSource.symm.trans hEq)).1
  simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hNode
  rcases hNode with rfl | rfl | rfl | rfl | rfl | rfl
  · change 0 = 2 at hName; omega
  · change 1 = 2 at hName; omega
  · exact node_no_local bodyNode 0 (by decide) (by decide)
      BuilderLiteralListSearch.noRuleAtAccept rule hRule hEq
  · change 3 = 2 at hName; omega
  · change 4 = 2 at hName; omega
  · change 5 = 2 at hName; omega

theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  WorkMachineProgramGraph.noRuleAt_globalReject graph
theorem noRuleAtPadding : WorkMachineProgramGraph.NoRuleAt machine 2 :=
  WorkMachineProgramGraph.noRuleAt_globalDead graph
theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise graph graph_wellFormed
theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := by decide

theorem noRuleAtSeparator : WorkMachineProgramGraph.NoRuleAt machine separatorState := by
  intro rule hMem hEq
  change rule ∈ graph.nodes.flatMap Node.rules at hMem
  rcases List.mem_flatMap.mp hMem with ⟨node, hNode, hRule⟩
  rcases node_rule_source hRule with ⟨localState, hSource⟩
  have hName : node.name = 4 := (WorkMachineProgramGraph.nodeState_injective (hSource.symm.trans hEq)).1
  simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hNode
  rcases hNode with rfl | rfl | rfl | rfl | rfl | rfl
  · change 0 = 4 at hName; omega
  · change 1 = 4 at hName; omega
  · change 2 = 4 at hName; omega
  · change 3 = 4 at hName; omega
  · exact node_no_local separatorNode 0 (by decide) (by decide) (by intro r h; cases h) rule hRule hEq
  · change 5 = 4 at hName; omega

theorem noRuleAtFinish : WorkMachineProgramGraph.NoRuleAt machine finishState := by
  intro rule hMem hEq
  change rule ∈ graph.nodes.flatMap Node.rules at hMem
  rcases List.mem_flatMap.mp hMem with ⟨node, hNode, hRule⟩
  rcases node_rule_source hRule with ⟨localState, hSource⟩
  have hName : node.name = 5 := (WorkMachineProgramGraph.nodeState_injective (hSource.symm.trans hEq)).1
  simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hNode
  rcases hNode with rfl | rfl | rfl | rfl | rfl | rfl
  · change 0 = 5 at hName; omega
  · change 1 = 5 at hName; omega
  · change 2 = 5 at hName; omega
  · change 3 = 5 at hName; omega
  · change 4 = 5 at hName; omega
  · exact node_no_local finishNode 0 (by decide) (by decide) (by intro r h; cases h) rule hRule hEq

private theorem find_none (rules : List WorkRule) (state : Nat)
    (hNone : ∀ rule, rule ∈ rules → rule.sourceState ≠ state) (symbol : WorkSymbol) :
    findWorkRule rules state symbol = none := by
  induction rules with
  | nil => rfl
  | cons rule rest ih =>
      rw [findWorkRule_cons_of_not_matches]
      · exact ih (fun item hMem => hNone item (List.Mem.tail rule hMem))
      · intro hMatch
        exact hNone rule (List.Mem.head _) hMatch.1

/-- Changing declared endpoints cannot remove a successful transition when those
new endpoints already have no rules. This includes the machine's halt check. -/
private theorem same_rules_step (source target : WorkMachine)
    (hRules : target.rules = source.rules)
    (hAccept : WorkMachineProgramGraph.NoRuleAt target target.acceptState)
    (hReject : WorkMachineProgramGraph.NoRuleAt target target.rejectState)
    (config next : WorkConfiguration) (hStep : workStep? source config = some next) :
    workStep? target config = some next := by
  rcases workStep?_some_exists source config next hStep with ⟨rule, _, hFind, hNext⟩
  have hFound : findWorkRule target.rules config.state config.tape.head = some rule := by
    rw [hRules]
    exact hFind
  have hA : config.state ≠ target.acceptState := by
    intro hEq
    rw [hEq, find_none target.rules target.acceptState hAccept] at hFound
    cases hFound
  have hR : config.state ≠ target.rejectState := by
    intro hEq
    rw [hEq, find_none target.rules target.rejectState hReject] at hFound
    cases hFound
  have hHalted : target.isHalted config = false := by
    simp only [WorkMachine.isHalted, beq_eq_false_iff_ne.mpr hA, beq_eq_false_iff_ne.mpr hR]
    rfl
  rw [hNext]
  exact workStep?_eq_apply_of_find target config rule hHalted hFound

private theorem same_rules_run (source target : WorkMachine)
    (hRules : target.rules = source.rules)
    (hAccept : WorkMachineProgramGraph.NoRuleAt target target.acceptState)
    (hReject : WorkMachineProgramGraph.NoRuleAt target target.rejectState)
    (steps : Nat) (initial final : WorkConfiguration)
    (hRun : workRunExact? source steps initial = some final) :
    workRunExact? target steps initial = some final := by
  have h := PipelineStageBridges.workRunExact?_transport source target (fun state => state)
    (fun config next hStep => same_rules_step source target hRules hAccept hReject config next hStep)
    steps initial final hRun
  exact h

def initialValues {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat) (older : List Nat) : List Nat :=
  BuilderLiteralListSearch.initialValues literals position older
def entryOlder {width : Nat} (literals : List (BoundedLiteral width)) (older : List Nat) : List Nat :=
  older ++ (literalListValues literals).reverse ++ [0, literals.length]
def bodyOutside (outside : List WorkSymbol) : List WorkSymbol := WorkSymbol.blank :: outside
def bodyEndpoint {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat) : Endpoint :=
  match BuilderLiteralListSearch.endpoint literals position with
  | .accept => .node trueReference
  | .reject => .reject
  | _ => .dead
def afterEndpoint {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat) : Endpoint :=
  if position < DirectToken.boundedLiteralListWidth literals then bodyEndpoint literals position
  else if position - DirectToken.boundedLiteralListWidth literals = 0 then .node finishNode.reference else .dead
def endpoint {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat) : Endpoint :=
  if position = 0 then .node separatorNode.reference else afterEndpoint literals (position - 1)
def afterSteps {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat) : Nat :=
  if position < DirectToken.boundedLiteralListWidth literals then
    match BuilderLiteralListSearch.endpoint literals position with
    | .reject => 1
    | _ => 0
  else 5
def workSteps {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat) : Nat :=
  4 + if position = 0 then 0
    else 3 + BuilderLiteralListSearch.workSteps literals (position - 1) + afterSteps literals (position - 1)
def finalValues {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat) (older : List Nat) : List Nat :=
  if position = 0 then initialValues literals position older
  else BuilderLiteralListSearch.finalValues literals (position - 1) older
def finalOutside {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  if position = 0 then outside
  else BuilderLiteralListSearch.finalOutside literals (position - 1) (bodyOutside outside)
def initialConfiguration {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat)
    (older : List Nat) (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration machine (endTape (initialValues literals position older) inside outside)
def finalConfiguration {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat)
    (older : List Nat) (inside outside : List WorkSymbol) : WorkConfiguration :=
  endpointConfiguration (endpoint literals position)
    (endTape (finalValues literals position older) inside (finalOutside literals position outside))
def observe (configuration : WorkConfiguration) : Option CNFToken :=
  if configuration.state = trueState then some .t else if configuration.state = 1 then some .f
  else if configuration.state = separatorState then some .sep else if configuration.state = finishState then some .finish else none

theorem initial_values_suffix {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat) (older : List Nat) :
    initialValues literals position older = entryOlder literals older ++ [position] := by
  simp only [initialValues, BuilderLiteralListSearch.initialValues, entryOlder, List.append_assoc, List.cons_append, List.nil_append]
theorem zero_test_steps (position : Nat) : BuilderUnaryTagMatch.workSteps 0 position = 3 := by
  simp only [BuilderUnaryTagMatch.workSteps, Nat.min_zero, Nat.zero_min, Nat.mul_zero, Nat.zero_add]

private theorem literal_terminal (positive : Bool) (value position : Nat) (hHit : position < value + 2) :
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

theorem search_body_endpoint {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat)
    (hBody : position < DirectToken.boundedLiteralListWidth literals) :
    BuilderLiteralListSearch.endpoint literals position = .accept ∨
      BuilderLiteralListSearch.endpoint literals position = .reject := by
  induction literals generalizing position with
  | nil => exfalso; change position < 0 at hBody; omega
  | cons item rest ih =>
      change position < item.index.val + 2 + DirectToken.boundedLiteralListWidth rest at hBody
      by_cases hHit : position < item.index.val + 2
      · rw [BuilderLiteralListSearch.endpoint, if_pos hHit]
        exact literal_terminal item.positive item.index.val position hHit
      · rw [BuilderLiteralListSearch.endpoint, if_neg hHit]
        apply ih
        simp only [BuilderLiteralSearchFrame.residual, if_neg hHit]
        omega

/-- The exhausted suffix is derived from the complete search, not provided as input. -/
theorem search_exhausted_frame {width : Nat} (literals : List (BoundedLiteral width))
    (payload older prior : List Nat) (ordinal position : Nat)
    (hPast : DirectToken.boundedLiteralListWidth literals ≤ position) :
    BuilderLiteralListSearch.endpoint literals position = .dead ∧
      ∃ before, BuilderLiteralListSearch.finishValues payload older literals ordinal prior position =
        before ++ [position - DirectToken.boundedLiteralListWidth literals] := by
  induction literals generalizing prior ordinal position with
  | nil =>
      refine ⟨rfl, (BuilderLiteralSearchComparison.baseValues payload older prior ++ [ordinal,0]), ?_⟩
      simp only [BuilderLiteralListSearch.finishValues, BuilderLiteralSearchComparison.initialValues,
        DirectToken.boundedLiteralListWidth, Nat.sub_zero, List.append_assoc, List.cons_append, List.nil_append]
  | cons item rest ih =>
      change item.index.val + 2 + DirectToken.boundedLiteralListWidth rest ≤ position at hPast
      have hHit : ¬ position < item.index.val + 2 := by omega
      have hTail : DirectToken.boundedLiteralListWidth rest ≤ BuilderLiteralSearchFrame.residual position item.index.val := by
        simp only [BuilderLiteralSearchFrame.residual, if_neg hHit]
        omega
      rcases ih (prior ++ BuilderLiteralSearchFrame.chunk ordinal (rest.length + 1) position item.index.val)
        (ordinal + 1) (BuilderLiteralSearchFrame.residual position item.index.val) hTail with ⟨hEnd, before, hValues⟩
      have hResidual : BuilderLiteralSearchFrame.residual position item.index.val -
          DirectToken.boundedLiteralListWidth rest =
          position - DirectToken.boundedLiteralListWidth (item :: rest) := by
        simp only [BuilderLiteralSearchFrame.residual, if_neg hHit,
          DirectToken.boundedLiteralListWidth, DirectToken.boundedLiteralWidth]
        omega
      constructor
      · simpa only [BuilderLiteralListSearch.endpoint, if_neg hHit] using hEnd
      · refine ⟨before, ?_⟩
        simpa only [BuilderLiteralListSearch.finishValues, if_neg hHit, hResidual] using hValues

private theorem search_start : searchMachine.startState = BuilderLiteralListSearch.machine.startState := rfl
private theorem search_accept : searchMachine.acceptState = 2 := rfl
private theorem search_reject : searchMachine.rejectState = 1 := rfl

private theorem search_run {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat)
    (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? searchMachine (BuilderLiteralListSearch.workSteps literals position)
      (BuilderLiteralListSearch.initialConfiguration literals position older inside outside) =
      some (BuilderLiteralListSearch.finalConfiguration literals position older inside outside) :=
  same_rules_run BuilderLiteralListSearch.machine searchMachine rfl search_good.2.1 search_good.2.2.1
    _ _ _ (BuilderLiteralListSearch.workRunExact literals position older inside outside)

private theorem body_start_projection (tape : WorkTape) :
    renameConfiguration bodyNode.encode (workStartConfiguration searchMachine tape) =
      endpointConfiguration (.node bodyNode.reference) tape := rfl
private theorem body_true_projection (tape : WorkTape) :
    renameConfiguration bodyNode.encode (endpointConfiguration .accept tape) =
      endpointConfiguration (.node trueReference) tape := rfl
private theorem entry_projection (tape : WorkTape) :
    endpointConfiguration (.node positionNode.reference) tape = workStartConfiguration machine tape := rfl

private theorem body_run {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat)
    (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (WorkMachineProgramGraph.machine graph)
      (BuilderLiteralListSearch.workSteps literals position + afterSteps literals position)
      (endpointConfiguration (.node bodyNode.reference) (endTape (initialValues literals position older) inside outside)) =
      some (endpointConfiguration (afterEndpoint literals position)
        (endTape (BuilderLiteralListSearch.finalValues literals position older) inside
          (BuilderLiteralListSearch.finalOutside literals position outside))) := by
  have hSearch := search_run literals position older inside outside
  by_cases hBody : position < DirectToken.boundedLiteralListWidth literals
  · rcases search_body_endpoint literals position hBody with hTrue | hFalse
    · have hLift := WorkMachineProgramGraph.local_workRunExact graph bodyNode
        (BuilderLiteralListSearch.workSteps literals position) _ _ graph_wellFormed member_2 hSearch
      have hStart :
          renameConfiguration bodyNode.encode (BuilderLiteralListSearch.initialConfiguration literals position older inside outside) =
            endpointConfiguration (.node bodyNode.reference) (endTape (initialValues literals position older) inside outside) := rfl
      rw [hStart, BuilderLiteralListSearch.finalConfiguration, hTrue, body_true_projection] at hLift
      simpa only [afterSteps, afterEndpoint, if_pos hBody, hTrue, bodyEndpoint, Nat.add_zero] using hLift
    · have hLocal : LocalRejectRun bodyNode (BuilderLiteralListSearch.workSteps literals position)
          (endTape (initialValues literals position older) inside outside)
          (endTape (BuilderLiteralListSearch.finalValues literals position older) inside
            (BuilderLiteralListSearch.finalOutside literals position outside)) := by
        simpa only [LocalRejectRun, bodyNode, initialValues, BuilderLiteralListSearch.initialConfiguration,
          BuilderLiteralListSearch.finalConfiguration, workStartConfiguration, endpointConfiguration,
          endpointState, WorkMachineProgramGraph.globalRejectState, search_start, search_reject, hFalse] using hSearch
      have hPath := AcceptPath.stepReject (graph := graph) bodyNode .reject _ 0 _ _ _ member_2 hLocal (.terminal .reject _)
      have hRun := WorkMachineProgramPath.runExact graph _ _ _ _ _ graph_wellFormed hPath
      simpa only [afterSteps, afterEndpoint, if_pos hBody, hFalse, bodyEndpoint, Nat.add_zero] using hRun
  · rcases search_exhausted_frame literals (literalListValues literals) older [] 0 position (by omega) with
      ⟨hEnd, before, hValues⟩
    change BuilderLiteralListSearch.finalValues literals position older =
      before ++ [position - DirectToken.boundedLiteralListWidth literals] at hValues
    have hLocal : LocalAcceptRun bodyNode (BuilderLiteralListSearch.workSteps literals position)
        (endTape (initialValues literals position older) inside outside)
        (endTape (BuilderLiteralListSearch.finalValues literals position older) inside
          (BuilderLiteralListSearch.finalOutside literals position outside)) := by
      simpa only [LocalAcceptRun, bodyNode, initialValues, BuilderLiteralListSearch.initialConfiguration,
        BuilderLiteralListSearch.finalConfiguration, workStartConfiguration, endpointConfiguration,
        endpointState, WorkMachineProgramGraph.globalDeadState, search_start, search_accept, hEnd] using hSearch
    by_cases hZero : position - DirectToken.boundedLiteralListWidth literals = 0
    · have hTag : LocalAcceptRun residualNode 3
          (endTape (BuilderLiteralListSearch.finalValues literals position older) inside
            (BuilderLiteralListSearch.finalOutside literals position outside))
          (endTape (BuilderLiteralListSearch.finalValues literals position older) inside
            (BuilderLiteralListSearch.finalOutside literals position outside)) := by
        rw [hValues, hZero]
        simpa only [zero_test_steps, LocalAcceptRun, residualNode, workStartConfiguration] using
          BuilderUnaryTagMatch.accept_workRunExact 0 before inside
          (BuilderLiteralListSearch.finalOutside literals position outside)
      have hTail := AcceptPath.step (graph := graph) residualNode (.node finishNode.reference) 3 0 _ _ _ member_3 hTag (.terminal _ _)
      have hPath := AcceptPath.step (graph := graph) bodyNode (.node finishNode.reference) _ _ _ _ _ member_2 hLocal hTail
      have hRun := WorkMachineProgramPath.runExact graph _ _ _ _ _ graph_wellFormed hPath
      simpa only [afterSteps, afterEndpoint, if_neg hBody, if_pos hZero, Nat.add_zero, Nat.add_assoc] using hRun
    · have hTag : LocalRejectRun residualNode 3
          (endTape (BuilderLiteralListSearch.finalValues literals position older) inside
            (BuilderLiteralListSearch.finalOutside literals position outside))
          (endTape (BuilderLiteralListSearch.finalValues literals position older) inside
            (BuilderLiteralListSearch.finalOutside literals position outside)) := by
        rw [hValues]
        simpa only [zero_test_steps, LocalRejectRun, residualNode, workStartConfiguration] using
          BuilderUnaryTagMatch.reject_workRunExact 0
          (position - DirectToken.boundedLiteralListWidth literals) before inside
          (BuilderLiteralListSearch.finalOutside literals position outside) hZero
      have hTail := AcceptPath.stepReject (graph := graph) residualNode .dead 3 0 _ _ _ member_3 hTag (.terminal .dead _)
      have hPath := AcceptPath.step (graph := graph) bodyNode .dead _ _ _ _ _ member_2 hLocal hTail
      have hRun := WorkMachineProgramPath.runExact graph _ _ _ _ _ graph_wellFormed hPath
      simpa only [afterSteps, afterEndpoint, if_neg hBody, if_neg hZero, Nat.add_zero, Nat.add_assoc] using hRun

private theorem positive_prefix {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat)
    (older : List Nat) (inside outside : List WorkSymbol) (hPositive : 0 < position) :
    AcceptPath graph (.node positionNode.reference) (.node bodyNode.reference) 7
      (endTape (initialValues literals position older) inside outside)
      (endTape (initialValues literals (position - 1) older) inside (bodyOutside outside)) := by
  have hTag : LocalRejectRun positionNode 3
      (endTape (initialValues literals position older) inside outside)
      (endTape (initialValues literals position older) inside outside) := by
    rw [initial_values_suffix]
    simpa only [zero_test_steps, LocalRejectRun, positionNode, workStartConfiguration] using
      BuilderUnaryTagMatch.reject_workRunExact 0 position (entryOlder literals older) inside outside (by omega)
  have hSucc : position - 1 + 1 = position := by omega
  have hDecrement : LocalAcceptRun decrementNode 2
      (endTape (initialValues literals position older) inside outside)
      (endTape (initialValues literals (position - 1) older) inside (bodyOutside outside)) := by
    have h := BuilderRegisterCountdownControl.decrement_workRunExact (position - 1)
      (registerWord (entryOlder literals older)) inside outside
    rw [initial_values_suffix, initial_values_suffix]
    simpa only [LocalAcceptRun, decrementNode, workStartConfiguration, bodyOutside, endTape,
      registerWord_append, registerWord, List.append_nil, List.reverse_append, List.reverse_cons,
      List.reverse_replicate, List.nil_append, List.cons_append, List.append_assoc, hSucc] using h
  exact AcceptPath.stepReject positionNode _ 3 3 _ _ _ member_0 hTag
    (AcceptPath.step decrementNode _ 2 0 _ _ _ member_1 hDecrement (.terminal _ _))

theorem workRunExact {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat)
    (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps literals position) (initialConfiguration literals position older inside outside) =
      some (finalConfiguration literals position older inside outside) := by
  apply same_rules_run (WorkMachineProgramGraph.machine graph) machine rfl noRuleAtAccept noRuleAtReject
  by_cases hZero : position = 0
  · subst position
    have hTag : LocalAcceptRun positionNode 3
        (endTape (initialValues literals 0 older) inside outside)
        (endTape (initialValues literals 0 older) inside outside) := by
      rw [initial_values_suffix]
      simpa only [zero_test_steps, LocalAcceptRun, positionNode, workStartConfiguration] using
        BuilderUnaryTagMatch.accept_workRunExact 0 (entryOlder literals older) inside outside
    have hPath := AcceptPath.step (graph := graph) positionNode (.node separatorNode.reference) 3 0 _ _ _ member_0 hTag (.terminal _ _)
    have hRun := WorkMachineProgramPath.runExact graph _ _ _ _ _ graph_wellFormed hPath
    rw [entry_projection] at hRun
    simpa only [initialConfiguration, workSteps, finalConfiguration, endpoint, finalValues, finalOutside,
      if_pos rfl, ite_true, Nat.add_zero] using hRun
  · have hPrefix := WorkMachineProgramPath.runExact graph _ _ _ _ _ graph_wellFormed
      (positive_prefix literals position older inside outside (by omega))
    have hBody := body_run literals (position - 1) older inside (bodyOutside outside)
    have hRun := PipelineMachineSimulation.workRunExact?_compose
      (WorkMachineProgramGraph.machine graph) 7
      (BuilderLiteralListSearch.workSteps literals (position - 1) + afterSteps literals (position - 1))
      _ _ _ hPrefix hBody
    rw [entry_projection] at hRun
    simpa only [initialConfiguration, workSteps, finalConfiguration, endpoint, finalValues, finalOutside,
      if_neg hZero, ← Nat.add_assoc] using hRun

theorem run_compile_exact {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat)
    (older : List Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps literals position)
      (encodeWorkConfiguration (initialConfiguration literals position older inside outside)) =
      encodeWorkConfiguration (finalConfiguration literals position older inside outside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact literals position older inside outside)

theorem final_tape {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat)
    (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration literals position older inside outside).tape =
      endTape (finalValues literals position older) inside (finalOutside literals position outside) := rfl

theorem clause_cases {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat) :
    DirectToken.clauseSlot literals position =
      if position = 0 then some .sep
      else if position - 1 < DirectToken.boundedLiteralListWidth literals then
        DirectToken.boundedLiteralListSlot literals (position - 1)
      else if position - 1 - DirectToken.boundedLiteralListWidth literals = 0 then some .finish else none := by
  cases position with
  | zero => rfl
  | succ position =>
      have hZero : ¬ position + 1 = 0 := by omega
      have hFirst : ¬ position + 1 < 1 := by omega
      simp only [DirectToken.clauseSlot, DirectSlot.append, if_neg hFirst, Nat.add_sub_cancel, if_neg hZero]
      by_cases hBody : position < DirectToken.boundedLiteralListWidth literals
      · rw [if_pos hBody, if_pos hBody]
      · rw [if_neg hBody, if_neg hBody]
        cases hRest : position - DirectToken.boundedLiteralListWidth literals with
        | zero => rfl
        | succ rest => rfl

private theorem observe_body {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat)
    (tape : WorkTape) (hBody : position < DirectToken.boundedLiteralListWidth literals) :
    observe (endpointConfiguration (bodyEndpoint literals position) tape) =
      DirectToken.boundedLiteralListSlot literals position := by
  rw [← BuilderLiteralListSearch.endpoint_observes_list literals position tape]
  rcases search_body_endpoint literals position hBody with hTrue | hFalse
  · rw [bodyEndpoint, hTrue]
    rfl
  · rw [bodyEndpoint, hFalse]
    rfl
private theorem observe_separator (tape : WorkTape) :
    observe (endpointConfiguration (.node separatorNode.reference) tape) = some .sep := rfl
private theorem observe_finish (tape : WorkTape) :
    observe (endpointConfiguration (.node finishNode.reference) tape) = some .finish := rfl
private theorem observe_padding (tape : WorkTape) :
    observe (endpointConfiguration .dead tape) = none := rfl

theorem canonical_result {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat)
    (older : List Nat) (inside outside : List WorkSymbol) :
    observe (finalConfiguration literals position older inside outside) =
      (encodeClauseTokens (BoundedClause.emit literals))[position]? := by
  rw [← DirectToken.clauseSlot_eq_encodeClauseTokens_getElem?, clause_cases]
  unfold finalConfiguration endpoint
  by_cases hZero : position = 0
  · rw [if_pos hZero, if_pos hZero, observe_separator]
  · rw [if_neg hZero, if_neg hZero]
    unfold afterEndpoint
    by_cases hBody : position - 1 < DirectToken.boundedLiteralListWidth literals
    · rw [if_pos hBody, if_pos hBody]
      exact observe_body literals (position - 1) _ hBody
    · rw [if_neg hBody, if_neg hBody]
      by_cases hFinish : position - 1 - DirectToken.boundedLiteralListWidth literals = 0
      · rw [if_pos hFinish, if_pos hFinish, observe_finish]
      · rw [if_neg hFinish, if_neg hFinish, observe_padding]

theorem workRun_observes_encoding {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat)
    (older : List Nat) (inside outside : List WorkSymbol) :
    observe (workRun machine (workSteps literals position) (initialConfiguration literals position older inside outside)) =
      (encodeClauseTokens (BoundedClause.emit literals))[position]? := by
  rw [workRun_eq_of_workRunExact _ _ _ _ (workRunExact literals position older inside outside)]
  exact canonical_result literals position older inside outside

theorem body_input_span {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat)
    (older : List Nat) (outside : List WorkSymbol) (hPositive : 0 < position) :
    (registerWord (BuilderLiteralListSearch.initialValues literals (position - 1) older)).length +
        (bodyOutside outside).length =
      (registerWord (initialValues literals position older)).length + outside.length := by
  simp only [initialValues, BuilderLiteralListSearch.initialValues, bodyOutside, registerWord_length,
    List.length_append, List.sum_append, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
  omega

theorem after_steps_le {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat) :
    afterSteps literals position ≤ 5 := by
  unfold afterSteps
  split
  · cases BuilderLiteralListSearch.endpoint literals position <;> simp only <;> omega
  · exact Nat.le_refl 5

def spanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add bound (BuilderLiteralListSearchBounds.spanPolynomial bound)
def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.constant 72) (BuilderLiteralListSearchBounds.rawTimePolynomial bound)

theorem source_polynomial_bounds {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat)
    (older : List Nat) (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues literals position older)).length + outside.length ≤ bound.eval input) :
    (registerWord (finalValues literals position older)).length +
        (finalOutside literals position outside).length ≤ (spanPolynomial bound).eval input ∧
      6 * workSteps literals position ≤ (rawTimePolynomial bound).eval input := by
  by_cases hZero : position = 0
  · constructor
    · simp only [finalValues, finalOutside, if_pos hZero, spanPolynomial, NatPolynomial.eval_add]
      omega
    · simp only [workSteps, if_pos hZero, rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
      omega
  · have hEntry : (registerWord (BuilderLiteralListSearch.initialValues literals (position - 1) older)).length +
        (bodyOutside outside).length ≤ bound.eval input := by
      rw [body_input_span literals position older outside (by omega)]
      exact hSpan
    have hBounds := BuilderLiteralListSearchBounds.source_polynomial_bounds literals (position - 1) older
      (bodyOutside outside) bound input hEntry
    have hAfter := after_steps_le literals (position - 1)
    constructor
    · simp only [finalValues, finalOutside, if_neg hZero, spanPolynomial, NatPolynomial.eval_add]
      omega
    · have hTime := hBounds.2
      simp only [workSteps, if_neg hZero, rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
      omega

/-- One fixed raw machine handles every complete canonical clause and position. -/
theorem uniform_polynomial_lookup {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat)
    (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues literals position older)).length + outside.length ≤ bound.eval input) :
    ∃ rawSteps, rawSteps ≤ (rawTimePolynomial bound).eval input ∧
      run (compileWorkMachine machine) rawSteps
        (encodeWorkConfiguration (initialConfiguration literals position older inside outside)) =
        encodeWorkConfiguration (finalConfiguration literals position older inside outside) ∧
      observe (finalConfiguration literals position older inside outside) =
        (encodeClauseTokens (BoundedClause.emit literals))[position]? ∧
      (registerWord (finalValues literals position older)).length +
        (finalOutside literals position outside).length ≤ (spanPolynomial bound).eval input := by
  have hBounds := source_polynomial_bounds literals position older outside bound input hSpan
  exact ⟨6 * workSteps literals position, hBounds.2, run_compile_exact literals position older inside outside,
    canonical_result literals position older inside outside, hBounds.1⟩

end PNP.Concrete.CookLevin.BuilderLiteralClauseTokenSelector
