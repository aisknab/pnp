/-
Copyright (c) 2026 PNP Labs.

A fixed source-family machine wraps actual payload-body search with separator,
finish and padding selection. The search derives all literals and its exhausted
residual from the original encoded source. The wrapper retains that source and
request and adds only constant control overhead to the original-input bound.

This is the first/body clause route of an actual local constraint. The outer
clause-index dispatcher, negative-pair route integration, cleanup and complete
formula builder remain separate obligations.
-/
import PNP.Concrete.CookLevinBuilderPayloadSourceSearchBounds
import PNP.Concrete.CookLevinBuilderLiteralClauseTokenSelector

namespace PNP.Concrete.CookLevin.BuilderPayloadClauseTokenSelector

open PipelineTape
open BuilderUnaryPolynomial (registerWord registerWord_length registerWord_append)
open BuilderDividerOperands (endTape)
open BuilderPayloadSearchSource (Family Request family body requestValues)
open WorkMachineProgramGraph (Node Graph Endpoint endpointConfiguration endpointState)
open WorkMachineProgramPath (AcceptPath LocalAcceptRun LocalRejectRun)
open PipelineStateNamespace (renameConfiguration)

/-- Expose actual exhaustion to the residual test while preserving both bit states. -/
def searchMachine (route : Family) : WorkMachine :=
  {BuilderPayloadSourceSearchControl.machine route with acceptState := 2}
def stopMachine : WorkMachine := {rules := [], startState := 0, acceptState := 1, rejectState := 2}
def finishNode : Node := {name := 5, program := stopMachine, onAccept := .dead, onReject := .dead}
def separatorNode : Node := {name := 4, program := stopMachine, onAccept := .dead, onReject := .dead}
def residualNode : Node :=
  {name := 3, program := BuilderUnaryTagMatch.machine 0, onAccept := .node finishNode.reference, onReject := .dead}
def bodyNode (route : Family) : Node :=
  {name := 2, program := searchMachine route, onAccept := .node residualNode.reference, onReject := .reject}
def decrementNode (route : Family) : Node :=
  {name := 1, program := BuilderRegisterCountdownControl.decrement,
   onAccept := .node (bodyNode route).reference, onReject := .dead}
def positionNode (route : Family) : Node :=
  {name := 0, program := BuilderUnaryTagMatch.machine 0,
   onAccept := .node separatorNode.reference, onReject := .node (decrementNode route).reference}
def graph (route : Family) : Graph :=
  {nodes := [positionNode route,decrementNode route,bodyNode route,residualNode,separatorNode,finishNode],
   entry := (positionNode route).reference}
def trueReference : WorkMachineProgramGraph.NodeRef := BuilderLiteralClauseTokenSelector.trueReference
def trueState : Nat := BuilderLiteralClauseTokenSelector.trueState
def separatorState : Nat := BuilderLiteralClauseTokenSelector.separatorState
def finishState : Nat := BuilderLiteralClauseTokenSelector.finishState
def machine (route : Family) : WorkMachine := {WorkMachineProgramGraph.machine (graph route) with acceptState := trueState}

theorem graph_nodes_length (route : Family) : (graph route).nodes.length = 6 := rfl
theorem terminal_states_distinct :
    ([trueState,1,2,separatorState,finishState] : List Nat).Pairwise (fun left right => left ≠ right) :=
  BuilderLiteralClauseTokenSelector.terminal_states_distinct

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineProgramGraph.QueryDistinct ∧
    WorkMachineProgramGraph.NoRuleAt program program.acceptState ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧ program.acceptState ≠ program.rejectState
private theorem tag_good : Good (BuilderUnaryTagMatch.machine 0) :=
  ⟨BuilderUnaryTagMatch.rules_pairwise_query_distinct 0, BuilderUnaryTagMatch.noRuleAtAccept 0,
   BuilderUnaryTagMatch.noRuleAtReject 0, BuilderUnaryTagMatch.acceptState_ne_rejectState 0⟩
private theorem search_good (route : Family) : Good (searchMachine route) :=
  ⟨WorkMachineProgramGraph.rules_pairwise (BuilderPayloadSourceSearchControl.graph route)
      (BuilderPayloadSourceSearchControl.graph_wellFormed route),
   WorkMachineProgramGraph.noRuleAt_globalDead (BuilderPayloadSourceSearchControl.graph route),
   WorkMachineProgramGraph.noRuleAt_globalReject (BuilderPayloadSourceSearchControl.graph route), (by change (2 : Nat) ≠ 1; decide)⟩
private theorem stop_good : Good stopMachine :=
  ⟨List.Pairwise.nil, (by intro rule h; cases h), (by intro rule h; cases h), (by decide)⟩
private theorem member_0 (route : Family) : (positionNode route) ∈ (graph route).nodes := List.Mem.head _
private theorem member_1 (route : Family) : (decrementNode route) ∈ (graph route).nodes := List.Mem.tail _ (List.Mem.head _)
private theorem member_2 (route : Family) : (bodyNode route) ∈ (graph route).nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
private theorem member_3 (route : Family) : residualNode ∈ (graph route).nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
private theorem member_4 (route : Family) : separatorNode ∈ (graph route).nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
private theorem member_5 (route : Family) : finishNode ∈ (graph route).nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem graph_wellFormed (route : Family) : (graph route).WellFormed := by
  have hNames : ((graph route).nodes.map Node.name).Pairwise (fun left right : Nat => left ≠ right) := by
    change ([0,1,2,3,4,5] : List Nat).Pairwise _
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.pairwise_map] using hNames
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl
    · exact tag_good
    · exact BuilderRegisterCountdownControl.decrement_control
    · exact (search_good route)
    · exact tag_good
    · exact stop_good
    · exact stop_good
  · exact ⟨(positionNode route), (member_0 route), rfl, rfl⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨separatorNode, (member_4 route), rfl, rfl⟩, ⟨(decrementNode route), (member_1 route), rfl, rfl⟩⟩
    · exact ⟨⟨(bodyNode route), (member_2 route), rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨residualNode, (member_3 route), rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨finishNode, (member_5 route), rfl, rfl⟩, True.intro⟩
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

theorem noRuleAtAccept (route : Family) : WorkMachineChain.NoRuleAtAccept (machine route) := by
  intro rule hMem hEq
  change rule ∈ (graph route).nodes.flatMap Node.rules at hMem
  rcases List.mem_flatMap.mp hMem with ⟨node, hNode, hRule⟩
  rcases node_rule_source hRule with ⟨localState, hSource⟩
  have hName : node.name = 2 := (WorkMachineProgramGraph.nodeState_injective (hSource.symm.trans hEq)).1
  simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hNode
  rcases hNode with rfl | rfl | rfl | rfl | rfl | rfl
  · change 0 = 2 at hName; omega
  · change 1 = 2 at hName; omega
  · exact node_no_local (bodyNode route) 0 (by change (0 : Nat) ≠ 2; decide) (by change (0 : Nat) ≠ 1; decide)
      (WorkMachineProgramGraph.noRuleAt_globalAccept (BuilderPayloadSourceSearchControl.graph route)) rule hRule hEq
  · change 3 = 2 at hName; omega
  · change 4 = 2 at hName; omega
  · change 5 = 2 at hName; omega

theorem noRuleAtReject (route : Family) : WorkMachineProgramGraph.NoRuleAt (machine route) (machine route).rejectState :=
  WorkMachineProgramGraph.noRuleAt_globalReject (graph route)
theorem noRuleAtPadding (route : Family) : WorkMachineProgramGraph.NoRuleAt (machine route) 2 :=
  WorkMachineProgramGraph.noRuleAt_globalDead (graph route)
theorem rules_pairwise_query_distinct (route : Family) : (machine route).rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise (graph route) (graph_wellFormed route)
theorem acceptState_ne_rejectState (route : Family) : (machine route).acceptState ≠ (machine route).rejectState := by
  change BuilderLiteralClauseTokenSelector.trueState ≠ 1
  decide

theorem noRuleAtSeparator (route : Family) : WorkMachineProgramGraph.NoRuleAt (machine route) separatorState := by
  intro rule hMem hEq
  change rule ∈ (graph route).nodes.flatMap Node.rules at hMem
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

theorem noRuleAtFinish (route : Family) : WorkMachineProgramGraph.NoRuleAt (machine route) finishState := by
  intro rule hMem hEq
  change rule ∈ (graph route).nodes.flatMap Node.rules at hMem
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


def initialValues {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (position : Nat) (older : List Nat) : List Nat :=
  BuilderPayloadSearchSource.initialValues constraint request older [] 0 (body constraint).length position
def entryOlder {width : Nat} (constraint : LocalConstraint width) (request : Request) (older : List Nat) : List Nat :=
  requestValues constraint request older ++ [0,(body constraint).length]
def bodyOutside (outside : List WorkSymbol) : List WorkSymbol := WorkSymbol.blank :: outside
def afterEndpoint {width : Nat} (constraint : LocalConstraint width) (position : Nat) : Endpoint :=
  BuilderLiteralClauseTokenSelector.afterEndpoint (body constraint) position
def endpoint {width : Nat} (constraint : LocalConstraint width) (position : Nat) : Endpoint :=
  BuilderLiteralClauseTokenSelector.endpoint (body constraint) position
def afterSteps {width : Nat} (constraint : LocalConstraint width) (position : Nat) : Nat :=
  BuilderLiteralClauseTokenSelector.afterSteps (body constraint) position
def observe (configuration : WorkConfiguration) : Option CNFToken :=
  BuilderLiteralClauseTokenSelector.observe configuration

theorem initial_values_suffix {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (position : Nat) (older : List Nat) :
    initialValues constraint request position older = entryOlder constraint request older ++ [position] := by
  simp only [initialValues, BuilderPayloadSearchSource.initialValues, BuilderPayloadSearchSource.baseValues,
    entryOlder, List.append_nil, List.append_assoc, List.cons_append, List.nil_append]

theorem endpoint_observes_encoding {width : Nat} (constraint : LocalConstraint width)
    (position : Nat) (tape : WorkTape) :
    observe (endpointConfiguration (endpoint constraint position) tape) =
      (encodeClauseTokens (BoundedClause.emit (body constraint)))[position]? := by
  have hObserve : observe (endpointConfiguration (endpoint constraint position) tape) =
      BuilderLiteralClauseTokenSelector.observe
        (BuilderLiteralClauseTokenSelector.finalConfiguration (body constraint) position [] [] []) := by rfl
  exact hObserve.trans (BuilderLiteralClauseTokenSelector.canonical_result (body constraint) position [] [] [])

private theorem separator_reference :
    separatorNode.reference = BuilderLiteralClauseTokenSelector.separatorNode.reference := rfl
private theorem finish_reference :
    finishNode.reference = BuilderLiteralClauseTokenSelector.finishNode.reference := rfl

private theorem search_start (route : Family) :
    (searchMachine route).startState = (BuilderPayloadSourceSearchControl.machine route).startState := rfl
private theorem search_accept (route : Family) : (searchMachine route).acceptState = 2 := rfl
private theorem search_reject (route : Family) : (searchMachine route).rejectState = 1 := rfl
private theorem body_true_projection (route : Family) (tape : WorkTape) :
    renameConfiguration (bodyNode route).encode (endpointConfiguration .accept tape) =
      endpointConfiguration (.node trueReference) tape := rfl
private theorem entry_projection (route : Family) (tape : WorkTape) :
    endpointConfiguration (.node (positionNode route).reference) tape = workStartConfiguration (machine route) tape := rfl

/-- This internal composition consumes the execution produced by actual source
search. The public theorem below constructs that evidence itself. -/
private theorem body_run {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (position : Nat) (older : List Nat) (inside outside : List WorkSymbol)
    (steps : Nat) (values : List Nat) (resultOutside : List WorkSymbol)
    (hSource : workRunExact? (BuilderPayloadSourceSearchControl.machine (family constraint)) steps
      (workStartConfiguration (BuilderPayloadSourceSearchControl.machine (family constraint))
        (endTape (initialValues constraint request position older) inside outside)) =
      some (endpointConfiguration (BuilderLiteralListSearch.endpoint (body constraint) position)
        (endTape values inside resultOutside)))
    (hExhausted : BuilderLiteralListSearch.endpoint (body constraint) position = .dead →
      ∃ prior, prior.length = 17 * (body constraint).length ∧
        values = BuilderPayloadSearchSource.initialValues constraint request older prior (body constraint).length 0
          (position - DirectToken.boundedLiteralListWidth (body constraint))) :
    workRunExact? (WorkMachineProgramGraph.machine (graph (family constraint)))
      (steps + afterSteps constraint position)
      (endpointConfiguration (.node (bodyNode (family constraint)).reference)
        (endTape (initialValues constraint request position older) inside outside)) =
      some (endpointConfiguration (afterEndpoint constraint position) (endTape values inside resultOutside)) := by
  have hSearch := same_rules_run (BuilderPayloadSourceSearchControl.machine (family constraint))
    (searchMachine (family constraint)) rfl (search_good (family constraint)).2.1
    (search_good (family constraint)).2.2.1 _ _ _ hSource
  by_cases hBody : position < DirectToken.boundedLiteralListWidth (body constraint)
  · rcases BuilderLiteralClauseTokenSelector.search_body_endpoint (body constraint) position hBody with hTrue | hFalse
    · have hLift := WorkMachineProgramGraph.local_workRunExact (graph (family constraint)) (bodyNode (family constraint))
        steps _ _ (graph_wellFormed (family constraint)) (member_2 (family constraint)) hSearch
      have hStart :
          renameConfiguration (bodyNode (family constraint)).encode
            (workStartConfiguration (BuilderPayloadSourceSearchControl.machine (family constraint))
              (endTape (initialValues constraint request position older) inside outside)) =
            endpointConfiguration (.node (bodyNode (family constraint)).reference)
              (endTape (initialValues constraint request position older) inside outside) := rfl
      rw [hStart, hTrue, body_true_projection] at hLift
      simpa only [afterSteps, afterEndpoint, BuilderLiteralClauseTokenSelector.afterSteps,
        BuilderLiteralClauseTokenSelector.afterEndpoint, BuilderLiteralClauseTokenSelector.bodyEndpoint,
        if_pos hBody, hTrue, trueReference, Nat.add_zero] using hLift
    · have hLocal : LocalRejectRun (bodyNode (family constraint)) steps
          (endTape (initialValues constraint request position older) inside outside)
          (endTape values inside resultOutside) := by
        simpa only [LocalRejectRun, bodyNode, workStartConfiguration, endpointConfiguration, endpointState,
          WorkMachineProgramGraph.globalRejectState, search_start, search_reject, hFalse] using hSearch
      have hPath := AcceptPath.stepReject (graph := graph (family constraint)) (bodyNode (family constraint))
        .reject steps 0 _ _ _ (member_2 (family constraint)) hLocal (.terminal .reject _)
      have hRun := WorkMachineProgramPath.runExact (graph (family constraint)) _ _ _ _ _
        (graph_wellFormed (family constraint)) hPath
      simpa only [afterSteps, afterEndpoint, BuilderLiteralClauseTokenSelector.afterSteps,
        BuilderLiteralClauseTokenSelector.afterEndpoint, BuilderLiteralClauseTokenSelector.bodyEndpoint,
        if_pos hBody, hFalse, Nat.add_zero] using hRun
  · have hEnd := (BuilderLiteralClauseTokenSelector.search_exhausted_frame (body constraint)
      [] [] [] 0 position (by omega)).1
    obtain ⟨prior, _, hValues⟩ := hExhausted hEnd
    let before := BuilderPayloadSearchSource.baseValues constraint request older prior ++ [(body constraint).length,0]
    have hSuffix : values = before ++ [position - DirectToken.boundedLiteralListWidth (body constraint)] := by
      rw [hValues]
      simp only [BuilderPayloadSearchSource.initialValues, before, List.append_assoc, List.cons_append, List.nil_append]
    have hLocal : LocalAcceptRun (bodyNode (family constraint)) steps
        (endTape (initialValues constraint request position older) inside outside)
        (endTape values inside resultOutside) := by
      simpa only [LocalAcceptRun, bodyNode, workStartConfiguration, endpointConfiguration, endpointState,
        WorkMachineProgramGraph.globalDeadState, search_start, search_accept, hEnd] using hSearch
    by_cases hZero : position - DirectToken.boundedLiteralListWidth (body constraint) = 0
    · have hTag : LocalAcceptRun residualNode 3
          (endTape values inside resultOutside) (endTape values inside resultOutside) := by
        rw [hSuffix, hZero]
        simpa only [BuilderLiteralClauseTokenSelector.zero_test_steps, LocalAcceptRun, residualNode, workStartConfiguration] using
          BuilderUnaryTagMatch.accept_workRunExact 0 before inside resultOutside
      have hTail := AcceptPath.step (graph := graph (family constraint)) residualNode (.node finishNode.reference)
        3 0 _ _ _ (member_3 (family constraint)) hTag (.terminal _ _)
      have hPath := AcceptPath.step (graph := graph (family constraint)) (bodyNode (family constraint))
        (.node finishNode.reference) steps _ _ _ _ (member_2 (family constraint)) hLocal hTail
      have hRun := WorkMachineProgramPath.runExact (graph (family constraint)) _ _ _ _ _
        (graph_wellFormed (family constraint)) hPath
      simpa only [afterSteps, afterEndpoint, BuilderLiteralClauseTokenSelector.afterSteps,
        BuilderLiteralClauseTokenSelector.afterEndpoint, if_neg hBody, if_pos hZero, finish_reference, Nat.add_zero, Nat.add_assoc] using hRun
    · have hTag : LocalRejectRun residualNode 3
          (endTape values inside resultOutside) (endTape values inside resultOutside) := by
        rw [hSuffix]
        simpa only [BuilderLiteralClauseTokenSelector.zero_test_steps, LocalRejectRun, residualNode, workStartConfiguration] using
          BuilderUnaryTagMatch.reject_workRunExact 0
            (position - DirectToken.boundedLiteralListWidth (body constraint)) before inside resultOutside hZero
      have hTail := AcceptPath.stepReject (graph := graph (family constraint)) residualNode .dead
        3 0 _ _ _ (member_3 (family constraint)) hTag (.terminal .dead _)
      have hPath := AcceptPath.step (graph := graph (family constraint)) (bodyNode (family constraint))
        .dead steps _ _ _ _ (member_2 (family constraint)) hLocal hTail
      have hRun := WorkMachineProgramPath.runExact (graph (family constraint)) _ _ _ _ _
        (graph_wellFormed (family constraint)) hPath
      simpa only [afterSteps, afterEndpoint, BuilderLiteralClauseTokenSelector.afterSteps,
        BuilderLiteralClauseTokenSelector.afterEndpoint, if_neg hBody, if_neg hZero, Nat.add_zero, Nat.add_assoc] using hRun

private theorem positive_prefix {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (position : Nat) (older : List Nat) (inside outside : List WorkSymbol) (hPositive : 0 < position) :
    AcceptPath (graph (family constraint)) (.node (positionNode (family constraint)).reference)
      (.node (bodyNode (family constraint)).reference) 7
      (endTape (initialValues constraint request position older) inside outside)
      (endTape (initialValues constraint request (position - 1) older) inside (bodyOutside outside)) := by
  have hTag : LocalRejectRun (positionNode (family constraint)) 3
      (endTape (initialValues constraint request position older) inside outside)
      (endTape (initialValues constraint request position older) inside outside) := by
    rw [initial_values_suffix]
    simpa only [BuilderLiteralClauseTokenSelector.zero_test_steps, LocalRejectRun, positionNode, workStartConfiguration] using
      BuilderUnaryTagMatch.reject_workRunExact 0 position (entryOlder constraint request older) inside outside (by omega)
  have hSucc : position - 1 + 1 = position := by omega
  have hDecrement : LocalAcceptRun (decrementNode (family constraint)) 2
      (endTape (initialValues constraint request position older) inside outside)
      (endTape (initialValues constraint request (position - 1) older) inside (bodyOutside outside)) := by
    have h := BuilderRegisterCountdownControl.decrement_workRunExact (position - 1)
      (registerWord (entryOlder constraint request older)) inside outside
    rw [initial_values_suffix, initial_values_suffix]
    simpa only [LocalAcceptRun, decrementNode, workStartConfiguration, bodyOutside, endTape,
      registerWord_append, registerWord, List.append_nil, List.reverse_append, List.reverse_cons,
      List.reverse_replicate, List.nil_append, List.cons_append, List.append_assoc, hSucc] using h
  exact AcceptPath.stepReject (positionNode (family constraint)) _ 3 3 _ _ _ (member_0 (family constraint)) hTag
    (AcceptPath.step (decrementNode (family constraint)) _ 2 0 _ _ _ (member_1 (family constraint)) hDecrement (.terminal _ _))

theorem body_input_span {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (position : Nat) (older : List Nat) (outside : List WorkSymbol) (hPositive : 0 < position) :
    (registerWord (initialValues constraint request (position - 1) older)).length +
        (bodyOutside outside).length =
      (registerWord (initialValues constraint request position older)).length + outside.length := by
  simp only [initial_values_suffix, bodyOutside, registerWord_length, List.length_append,
    List.sum_append, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
  omega

def spanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add bound (BuilderPayloadSourceSearchEnvelope.spanPolynomial bound)
def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.constant 72) (BuilderPayloadSourceSearchEnvelope.rawTimePolynomial bound)

/-- The actual encoded source produces its entire body clause at every position,
with no supplied run, literal, width verdict or cost certificate. -/
theorem workRun_polynomial_lookup {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (position : Nat) (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues constraint request position older)).length + outside.length ≤ bound.eval input) :
    ∃ (steps : Nat) (values : List Nat) (resultOutside : List WorkSymbol),
      workRunExact? (machine (family constraint)) steps
        (workStartConfiguration (machine (family constraint))
          (endTape (initialValues constraint request position older) inside outside)) =
        some (endpointConfiguration (endpoint constraint position) (endTape values inside resultOutside)) ∧
      observe (endpointConfiguration (endpoint constraint position) (endTape values inside resultOutside)) =
        (encodeClauseTokens (BoundedClause.emit (body constraint)))[position]? ∧
      (∃ scratch, values = requestValues constraint request older ++ scratch) ∧
      (registerWord values).length + resultOutside.length ≤ (spanPolynomial bound).eval input ∧
      6 * steps ≤ (rawTimePolynomial bound).eval input := by
  by_cases hZero : position = 0
  · subst position
    have hTag : LocalAcceptRun (positionNode (family constraint)) 3
        (endTape (initialValues constraint request 0 older) inside outside)
        (endTape (initialValues constraint request 0 older) inside outside) := by
      rw [initial_values_suffix]
      simpa only [BuilderLiteralClauseTokenSelector.zero_test_steps, LocalAcceptRun, positionNode, workStartConfiguration] using
        BuilderUnaryTagMatch.accept_workRunExact 0 (entryOlder constraint request older) inside outside
    have hPath := AcceptPath.step (graph := graph (family constraint)) (positionNode (family constraint))
      (.node separatorNode.reference) 3 0 _ _ _ (member_0 (family constraint)) hTag (.terminal _ _)
    have hRun := WorkMachineProgramPath.runExact (graph (family constraint)) _ _ _ _ _
      (graph_wellFormed (family constraint)) hPath
    rw [entry_projection] at hRun
    have hFull := same_rules_run (WorkMachineProgramGraph.machine (graph (family constraint)))
      (machine (family constraint)) rfl (noRuleAtAccept (family constraint)) (noRuleAtReject (family constraint))
      _ _ _ hRun
    refine ⟨4, initialValues constraint request 0 older, outside, ?_,
      endpoint_observes_encoding constraint 0 _, ⟨[0,(body constraint).length,0], ?_⟩, ?_, ?_⟩
    · simpa only [endpoint, BuilderLiteralClauseTokenSelector.endpoint, if_pos rfl, ite_true, separator_reference, Nat.add_zero] using hFull
    · simp only [initialValues, BuilderPayloadSearchSource.initialValues, BuilderPayloadSearchSource.baseValues, List.append_nil]
    · simp only [spanPolynomial, NatPolynomial.eval_add]
      omega
    · simp only [rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
      omega
  · have hEntry : (registerWord (initialValues constraint request (position - 1) older)).length +
        (bodyOutside outside).length ≤ bound.eval input := by
      rw [body_input_span constraint request position older outside (by omega)]
      exact hSpan
    obtain ⟨steps, values, resultOutside, hSource, _, hRetained, hExhausted, hSpace, hTime⟩ :=
      BuilderPayloadSourceSearchBounds.source_polynomial_bounds constraint request (position - 1) older
        inside (bodyOutside outside) bound input hEntry
    have hPrefix := WorkMachineProgramPath.runExact (graph (family constraint)) _ _ _ _ _
      (graph_wellFormed (family constraint)) (positive_prefix constraint request position older inside outside (by omega))
    have hBody := body_run constraint request (position - 1) older inside (bodyOutside outside)
      steps values resultOutside hSource hExhausted
    have hRun := PipelineMachineSimulation.workRunExact?_compose (WorkMachineProgramGraph.machine (graph (family constraint)))
      7 (steps + afterSteps constraint (position - 1)) _ _ _ hPrefix hBody
    rw [entry_projection] at hRun
    have hFull := same_rules_run (WorkMachineProgramGraph.machine (graph (family constraint)))
      (machine (family constraint)) rfl (noRuleAtAccept (family constraint)) (noRuleAtReject (family constraint))
      _ _ _ hRun
    refine ⟨7 + (steps + afterSteps constraint (position - 1)), values, resultOutside, ?_,
      endpoint_observes_encoding constraint position _, hRetained, ?_, ?_⟩
    · simpa only [endpoint, afterEndpoint, BuilderLiteralClauseTokenSelector.endpoint, if_neg hZero] using hFull
    · simp only [spanPolynomial, NatPolynomial.eval_add]
      omega
    · have hAfter := BuilderLiteralClauseTokenSelector.after_steps_le (body constraint) (position - 1)
      change afterSteps constraint (position - 1) ≤ 5 at hAfter
      simp only [rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant, Nat.mul_add]
      omega

/-- The same complete clause lookup runs in the compiled raw machine with a
uniform encoded-input polynomial bound and the original request intact. -/
theorem uniform_polynomial_lookup {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (position : Nat) (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues constraint request position older)).length + outside.length ≤ bound.eval input) :
    ∃ (rawSteps : Nat) (values : List Nat) (resultOutside : List WorkSymbol),
      rawSteps ≤ (rawTimePolynomial bound).eval input ∧
      run (compileWorkMachine (machine (family constraint))) rawSteps
        (encodeWorkConfiguration (workStartConfiguration (machine (family constraint))
          (endTape (initialValues constraint request position older) inside outside))) =
        encodeWorkConfiguration (endpointConfiguration (endpoint constraint position) (endTape values inside resultOutside)) ∧
      observe (endpointConfiguration (endpoint constraint position) (endTape values inside resultOutside)) =
        (encodeClauseTokens (BoundedClause.emit (body constraint)))[position]? ∧
      (∃ scratch, values = requestValues constraint request older ++ scratch) ∧
      (registerWord values).length + resultOutside.length ≤ (spanPolynomial bound).eval input := by
  obtain ⟨steps, values, resultOutside, hRun, hToken, hRetained, hSpace, hTime⟩ :=
    workRun_polynomial_lookup constraint request position older inside outside bound input hSpan
  exact ⟨6 * steps, values, resultOutside, hTime, run_compileWorkMachine_mul_of_workRunExact _ _ _ _ hRun,
    hToken, hRetained, hSpace⟩

end PNP.Concrete.CookLevin.BuilderPayloadClauseTokenSelector
