/-
Copyright (c) 2026 PNP Labs.

The fixed outer work-machine graph for the all-bitstring CNF-to-NAND
compiler.

The source parser is the only node reachable on an arbitrary raw input.  A
successful parse launches the canonical CNF carrier encoder, whose success
launches the finite carrier controller.  Every local rejection instead
crosses a literal bridge to the graph's global reject halt.  Consequently no
malformed source can enter the canonical-only carrier/controller proof.
-/

import PNP.Concrete.CNFSourceParserCorrectness
import PNP.Concrete.CNFToNANDCarrierEncoder
import PNP.Concrete.CNFToNANDController

namespace PNP.Concrete.CNFToNANDCompilerMachine

open PNP.Concrete.WorkMachineProgramGraph

/-! ## Three-node materialized graph -/

def parserRef : NodeRef :=
  { name := 0
    startState := CNFSourceParser.machine.startState }

def carrierRef : NodeRef :=
  { name := 1
    startState := CNFToNANDCarrierEncoder.machine.startState }

def controllerRef : NodeRef :=
  { name := 2
    startState := CNFToNANDController.machine.startState }

def parserNode : Node :=
  { name := parserRef.name
    program := CNFSourceParser.machine
    onAccept := .node carrierRef
    onReject := .reject }

def carrierNode : Node :=
  { name := carrierRef.name
    program := CNFToNANDCarrierEncoder.machine
    onAccept := .node controllerRef
    onReject := .reject }

def controllerNode : Node :=
  { name := controllerRef.name
    program := CNFToNANDController.machine
    onAccept := .accept
    onReject := .reject }

def nodes : List Node :=
  [parserNode, carrierNode, controllerNode]

def graph : Graph :=
  { nodes := nodes
    entry := parserRef }

def machine : WorkMachine :=
  WorkMachineProgramGraph.machine graph

def compiledMachine : Machine :=
  compileWorkMachine machine

/-! ## Structural certification -/

theorem parserNode_member :
    parserNode ∈ nodes := by
  simp [nodes]

theorem carrierNode_member :
    carrierNode ∈ nodes := by
  simp [nodes]

theorem controllerNode_member :
    controllerNode ∈ nodes := by
  simp [nodes]

private theorem parserNoRuleAtAccept :
    NoRuleAt CNFSourceParser.machine
      CNFSourceParser.machine.acceptState :=
  noRuleAt_of_findWorkRule_none _ _
    CNFSourceParser.no_rule_at_accept

private theorem parserNoRuleAtReject :
    NoRuleAt CNFSourceParser.machine
      CNFSourceParser.machine.rejectState :=
  noRuleAt_of_findWorkRule_none _ _
    CNFSourceParser.no_rule_at_reject

private theorem carrierNoRuleAtAccept :
    NoRuleAt CNFToNANDCarrierEncoder.machine
      CNFToNANDCarrierEncoder.machine.acceptState :=
  noRuleAt_of_findWorkRule_none _ _
    CNFToNANDCarrierEncoder.no_rule_at_accept

private theorem carrierNoRuleAtReject :
    NoRuleAt CNFToNANDCarrierEncoder.machine
      CNFToNANDCarrierEncoder.machine.rejectState :=
  noRuleAt_of_findWorkRule_none _ _
    CNFToNANDCarrierEncoder.no_rule_at_reject

private theorem controllerNoRuleAtAccept :
    NoRuleAt CNFToNANDController.machine
      CNFToNANDController.machine.acceptState :=
  noRuleAt_of_findWorkRule_none _ _
    CNFToNANDController.no_rule_at_accept

private theorem controllerNoRuleAtReject :
    NoRuleAt CNFToNANDController.machine
      CNFToNANDController.machine.rejectState :=
  noRuleAt_of_findWorkRule_none _ _
    CNFToNANDController.no_rule_at_reject

private theorem parserNode_wellFormed :
    parserNode.WellFormed := by
  refine
    ⟨?_, parserNoRuleAtAccept, parserNoRuleAtReject,
      CNFSourceParser.machine_acceptState_ne_rejectState⟩
  change CNFSourceParser.rules.Pairwise
    (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol))
  apply CNFSourceParser.rules_pairwise_query_distinct.imp
  intro left right distinct
  simpa only [CNFSourceParser.QueryDistinct] using distinct

private theorem carrierNode_wellFormed :
    carrierNode.WellFormed := by
  exact
    ⟨CNFToNANDCarrierEncoder.rules_pairwise,
      carrierNoRuleAtAccept,
      carrierNoRuleAtReject,
      CNFToNANDCarrierEncoder.machine_accept_ne_reject⟩

private theorem controllerNode_wellFormed :
    controllerNode.WellFormed := by
  exact
    ⟨CNFToNANDController.rules_pairwise,
      controllerNoRuleAtAccept,
      controllerNoRuleAtReject,
      CNFToNANDController.machine_accept_ne_reject⟩

private theorem nodeNames_pairwise :
    nodes.Pairwise (fun left right => left.name ≠ right.name) := by
  decide

private theorem nodes_wellFormed :
    ∀ node, node ∈ nodes → node.WellFormed := by
  intro node member
  simp only [nodes, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with nodeEq | nodeEq | nodeEq
  · subst node
    exact parserNode_wellFormed
  · subst node
    exact carrierNode_wellFormed
  · subst node
    exact controllerNode_wellFormed

private theorem parser_resolves :
    Endpoint.Resolves nodes (.node parserRef) :=
  ⟨parserNode, parserNode_member, rfl, rfl⟩

private theorem carrier_resolves :
    Endpoint.Resolves nodes (.node carrierRef) :=
  ⟨carrierNode, carrierNode_member, rfl, rfl⟩

private theorem controller_resolves :
    Endpoint.Resolves nodes (.node controllerRef) :=
  ⟨controllerNode, controllerNode_member, rfl, rfl⟩

private theorem nodes_endpoints_resolve :
    ∀ node, node ∈ nodes →
      Endpoint.Resolves nodes node.onAccept ∧
        Endpoint.Resolves nodes node.onReject := by
  intro node member
  simp only [nodes, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with nodeEq | nodeEq | nodeEq
  · subst node
    exact ⟨carrier_resolves, trivial⟩
  · subst node
    exact ⟨controller_resolves, trivial⟩
  · subst node
    exact ⟨trivial, trivial⟩

theorem graph_wellFormed :
    graph.WellFormed :=
  ⟨nodeNames_pairwise, nodes_wellFormed,
    parser_resolves, nodes_endpoints_resolve⟩

theorem rules_pairwise :
    machine.rules.Pairwise QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise graph graph_wellFormed

theorem machine_start_ne_accept :
    machine.startState ≠ machine.acceptState :=
  WorkMachineProgramGraph.machine_start_ne_accept graph

theorem machine_start_ne_reject :
    machine.startState ≠ machine.rejectState :=
  WorkMachineProgramGraph.machine_start_ne_reject graph

theorem machine_accept_ne_reject :
    machine.acceptState ≠ machine.rejectState :=
  WorkMachineProgramGraph.machine_accept_ne_reject graph

theorem no_rule_at_accept (symbol : WorkSymbol) :
    findWorkRule machine.rules machine.acceptState symbol = none :=
  WorkMachineProgramGraph.no_rule_at_accept graph symbol

theorem no_rule_at_reject (symbol : WorkSymbol) :
    findWorkRule machine.rules machine.rejectState symbol = none :=
  WorkMachineProgramGraph.no_rule_at_reject graph symbol

theorem no_rule_at_dead (symbol : WorkSymbol) :
    findWorkRule machine.rules globalDeadState symbol = none :=
  WorkMachineProgramGraph.no_rule_at_dead graph symbol

theorem accept_halted (tape : WorkTape) :
    machine.isHalted
      { state := machine.acceptState, tape := tape } = true :=
  WorkMachineProgramGraph.global_accept_halted graph tape

theorem reject_halted (tape : WorkTape) :
    machine.isHalted
      { state := machine.rejectState, tape := tape } = true :=
  WorkMachineProgramGraph.global_reject_halted graph tape

theorem dead_stuck (tape : WorkTape) :
    workStep? machine
      { state := globalDeadState, tape := tape } = none :=
  WorkMachineProgramGraph.dead_stuck graph tape

def nodeCount : Nat := 3

theorem nodes_length_literal :
    nodes.length = nodeCount := by
  rfl

/-- Three local rule tables plus two total nine-symbol bridge rows at each
node. -/
def ruleCount : Nat := 135070

private theorem machine_rules_eq_graph_rules :
    machine.rules = WorkMachineProgramGraph.rules graph := by
  rfl

private theorem graph_nodes_eq_literal :
    graph.nodes = [parserNode, carrierNode, controllerNode] := by
  rfl

private theorem parserNode_program_rules_length :
    parserNode.program.rules.length = 99 := by
  exact CNFSourceParser.rules_length

private theorem carrierNode_program_rules_length :
    carrierNode.program.rules.length = 13844 := by
  exact CNFToNANDCarrierEncoder.rules_length

private theorem controllerNode_program_rules_length :
    controllerNode.program.rules.length = 121073 := by
  exact CNFToNANDController.rules_length_literal

private theorem three_node_rule_sum
    (first second third : Node)
    (firstCount secondCount thirdCount : Nat)
    (firstLength : first.program.rules.length = firstCount)
    (secondLength : second.program.rules.length = secondCount)
    (thirdLength : third.program.rules.length = thirdCount) :
    ([first, second, third].map
      (fun node => 18 + node.program.rules.length)).sum =
        18 + firstCount +
          (18 + secondCount + (18 + thirdCount + 0)) := by
  simp only [List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  rw [firstLength, secondLength, thirdLength]

private theorem graph_rule_sum_eq_literal :
    (graph.nodes.map
      (fun node => 18 + node.program.rules.length)).sum =
        ruleCount := by
  calc
    (graph.nodes.map
        (fun node => 18 + node.program.rules.length)).sum =
        ([parserNode, carrierNode, controllerNode].map
          (fun node => 18 + node.program.rules.length)).sum :=
      congrArg
        (fun nodeList =>
          (nodeList.map
            (fun node => 18 + node.program.rules.length)).sum)
        graph_nodes_eq_literal
    _ = 18 + 99 + (18 + 13844 + (18 + 121073 + 0)) :=
      three_node_rule_sum
        parserNode carrierNode controllerNode
        99 13844 121073
        parserNode_program_rules_length
        carrierNode_program_rules_length
        controllerNode_program_rules_length
    _ = ruleCount := by
      unfold ruleCount
      omega

theorem rules_length_literal :
    machine.rules.length = ruleCount := by
  calc
    machine.rules.length =
        (WorkMachineProgramGraph.rules graph).length :=
      congrArg List.length machine_rules_eq_graph_rules
    _ = (graph.nodes.map
          (fun node => 18 + node.program.rules.length)).sum :=
      WorkMachineProgramGraph.rules_length graph
    _ = ruleCount := graph_rule_sum_eq_literal

end PNP.Concrete.CNFToNANDCompilerMachine
