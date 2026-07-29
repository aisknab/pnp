/-
Copyright (c) 2026 PNP Labs.

Generic finite program-graph composition for literal work machines.

Every node receives a structural, collision-free state namespace.  Its local
accept and reject endpoints are replaced by total nine-symbol bridge tables
whose destinations are stored directly in the finite graph.  The combined
machine therefore performs no host-side node lookup while it runs.
-/

import PNP.Concrete.WorkMachineChain

namespace PNP.Concrete.WorkMachineProgramGraph

open PNP.Concrete
open PipelineStateNamespace PipelineStageBridges

/-! ### Structural state namespaces and explicit endpoints -/

/-- Prefix-code pairing of a node name and one local state. -/
def payloadState : Nat → Nat → Nat
  | 0, localState => 2 * localState
  | nodeName + 1, localState =>
      2 * payloadState nodeName localState + 1

theorem payloadState_injective
    {leftName rightName leftState rightState : Nat}
    (equality :
      payloadState leftName leftState =
        payloadState rightName rightState) :
    leftName = rightName ∧ leftState = rightState := by
  induction leftName generalizing rightName leftState rightState with
  | zero =>
      cases rightName with
      | zero =>
          simp [payloadState] at equality
          constructor
          · rfl
          · omega
      | succ rightName =>
          simp [payloadState] at equality
          omega
  | succ leftName inductionHypothesis =>
      cases rightName with
      | zero =>
          simp [payloadState] at equality
          omega
      | succ rightName =>
          have inner :
              payloadState leftName leftState =
                payloadState rightName rightState := by
            simp [payloadState] at equality
            omega
          have parts := inductionHypothesis inner
          exact ⟨congrArg Nat.succ parts.1, parts.2⟩

/-- Node states are kept above the three explicit global endpoints. -/
def nodeState (nodeName localState : Nat) : Nat :=
  payloadState nodeName localState + 3

theorem nodeState_injective
    {leftName rightName leftState rightState : Nat}
    (equality :
      nodeState leftName leftState =
        nodeState rightName rightState) :
    leftName = rightName ∧ leftState = rightState := by
  apply payloadState_injective
  unfold nodeState at equality
  omega

theorem nodeState_fixed_injective (nodeName : Nat) :
    Function.Injective (nodeState nodeName) := by
  intro left right equality
  exact (nodeState_injective equality).2

theorem nodeState_ne_of_name_ne
    {leftName rightName : Nat} (nameNe : leftName ≠ rightName)
    (leftState rightState : Nat) :
    nodeState leftName leftState ≠
      nodeState rightName rightState := by
  intro equality
  exact nameNe (nodeState_injective equality).1

theorem nodeState_ge_three (nodeName localState : Nat) :
    3 ≤ nodeState nodeName localState := by
  unfold nodeState
  omega

def globalAcceptState : Nat := 0
def globalRejectState : Nat := 1
def globalDeadState : Nat := 2

structure NodeRef where
  name : Nat
  startState : Nat
deriving DecidableEq, Repr

inductive Endpoint where
  | node (target : NodeRef)
  | accept
  | reject
  | dead
deriving DecidableEq, Repr

def endpointState : Endpoint → Nat
  | .node target => nodeState target.name target.startState
  | .accept => globalAcceptState
  | .reject => globalRejectState
  | .dead => globalDeadState

theorem endpointState_injective :
    Function.Injective endpointState := by
  intro left right equality
  cases left with
  | node leftTarget =>
      cases right with
      | node rightTarget =>
          have parts := nodeState_injective equality
          cases leftTarget
          cases rightTarget
          simp only at parts
          simp [parts.1, parts.2]
      | accept =>
          have bound := nodeState_ge_three
            leftTarget.name leftTarget.startState
          simp [endpointState, globalAcceptState] at equality
          omega
      | reject =>
          have bound := nodeState_ge_three
            leftTarget.name leftTarget.startState
          simp [endpointState, globalRejectState] at equality
          omega
      | dead =>
          have bound := nodeState_ge_three
            leftTarget.name leftTarget.startState
          simp [endpointState, globalDeadState] at equality
          omega
  | accept =>
      cases right with
      | node rightTarget =>
          have bound := nodeState_ge_three
            rightTarget.name rightTarget.startState
          simp [endpointState, globalAcceptState] at equality
          omega
      | accept => rfl
      | reject =>
          simp [endpointState, globalAcceptState,
            globalRejectState] at equality
      | dead =>
          simp [endpointState, globalAcceptState,
            globalDeadState] at equality
  | reject =>
      cases right with
      | node rightTarget =>
          have bound := nodeState_ge_three
            rightTarget.name rightTarget.startState
          simp [endpointState, globalRejectState] at equality
          omega
      | accept =>
          simp [endpointState, globalAcceptState,
            globalRejectState] at equality
      | reject => rfl
      | dead =>
          simp [endpointState, globalRejectState,
            globalDeadState] at equality
  | dead =>
      cases right with
      | node rightTarget =>
          have bound := nodeState_ge_three
            rightTarget.name rightTarget.startState
          simp [endpointState, globalDeadState] at equality
          omega
      | accept =>
          simp [endpointState, globalAcceptState,
            globalDeadState] at equality
      | reject =>
          simp [endpointState, globalRejectState,
            globalDeadState] at equality
      | dead => rfl

theorem nodeEndpoints_ne_of_name_ne
    (left right : NodeRef) (nameNe : left.name ≠ right.name) :
    endpointState (.node left) ≠ endpointState (.node right) := by
  exact nodeState_ne_of_name_ne nameNe
    left.startState right.startState

/-! ### Finite graph materialization -/

structure Node where
  name : Nat
  program : WorkMachine
  onAccept : Endpoint
  onReject : Endpoint

def Node.reference (node : Node) : NodeRef :=
  { name := node.name
    startState := node.program.startState }

def Node.conditional (name : Nat) (program : WorkMachine)
    (acceptSuccessor rejectSuccessor : NodeRef) : Node :=
  { name := name
    program := program
    onAccept := .node acceptSuccessor
    onReject := .node rejectSuccessor }

theorem Node.conditional_accept_target
    (name : Nat) (program : WorkMachine)
    (acceptSuccessor rejectSuccessor : NodeRef) :
    (Node.conditional name program
      acceptSuccessor rejectSuccessor).onAccept =
        .node acceptSuccessor := by
  rfl

theorem Node.conditional_reject_target
    (name : Nat) (program : WorkMachine)
    (acceptSuccessor rejectSuccessor : NodeRef) :
    (Node.conditional name program
      acceptSuccessor rejectSuccessor).onReject =
        .node rejectSuccessor := by
  rfl

theorem Node.conditional_targets_distinct
    (name : Nat) (program : WorkMachine)
    (acceptSuccessor rejectSuccessor : NodeRef)
    (distinct : acceptSuccessor ≠ rejectSuccessor) :
    endpointState
        (Node.conditional name program
          acceptSuccessor rejectSuccessor).onAccept ≠
      endpointState
        (Node.conditional name program
          acceptSuccessor rejectSuccessor).onReject := by
  intro equality
  have targetEquality := endpointState_injective equality
  apply distinct
  simpa [Node.conditional] using targetEquality

def Node.encode (node : Node) (localState : Nat) : Nat :=
  nodeState node.name localState

theorem Node.encode_injective (node : Node) :
    Function.Injective node.encode :=
  nodeState_fixed_injective node.name

def Node.acceptBridgeRules (node : Node) : List WorkRule :=
  launchRules
    (node.encode node.program.acceptState)
    (endpointState node.onAccept)

def Node.rejectBridgeRules (node : Node) : List WorkRule :=
  launchRules
    (node.encode node.program.rejectState)
    (endpointState node.onReject)

def Node.localRules (node : Node) : List WorkRule :=
  node.program.rules.map (renameRule node.encode)

def Node.rules (node : Node) : List WorkRule :=
  node.acceptBridgeRules ++
    (node.rejectBridgeRules ++ node.localRules)

structure Graph where
  nodes : List Node
  entry : NodeRef

def rules (graph : Graph) : List WorkRule :=
  graph.nodes.flatMap Node.rules

def machine (graph : Graph) : WorkMachine :=
  { rules := rules graph
    startState := nodeState graph.entry.name graph.entry.startState
    acceptState := globalAcceptState
    rejectState := globalRejectState }

def compiledMachine (graph : Graph) : Machine :=
  compileWorkMachine (machine graph)

def QueryDistinct (left right : WorkRule) : Prop :=
  (left.sourceState, left.readSymbol) ≠
    (right.sourceState, right.readSymbol)

def NoRuleAt (program : WorkMachine) (state : Nat) : Prop :=
  ∀ rule, rule ∈ program.rules → rule.sourceState ≠ state

private theorem noSourceMember_of_findWorkRule_none
    (rules : List WorkRule) (state : Nat)
    (missing :
      ∀ symbol, findWorkRule rules state symbol = none) :
    ∀ rule, rule ∈ rules → rule.sourceState ≠ state := by
  induction rules with
  | nil =>
      intro rule member
      contradiction
  | cons first rest inductionHypothesis =>
      intro rule member sourceEquality
      cases member with
      | head =>
          have found := findWorkRule_cons_of_matches
            first rest state first.readSymbol
            ⟨sourceEquality, rfl⟩
          rw [missing first.readSymbol] at found
          contradiction
      | tail _ restMember =>
          have restMissing :
              ∀ symbol,
                findWorkRule rest state symbol = none := by
            intro symbol
            by_cases queryMatches :
                first.sourceState = state ∧
                  first.readSymbol = symbol
            · have found := findWorkRule_cons_of_matches
                first rest state symbol queryMatches
              rw [missing symbol] at found
              contradiction
            · rw [← findWorkRule_cons_of_not_matches
                  first rest state symbol queryMatches]
              exact missing symbol
          exact inductionHypothesis restMissing
            rule restMember sourceEquality

theorem noRuleAt_of_findWorkRule_none
    (program : WorkMachine) (state : Nat)
    (missing :
      ∀ symbol, findWorkRule program.rules state symbol = none) :
    NoRuleAt program state :=
  noSourceMember_of_findWorkRule_none
    program.rules state missing

def Node.WellFormed (node : Node) : Prop :=
  node.program.rules.Pairwise QueryDistinct ∧
    NoRuleAt node.program node.program.acceptState ∧
    NoRuleAt node.program node.program.rejectState ∧
    node.program.acceptState ≠ node.program.rejectState

def Endpoint.Resolves (nodes : List Node) : Endpoint → Prop
  | .node target =>
      ∃ node ∈ nodes,
        node.name = target.name ∧
          node.program.startState = target.startState
  | .accept | .reject | .dead => True

def Graph.WellFormed (graph : Graph) : Prop :=
  graph.nodes.Pairwise (fun left right => left.name ≠ right.name) ∧
    (∀ node, node ∈ graph.nodes → node.WellFormed) ∧
    Endpoint.Resolves graph.nodes (.node graph.entry) ∧
    (∀ node, node ∈ graph.nodes →
      Endpoint.Resolves graph.nodes node.onAccept ∧
        Endpoint.Resolves graph.nodes node.onReject)

/-! ### Literal rule-count accounting -/

theorem Node.acceptBridgeRules_length (node : Node) :
    node.acceptBridgeRules.length = 9 := by
  rfl

theorem Node.rejectBridgeRules_length (node : Node) :
    node.rejectBridgeRules.length = 9 := by
  rfl

theorem Node.localRules_length (node : Node) :
    node.localRules.length = node.program.rules.length := by
  simp [Node.localRules]

theorem Node.rules_length (node : Node) :
    node.rules.length = 18 + node.program.rules.length := by
  simp [Node.rules, Node.acceptBridgeRules_length,
    Node.rejectBridgeRules_length, Node.localRules_length]
  omega

theorem rules_length (graph : Graph) :
    (rules graph).length =
      (graph.nodes.map
        (fun node => 18 + node.program.rules.length)).sum := by
  unfold rules
  induction graph.nodes with
  | nil => simp
  | cons node rest inductionHypothesis =>
      simp [Node.rules_length, inductionHypothesis]

/-! ### Global query distinctness -/

private theorem queryDistinct_of_source_ne
    (left right : WorkRule)
    (sourceNe : left.sourceState ≠ right.sourceState) :
    QueryDistinct left right := by
  intro equality
  exact sourceNe (congrArg Prod.fst equality)

private theorem launchRules_pairwise (source target : Nat) :
    (launchRules source target).Pairwise QueryDistinct := by
  unfold launchRules PipelineMachineSimulation.allWorkSymbols
  simp [QueryDistinct, launchRule, WorkSymbol.blank,
    WorkSymbol.blankZero, WorkSymbol.blankOne,
    WorkSymbol.zeroBlank, WorkSymbol.zeroZero,
    WorkSymbol.zeroOne, WorkSymbol.oneBlank,
    WorkSymbol.oneZero, WorkSymbol.oneOne]

private theorem launchRules_source_eq
    {source target : Nat} {rule : WorkRule}
    (member : rule ∈ launchRules source target) :
    rule.sourceState = source := by
  rcases List.mem_map.mp member with
    ⟨symbol, _symbolMember, equality⟩
  rw [← equality]
  rfl

private theorem renamedRules_pairwise
    (encode : Nat → Nat) (injective : Function.Injective encode)
    (localRules : List WorkRule)
    (pairwise : localRules.Pairwise QueryDistinct) :
    (localRules.map (renameRule encode)).Pairwise QueryDistinct := by
  exact List.Pairwise.map (renameRule encode)
    (fun left right distinct => by
      intro equality
      apply distinct
      apply Prod.ext
      · exact injective (by
          simpa [renameRule] using
            congrArg Prod.fst equality)
      · simpa [renameRule] using
          congrArg Prod.snd equality)
    pairwise

private theorem localRules_source
    {node : Node} {rule : WorkRule}
    (member : rule ∈ node.localRules) :
    ∃ localRule ∈ node.program.rules,
      rule.sourceState =
        node.encode localRule.sourceState := by
  rcases List.mem_map.mp member with
    ⟨localRule, localMember, equality⟩
  exact ⟨localRule, localMember, by
    rw [← equality]
    rfl⟩

private theorem launchLaunch_cross
    (leftSource leftTarget rightSource rightTarget : Nat)
    (sourceNe : leftSource ≠ rightSource) :
    ∀ leftRule ∈ launchRules leftSource leftTarget,
      ∀ rightRule ∈ launchRules rightSource rightTarget,
        QueryDistinct leftRule rightRule := by
  intro leftRule leftMember rightRule rightMember
  apply queryDistinct_of_source_ne
  rw [launchRules_source_eq leftMember,
    launchRules_source_eq rightMember]
  exact sourceNe

private theorem launchLocal_cross
    (node : Node) (source target localState : Nat)
    (sourceEq : source = node.encode localState)
    (noRule :
      NoRuleAt node.program localState) :
    ∀ bridgeRule ∈ launchRules source target,
      ∀ localRule ∈ node.localRules,
        QueryDistinct bridgeRule localRule := by
  intro bridgeRule bridgeMember renamed localMember
  rcases localRules_source localMember with
    ⟨rule, ruleMember, renamedSource⟩
  apply queryDistinct_of_source_ne
  rw [launchRules_source_eq bridgeMember,
    renamedSource, sourceEq]
  intro equality
  exact noRule rule ruleMember
    (node.encode_injective equality).symm

private theorem Node.rules_pairwise
    (node : Node) (wellFormed : node.WellFormed) :
    node.rules.Pairwise QueryDistinct := by
  rcases wellFormed with
    ⟨localPairwise, noAccept, noReject,
      acceptNeReject⟩
  have acceptPairwise := launchRules_pairwise
    (node.encode node.program.acceptState)
    (endpointState node.onAccept)
  have rejectPairwise := launchRules_pairwise
    (node.encode node.program.rejectState)
    (endpointState node.onReject)
  have localPairwiseRenamed :=
    renamedRules_pairwise node.encode node.encode_injective
      node.program.rules localPairwise
  have acceptSourceNeReject :
      node.encode node.program.acceptState ≠
        node.encode node.program.rejectState :=
    fun equality =>
      acceptNeReject (node.encode_injective equality)
  have rejectAndLocal :
      (node.rejectBridgeRules ++ node.localRules).Pairwise
        QueryDistinct := by
    rw [List.pairwise_append]
    exact
      ⟨rejectPairwise, localPairwiseRenamed,
        launchLocal_cross node
          (node.encode node.program.rejectState)
          (endpointState node.onReject)
          node.program.rejectState rfl noReject⟩
  unfold Node.rules
  rw [List.pairwise_append]
  refine ⟨acceptPairwise, rejectAndLocal, ?_⟩
  intro acceptRule acceptMember tailRule tailMember
  simp only [List.mem_append] at tailMember
  rcases tailMember with rejectMember | localMember
  · exact launchLaunch_cross
      (node.encode node.program.acceptState)
      (endpointState node.onAccept)
      (node.encode node.program.rejectState)
      (endpointState node.onReject)
      acceptSourceNeReject
      acceptRule acceptMember tailRule rejectMember
  · exact launchLocal_cross node
      (node.encode node.program.acceptState)
      (endpointState node.onAccept)
      node.program.acceptState rfl noAccept
      acceptRule acceptMember tailRule localMember

private theorem Node.rules_source
    {node : Node} {rule : WorkRule}
    (member : rule ∈ node.rules) :
    ∃ localState,
      rule.sourceState = node.encode localState := by
  simp only [Node.rules, List.mem_append] at member
  rcases member with acceptMember | rejectMember | localMember
  · exact ⟨node.program.acceptState,
      launchRules_source_eq acceptMember⟩
  · exact ⟨node.program.rejectState,
      launchRules_source_eq rejectMember⟩
  · rcases localRules_source localMember with
      ⟨localRule, _localMember, sourceEquality⟩
    exact ⟨localRule.sourceState, sourceEquality⟩

private theorem Node.rules_cross
    (left right : Node) (nameNe : left.name ≠ right.name) :
    ∀ leftRule ∈ left.rules,
      ∀ rightRule ∈ right.rules,
        QueryDistinct leftRule rightRule := by
  intro leftRule leftMember rightRule rightMember
  rcases Node.rules_source leftMember with
    ⟨leftState, leftSource⟩
  rcases Node.rules_source rightMember with
    ⟨rightState, rightSource⟩
  apply queryDistinct_of_source_ne
  rw [leftSource, rightSource]
  exact nodeState_ne_of_name_ne nameNe
    leftState rightState

private theorem materialized_pairwise
    (nodes : List Node)
    (namesPairwise :
      nodes.Pairwise (fun left right =>
        left.name ≠ right.name))
    (nodesWellFormed :
      ∀ node, node ∈ nodes → node.WellFormed) :
    (nodes.flatMap Node.rules).Pairwise QueryDistinct := by
  induction nodes with
  | nil =>
      simp
  | cons node rest inductionHypothesis =>
      rw [List.flatMap_cons, List.pairwise_append]
      have pairwiseParts := List.pairwise_cons.mp namesPairwise
      refine
        ⟨Node.rules_pairwise node
            (nodesWellFormed node (List.Mem.head rest)),
          inductionHypothesis pairwiseParts.2
            (fun item member =>
              nodesWellFormed item
                (List.Mem.tail node member)),
          ?_⟩
      intro leftRule leftMember rightRule rightMember
      rcases List.mem_flatMap.mp rightMember with
        ⟨rightNode, rightNodeMember, rightRuleMember⟩
      exact Node.rules_cross node rightNode
        (pairwiseParts.1 rightNode rightNodeMember)
        leftRule leftMember rightRule rightRuleMember

theorem rules_pairwise (graph : Graph)
    (wellFormed : graph.WellFormed) :
    (rules graph).Pairwise QueryDistinct := by
  exact materialized_pairwise graph.nodes
    wellFormed.1 wellFormed.2.1

/-! ### Explicit global halt and dead endpoints -/

theorem machine_start_ne_accept (graph : Graph) :
    (machine graph).startState ≠
      (machine graph).acceptState := by
  have bound := nodeState_ge_three
    graph.entry.name graph.entry.startState
  change
    nodeState graph.entry.name graph.entry.startState ≠
      globalAcceptState
  unfold globalAcceptState
  omega

theorem machine_start_ne_reject (graph : Graph) :
    (machine graph).startState ≠
      (machine graph).rejectState := by
  have bound := nodeState_ge_three
    graph.entry.name graph.entry.startState
  change
    nodeState graph.entry.name graph.entry.startState ≠
      globalRejectState
  unfold globalRejectState
  omega

theorem machine_accept_ne_reject (graph : Graph) :
    (machine graph).acceptState ≠
      (machine graph).rejectState := by
  change globalAcceptState ≠ globalRejectState
  unfold globalAcceptState globalRejectState
  omega

private theorem rule_source_ge_three
    {graph : Graph} {rule : WorkRule}
    (member : rule ∈ rules graph) :
    3 ≤ rule.sourceState := by
  rcases List.mem_flatMap.mp member with
    ⟨node, _nodeMember, ruleMember⟩
  rcases Node.rules_source ruleMember with
    ⟨localState, sourceEquality⟩
  rw [sourceEquality]
  exact nodeState_ge_three node.name localState

theorem noRuleAt_globalAccept (graph : Graph) :
    NoRuleAt (machine graph) globalAcceptState := by
  intro rule member
  have bound := rule_source_ge_three member
  unfold globalAcceptState
  omega

theorem noRuleAt_globalReject (graph : Graph) :
    NoRuleAt (machine graph) globalRejectState := by
  intro rule member
  have bound := rule_source_ge_three member
  unfold globalRejectState
  omega

theorem noRuleAt_globalDead (graph : Graph) :
    NoRuleAt (machine graph) globalDeadState := by
  intro rule member
  have bound := rule_source_ge_three member
  unfold globalDeadState
  omega

private theorem findWorkRule_none_of_noRuleAt
    (rules : List WorkRule) (state : Nat)
    (noRule :
      ∀ rule, rule ∈ rules → rule.sourceState ≠ state)
    (symbol : WorkSymbol) :
    findWorkRule rules state symbol = none := by
  induction rules with
  | nil => rfl
  | cons rule rest inductionHypothesis =>
      rw [findWorkRule_cons_of_not_matches]
      · exact inductionHypothesis
          (fun item member =>
            noRule item (List.Mem.tail rule member))
      · intro matched
        exact noRule rule (List.Mem.head rest) matched.1

theorem no_rule_at_accept (graph : Graph)
    (symbol : WorkSymbol) :
    findWorkRule (machine graph).rules
      globalAcceptState symbol = none := by
  exact findWorkRule_none_of_noRuleAt
    (machine graph).rules globalAcceptState
    (noRuleAt_globalAccept graph) symbol

theorem no_rule_at_reject (graph : Graph)
    (symbol : WorkSymbol) :
    findWorkRule (machine graph).rules
      globalRejectState symbol = none := by
  exact findWorkRule_none_of_noRuleAt
    (machine graph).rules globalRejectState
    (noRuleAt_globalReject graph) symbol

theorem no_rule_at_dead (graph : Graph)
    (symbol : WorkSymbol) :
    findWorkRule (machine graph).rules
      globalDeadState symbol = none := by
  exact findWorkRule_none_of_noRuleAt
    (machine graph).rules globalDeadState
    (noRuleAt_globalDead graph) symbol

theorem global_accept_halted
    (graph : Graph) (tape : WorkTape) :
    (machine graph).isHalted
      { state := globalAcceptState, tape := tape } = true := by
  rfl

theorem global_reject_halted
    (graph : Graph) (tape : WorkTape) :
    (machine graph).isHalted
      { state := globalRejectState, tape := tape } = true := by
  rfl

theorem node_configuration_not_halted
    (graph : Graph) (nodeName localState : Nat)
    (tape : WorkTape) :
    (machine graph).isHalted
      { state := nodeState nodeName localState, tape := tape } =
        false := by
  have bound := nodeState_ge_three nodeName localState
  unfold WorkMachine.isHalted machine
  have acceptNe :
      nodeState nodeName localState ≠ globalAcceptState := by
    unfold globalAcceptState
    omega
  have rejectNe :
      nodeState nodeName localState ≠ globalRejectState := by
    unfold globalRejectState
    omega
  simp [acceptNe, rejectNe]

theorem dead_configuration_not_halted
    (graph : Graph) (tape : WorkTape) :
    (machine graph).isHalted
      { state := globalDeadState, tape := tape } = false := by
  rfl

theorem dead_stuck (graph : Graph) (tape : WorkTape) :
    workStep? (machine graph)
      { state := globalDeadState, tape := tape } = none := by
  have notHalted :=
    dead_configuration_not_halted graph tape
  unfold workStep?
  rw [notHalted]
  change
    (match findWorkRule (machine graph).rules
        globalDeadState tape.head with
     | none => none
     | some rule =>
         some (applyWorkRule rule
           { state := globalDeadState, tape := tape })) = none
  rw [no_rule_at_dead]

/-! ### Lookup isolation and exact trace transport -/

private theorem state_ne_accept_of_not_halted
    (program : WorkMachine) (config : WorkConfiguration)
    (notHalted : program.isHalted config = false) :
    config.state ≠ program.acceptState := by
  intro equality
  unfold WorkMachine.isHalted at notHalted
  rw [equality] at notHalted
  have reflexive :
      (program.acceptState == program.acceptState) = true :=
    (nat_beq_true_iff _ _).mpr rfl
  rw [reflexive] at notHalted
  contradiction

private theorem state_ne_reject_of_not_halted
    (program : WorkMachine) (config : WorkConfiguration)
    (notHalted : program.isHalted config = false) :
    config.state ≠ program.rejectState := by
  intro equality
  unfold WorkMachine.isHalted at notHalted
  rw [equality] at notHalted
  have reflexive :
      (program.rejectState == program.rejectState) = true :=
    (nat_beq_true_iff _ _).mpr rfl
  rw [reflexive] at notHalted
  simp at notHalted

private theorem Node.find_local_of_some
    (node : Node) (state : Nat) (symbol : WorkSymbol)
    (localRule : WorkRule)
    (stateNeAccept : state ≠ node.program.acceptState)
    (stateNeReject : state ≠ node.program.rejectState)
    (found :
      findWorkRule node.program.rules state symbol =
        some localRule) :
    findWorkRule node.rules (node.encode state) symbol =
      some (renameRule node.encode localRule) := by
  have acceptNone :
      findWorkRule node.acceptBridgeRules
          (node.encode state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    intro equality
    exact stateNeAccept
      (node.encode_injective equality).symm
  have rejectNone :
      findWorkRule node.rejectBridgeRules
          (node.encode state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    intro equality
    exact stateNeReject
      (node.encode_injective equality).symm
  have renamedFound :=
    findWorkRule_rename node.encode node.encode_injective
      node.program.rules state symbol
  rw [found] at renamedFound
  unfold Node.rules
  rw [findWorkRule_append_of_none _ _ _ _ acceptNone,
    findWorkRule_append_of_none _ _ _ _ rejectNone]
  exact renamedFound

private theorem Node.find_accept_bridge
    (node : Node) (symbol : WorkSymbol) :
    findWorkRule node.rules
        (node.encode node.program.acceptState) symbol =
      some (launchRule
        (node.encode node.program.acceptState)
        (endpointState node.onAccept) symbol) := by
  have found := findWorkRule_launchRules
    (node.encode node.program.acceptState)
    (endpointState node.onAccept) symbol
  unfold Node.rules
  exact findWorkRule_append_of_some _ _ _ _ _ found

private theorem Node.find_reject_bridge
    (node : Node) (symbol : WorkSymbol)
    (acceptNeReject :
      node.program.acceptState ≠ node.program.rejectState) :
    findWorkRule node.rules
        (node.encode node.program.rejectState) symbol =
      some (launchRule
        (node.encode node.program.rejectState)
        (endpointState node.onReject) symbol) := by
  have acceptNone :
      findWorkRule node.acceptBridgeRules
          (node.encode node.program.rejectState) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    intro equality
    exact acceptNeReject
      (node.encode_injective equality)
  have rejectFound := findWorkRule_launchRules
    (node.encode node.program.rejectState)
    (endpointState node.onReject) symbol
  unfold Node.rules
  rw [findWorkRule_append_of_none _ _ _ _ acceptNone]
  exact findWorkRule_append_of_some _ _ _ _ _ rejectFound

private theorem Node.find_none_of_name_ne
    (left right : Node) (nameNe : left.name ≠ right.name)
    (rightState : Nat) (symbol : WorkSymbol) :
    findWorkRule left.rules
        (right.encode rightState) symbol = none := by
  apply findWorkRule_none_of_noRuleAt
  intro rule member equality
  rcases Node.rules_source member with
    ⟨leftState, sourceEquality⟩
  rw [sourceEquality] at equality
  exact nodeState_ne_of_name_ne nameNe
    leftState rightState equality

private theorem findWorkRule_flatMap_of_node_some
    (nodes : List Node) (node : Node)
    (state : Nat) (symbol : WorkSymbol) (rule : WorkRule)
    (namesPairwise :
      nodes.Pairwise (fun left right =>
        left.name ≠ right.name))
    (member : node ∈ nodes)
    (nodeFound :
      findWorkRule node.rules (node.encode state) symbol =
        some rule) :
    findWorkRule (nodes.flatMap Node.rules)
        (node.encode state) symbol = some rule := by
  induction nodes with
  | nil =>
      contradiction
  | cons first rest inductionHypothesis =>
      have pairwiseParts :=
        List.pairwise_cons.mp namesPairwise
      cases member with
      | head =>
          exact findWorkRule_append_of_some _ _ _ _ _
            nodeFound
      | tail _ tailMember =>
          have firstNone :=
            Node.find_none_of_name_ne first node
              (pairwiseParts.1 node tailMember)
              state symbol
          rw [List.flatMap_cons,
            findWorkRule_append_of_none _ _ _ _ firstNone]
          exact inductionHypothesis pairwiseParts.2
            tailMember

theorem findWorkRule_local_of_some
    (graph : Graph) (node : Node)
    (state : Nat) (symbol : WorkSymbol)
    (localRule : WorkRule)
    (wellFormed : graph.WellFormed)
    (member : node ∈ graph.nodes)
    (stateNeAccept : state ≠ node.program.acceptState)
    (stateNeReject : state ≠ node.program.rejectState)
    (found :
      findWorkRule node.program.rules state symbol =
        some localRule) :
    findWorkRule (machine graph).rules
        (node.encode state) symbol =
      some (renameRule node.encode localRule) := by
  exact findWorkRule_flatMap_of_node_some
    graph.nodes node state symbol
    (renameRule node.encode localRule)
    wellFormed.1 member
    (Node.find_local_of_some node state symbol localRule
      stateNeAccept stateNeReject found)

theorem findWorkRule_accept_bridge
    (graph : Graph) (node : Node)
    (symbol : WorkSymbol)
    (wellFormed : graph.WellFormed)
    (member : node ∈ graph.nodes) :
    findWorkRule (machine graph).rules
        (node.encode node.program.acceptState) symbol =
      some (launchRule
        (node.encode node.program.acceptState)
        (endpointState node.onAccept) symbol) := by
  exact findWorkRule_flatMap_of_node_some
    graph.nodes node node.program.acceptState symbol
    (launchRule
      (node.encode node.program.acceptState)
      (endpointState node.onAccept) symbol)
    wellFormed.1 member
    (Node.find_accept_bridge node symbol)

theorem findWorkRule_reject_bridge
    (graph : Graph) (node : Node)
    (symbol : WorkSymbol)
    (wellFormed : graph.WellFormed)
    (member : node ∈ graph.nodes) :
    findWorkRule (machine graph).rules
        (node.encode node.program.rejectState) symbol =
      some (launchRule
        (node.encode node.program.rejectState)
        (endpointState node.onReject) symbol) := by
  have nodeWellFormed := wellFormed.2.1 node member
  exact findWorkRule_flatMap_of_node_some
    graph.nodes node node.program.rejectState symbol
    (launchRule
      (node.encode node.program.rejectState)
      (endpointState node.onReject) symbol)
    wellFormed.1 member
    (Node.find_reject_bridge node symbol
      nodeWellFormed.2.2.2)

theorem local_workStep_of_some
    (graph : Graph) (node : Node)
    (config next : WorkConfiguration)
    (wellFormed : graph.WellFormed)
    (member : node ∈ graph.nodes)
    (step :
      workStep? node.program config = some next) :
    workStep? (machine graph)
        (renameConfiguration node.encode config) =
      some (renameConfiguration node.encode next) := by
  rcases workStep?_some_exists node.program config next step with
    ⟨localRule, notHalted, found, nextEquality⟩
  have stateNeAccept :=
    state_ne_accept_of_not_halted
      node.program config notHalted
  have stateNeReject :=
    state_ne_reject_of_not_halted
      node.program config notHalted
  have globalFound :=
    findWorkRule_local_of_some graph node
      config.state config.tape.head localRule
      wellFormed member stateNeAccept stateNeReject found
  have globalNotHalted :
      (machine graph).isHalted
        (renameConfiguration node.encode config) = false := by
    simpa [Node.encode, renameConfiguration] using
      node_configuration_not_halted graph node.name
        config.state config.tape
  have globalStep := workStep?_eq_apply_of_find
    (machine graph)
    (renameConfiguration node.encode config)
    (renameRule node.encode localRule)
    globalNotHalted globalFound
  calc
    workStep? (machine graph)
        (renameConfiguration node.encode config) =
      some (applyWorkRule (renameRule node.encode localRule)
        (renameConfiguration node.encode config)) :=
      globalStep
    _ = some (renameConfiguration node.encode
        (applyWorkRule localRule config)) :=
      congrArg Option.some
        (applyWorkRule_rename node.encode localRule config)
    _ = some (renameConfiguration node.encode next) :=
      congrArg (fun value =>
        some (renameConfiguration node.encode value))
        nextEquality.symm

theorem local_workRunExact
    (graph : Graph) (node : Node)
    (steps : Nat) (initial final : WorkConfiguration)
    (wellFormed : graph.WellFormed)
    (member : node ∈ graph.nodes)
    (run :
      workRunExact? node.program steps initial =
        some final) :
    workRunExact? (machine graph) steps
        (renameConfiguration node.encode initial) =
      some (renameConfiguration node.encode final) := by
  exact PipelineStageBridges.workRunExact?_transport
    node.program (machine graph) node.encode
    (fun config next localStep =>
      local_workStep_of_some graph node config next
        wellFormed member localStep)
    steps initial final run

def endpointConfiguration
    (endpoint : Endpoint) (tape : WorkTape) :
    WorkConfiguration :=
  { state := endpointState endpoint
    tape := tape }

theorem accept_bridge_step
    (graph : Graph) (node : Node) (tape : WorkTape)
    (wellFormed : graph.WellFormed)
    (member : node ∈ graph.nodes) :
    workStep? (machine graph)
        (renameConfiguration node.encode
          { state := node.program.acceptState, tape := tape }) =
      some (endpointConfiguration node.onAccept tape) := by
  have notHalted :
      (machine graph).isHalted
        (renameConfiguration node.encode
          { state := node.program.acceptState,
            tape := tape }) = false := by
    simpa [Node.encode, renameConfiguration] using
      node_configuration_not_halted graph node.name
        node.program.acceptState tape
  have found := findWorkRule_accept_bridge
    graph node tape.head wellFormed member
  have stepped := workStep?_eq_apply_of_find
    (machine graph)
    (renameConfiguration node.encode
      { state := node.program.acceptState, tape := tape })
    (launchRule
      (node.encode node.program.acceptState)
      (endpointState node.onAccept) tape.head)
    notHalted found
  simpa [launchRule, applyWorkRule, WorkTape.write,
    WorkTape.move, renameConfiguration,
    endpointConfiguration] using stepped

theorem reject_bridge_step
    (graph : Graph) (node : Node) (tape : WorkTape)
    (wellFormed : graph.WellFormed)
    (member : node ∈ graph.nodes) :
    workStep? (machine graph)
        (renameConfiguration node.encode
          { state := node.program.rejectState, tape := tape }) =
      some (endpointConfiguration node.onReject tape) := by
  have notHalted :
      (machine graph).isHalted
        (renameConfiguration node.encode
          { state := node.program.rejectState,
            tape := tape }) = false := by
    simpa [Node.encode, renameConfiguration] using
      node_configuration_not_halted graph node.name
        node.program.rejectState tape
  have found := findWorkRule_reject_bridge
    graph node tape.head wellFormed member
  have stepped := workStep?_eq_apply_of_find
    (machine graph)
    (renameConfiguration node.encode
      { state := node.program.rejectState, tape := tape })
    (launchRule
      (node.encode node.program.rejectState)
      (endpointState node.onReject) tape.head)
    notHalted found
  simpa [launchRule, applyWorkRule, WorkTape.write,
    WorkTape.move, renameConfiguration,
    endpointConfiguration] using stepped

private theorem accept_bridge_step_from_config
    (graph : Graph) (node : Node)
    (config : WorkConfiguration)
    (wellFormed : graph.WellFormed)
    (member : node ∈ graph.nodes)
    (atAccept :
      config.state = node.program.acceptState) :
    workStep? (machine graph)
        (renameConfiguration node.encode config) =
      some (endpointConfiguration node.onAccept config.tape) := by
  cases config with
  | mk state tape =>
      simp only at atAccept
      subst state
      exact accept_bridge_step graph node tape
        wellFormed member

private theorem reject_bridge_step_from_config
    (graph : Graph) (node : Node)
    (config : WorkConfiguration)
    (wellFormed : graph.WellFormed)
    (member : node ∈ graph.nodes)
    (atReject :
      config.state = node.program.rejectState) :
    workStep? (machine graph)
        (renameConfiguration node.encode config) =
      some (endpointConfiguration node.onReject config.tape) := by
  cases config with
  | mk state tape =>
      simp only at atReject
      subst state
      exact reject_bridge_step graph node tape
        wellFormed member

theorem local_then_accept
    (graph : Graph) (node : Node)
    (steps : Nat) (initial final : WorkConfiguration)
    (wellFormed : graph.WellFormed)
    (member : node ∈ graph.nodes)
    (run :
      workRunExact? node.program steps initial =
        some final)
    (atAccept :
      final.state = node.program.acceptState) :
    workRunExact? (machine graph) (steps + 1)
        (renameConfiguration node.encode initial) =
      some (endpointConfiguration node.onAccept final.tape) := by
  have transported := local_workRunExact
    graph node steps initial final wellFormed member run
  have bridge :
      workRunExact? (machine graph) 1
          (renameConfiguration node.encode final) =
        some (endpointConfiguration node.onAccept final.tape) := by
    change
      (match workStep? (machine graph)
          (renameConfiguration node.encode final) with
       | none => none
       | some next =>
           workRunExact? (machine graph) 0 next) =
        some (endpointConfiguration node.onAccept final.tape)
    rw [accept_bridge_step_from_config
      graph node final wellFormed member atAccept]
    rfl
  exact PipelineMachineSimulation.workRunExact?_compose
    (machine graph) steps 1
    (renameConfiguration node.encode initial)
    (renameConfiguration node.encode final)
    (endpointConfiguration node.onAccept final.tape)
    transported bridge

theorem local_then_reject
    (graph : Graph) (node : Node)
    (steps : Nat) (initial final : WorkConfiguration)
    (wellFormed : graph.WellFormed)
    (member : node ∈ graph.nodes)
    (run :
      workRunExact? node.program steps initial =
        some final)
    (atReject :
      final.state = node.program.rejectState) :
    workRunExact? (machine graph) (steps + 1)
        (renameConfiguration node.encode initial) =
      some (endpointConfiguration node.onReject final.tape) := by
  have transported := local_workRunExact
    graph node steps initial final wellFormed member run
  have bridge :
      workRunExact? (machine graph) 1
          (renameConfiguration node.encode final) =
        some (endpointConfiguration node.onReject final.tape) := by
    change
      (match workStep? (machine graph)
          (renameConfiguration node.encode final) with
       | none => none
       | some next =>
           workRunExact? (machine graph) 0 next) =
        some (endpointConfiguration node.onReject final.tape)
    rw [reject_bridge_step_from_config
      graph node final wellFormed member atReject]
    rfl
  exact PipelineMachineSimulation.workRunExact?_compose
    (machine graph) steps 1
    (renameConfiguration node.encode initial)
    (renameConfiguration node.encode final)
    (endpointConfiguration node.onReject final.tape)
    transported bridge

/-! ### Additive and polynomial path accounting -/

def bridgedNodeWorkSteps (localSteps : Nat) : Nat :=
  localSteps + 1

theorem bridgedNodeWorkSteps_evaluated (localSteps : Nat) :
    bridgedNodeWorkSteps localSteps = localSteps + 1 := by
  rfl

def additiveWorkSteps (localSteps : List Nat) : Nat :=
  (localSteps.map bridgedNodeWorkSteps).sum

theorem additiveWorkSteps_nil :
    additiveWorkSteps [] = 0 := by
  rfl

theorem additiveWorkSteps_cons
    (head : Nat) (tail : List Nat) :
    additiveWorkSteps (head :: tail) =
      bridgedNodeWorkSteps head + additiveWorkSteps tail := by
  rfl

theorem additiveWorkSteps_eq_sum_add_length
    (localSteps : List Nat) :
    additiveWorkSteps localSteps =
      localSteps.sum + localSteps.length := by
  induction localSteps with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [additiveWorkSteps_cons, inductionHypothesis]
      simp [bridgedNodeWorkSteps]
      omega

def polynomialWorkBound
    (nodeCount maxLocalSteps : Nat) : Nat :=
  nodeCount * (maxLocalSteps + 1)

private theorem additiveWorkSteps_le_length_mul
    (localSteps : List Nat) (maxLocalSteps : Nat)
    (bounded :
      ∀ steps, steps ∈ localSteps →
        steps ≤ maxLocalSteps) :
    additiveWorkSteps localSteps ≤
      localSteps.length * (maxLocalSteps + 1) := by
  induction localSteps with
  | nil =>
      simp [additiveWorkSteps]
  | cons head tail inductionHypothesis =>
      have headLe :
          head ≤ maxLocalSteps :=
        bounded head (List.Mem.head tail)
      have tailBounded :
          ∀ steps, steps ∈ tail →
            steps ≤ maxLocalSteps := by
        intro steps member
        exact bounded steps (List.Mem.tail head member)
      have tailLe := inductionHypothesis tailBounded
      rw [additiveWorkSteps_cons]
      unfold bridgedNodeWorkSteps
      simp only [List.length_cons]
      rw [Nat.succ_mul]
      omega

theorem additiveWorkSteps_le_polynomialWorkBound
    (localSteps : List Nat)
    (nodeCount maxLocalSteps : Nat)
    (lengthBound : localSteps.length ≤ nodeCount)
    (bounded :
      ∀ steps, steps ∈ localSteps →
        steps ≤ maxLocalSteps) :
    additiveWorkSteps localSteps ≤
      polynomialWorkBound nodeCount maxLocalSteps := by
  have localBound :=
    additiveWorkSteps_le_length_mul
      localSteps maxLocalSteps bounded
  unfold polynomialWorkBound
  exact Nat.le_trans localBound
    (Nat.mul_le_mul_right
      (maxLocalSteps + 1) lengthBound)

end PNP.Concrete.WorkMachineProgramGraph
