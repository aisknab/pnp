/-
Copyright (c) 2026 PNP Labs.

One fixed dispatcher over the five canonical constraint regions. Every branch
runs the actual register selector and writes its own literal region tag.
Input-derived lengths and coordinates never construct its control table.

This selects a region and local coordinate. Region-local decoding, emission,
scratch recovery, Finish and the complete formula-builder loop remain separate.
-/

import PNP.Concrete.CookLevinBuilderRegionResidualOperands

namespace PNP.Concrete.CookLevin.BuilderConstraintRegionDispatch

open PipelineTape PipelineStateNamespace BuilderUnaryPolynomial
open BuilderDividerOperands (endTape inside count)
open BuilderArbitrarySlotHeaderRouter
open BuilderConstraintRegionRegisters (Region)
open WorkMachineProgramGraph (Node Graph Endpoint)
open WorkMachineProgramPath (LocalAcceptRun LocalRejectRun AcceptPath)

private theorem chain_run (first second : WorkMachine) (firstSteps secondSteps : Nat)
    (initial middle final : WorkTape)
    (hFirst : workRunExact? first firstSteps (workStartConfiguration first initial) =
      some { state := first.acceptState, tape := middle })
    (hSecond : workRunExact? second secondSteps (workStartConfiguration second middle) =
      some { state := second.acceptState, tape := final }) :
    workRunExact? (WorkMachineChain.machine first second) (firstSteps + 1 + secondSteps)
      (workStartConfiguration (WorkMachineChain.machine first second) initial) =
      some { state := (WorkMachineChain.machine first second).acceptState, tape := final } :=
  WorkMachineChain.workRunExact first second firstSteps secondSteps _ _ _ hFirst rfl hSecond

private theorem chain_noRuleAtReject (first second : WorkMachine)
    (hSecond : WorkMachineProgramGraph.NoRuleAt second second.rejectState) :
    WorkMachineProgramGraph.NoRuleAt (WorkMachineChain.machine first second)
      (WorkMachineChain.machine first second).rejectState :=
  WorkMachineChain.noRuleAtAccept first { second with acceptState := second.rejectState } hSecond

private theorem chain_rules_length (first second : WorkMachine) :
    (WorkMachineChain.machine first second).rules.length =
      9 + first.rules.length + second.rules.length := by
  change (WorkMachineChain.bridgeRules first second ++
    (first.rules.map (renameRule WorkMachineChain.firstState) ++
      second.rules.map (renameRule WorkMachineChain.secondState))).length = _
  have hBridge : (WorkMachineChain.bridgeRules first second).length = 9 := rfl
  simp only [List.length_append, List.length_map, hBridge, Nat.add_assoc]

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineChain.QueryDistinct ∧
    WorkMachineChain.NoRuleAtAccept program ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧
    program.acceptState ≠ program.rejectState

private theorem chain_good (first second : WorkMachine) (hFirst : Good first) (hSecond : Good second) :
    Good (WorkMachineChain.machine first second) :=
  ⟨WorkMachineChain.rules_pairwise_query_distinct _ _ hFirst.1 hSecond.1 hFirst.2.1,
   WorkMachineChain.noRuleAtAccept _ _ hSecond.2.1,
   chain_noRuleAtReject _ _ hSecond.2.2.1,
   WorkMachineChain.machine_acceptState_ne_rejectState _ _ hSecond.2.2.2⟩

private theorem delimiter_good : Good BuilderDividerOperands.Delimiter.machine := by
  refine ⟨BuilderDividerOperands.Delimiter.rules_pairwise_query_distinct,
    BuilderDividerOperands.Delimiter.noRuleAtAccept, ?_,
    BuilderDividerOperands.Delimiter.acceptState_ne_rejectState⟩
  intro rule hMem
  decide +revert

private theorem increment_good : Good BuilderConstraintRegionAssembly.Increment.machine := by
  refine ⟨BuilderConstraintRegionAssembly.Increment.rules_pairwise_query_distinct,
    BuilderConstraintRegionAssembly.Increment.noRuleAtAccept, ?_,
    BuilderConstraintRegionAssembly.Increment.acceptState_ne_rejectState⟩
  intro rule hMem
  decide +revert

namespace Tag

/-- A control-fixed literal, written by a delimiter and actual increments. -/
def machine : Nat → WorkMachine
  | 0 => BuilderDividerOperands.Delimiter.machine
  | tag + 1 => WorkMachineChain.machine (machine tag) BuilderConstraintRegionAssembly.Increment.machine

def steps (tag : Nat) : Nat := 2 + 3 * tag

theorem workRunExact (tag : Nat) (values : List Nat) (workspace tail : List WorkSymbol) :
    workRunExact? (machine tag) (steps tag)
      (workStartConfiguration (machine tag) (endTape values workspace tail)) =
      some {
        state := (machine tag).acceptState
        tape := endTape (values ++ [tag]) workspace (tail.drop (tag + 1))
      } := by
  induction tag with
  | zero => exact BuilderDividerOperands.Delimiter.workRunExact values workspace tail
  | succ tag ih =>
    have hIncrement := BuilderConstraintRegionAssembly.Increment.workRunExact values tag
      workspace (tail.drop (tag + 1))
    have hAll := chain_run (machine tag) BuilderConstraintRegionAssembly.Increment.machine
      (steps tag) 2 _ _ _ ih hIncrement
    have hSteps : steps tag + 1 + 2 = steps (tag + 1) := by unfold steps; omega
    rw [hSteps] at hAll
    simpa only [machine, List.drop_drop, Nat.add_assoc] using hAll

private theorem good (tag : Nat) : Good (machine tag) := by
  induction tag with
  | zero => exact delimiter_good
  | succ tag ih => exact chain_good _ _ ih increment_good

theorem rules_length (tag : Nat) : (machine tag).rules.length = 18 + 27 * tag := by
  induction tag with
  | zero => exact BuilderDividerOperands.Delimiter.rules_length
  | succ tag ih =>
    change (WorkMachineChain.machine (machine tag) BuilderConstraintRegionAssembly.Increment.machine).rules.length = _
    rw [chain_rules_length, ih, BuilderConstraintRegionAssembly.Increment.rules_length]
    omega

theorem rules_pairwise_query_distinct (tag : Nat) :
    (machine tag).rules.Pairwise WorkMachineChain.QueryDistinct := (good tag).1

theorem noRuleAtAccept (tag : Nat) : WorkMachineChain.NoRuleAtAccept (machine tag) := (good tag).2.1

theorem noRuleAtReject (tag : Nat) :
    WorkMachineProgramGraph.NoRuleAt (machine tag) (machine tag).rejectState := (good tag).2.2.1

theorem acceptState_ne_rejectState (tag : Nat) :
    (machine tag).acceptState ≠ (machine tag).rejectState := (good tag).2.2.2

end Tag

def regionTag : Region → Nat
  | .shape => 0
  | .initial => 1
  | .control => 2
  | .preservation => 3
  | .accepting => 4

def tagNode (tag : Nat) : Node :=
  { name := 5 + tag
    program := Tag.machine tag
    onAccept := .accept
    onReject := .dead }

def acceptingNode : Node :=
  { name := 4
    program := BuilderRegionResidualOperands.machine 20
    onAccept := .node (tagNode 4).reference
    onReject := .reject }

def preservationNode : Node :=
  { name := 3
    program := BuilderRegionResidualOperands.machine 15
    onAccept := .node (tagNode 3).reference
    onReject := .node acceptingNode.reference }

def controlNode : Node :=
  { name := 2
    program := BuilderRegionResidualOperands.machine 10
    onAccept := .node (tagNode 2).reference
    onReject := .node preservationNode.reference }

def initialNode : Node :=
  { name := 1
    program := BuilderRegionResidualOperands.machine 5
    onAccept := .node (tagNode 1).reference
    onReject := .node controlNode.reference }

def shapeNode : Node :=
  { name := 0
    program := BuilderRegionResidualOperands.machine 0
    onAccept := .node (tagNode 0).reference
    onReject := .node initialNode.reference }

def nodeFor : Region → Node
  | .shape => shapeNode
  | .initial => initialNode
  | .control => controlNode
  | .preservation => preservationNode
  | .accepting => acceptingNode

def graph : Graph :=
  { nodes := [shapeNode, initialNode, controlNode, preservationNode, acceptingNode,
      tagNode 0, tagNode 1, tagNode 2, tagNode 3, tagNode 4]
    entry := shapeNode.reference }

def machine : WorkMachine := WorkMachineProgramGraph.machine graph

private theorem node_mem (region : Region) : nodeFor region ∈ graph.nodes := by
  cases region with
  | shape => exact List.Mem.head _
  | initial => exact List.Mem.tail _ (List.Mem.head _)
  | control => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  | preservation => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  | accepting => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

private theorem tag_mem (region : Region) : tagNode (regionTag region) ∈ graph.nodes := by
  cases region with
  | shape => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
  | initial => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
  | control => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
  | preservation => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
  | accepting => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

private theorem selector_good (offset : Nat) : Good (BuilderRegionResidualOperands.machine offset) :=
  ⟨BuilderRegionResidualOperands.rules_pairwise_query_distinct offset,
   BuilderRegionResidualOperands.noRuleAtAccept offset,
   BuilderRegionResidualOperands.noRuleAtReject offset,
   BuilderRegionResidualOperands.acceptState_ne_rejectState offset⟩

private theorem tag_good (tag : Nat) : Good (Tag.machine tag) :=
  ⟨Tag.rules_pairwise_query_distinct tag, Tag.noRuleAtAccept tag,
   Tag.noRuleAtReject tag, Tag.acceptState_ne_rejectState tag⟩

theorem graph_wellFormed : graph.WellFormed := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact selector_good 0
    · exact selector_good 5
    · exact selector_good 10
    · exact selector_good 15
    · exact selector_good 20
    · exact tag_good 0
    · exact tag_good 1
    · exact tag_good 2
    · exact tag_good 3
    · exact tag_good 4
  · exact ⟨shapeNode, node_mem .shape, rfl, rfl⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨tagNode 0, tag_mem .shape, rfl, rfl⟩,
        ⟨initialNode, node_mem .initial, rfl, rfl⟩⟩
    · exact ⟨⟨tagNode 1, tag_mem .initial, rfl, rfl⟩,
        ⟨controlNode, node_mem .control, rfl, rfl⟩⟩
    · exact ⟨⟨tagNode 2, tag_mem .control, rfl, rfl⟩,
        ⟨preservationNode, node_mem .preservation, rfl, rfl⟩⟩
    · exact ⟨⟨tagNode 3, tag_mem .preservation, rfl, rfl⟩,
        ⟨acceptingNode, node_mem .accepting, rfl, rfl⟩⟩
    · exact ⟨⟨tagNode 4, tag_mem .accepting, rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨True.intro, True.intro⟩

theorem rules_length : machine.rules.length = 5080 := by
  change (WorkMachineProgramGraph.rules graph).length = _
  rw [WorkMachineProgramGraph.rules_length]
  simp only [graph, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    shapeNode, initialNode, controlNode, preservationNode, acceptingNode, tagNode,
    BuilderRegionResidualOperands.rules_length, Tag.rules_length]
  rfl

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise graph graph_wellFormed

theorem noRuleAtAccept : WorkMachineChain.NoRuleAtAccept machine :=
  WorkMachineProgramGraph.noRuleAt_globalAccept graph

theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  WorkMachineProgramGraph.noRuleAt_globalReject graph

theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := by decide

/-- Arbitrary data lengths; the canonical source fixes the accepting length to one. -/
structure Lengths where
  shape : Nat
  initial : Nat
  control : Nat
  preservation : Nat
  accepting : Nat
deriving DecidableEq, Repr

def boundary (lengths : Lengths) : Region → Nat
  | .shape => lengths.shape
  | .initial => lengths.initial
  | .control => lengths.control
  | .preservation => lengths.preservation
  | .accepting => lengths.accepting

def frame (lengths : Lengths) : List Nat :=
  [lengths.accepting, lengths.preservation, lengths.control, lengths.initial, lengths.shape]

def total (lengths : Lengths) : Nat :=
  lengths.shape + lengths.initial + lengths.control + lengths.preservation + lengths.accepting

def remaining (lengths : Lengths) (coordinate : Nat) : Region → Nat
  | .shape => coordinate
  | .initial => coordinate - lengths.shape
  | .control => coordinate - lengths.shape - lengths.initial
  | .preservation => coordinate - lengths.shape - lengths.initial - lengths.control
  | .accepting => coordinate - lengths.shape - lengths.initial - lengths.control - lengths.preservation

def restored (coordinate boundary : Nat) : List Nat :=
  BuilderRegionResidualRegisters.restoredValues
    (BuilderRegionResidualRegisters.ofComparison (RawRouter.compareResult 0 coordinate boundary))

theorem restored_length (coordinate boundary : Nat) : (restored coordinate boundary).length = 3 := rfl

def extendNewer (boundary : Nat) (newer : List Nat) (coordinate : Nat) : List Nat :=
  [boundary] ++ newer ++ [coordinate] ++ restored coordinate boundary

private def newerInitial (lengths : Lengths) (coordinate : Nat) : List Nat :=
  extendNewer lengths.shape [] coordinate

private def newerControl (lengths : Lengths) (coordinate : Nat) : List Nat :=
  extendNewer lengths.initial (newerInitial lengths coordinate) (remaining lengths coordinate .initial)

private def newerPreservation (lengths : Lengths) (coordinate : Nat) : List Nat :=
  extendNewer lengths.control (newerControl lengths coordinate) (remaining lengths coordinate .control)

private def newerAccepting (lengths : Lengths) (coordinate : Nat) : List Nat :=
  extendNewer lengths.preservation (newerPreservation lengths coordinate) (remaining lengths coordinate .preservation)

def newerValues (lengths : Lengths) (coordinate : Nat) : Region → List Nat
  | .shape => []
  | .initial => newerInitial lengths coordinate
  | .control => newerControl lengths coordinate
  | .preservation => newerPreservation lengths coordinate
  | .accepting => newerAccepting lengths coordinate

def olderValues (lengths : Lengths) (older : List Nat) : Region → List Nat
  | .shape => older ++ [lengths.accepting, lengths.preservation, lengths.control, lengths.initial]
  | .initial => older ++ [lengths.accepting, lengths.preservation, lengths.control]
  | .control => older ++ [lengths.accepting, lengths.preservation]
  | .preservation => older ++ [lengths.accepting]
  | .accepting => older

def initialValues (lengths : Lengths) (coordinate : Nat) (older : List Nat) : List Nat :=
  older ++ frame lengths ++ [coordinate]

def stageInput (lengths : Lengths) (coordinate : Nat) (older : List Nat) (region : Region) : List Nat :=
  BuilderRegionComparisonOperands.inputValues (olderValues lengths older region)
    (newerValues lengths coordinate region) (remaining lengths coordinate region) (boundary lengths region)

def stageCost (lengths : Lengths) (coordinate : Nat) (region : Region) : Nat :=
  BuilderRegionResidualOperands.workSteps (newerValues lengths coordinate region)
    (remaining lengths coordinate region) (boundary lengths region)

def nextRegion : Region → Option Region
  | .shape => some .initial
  | .initial => some .control
  | .control => some .preservation
  | .preservation => some .accepting
  | .accepting => none

theorem newer_length (lengths : Lengths) (coordinate : Nat) (region : Region) :
    (newerValues lengths coordinate region).length = 5 * regionTag region := by
  cases region <;>
    simp only [newerValues, newerInitial, newerControl, newerPreservation, newerAccepting,
      extendNewer, List.length_append, List.length_cons, List.length_nil, restored_length, regionTag] <;> omega

theorem stageInput_shape (lengths : Lengths) (coordinate : Nat) (older : List Nat) :
    stageInput lengths coordinate older .shape = initialValues lengths coordinate older := by
  simp only [stageInput, BuilderRegionComparisonOperands.inputValues, olderValues, newerValues,
    remaining, boundary, initialValues, frame, List.append_assoc, List.cons_append,
    List.nil_append, List.append_nil]

private theorem node_program (region : Region) :
    (nodeFor region).program = BuilderRegionResidualOperands.machine (5 * regionTag region) := by
  cases region <;> rfl

private theorem node_accept (region : Region) :
    (nodeFor region).onAccept = .node (tagNode (regionTag region)).reference := by
  cases region <;> rfl

private theorem node_reject (region following : Region) (hNext : nextRegion region = some following) :
    (nodeFor region).onReject = .node (nodeFor following).reference := by
  cases region with
  | shape =>
    have h : Region.initial = following := Option.some.inj hNext
    subst following
    rfl
  | initial =>
    have h : Region.control = following := Option.some.inj hNext
    subst following
    rfl
  | control =>
    have h : Region.preservation = following := Option.some.inj hNext
    subst following
    rfl
  | preservation =>
    have h : Region.accepting = following := Option.some.inj hNext
    subst following
    rfl
  | accepting => cases hNext

private theorem next_stage (lengths : Lengths) (coordinate : Nat) (older : List Nat)
    (region following : Region) (hNext : nextRegion region = some following) :
    (stageInput lengths coordinate older region ++
      restored (remaining lengths coordinate region) (boundary lengths region)) ++
        [remaining lengths coordinate region - boundary lengths region] =
      stageInput lengths coordinate older following := by
  cases region with
  | shape =>
    have h : Region.initial = following := Option.some.inj hNext
    subst following
    simp only [stageInput, BuilderRegionComparisonOperands.inputValues, olderValues, newerValues,
      newerInitial, extendNewer, remaining, boundary, List.append_assoc, List.cons_append,
      List.nil_append, List.append_nil]
  | initial =>
    have h : Region.control = following := Option.some.inj hNext
    subst following
    simp only [stageInput, BuilderRegionComparisonOperands.inputValues, olderValues, newerValues,
      newerControl, extendNewer, remaining, boundary, List.append_assoc, List.cons_append,
      List.nil_append]
  | control =>
    have h : Region.preservation = following := Option.some.inj hNext
    subst following
    simp only [stageInput, BuilderRegionComparisonOperands.inputValues, olderValues, newerValues,
      newerPreservation, extendNewer, remaining, boundary, List.append_assoc, List.cons_append,
      List.nil_append]
  | preservation =>
    have h : Region.accepting = following := Option.some.inj hNext
    subst following
    simp only [stageInput, BuilderRegionComparisonOperands.inputValues, olderValues, newerValues,
      newerAccepting, extendNewer, remaining, boundary, List.append_assoc, List.cons_append,
      List.nil_append]
  | accepting => cases hNext

structure Outcome where
  region : Option Region
  values : List Nat
  steps : Nat
deriving Repr

def outcomeEndpoint : Option Region → Endpoint
  | some _ => .accept
  | none => .reject

def acceptedOutcome (lengths : Lengths) (coordinate : Nat) (older : List Nat) (region : Region) : Outcome :=
  { region := some region
    values := (stageInput lengths coordinate older region ++
      restored (remaining lengths coordinate region) (boundary lengths region)) ++
        [remaining lengths coordinate region, regionTag region]
    steps := stageCost lengths coordinate region + 1 + (Tag.steps (regionTag region) + 1) }

def rejectedOutcome (lengths : Lengths) (coordinate : Nat) (older : List Nat) : Outcome :=
  { region := none
    values := (stageInput lengths coordinate older .accepting ++
      restored (remaining lengths coordinate .accepting) lengths.accepting) ++
        [remaining lengths coordinate .accepting - lengths.accepting]
    steps := stageCost lengths coordinate .accepting + 1 }

def prependOutcome (cost : Nat) (outcome : Outcome) : Outcome :=
  { outcome with steps := cost + 1 + outcome.steps }

def acceptingOutcome (lengths : Lengths) (coordinate : Nat) (older : List Nat) : Outcome :=
  if remaining lengths coordinate .accepting < lengths.accepting then
    acceptedOutcome lengths coordinate older .accepting
  else rejectedOutcome lengths coordinate older

def preservationOutcome (lengths : Lengths) (coordinate : Nat) (older : List Nat) : Outcome :=
  if remaining lengths coordinate .preservation < lengths.preservation then
    acceptedOutcome lengths coordinate older .preservation
  else prependOutcome (stageCost lengths coordinate .preservation) (acceptingOutcome lengths coordinate older)

def controlOutcome (lengths : Lengths) (coordinate : Nat) (older : List Nat) : Outcome :=
  if remaining lengths coordinate .control < lengths.control then
    acceptedOutcome lengths coordinate older .control
  else prependOutcome (stageCost lengths coordinate .control) (preservationOutcome lengths coordinate older)

def initialOutcome (lengths : Lengths) (coordinate : Nat) (older : List Nat) : Outcome :=
  if remaining lengths coordinate .initial < lengths.initial then
    acceptedOutcome lengths coordinate older .initial
  else prependOutcome (stageCost lengths coordinate .initial) (controlOutcome lengths coordinate older)

def outcome (lengths : Lengths) (coordinate : Nat) (older : List Nat) : Outcome :=
  if coordinate < lengths.shape then acceptedOutcome lengths coordinate older .shape
  else prependOutcome (stageCost lengths coordinate .shape) (initialOutcome lengths coordinate older)

def workSteps (lengths : Lengths) (coordinate : Nat) : Nat := (outcome lengths coordinate []).steps

def initialConfiguration (lengths : Lengths) (coordinate : Nat) (older : List Nat)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration machine (endTape (initialValues lengths coordinate older) workspace [])

def finalConfiguration (lengths : Lengths) (coordinate : Nat) (older : List Nat)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  let result := outcome lengths coordinate older
  WorkMachineProgramGraph.endpointConfiguration (outcomeEndpoint result.region)
    (endTape result.values workspace [])

private theorem configuration_eq (configuration : WorkConfiguration) (state : Nat) (tape : WorkTape)
    (hState : configuration.state = state) (hTape : configuration.tape = tape) :
    configuration = { state := state, tape := tape } := by
  cases configuration
  cases hState
  cases hTape
  rfl

private theorem local_accept (lengths : Lengths) (coordinate : Nat) (older : List Nat)
    (workspace : List WorkSymbol) (region : Region)
    (hLt : remaining lengths coordinate region < boundary lengths region) :
    LocalAcceptRun (nodeFor region) (stageCost lengths coordinate region)
      (endTape (stageInput lengths coordinate older region) workspace [])
      (endTape ((stageInput lengths coordinate older region ++
        restored (remaining lengths coordinate region) (boundary lengths region)) ++
        [remaining lengths coordinate region]) workspace []) := by
  unfold LocalAcceptRun
  rw [node_program]
  have hRun := BuilderRegionResidualOperands.workRunExact (5 * regionTag region)
    (olderValues lengths older region) (newerValues lengths coordinate region)
    (remaining lengths coordinate region) (boundary lengths region) workspace
    (newer_length lengths coordinate region)
  have hState := (BuilderRegionResidualOperands.final_accept_iff (5 * regionTag region)
    (olderValues lengths older region) (newerValues lengths coordinate region)
    (remaining lengths coordinate region) (boundary lengths region) workspace).2 hLt
  have hTape :
      (BuilderRegionResidualOperands.finalConfiguration (olderValues lengths older region)
        (newerValues lengths coordinate region) (remaining lengths coordinate region)
        (boundary lengths region) workspace).tape =
      endTape ((stageInput lengths coordinate older region ++
        restored (remaining lengths coordinate region) (boundary lengths region)) ++
        [remaining lengths coordinate region]) workspace [] := by
    rw [BuilderRegionResidualOperands.final_tape, BuilderRegionResidualOperands.finalValues_eq,
      if_pos hLt]
    rfl
  rw [configuration_eq _ _ _ hState hTape] at hRun
  exact hRun

private theorem local_reject (lengths : Lengths) (coordinate : Nat) (older : List Nat)
    (workspace : List WorkSymbol) (region : Region)
    (hLe : boundary lengths region ≤ remaining lengths coordinate region) :
    LocalRejectRun (nodeFor region) (stageCost lengths coordinate region)
      (endTape (stageInput lengths coordinate older region) workspace [])
      (endTape ((stageInput lengths coordinate older region ++
        restored (remaining lengths coordinate region) (boundary lengths region)) ++
        [remaining lengths coordinate region - boundary lengths region]) workspace []) := by
  unfold LocalRejectRun
  rw [node_program]
  have hRun := BuilderRegionResidualOperands.workRunExact (5 * regionTag region)
    (olderValues lengths older region) (newerValues lengths coordinate region)
    (remaining lengths coordinate region) (boundary lengths region) workspace
    (newer_length lengths coordinate region)
  have hState := (BuilderRegionResidualOperands.final_reject_iff (5 * regionTag region)
    (olderValues lengths older region) (newerValues lengths coordinate region)
    (remaining lengths coordinate region) (boundary lengths region) workspace).2 hLe
  have hTape :
      (BuilderRegionResidualOperands.finalConfiguration (olderValues lengths older region)
        (newerValues lengths coordinate region) (remaining lengths coordinate region)
        (boundary lengths region) workspace).tape =
      endTape ((stageInput lengths coordinate older region ++
        restored (remaining lengths coordinate region) (boundary lengths region)) ++
        [remaining lengths coordinate region - boundary lengths region]) workspace [] := by
    rw [BuilderRegionResidualOperands.final_tape, BuilderRegionResidualOperands.finalValues_eq,
      if_neg (Nat.not_lt.mpr hLe)]
    rfl
  rw [configuration_eq _ _ _ hState hTape] at hRun
  exact hRun

private def OutcomePath (lengths : Lengths) (coordinate : Nat) (older : List Nat)
    (workspace : List WorkSymbol) (region : Region) (result : Outcome) : Prop :=
  AcceptPath graph (.node (nodeFor region).reference) (outcomeEndpoint result.region) result.steps
    (endTape (stageInput lengths coordinate older region) workspace [])
    (endTape result.values workspace [])

private theorem selected_path (lengths : Lengths) (coordinate : Nat) (older : List Nat)
    (workspace : List WorkSymbol) (region : Region)
    (hLt : remaining lengths coordinate region < boundary lengths region) :
    OutcomePath lengths coordinate older workspace region
      (acceptedOutcome lengths coordinate older region) := by
  have hSelect := local_accept lengths coordinate older workspace region hLt
  have hWrite := Tag.workRunExact (regionTag region)
    ((stageInput lengths coordinate older region ++
      restored (remaining lengths coordinate region) (boundary lengths region)) ++
      [remaining lengths coordinate region]) workspace []
  simp only [List.drop_nil, List.append_assoc, List.cons_append, List.nil_append] at hWrite
  have hTag := AcceptPath.step (tagNode (regionTag region)) .accept (Tag.steps (regionTag region)) 0
    _ _ _ (tag_mem region) hWrite (.terminal .accept _)
  have hTail :
      AcceptPath graph (nodeFor region).onAccept .accept (Tag.steps (regionTag region) + 1)
        (endTape ((stageInput lengths coordinate older region ++
          restored (remaining lengths coordinate region) (boundary lengths region)) ++
          [remaining lengths coordinate region]) workspace [])
        (endTape (acceptedOutcome lengths coordinate older region).values workspace []) := by
    rw [node_accept]
    simpa only [Nat.add_zero, acceptedOutcome, List.append_assoc, List.cons_append, List.nil_append] using hTag
  exact AcceptPath.step (nodeFor region) .accept (stageCost lengths coordinate region)
    (Tag.steps (regionTag region) + 1) _ _ _ (node_mem region) hSelect hTail

private theorem rejected_prefix (lengths : Lengths) (coordinate : Nat) (older : List Nat)
    (workspace : List WorkSymbol) (region following : Region) (result : Outcome)
    (hNext : nextRegion region = some following)
    (hLe : boundary lengths region ≤ remaining lengths coordinate region)
    (hTail : OutcomePath lengths coordinate older workspace following result) :
    OutcomePath lengths coordinate older workspace region
      (prependOutcome (stageCost lengths coordinate region) result) := by
  have hReject := local_reject lengths coordinate older workspace region hLe
  rw [next_stage lengths coordinate older region following hNext] at hReject
  have hFollow :
      AcceptPath graph (nodeFor region).onReject (outcomeEndpoint result.region) result.steps
        (endTape (stageInput lengths coordinate older following) workspace [])
        (endTape result.values workspace []) := by
    rw [node_reject region following hNext]
    exact hTail
  exact AcceptPath.stepReject (nodeFor region) (outcomeEndpoint result.region)
    (stageCost lengths coordinate region) result.steps _ _ _ (node_mem region) hReject hFollow

private theorem rejected_path (lengths : Lengths) (coordinate : Nat) (older : List Nat)
    (workspace : List WorkSymbol)
    (hLe : lengths.accepting ≤ remaining lengths coordinate .accepting) :
    OutcomePath lengths coordinate older workspace .accepting (rejectedOutcome lengths coordinate older) := by
  have hReject := local_reject lengths coordinate older workspace .accepting hLe
  have hPath := AcceptPath.stepReject acceptingNode .reject (stageCost lengths coordinate .accepting) 0
    _ _ _ (node_mem .accepting) hReject (.terminal .reject _)
  simpa only [OutcomePath, rejectedOutcome, outcomeEndpoint, Nat.add_zero, nodeFor, boundary] using hPath

private theorem accepting_path (lengths : Lengths) (coordinate : Nat) (older : List Nat)
    (workspace : List WorkSymbol) :
    OutcomePath lengths coordinate older workspace .accepting (acceptingOutcome lengths coordinate older) := by
  unfold acceptingOutcome
  split
  · exact selected_path lengths coordinate older workspace .accepting ‹_›
  · exact rejected_path lengths coordinate older workspace (Nat.le_of_not_gt ‹_›)

private theorem preservation_path (lengths : Lengths) (coordinate : Nat) (older : List Nat)
    (workspace : List WorkSymbol) :
    OutcomePath lengths coordinate older workspace .preservation (preservationOutcome lengths coordinate older) := by
  unfold preservationOutcome
  split
  · exact selected_path lengths coordinate older workspace .preservation ‹_›
  · exact rejected_prefix lengths coordinate older workspace .preservation .accepting _ rfl
      (Nat.le_of_not_gt ‹_›) (accepting_path lengths coordinate older workspace)

private theorem control_path (lengths : Lengths) (coordinate : Nat) (older : List Nat)
    (workspace : List WorkSymbol) :
    OutcomePath lengths coordinate older workspace .control (controlOutcome lengths coordinate older) := by
  unfold controlOutcome
  split
  · exact selected_path lengths coordinate older workspace .control ‹_›
  · exact rejected_prefix lengths coordinate older workspace .control .preservation _ rfl
      (Nat.le_of_not_gt ‹_›) (preservation_path lengths coordinate older workspace)

private theorem initial_path (lengths : Lengths) (coordinate : Nat) (older : List Nat)
    (workspace : List WorkSymbol) :
    OutcomePath lengths coordinate older workspace .initial (initialOutcome lengths coordinate older) := by
  unfold initialOutcome
  split
  · exact selected_path lengths coordinate older workspace .initial ‹_›
  · exact rejected_prefix lengths coordinate older workspace .initial .control _ rfl
      (Nat.le_of_not_gt ‹_›) (control_path lengths coordinate older workspace)

private theorem outcome_path (lengths : Lengths) (coordinate : Nat) (older : List Nat)
    (workspace : List WorkSymbol) :
    OutcomePath lengths coordinate older workspace .shape (outcome lengths coordinate older) := by
  unfold outcome
  split
  · exact selected_path lengths coordinate older workspace .shape ‹_›
  · exact rejected_prefix lengths coordinate older workspace .shape .initial _ rfl
      (Nat.le_of_not_gt ‹_›) (initial_path lengths coordinate older workspace)

theorem outcome_steps_eq (lengths : Lengths) (coordinate : Nat) (older : List Nat) :
    (outcome lengths coordinate older).steps = workSteps lengths coordinate := by
  unfold workSteps outcome
  split
  · rfl
  · unfold initialOutcome
    split
    · rfl
    · unfold controlOutcome
      split
      · rfl
      · unfold preservationOutcome
        split
        · rfl
        · unfold acceptingOutcome
          split <;> rfl

private theorem initialEndpoint_eq (tape : WorkTape) :
    WorkMachineProgramGraph.endpointConfiguration (.node (nodeFor .shape).reference) tape =
      workStartConfiguration machine tape := rfl

theorem workRunExact (lengths : Lengths) (coordinate : Nat) (older : List Nat) (workspace : List WorkSymbol) :
    workRunExact? machine (workSteps lengths coordinate)
      (initialConfiguration lengths coordinate older workspace) =
      some (finalConfiguration lengths coordinate older workspace) := by
  have hPath := outcome_path lengths coordinate older workspace
  have hRun := WorkMachineProgramPath.runExact graph _ _ _ _ _ graph_wellFormed hPath
  rw [outcome_steps_eq, stageInput_shape, initialEndpoint_eq] at hRun
  exact hRun

theorem run_compile_exact (lengths : Lengths) (coordinate : Nat) (older : List Nat) (workspace : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps lengths coordinate)
      (encodeWorkConfiguration (initialConfiguration lengths coordinate older workspace)) =
      encodeWorkConfiguration (finalConfiguration lengths coordinate older workspace) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact lengths coordinate older workspace)

def selectedRegion (lengths : Lengths) (coordinate : Nat) : Option Region :=
  if coordinate < lengths.shape then some .shape
  else if remaining lengths coordinate .initial < lengths.initial then some .initial
  else if remaining lengths coordinate .control < lengths.control then some .control
  else if remaining lengths coordinate .preservation < lengths.preservation then some .preservation
  else if remaining lengths coordinate .accepting < lengths.accepting then some .accepting
  else none

theorem outcome_region_eq (lengths : Lengths) (coordinate : Nat) (older : List Nat) :
    (outcome lengths coordinate older).region = selectedRegion lengths coordinate := by
  unfold outcome selectedRegion
  split
  · rfl
  · unfold initialOutcome
    split
    · rfl
    · unfold controlOutcome
      split
      · rfl
      · unfold preservationOutcome
        split
        · rfl
        · unfold acceptingOutcome
          split <;> rfl

theorem outcome_values_eq (lengths : Lengths) (coordinate : Nat) (older : List Nat) :
    (outcome lengths coordinate older).values =
      match selectedRegion lengths coordinate with
      | some region => (acceptedOutcome lengths coordinate older region).values
      | none => (rejectedOutcome lengths coordinate older).values := by
  unfold outcome selectedRegion
  split
  · rfl
  · unfold initialOutcome
    split
    · rfl
    · unfold controlOutcome
      split
      · rfl
      · unfold preservationOutcome
        split
        · rfl
        · unfold acceptingOutcome
          split <;> rfl

theorem selectedRegion_local_valid (lengths : Lengths) (coordinate : Nat) (region : Region)
    (hRegion : selectedRegion lengths coordinate = some region) :
    remaining lengths coordinate region < boundary lengths region := by
  unfold selectedRegion at hRegion
  split at hRegion
  · cases Option.some.inj hRegion
    exact ‹coordinate < lengths.shape›
  · split at hRegion
    · cases Option.some.inj hRegion
      exact ‹remaining lengths coordinate .initial < lengths.initial›
    · split at hRegion
      · cases Option.some.inj hRegion
        exact ‹remaining lengths coordinate .control < lengths.control›
      · split at hRegion
        · cases Option.some.inj hRegion
          exact ‹remaining lengths coordinate .preservation < lengths.preservation›
        · split at hRegion
          · cases Option.some.inj hRegion
            exact ‹remaining lengths coordinate .accepting < lengths.accepting›
          · cases hRegion

theorem selectedRegion_none_iff (lengths : Lengths) (coordinate : Nat) :
    selectedRegion lengths coordinate = none ↔ total lengths ≤ coordinate := by
  unfold selectedRegion
  split
  · constructor
    · intro h; cases h
    · intro h
      unfold total at h
      omega
  · split
    · constructor
      · intro h; cases h
      · intro h
        simp only [remaining, total] at *
        omega
    · split
      · constructor
        · intro h; cases h
        · intro h
          simp only [remaining, total] at *
          omega
      · split
        · constructor
          · intro h; cases h
          · intro h
            simp only [remaining, total] at *
            omega
        · split
          · constructor
            · intro h; cases h
            · intro h
              simp only [remaining, total] at *
              omega
          · constructor
            · intro _
              simp only [remaining, total] at *
              omega
            · intro _; rfl

theorem selectedRegion_some_lt (lengths : Lengths) (coordinate : Nat) (region : Region)
    (hRegion : selectedRegion lengths coordinate = some region) :
    coordinate < total lengths := by
  apply Nat.lt_of_not_ge
  intro hLe
  have hNone := (selectedRegion_none_iff lengths coordinate).2 hLe
  rw [hRegion] at hNone
  cases hNone

theorem final_state_eq (lengths : Lengths) (coordinate : Nat) (older : List Nat) (workspace : List WorkSymbol) :
    (finalConfiguration lengths coordinate older workspace).state =
      match selectedRegion lengths coordinate with
      | some _ => machine.acceptState
      | none => machine.rejectState := by
  dsimp only [finalConfiguration, WorkMachineProgramGraph.endpointConfiguration]
  rw [outcome_region_eq]
  cases selectedRegion lengths coordinate <;> rfl

theorem final_accept_iff (lengths : Lengths) (coordinate : Nat) (older : List Nat) (workspace : List WorkSymbol) :
    (finalConfiguration lengths coordinate older workspace).state = machine.acceptState ↔
      coordinate < total lengths := by
  rw [final_state_eq]
  cases hRegion : selectedRegion lengths coordinate with
  | none =>
    have hLe := (selectedRegion_none_iff lengths coordinate).1 hRegion
    constructor
    · intro h; exact False.elim (acceptState_ne_rejectState h.symm)
    · intro h; omega
  | some region =>
    constructor
    · intro _; exact selectedRegion_some_lt lengths coordinate region hRegion
    · intro _; rfl

theorem final_reject_iff (lengths : Lengths) (coordinate : Nat) (older : List Nat) (workspace : List WorkSymbol) :
    (finalConfiguration lengths coordinate older workspace).state = machine.rejectState ↔
      total lengths ≤ coordinate := by
  rw [final_state_eq]
  cases hRegion : selectedRegion lengths coordinate with
  | none =>
    constructor
    · intro _; exact (selectedRegion_none_iff lengths coordinate).1 hRegion
    · intro _; rfl
  | some region =>
    have hLt := selectedRegion_some_lt lengths coordinate region hRegion
    constructor
    · intro h; exact False.elim (acceptState_ne_rejectState h)
    · intro h; omega

theorem final_tape (lengths : Lengths) (coordinate : Nat) (older : List Nat) (workspace : List WorkSymbol) :
    (finalConfiguration lengths coordinate older workspace).tape =
      endTape (outcome lengths coordinate older).values workspace [] := rfl

/-- Both the local coordinate and region tag are physically written by the machine. -/
theorem final_selected_tape (lengths : Lengths) (coordinate : Nat) (older : List Nat)
    (workspace : List WorkSymbol) (region : Region)
    (hRegion : selectedRegion lengths coordinate = some region) :
    (finalConfiguration lengths coordinate older workspace).tape =
      endTape ((stageInput lengths coordinate older region ++
        restored (remaining lengths coordinate region) (boundary lengths region)) ++
        [remaining lengths coordinate region, regionTag region]) workspace [] := by
  rw [final_tape, outcome_values_eq, hRegion]
  rfl

def rejectScratch (lengths : Lengths) (coordinate : Nat) (region : Region) : List Nat :=
  restored (remaining lengths coordinate region) (boundary lengths region) ++
    [remaining lengths coordinate region - boundary lengths region]

def prefixScratch (lengths : Lengths) (coordinate : Nat) : Region → List Nat
  | .shape => []
  | .initial => rejectScratch lengths coordinate .shape
  | .control => rejectScratch lengths coordinate .shape ++ rejectScratch lengths coordinate .initial
  | .preservation => rejectScratch lengths coordinate .shape ++ rejectScratch lengths coordinate .initial ++
      rejectScratch lengths coordinate .control
  | .accepting => rejectScratch lengths coordinate .shape ++ rejectScratch lengths coordinate .initial ++
      rejectScratch lengths coordinate .control ++ rejectScratch lengths coordinate .preservation

theorem stageInput_preserves_frame (lengths : Lengths) (coordinate : Nat) (older : List Nat) (region : Region) :
    stageInput lengths coordinate older region =
      initialValues lengths coordinate older ++ prefixScratch lengths coordinate region := by
  cases region <;>
    simp only [stageInput, BuilderRegionComparisonOperands.inputValues, olderValues, newerValues,
      newerInitial, newerControl, newerPreservation, newerAccepting, extendNewer,
      remaining, boundary, initialValues, frame, prefixScratch, rejectScratch,
      List.append_assoc, List.cons_append, List.nil_append, List.append_nil]

theorem final_selected_preserves_frame (lengths : Lengths) (coordinate : Nat) (older : List Nat)
    (workspace : List WorkSymbol) (region : Region)
    (hRegion : selectedRegion lengths coordinate = some region) :
    (finalConfiguration lengths coordinate older workspace).tape =
      endTape (initialValues lengths coordinate older ++
        (prefixScratch lengths coordinate region ++
          restored (remaining lengths coordinate region) (boundary lengths region) ++
          [remaining lengths coordinate region, regionTag region])) workspace [] := by
  rw [final_selected_tape lengths coordinate older workspace region hRegion, stageInput_preserves_frame]
  simp only [List.append_assoc]

theorem final_outer_empty (lengths : Lengths) (coordinate : Nat) (older : List Nat) (workspace : List WorkSymbol) :
    (finalConfiguration lengths coordinate older workspace).tape.left = [] := rfl

theorem remaining_le (lengths : Lengths) (coordinate : Nat) (region : Region) :
    remaining lengths coordinate region ≤ coordinate := by
  cases region <;> simp only [remaining] <;> omega

private theorem restored_size_le (coordinate boundary bound : Nat)
    (hCoordinate : coordinate ≤ bound) (hBoundary : boundary ≤ bound) :
    (restored coordinate boundary).length + (restored coordinate boundary).sum ≤ 3 + 4 * bound := by
  have h := BuilderRegionResidualOperands.scratch_size_le coordinate boundary bound hCoordinate hBoundary
  have hValues : BuilderRegionResidualSelection.scratchValues (RawRouter.compareResult 0 coordinate boundary) =
      restored coordinate boundary ++ [BuilderRegionResidualSelection.nextCoordinate coordinate boundary] := rfl
  simp only [hValues, List.length_append, List.length_cons, List.length_nil, restored_length,
    List.sum_append, List.sum_cons, List.sum_nil] at h
  rw [restored_length]
  omega

private theorem extendNewer_size_le (newer : List Nat) (coordinate boundary bound : Nat)
    (hCoordinate : coordinate ≤ bound) (hBoundary : boundary ≤ bound) :
    (extendNewer boundary newer coordinate).length + (extendNewer boundary newer coordinate).sum ≤
      newer.length + newer.sum + 5 + 6 * bound := by
  have h := restored_size_le coordinate boundary bound hCoordinate hBoundary
  simp only [extendNewer, List.length_append, List.length_cons, List.length_nil,
    List.sum_append, List.sum_cons, List.sum_nil]
  omega

/-- Four previous rejections add bounded scratch; this is not a control-table parameter. -/
theorem newer_size_le (lengths : Lengths) (coordinate bound : Nat) (region : Region)
    (hCoordinate : coordinate ≤ bound) (hBoundary : ∀ region, boundary lengths region ≤ bound) :
    (newerValues lengths coordinate region).length + (newerValues lengths coordinate region).sum ≤
      24 * bound + 20 := by
  have hInitial := extendNewer_size_le [] coordinate lengths.shape bound hCoordinate (hBoundary .shape)
  change (newerInitial lengths coordinate).length + (newerInitial lengths coordinate).sum ≤
    0 + 0 + 5 + 6 * bound at hInitial
  have hControl := extendNewer_size_le (newerInitial lengths coordinate)
    (remaining lengths coordinate .initial) lengths.initial bound
    (Nat.le_trans (remaining_le lengths coordinate .initial) hCoordinate) (hBoundary .initial)
  change (newerControl lengths coordinate).length + (newerControl lengths coordinate).sum ≤
    (newerInitial lengths coordinate).length + (newerInitial lengths coordinate).sum + 5 + 6 * bound at hControl
  have hPreservation := extendNewer_size_le (newerControl lengths coordinate)
    (remaining lengths coordinate .control) lengths.control bound
    (Nat.le_trans (remaining_le lengths coordinate .control) hCoordinate) (hBoundary .control)
  change (newerPreservation lengths coordinate).length + (newerPreservation lengths coordinate).sum ≤
    (newerControl lengths coordinate).length + (newerControl lengths coordinate).sum + 5 + 6 * bound at hPreservation
  have hAccepting := extendNewer_size_le (newerPreservation lengths coordinate)
    (remaining lengths coordinate .preservation) lengths.preservation bound
    (Nat.le_trans (remaining_le lengths coordinate .preservation) hCoordinate) (hBoundary .preservation)
  change (newerAccepting lengths coordinate).length + (newerAccepting lengths coordinate).sum ≤
    (newerPreservation lengths coordinate).length + (newerPreservation lengths coordinate).sum + 5 + 6 * bound at hAccepting
  cases region <;> simp only [newerValues, List.length_nil, List.sum_nil] <;> omega

private theorem stageCost_le (lengths : Lengths) (coordinate bound : Nat) (region : Region)
    (hCoordinate : coordinate ≤ bound) (hBoundary : ∀ region, boundary lengths region ≤ bound) :
    stageCost lengths coordinate region ≤ BuilderRegionResidualOperands.workBound (24 * bound + 20) := by
  have hCoordinate' := Nat.le_trans (remaining_le lengths coordinate region) hCoordinate
  have hBoundary' := hBoundary region
  exact BuilderRegionResidualOperands.workSteps_le _ _ _ _
    (by omega) (by omega) (newer_size_le lengths coordinate bound region hCoordinate hBoundary)

/-- At most five selectors/bridges and one literal tag/bridge. -/
def workBound (bound : Nat) : Nat := 5 * BuilderRegionResidualOperands.workBound (24 * bound + 20) + 20

theorem workSteps_le (lengths : Lengths) (coordinate bound : Nat)
    (hCoordinate : coordinate ≤ bound) (hBoundary : ∀ region, boundary lengths region ≤ bound) :
    workSteps lengths coordinate ≤ workBound bound := by
  have hShape := stageCost_le lengths coordinate bound .shape hCoordinate hBoundary
  have hInitial := stageCost_le lengths coordinate bound .initial hCoordinate hBoundary
  have hControl := stageCost_le lengths coordinate bound .control hCoordinate hBoundary
  have hPreservation := stageCost_le lengths coordinate bound .preservation hCoordinate hBoundary
  have hAccepting := stageCost_le lengths coordinate bound .accepting hCoordinate hBoundary
  unfold workBound workSteps outcome
  split
  · simp only [acceptedOutcome, Tag.steps, regionTag]
    omega
  · unfold initialOutcome
    split
    · simp only [prependOutcome, acceptedOutcome, Tag.steps, regionTag]
      omega
    · unfold controlOutcome
      split
      · simp only [prependOutcome, acceptedOutcome, Tag.steps, regionTag]
        omega
      · unfold preservationOutcome
        split
        · simp only [prependOutcome, acceptedOutcome, Tag.steps, regionTag]
          omega
        · unfold acceptingOutcome
          split <;> simp only [prependOutcome, acceptedOutcome, rejectedOutcome, Tag.steps, regionTag] <;> omega

def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.mul (.constant 5)
    (BuilderRegionResidualOperands.rawTimePolynomial
      (.add (.mul (.constant 24) bound) (.constant 20)))) (.constant 120)

theorem rawTimePolynomial_eval (bound : NatPolynomial) (input : Nat) :
    (rawTimePolynomial bound).eval input = 6 * workBound (bound.eval input) := by
  unfold rawTimePolynomial
  simp only [NatPolynomial.eval, BuilderRegionResidualOperands.rawTimePolynomial_eval]
  unfold workBound
  omega

theorem rawTimePolynomial_le (lengths : Lengths) (coordinate input : Nat) (bound : NatPolynomial)
    (hCoordinate : coordinate ≤ bound.eval input)
    (hBoundary : ∀ region, boundary lengths region ≤ bound.eval input) :
    6 * workSteps lengths coordinate ≤ (rawTimePolynomial bound).eval input := by
  rw [rawTimePolynomial_eval]
  exact Nat.mul_le_mul_left 6 (workSteps_le lengths coordinate (bound.eval input) hCoordinate hBoundary)

end PNP.Concrete.CookLevin.BuilderConstraintRegionDispatch
