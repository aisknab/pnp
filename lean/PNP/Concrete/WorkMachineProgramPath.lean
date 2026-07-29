/-
Copyright (c) 2026 PNP Labs.

Exact finite paths through a materialized work-machine program graph.

This module is deliberately independent of any concrete reduction.  A path
stores kernel-checked local executions and follows only the literal successor
endpoints already embedded in the graph.  It performs no runtime node lookup
and supplies no caller certificate to the executable machine.
-/

import PNP.Concrete.WorkMachineProgramGraph

namespace PNP.Concrete.WorkMachineProgramPath

open PNP.Concrete
open WorkMachineProgramGraph
open PipelineStateNamespace

/-- A local node execution begins at that node's declared start state and
ends at its accept endpoint, while exposing only the initial/final tapes. -/
def LocalAcceptRun (node : Node) (steps : Nat)
    (initialTape finalTape : WorkTape) : Prop :=
  workRunExact? node.program steps
      { state := node.program.startState, tape := initialTape } =
    some
      { state := node.program.acceptState, tape := finalTape }

def LocalRejectRun (node : Node) (steps : Nat)
    (initialTape finalTape : WorkTape) : Prop :=
  workRunExact? node.program steps
      { state := node.program.startState, tape := initialTape } =
    some
      { state := node.program.rejectState, tape := finalTape }

/-- A proof-level path through the finite graph.  The executable graph uses
only the compiled bridge destinations; this witness is used solely to compose
the already proved local traces. -/
inductive AcceptPath (graph : Graph) :
    Endpoint → Endpoint → Nat → WorkTape → WorkTape → Prop where
  | terminal (endpoint : Endpoint) (tape : WorkTape) :
      AcceptPath graph endpoint endpoint 0 tape tape
  | step (node : Node) (finalEndpoint : Endpoint)
      (localSteps tailSteps : Nat)
      (initialTape middleTape finalTape : WorkTape)
      (member : node ∈ graph.nodes)
      (localRun :
        LocalAcceptRun node localSteps initialTape middleTape)
      (tail :
        AcceptPath graph node.onAccept finalEndpoint
          tailSteps middleTape finalTape) :
      AcceptPath graph (.node node.reference) finalEndpoint
        (localSteps + 1 + tailSteps) initialTape finalTape
  | stepReject (node : Node) (finalEndpoint : Endpoint)
      (localSteps tailSteps : Nat)
      (initialTape middleTape finalTape : WorkTape)
      (member : node ∈ graph.nodes)
      (localRun :
        LocalRejectRun node localSteps initialTape middleTape)
      (tail :
        AcceptPath graph node.onReject finalEndpoint
          tailSteps middleTape finalTape) :
      AcceptPath graph (.node node.reference) finalEndpoint
        (localSteps + 1 + tailSteps) initialTape finalTape

theorem terminal_steps
    (graph : Graph) (endpoint : Endpoint) (tape : WorkTape) :
  AcceptPath graph endpoint endpoint 0 tape tape :=
  .terminal endpoint tape

theorem AcceptPath.trans
    (graph : Graph)
    (start middle final : Endpoint)
    (firstSteps secondSteps : Nat)
    (initialTape middleTape finalTape : WorkTape)
    (first :
      AcceptPath graph start middle firstSteps
        initialTape middleTape)
    (second :
      AcceptPath graph middle final secondSteps
        middleTape finalTape) :
    AcceptPath graph start final (firstSteps + secondSteps)
      initialTape finalTape := by
  induction first with
  | terminal endpoint tape =>
      simpa using second
  | @step node middleEndpoint localSteps tailSteps
      firstTape nextTape middleTape member localRun tail
      inductionHypothesis =>
      have combinedTail :=
        inductionHypothesis second
      have prefixed :=
        AcceptPath.step node final localSteps
          (tailSteps + secondSteps)
          firstTape nextTape finalTape
          member localRun combinedTail
      simpa [Nat.add_assoc] using prefixed
  | @stepReject node middleEndpoint localSteps tailSteps
      firstTape nextTape middleTape member localRun tail
      inductionHypothesis =>
      have combinedTail :=
        inductionHypothesis second
      have prefixed :=
        AcceptPath.stepReject node final localSteps
          (tailSteps + secondSteps)
          firstTape nextTape finalTape
          member localRun combinedTail
      simpa [Nat.add_assoc] using prefixed

/-- Every proof-level accept path is an exact execution of the one fixed
materialized graph machine. -/
theorem runExact
    (graph : Graph) (startEndpoint finalEndpoint : Endpoint)
    (steps : Nat) (initialTape finalTape : WorkTape)
    (wellFormed : graph.WellFormed)
    (path :
      AcceptPath graph startEndpoint finalEndpoint
        steps initialTape finalTape) :
    workRunExact? (machine graph) steps
        (endpointConfiguration startEndpoint initialTape) =
      some (endpointConfiguration finalEndpoint finalTape) := by
  induction path with
  | terminal endpoint tape =>
      rfl
  | @step node finalEndpoint localSteps tailSteps
      initialTape middleTape finalTape member localRun tail ih =>
      have localRunGlobal :
          workRunExact? (machine graph) (localSteps + 1)
              (endpointConfiguration
                (.node node.reference) initialTape) =
            some
              (endpointConfiguration node.onAccept middleTape) := by
        have transported :=
          local_then_accept graph node localSteps
            { state := node.program.startState,
              tape := initialTape }
            { state := node.program.acceptState,
              tape := middleTape }
            wellFormed member localRun rfl
        simpa [endpointConfiguration, endpointState,
          Node.reference, Node.encode, renameConfiguration] using
            transported
      exact PipelineMachineSimulation.workRunExact?_compose
        (machine graph) (localSteps + 1) tailSteps
        (endpointConfiguration (.node node.reference) initialTape)
        (endpointConfiguration node.onAccept middleTape)
        (endpointConfiguration finalEndpoint finalTape)
        localRunGlobal ih
  | @stepReject node finalEndpoint localSteps tailSteps
      initialTape middleTape finalTape member localRun tail ih =>
      have localRunGlobal :
          workRunExact? (machine graph) (localSteps + 1)
              (endpointConfiguration
                (.node node.reference) initialTape) =
            some
              (endpointConfiguration node.onReject middleTape) := by
        have transported :=
          local_then_reject graph node localSteps
            { state := node.program.startState,
              tape := initialTape }
            { state := node.program.rejectState,
              tape := middleTape }
            wellFormed member localRun rfl
        simpa [endpointConfiguration, endpointState,
          Node.reference, Node.encode, renameConfiguration] using
            transported
      exact PipelineMachineSimulation.workRunExact?_compose
        (machine graph) (localSteps + 1) tailSteps
        (endpointConfiguration (.node node.reference) initialTape)
        (endpointConfiguration node.onReject middleTape)
        (endpointConfiguration finalEndpoint finalTape)
        localRunGlobal ih

theorem runEntryToAccept
    (graph : Graph) (steps : Nat)
    (initialTape finalTape : WorkTape)
    (wellFormed : graph.WellFormed)
    (path :
      AcceptPath graph (.node graph.entry) .accept
        steps initialTape finalTape) :
    workRunExact? (machine graph) steps
        { state := (machine graph).startState, tape := initialTape } =
      some
        { state := (machine graph).acceptState, tape := finalTape } := by
  simpa [machine, endpointConfiguration, endpointState] using
    runExact graph (.node graph.entry) .accept
      steps initialTape finalTape wellFormed path

theorem runEntryToReject
    (graph : Graph) (steps : Nat)
    (initialTape finalTape : WorkTape)
    (wellFormed : graph.WellFormed)
    (path :
      AcceptPath graph (.node graph.entry) .reject
        steps initialTape finalTape) :
    workRunExact? (machine graph) steps
        { state := (machine graph).startState, tape := initialTape } =
      some
        { state := (machine graph).rejectState, tape := finalTape } := by
  simpa [machine, endpointConfiguration, endpointState] using
    runExact graph (.node graph.entry) .reject
      steps initialTape finalTape wellFormed path

end PNP.Concrete.WorkMachineProgramPath
