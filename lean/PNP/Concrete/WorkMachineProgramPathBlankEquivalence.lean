/-
Copyright (c) 2026 PNP Labs.

Blank-tail transport for exact paths through a materialized work-machine
program graph.
-/

import PNP.Concrete.WorkMachineProgramPath
import PNP.Concrete.WorkMachineBlankEquivalence

namespace PNP.Concrete.WorkMachineProgramPath

open PNP.Concrete
open WorkMachineProgramGraph

private theorem localAcceptRun_transport
    (node : Node) (steps : Nat)
    (canonicalInitial canonicalFinal actualInitial : WorkTape)
    (run :
      LocalAcceptRun node steps canonicalInitial canonicalFinal)
    (equivalent :
      WorkTape.BlankEquivalent actualInitial canonicalInitial) :
    ∃ actualFinal,
      LocalAcceptRun node steps actualInitial actualFinal ∧
      WorkTape.BlankEquivalent actualFinal canonicalFinal := by
  have configurationEquivalent :
      WorkConfiguration.BlankEquivalent
        { state := node.program.startState, tape := actualInitial }
        { state := node.program.startState, tape := canonicalInitial } :=
    ⟨rfl, equivalent⟩
  rcases
      workRunExact?_transport node.program steps
        configurationEquivalent run with
    ⟨actualFinal, actualRun, finalEquivalent⟩
  have stateEq :
      actualFinal.state = node.program.acceptState :=
    finalEquivalent.state
  rcases actualFinal with ⟨actualState, actualTape⟩
  simp only at stateEq
  subst actualState
  exact ⟨actualTape, actualRun, finalEquivalent.tape⟩

private theorem localRejectRun_transport
    (node : Node) (steps : Nat)
    (canonicalInitial canonicalFinal actualInitial : WorkTape)
    (run :
      LocalRejectRun node steps canonicalInitial canonicalFinal)
    (equivalent :
      WorkTape.BlankEquivalent actualInitial canonicalInitial) :
    ∃ actualFinal,
      LocalRejectRun node steps actualInitial actualFinal ∧
      WorkTape.BlankEquivalent actualFinal canonicalFinal := by
  have configurationEquivalent :
      WorkConfiguration.BlankEquivalent
        { state := node.program.startState, tape := actualInitial }
        { state := node.program.startState, tape := canonicalInitial } :=
    ⟨rfl, equivalent⟩
  rcases
      workRunExact?_transport node.program steps
        configurationEquivalent run with
    ⟨actualFinal, actualRun, finalEquivalent⟩
  have stateEq :
      actualFinal.state = node.program.rejectState :=
    finalEquivalent.state
  rcases actualFinal with ⟨actualState, actualTape⟩
  simp only at stateEq
  subst actualState
  exact ⟨actualTape, actualRun, finalEquivalent.tape⟩

/-- Transport a proof-level graph path from its canonical finite tape window
to any tape denoting the same infinite blank tape.  The endpoint window is
existential, while the graph endpoints and exact step count are retained. -/
theorem AcceptPath.transport
    {graph : Graph} {start final : Endpoint} {steps : Nat}
    {canonicalInitial canonicalFinal actualInitial : WorkTape}
    (path :
      AcceptPath graph start final steps
        canonicalInitial canonicalFinal)
    (equivalent :
      WorkTape.BlankEquivalent actualInitial canonicalInitial) :
    ∃ actualFinal,
      AcceptPath graph start final steps
        actualInitial actualFinal ∧
      WorkTape.BlankEquivalent actualFinal canonicalFinal := by
  induction path generalizing actualInitial with
  | terminal endpoint tape =>
      exact
        ⟨actualInitial, AcceptPath.terminal endpoint actualInitial,
          equivalent⟩
  | @step node finalEndpoint localSteps tailSteps
      initialTape middleTape finalTape member localRun tail
      inductionHypothesis =>
      rcases
          localAcceptRun_transport node localSteps
            initialTape middleTape actualInitial localRun equivalent with
        ⟨actualMiddle, actualLocalRun, middleEquivalent⟩
      rcases inductionHypothesis middleEquivalent with
        ⟨actualFinal, actualTail, finalEquivalent⟩
      exact
        ⟨actualFinal,
          AcceptPath.step node finalEndpoint localSteps tailSteps
            actualInitial actualMiddle actualFinal member
            actualLocalRun actualTail,
          finalEquivalent⟩
  | @stepReject node finalEndpoint localSteps tailSteps
      initialTape middleTape finalTape member localRun tail
      inductionHypothesis =>
      rcases
          localRejectRun_transport node localSteps
            initialTape middleTape actualInitial localRun equivalent with
        ⟨actualMiddle, actualLocalRun, middleEquivalent⟩
      rcases inductionHypothesis middleEquivalent with
        ⟨actualFinal, actualTail, finalEquivalent⟩
      exact
        ⟨actualFinal,
          AcceptPath.stepReject node finalEndpoint localSteps tailSteps
            actualInitial actualMiddle actualFinal member
            actualLocalRun actualTail,
          finalEquivalent⟩

end PNP.Concrete.WorkMachineProgramPath
