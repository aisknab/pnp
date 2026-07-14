/-
Copyright (c) 2026 PNP Labs.

Uniform sequential composition of two concrete raw machines in one literal
finite rule table.

The first component frames every raw input, simulates the first machine, and
materializes its represented output.  Either designated first-machine halt
then launches the second component directly at its lifted simulator start.
The second component simulates the second machine on that represented output,
hands its result to the terminal packer, and emits ordinary blank-delimited
raw output.  No host-interpreted composition occurs between the two machines.
-/

import PNP.Concrete.PipelineSequentialStateNamespace

namespace PNP.Concrete

namespace PipelineSequentialCompiler

open PipelineStateNamespace PipelineStageBridges PipelineTerminalBridge
  PipelineSequentialStateNamespace

/-! ### Literal machine and exact costs -/

/-- The raw finite machine compiled from the complete sequential work table. -/
def sequentialMachine (first second : Machine) : Machine :=
  compileWorkMachine (sequentialWorkMachine first second)

/-- Work used by the second lifted simulation, its represented handoff, and
its terminal output packer.  Its input framer is deliberately skipped because
the first handoff already supplies a represented ordinary tape. -/
def secondSuffixWorkSteps (secondSteps : Nat) (secondFinalTape : Tape) : Nat :=
  3 * secondSteps + 1 +
    PipelineOutputHandoff.framedOutputHandoffWorkSteps secondFinalTape +
      terminalBridgeWorkSteps secondFinalTape.outputBits

/-- Complete exact work cost of both simulations and their literal launch. -/
def sequentialWorkSteps (input : BitString) (firstSteps : Nat)
    (firstFinalTape : Tape) (secondSteps : Nat)
    (secondFinalTape : Tape) : Nat :=
  PipelineCompiler.bridgedWorkSteps input firstSteps firstFinalTape + 1 +
    secondSuffixWorkSteps secondSteps secondFinalTape

/-- Six raw transitions implement every work transition. -/
def sequentialRawSteps (input : BitString) (firstSteps : Nat)
    (firstFinalTape : Tape) (secondSteps : Nat)
    (secondFinalTape : Tape) : Nat :=
  6 * sequentialWorkSteps input firstSteps firstFinalTape secondSteps
    secondFinalTape

/-- Conservative first output length `m + p(m) + 1`. -/
def firstOutputSizeBound (firstBound : NatPolynomial) : NatPolynomial :=
  PipelineCompiler.pipelineOutputSizeBound firstBound

/-- Conservative second output length
`B₁(m) + q(B₁(m)) + 1`, expressed by polynomial substitution. -/
def sequentialOutputSizeBound (firstBound secondBound : NatPolynomial) :
    NatPolynomial :=
  NatPolynomial.substitute
    (PipelineCompiler.pipelineOutputSizeBound secondBound)
    (firstOutputSizeBound firstBound)

/-- External raw-time polynomial for framing, two simulations, two represented
handoffs, the inter-component launch, and terminal packing. -/
def sequentialRawTimeBound (firstBound secondBound : NatPolynomial) :
    NatPolynomial :=
  .add
    (.add (PipelineCompiler.pipelineRawTimeBound firstBound) (.constant 6))
    (NatPolynomial.substitute
      (PipelineCompiler.pipelineRawTimeBound secondBound)
      (firstOutputSizeBound firstBound))

theorem firstOutputSizeBound_eval (firstBound : NatPolynomial)
    (inputSize : Nat) :
    (firstOutputSizeBound firstBound).eval inputSize =
      inputSize + firstBound.eval inputSize + 1 := by
  rfl

theorem sequentialOutputSizeBound_eval
    (firstBound secondBound : NatPolynomial) (inputSize : Nat) :
    (sequentialOutputSizeBound firstBound secondBound).eval inputSize =
      (firstOutputSizeBound firstBound).eval inputSize +
        secondBound.eval ((firstOutputSizeBound firstBound).eval inputSize) +
          1 := by
  unfold sequentialOutputSizeBound
  rw [NatPolynomial.eval_substitute,
    PipelineCompiler.pipelineOutputSizeBound_eval]

/-! ### The second suffix from an arbitrary represented input -/

private theorem controlState_eq_acceptSentinel_of_state_eq_accept
    (machine : Machine) (config : Configuration)
    (hState : config.state = machine.acceptState) :
    PipelineMachineSimulation.controlState machine config.state =
      PipelineMachineSimulation.acceptSentinel := by
  unfold PipelineMachineSimulation.controlState
  rw [if_pos hState]

private theorem controlState_eq_rejectSentinel_of_state_eq_reject
    (machine : Machine) (config : Configuration)
    (hState : config.state = machine.rejectState)
    (hDistinct : machine.rejectState ≠ machine.acceptState) :
    PipelineMachineSimulation.controlState machine config.state =
      PipelineMachineSimulation.rejectSentinel := by
  have hNotAccept : config.state ≠ machine.acceptState := by
    intro hAccept
    exact hDistinct (hState.symm.trans hAccept)
  unfold PipelineMachineSimulation.controlState
  rw [if_neg hNotAccept, if_pos hState]

private theorem workRunExact_one (machine : WorkMachine)
    (start next : WorkConfiguration)
    (hStep : workStep? machine start = some next) :
    workRunExact? machine 1 start = some next := by
  change (match workStep? machine start with
    | none => none
    | some result => some result) = some next
  rw [hStep]

/-- A supplied accepting run of the second raw machine completes from any
work tape representing its ordinary input tape. -/
theorem secondAcceptingSuffix_workRunExact_of_rawRunExact
    (second : Machine) (steps : Nat) (input : BitString)
    (startWorkTape : WorkTape) (final : Configuration)
    (hInput : PipelineTape.Represents (Tape.ofInput input) startWorkTape)
    (hRaw : PipelineMachineSimulation.rawRunExact? second steps
      (startConfig second input) = some final)
    (hAccept : final.state = second.acceptState) :
    ∃ simulatorFinal handoffFinal outsideLeft outsideRight,
      PipelineMachineSimulation.RepresentsConfiguration
          second final simulatorFinal ∧
      PipelineTape.Represents final.tape.handoffTarget handoffFinal ∧
      handoffFinal = TerminalOutputPacker.terminalOutputPackerInputTape
        final.tape.outputBits outsideLeft outsideRight ∧
      workRunExact? (terminalBridgeMachine second)
          (secondSuffixWorkSteps steps final.tape)
          (renameConfiguration simulationState
            (PipelineMachineSimulation.liftConfiguration second
              (startConfig second input) startWorkTape)) =
        some (renameConfiguration acceptingPackerState
          (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
            final.tape.outputBits outsideLeft outsideRight)) := by
  rcases PipelineMachineSimulation.workRunExact_three_mul_of_rawRunExact
      second steps (startConfig second input) final startWorkTape hRaw hInput with
    ⟨simulatorFinal, hSimulationLocal, hFinalRepresents⟩
  have hSimulationBridge := simulation_workRunExact_of_exact second
    (3 * steps)
    (PipelineMachineSimulation.liftConfiguration second
      (startConfig second input) startWorkTape)
    simulatorFinal hSimulationLocal
  have hSimulation := bridged_workRunExact_of_exact second (3 * steps)
    (renameConfiguration simulationState
      (PipelineMachineSimulation.liftConfiguration second
        (startConfig second input) startWorkTape))
    (renameConfiguration simulationState simulatorFinal) hSimulationBridge
  have hControl := controlState_eq_acceptSentinel_of_state_eq_accept
    second final hAccept
  have hSimulatorState : simulatorFinal.state =
      PipelineMachineSimulation.acceptSentinel :=
    hFinalRepresents.1.trans hControl
  have hSimulatorEq : simulatorFinal =
      { state := PipelineMachineSimulation.acceptSentinel,
        tape := simulatorFinal.tape } := by
    cases simulatorFinal with
    | mk state tape =>
        change state = PipelineMachineSimulation.acceptSentinel at hSimulatorState
        cases hSimulatorState
        rfl
  have hLaunchBridge := acceptingLaunch_workStep second simulatorFinal.tape
  have hLaunchStep : workStep? (terminalBridgeMachine second)
      (renameConfiguration simulationState simulatorFinal) =
        some (renameConfiguration acceptingHandoffState
          (workStartConfiguration
            PipelineOutputHandoff.framedOutputHandoff simulatorFinal.tape)) := by
    rw [hSimulatorEq]
    exact bridged_workStep?_of_some second _ _ hLaunchBridge
  have hLaunch := workRunExact_one (terminalBridgeMachine second)
    (renameConfiguration simulationState simulatorFinal)
    (renameConfiguration acceptingHandoffState
      (workStartConfiguration
        PipelineOutputHandoff.framedOutputHandoff simulatorFinal.tape))
    hLaunchStep
  rcases PipelineOutputHandoff.framedOutputHandoff_workRunExact_of_represents
      hFinalRepresents.2 with
    ⟨handoffFinal, hHandoffRepresents, hHandoffLocal⟩
  have hHandoffBridge := acceptingHandoff_workRunExact_of_exact second
    (PipelineOutputHandoff.framedOutputHandoffWorkSteps final.tape)
    (workStartConfiguration PipelineOutputHandoff.framedOutputHandoff
      simulatorFinal.tape)
    (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration handoffFinal)
    hHandoffLocal
  have hHandoff := bridged_workRunExact_of_exact second
    (PipelineOutputHandoff.framedOutputHandoffWorkSteps final.tape)
    (renameConfiguration acceptingHandoffState
      (workStartConfiguration PipelineOutputHandoff.framedOutputHandoff
        simulatorFinal.tape))
    (renameConfiguration acceptingHandoffState
      (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration handoffFinal))
    hHandoffBridge
  have hSimulationAndLaunch := PipelineMachineSimulation.workRunExact?_compose
    (terminalBridgeMachine second) (3 * steps) 1
    (renameConfiguration simulationState
      (PipelineMachineSimulation.liftConfiguration second
        (startConfig second input) startWorkTape))
    (renameConfiguration simulationState simulatorFinal)
    (renameConfiguration acceptingHandoffState
      (workStartConfiguration PipelineOutputHandoff.framedOutputHandoff
        simulatorFinal.tape)) hSimulation hLaunch
  have hBridged := PipelineMachineSimulation.workRunExact?_compose
    (terminalBridgeMachine second) (3 * steps + 1)
    (PipelineOutputHandoff.framedOutputHandoffWorkSteps final.tape)
    (renameConfiguration simulationState
      (PipelineMachineSimulation.liftConfiguration second
        (startConfig second input) startWorkTape))
    (renameConfiguration acceptingHandoffState
      (workStartConfiguration PipelineOutputHandoff.framedOutputHandoff
        simulatorFinal.tape))
    (renameConfiguration acceptingHandoffState
      (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration handoffFinal))
    hSimulationAndLaunch hHandoff
  rcases acceptingTerminal_workRunExact_of_represents second
      hHandoffRepresents with
    ⟨outsideLeft, outsideRight, hPackerInput, hTerminal⟩
  have hComplete := PipelineMachineSimulation.workRunExact?_compose
    (terminalBridgeMachine second)
    (3 * steps + 1 +
      PipelineOutputHandoff.framedOutputHandoffWorkSteps final.tape)
    (terminalBridgeWorkSteps final.tape.outputBits)
    (renameConfiguration simulationState
      (PipelineMachineSimulation.liftConfiguration second
        (startConfig second input) startWorkTape))
    (renameConfiguration acceptingHandoffState
      (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration handoffFinal))
    (renameConfiguration acceptingPackerState
      (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
        final.tape.outputBits outsideLeft outsideRight)) hBridged hTerminal
  exact ⟨simulatorFinal, handoffFinal, outsideLeft, outsideRight,
    hFinalRepresents, hHandoffRepresents, hPackerInput, by
      simpa [secondSuffixWorkSteps] using hComplete⟩

/-- The rejecting second-machine endpoint uses the disjoint rejecting handoff
and packer images, from the same arbitrary represented input. -/
theorem secondRejectingSuffix_workRunExact_of_rawRunExact
    (second : Machine) (steps : Nat) (input : BitString)
    (startWorkTape : WorkTape) (final : Configuration)
    (hDistinct : second.rejectState ≠ second.acceptState)
    (hInput : PipelineTape.Represents (Tape.ofInput input) startWorkTape)
    (hRaw : PipelineMachineSimulation.rawRunExact? second steps
      (startConfig second input) = some final)
    (hReject : final.state = second.rejectState) :
    ∃ simulatorFinal handoffFinal outsideLeft outsideRight,
      PipelineMachineSimulation.RepresentsConfiguration
          second final simulatorFinal ∧
      PipelineTape.Represents final.tape.handoffTarget handoffFinal ∧
      handoffFinal = TerminalOutputPacker.terminalOutputPackerInputTape
        final.tape.outputBits outsideLeft outsideRight ∧
      workRunExact? (terminalBridgeMachine second)
          (secondSuffixWorkSteps steps final.tape)
          (renameConfiguration simulationState
            (PipelineMachineSimulation.liftConfiguration second
              (startConfig second input) startWorkTape)) =
        some (renameConfiguration rejectingPackerState
          (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
            final.tape.outputBits outsideLeft outsideRight)) := by
  rcases PipelineMachineSimulation.workRunExact_three_mul_of_rawRunExact
      second steps (startConfig second input) final startWorkTape hRaw hInput with
    ⟨simulatorFinal, hSimulationLocal, hFinalRepresents⟩
  have hSimulationBridge := simulation_workRunExact_of_exact second
    (3 * steps)
    (PipelineMachineSimulation.liftConfiguration second
      (startConfig second input) startWorkTape)
    simulatorFinal hSimulationLocal
  have hSimulation := bridged_workRunExact_of_exact second (3 * steps)
    (renameConfiguration simulationState
      (PipelineMachineSimulation.liftConfiguration second
        (startConfig second input) startWorkTape))
    (renameConfiguration simulationState simulatorFinal) hSimulationBridge
  have hControl := controlState_eq_rejectSentinel_of_state_eq_reject
    second final hReject hDistinct
  have hSimulatorState : simulatorFinal.state =
      PipelineMachineSimulation.rejectSentinel :=
    hFinalRepresents.1.trans hControl
  have hSimulatorEq : simulatorFinal =
      { state := PipelineMachineSimulation.rejectSentinel,
        tape := simulatorFinal.tape } := by
    cases simulatorFinal with
    | mk state tape =>
        change state = PipelineMachineSimulation.rejectSentinel at hSimulatorState
        cases hSimulatorState
        rfl
  have hLaunchBridge := rejectingLaunch_workStep second simulatorFinal.tape
  have hLaunchStep : workStep? (terminalBridgeMachine second)
      (renameConfiguration simulationState simulatorFinal) =
        some (renameConfiguration rejectingHandoffState
          (workStartConfiguration
            PipelineOutputHandoff.framedOutputHandoff simulatorFinal.tape)) := by
    rw [hSimulatorEq]
    exact bridged_workStep?_of_some second _ _ hLaunchBridge
  have hLaunch := workRunExact_one (terminalBridgeMachine second)
    (renameConfiguration simulationState simulatorFinal)
    (renameConfiguration rejectingHandoffState
      (workStartConfiguration
        PipelineOutputHandoff.framedOutputHandoff simulatorFinal.tape))
    hLaunchStep
  rcases PipelineOutputHandoff.framedOutputHandoff_workRunExact_of_represents
      hFinalRepresents.2 with
    ⟨handoffFinal, hHandoffRepresents, hHandoffLocal⟩
  have hHandoffBridge := rejectingHandoff_workRunExact_of_exact second
    (PipelineOutputHandoff.framedOutputHandoffWorkSteps final.tape)
    (workStartConfiguration PipelineOutputHandoff.framedOutputHandoff
      simulatorFinal.tape)
    (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration handoffFinal)
    hHandoffLocal
  have hHandoff := bridged_workRunExact_of_exact second
    (PipelineOutputHandoff.framedOutputHandoffWorkSteps final.tape)
    (renameConfiguration rejectingHandoffState
      (workStartConfiguration PipelineOutputHandoff.framedOutputHandoff
        simulatorFinal.tape))
    (renameConfiguration rejectingHandoffState
      (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration handoffFinal))
    hHandoffBridge
  have hSimulationAndLaunch := PipelineMachineSimulation.workRunExact?_compose
    (terminalBridgeMachine second) (3 * steps) 1
    (renameConfiguration simulationState
      (PipelineMachineSimulation.liftConfiguration second
        (startConfig second input) startWorkTape))
    (renameConfiguration simulationState simulatorFinal)
    (renameConfiguration rejectingHandoffState
      (workStartConfiguration PipelineOutputHandoff.framedOutputHandoff
        simulatorFinal.tape)) hSimulation hLaunch
  have hBridged := PipelineMachineSimulation.workRunExact?_compose
    (terminalBridgeMachine second) (3 * steps + 1)
    (PipelineOutputHandoff.framedOutputHandoffWorkSteps final.tape)
    (renameConfiguration simulationState
      (PipelineMachineSimulation.liftConfiguration second
        (startConfig second input) startWorkTape))
    (renameConfiguration rejectingHandoffState
      (workStartConfiguration PipelineOutputHandoff.framedOutputHandoff
        simulatorFinal.tape))
    (renameConfiguration rejectingHandoffState
      (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration handoffFinal))
    hSimulationAndLaunch hHandoff
  rcases rejectingTerminal_workRunExact_of_represents second
      hHandoffRepresents with
    ⟨outsideLeft, outsideRight, hPackerInput, hTerminal⟩
  have hComplete := PipelineMachineSimulation.workRunExact?_compose
    (terminalBridgeMachine second)
    (3 * steps + 1 +
      PipelineOutputHandoff.framedOutputHandoffWorkSteps final.tape)
    (terminalBridgeWorkSteps final.tape.outputBits)
    (renameConfiguration simulationState
      (PipelineMachineSimulation.liftConfiguration second
        (startConfig second input) startWorkTape))
    (renameConfiguration rejectingHandoffState
      (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration handoffFinal))
    (renameConfiguration rejectingPackerState
      (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
        final.tape.outputBits outsideLeft outsideRight)) hBridged hTerminal
  exact ⟨simulatorFinal, handoffFinal, outsideLeft, outsideRight,
    hFinalRepresents, hHandoffRepresents, hPackerInput, by
      simpa [secondSuffixWorkSteps] using hComplete⟩

/-! ### First component and the literal inter-component launch -/

/-- Either first-machine verdict reaches the same second simulator start,
with the first output still represented on the unchanged work tape. -/
theorem firstTraceAndLaunch_workRunExact_of_rawRunExact
    (first second : Machine) (steps : Nat) (input : BitString)
    (final : Configuration)
    (hRaw : PipelineMachineSimulation.rawRunExact? first steps
      (startConfig first input) = some final)
    (hFinal : final.state = first.acceptState ∨
      (final.state = first.rejectState ∧
        first.rejectState ≠ first.acceptState)) :
    ∃ simulatorFinal handoffFinal,
      PipelineMachineSimulation.RepresentsConfiguration
          first final simulatorFinal ∧
      PipelineTape.Represents final.tape.handoffTarget handoffFinal ∧
      workRunExact? (sequentialWorkMachine first second)
          (PipelineCompiler.bridgedWorkSteps input steps final.tape + 1)
          (workStartConfiguration (sequentialWorkMachine first second)
            (rawInputWorkTape input)) =
        some (renameConfiguration secondPipelineState
          (renameConfiguration simulationState
            (PipelineMachineSimulation.liftConfiguration second
              (startConfig second final.tape.outputBits) handoffFinal))) := by
  cases hFinal with
  | inl hAccept =>
      rcases PipelineCompiler.bridgedAccept_workRunExact_of_rawRunExact
          first steps input final hRaw hAccept with
        ⟨simulatorFinal, handoffFinal, hFinalRepresents,
          hHandoffRepresents, hBridge⟩
      have hFirst := first_workRunExact_of_exact first second
        (PipelineCompiler.bridgedWorkSteps input steps final.tape)
        (workStartConfiguration (bridgedMachine first)
          (rawInputWorkTape input))
        (renameConfiguration acceptingHandoffState
          (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
            handoffFinal)) hBridge
      have hFirst' : workRunExact? (sequentialWorkMachine first second)
          (PipelineCompiler.bridgedWorkSteps input steps final.tape)
          (workStartConfiguration (sequentialWorkMachine first second)
            (rawInputWorkTape input)) =
        some (renameConfiguration firstPipelineState
          (renameConfiguration acceptingHandoffState
            (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
              handoffFinal))) := by
        simpa [workStartConfiguration, sequentialWorkMachine,
          bridgedMachine, renameConfiguration] using hFirst
      have hLaunchStep := firstAcceptLaunch_workStep first second
        (renameConfiguration acceptingHandoffState
          (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
            handoffFinal))
        (acceptingHandoffFinal_state_eq_accept first handoffFinal)
      have hLaunchStep' : workStep? (sequentialWorkMachine first second)
          (renameConfiguration firstPipelineState
            (renameConfiguration acceptingHandoffState
              (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
                handoffFinal))) =
        some (renameConfiguration secondPipelineState
          (renameConfiguration simulationState
            (PipelineMachineSimulation.liftConfiguration second
              (startConfig second final.tape.outputBits) handoffFinal))) := by
        simpa [PipelineMachineSimulation.liftConfiguration,
          PipelineMachineSimulation.liftMachine, startConfig,
          renameConfiguration,
          PipelineOutputHandoff.framedOutputHandoffFinalConfiguration] using
            hLaunchStep
      have hLaunch := workRunExact_one
        (sequentialWorkMachine first second)
        (renameConfiguration firstPipelineState
          (renameConfiguration acceptingHandoffState
            (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
              handoffFinal)))
        (renameConfiguration secondPipelineState
          (renameConfiguration simulationState
            (PipelineMachineSimulation.liftConfiguration second
              (startConfig second final.tape.outputBits) handoffFinal)))
        hLaunchStep'
      have hComplete := PipelineMachineSimulation.workRunExact?_compose
        (sequentialWorkMachine first second)
        (PipelineCompiler.bridgedWorkSteps input steps final.tape) 1
        (workStartConfiguration (sequentialWorkMachine first second)
          (rawInputWorkTape input))
        (renameConfiguration firstPipelineState
          (renameConfiguration acceptingHandoffState
            (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
              handoffFinal)))
        (renameConfiguration secondPipelineState
          (renameConfiguration simulationState
            (PipelineMachineSimulation.liftConfiguration second
              (startConfig second final.tape.outputBits) handoffFinal)))
        hFirst' hLaunch
      exact ⟨simulatorFinal, handoffFinal, hFinalRepresents,
        hHandoffRepresents, hComplete⟩
  | inr hRejectEvidence =>
      rcases hRejectEvidence with ⟨hReject, hDistinct⟩
      rcases PipelineCompiler.bridgedReject_workRunExact_of_rawRunExact
          first steps input final hDistinct hRaw hReject with
        ⟨simulatorFinal, handoffFinal, hFinalRepresents,
          hHandoffRepresents, hBridge⟩
      have hFirst := first_workRunExact_of_exact first second
        (PipelineCompiler.bridgedWorkSteps input steps final.tape)
        (workStartConfiguration (bridgedMachine first)
          (rawInputWorkTape input))
        (renameConfiguration rejectingHandoffState
          (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
            handoffFinal)) hBridge
      have hFirst' : workRunExact? (sequentialWorkMachine first second)
          (PipelineCompiler.bridgedWorkSteps input steps final.tape)
          (workStartConfiguration (sequentialWorkMachine first second)
            (rawInputWorkTape input)) =
        some (renameConfiguration firstPipelineState
          (renameConfiguration rejectingHandoffState
            (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
              handoffFinal))) := by
        simpa [workStartConfiguration, sequentialWorkMachine,
          bridgedMachine, renameConfiguration] using hFirst
      have hLaunchStep := firstRejectLaunch_workStep first second
        (renameConfiguration rejectingHandoffState
          (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
            handoffFinal))
        (rejectingHandoffFinal_state_eq_reject first handoffFinal)
      have hLaunchStep' : workStep? (sequentialWorkMachine first second)
          (renameConfiguration firstPipelineState
            (renameConfiguration rejectingHandoffState
              (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
                handoffFinal))) =
        some (renameConfiguration secondPipelineState
          (renameConfiguration simulationState
            (PipelineMachineSimulation.liftConfiguration second
              (startConfig second final.tape.outputBits) handoffFinal))) := by
        simpa [PipelineMachineSimulation.liftConfiguration,
          PipelineMachineSimulation.liftMachine, startConfig,
          renameConfiguration,
          PipelineOutputHandoff.framedOutputHandoffFinalConfiguration] using
            hLaunchStep
      have hLaunch := workRunExact_one
        (sequentialWorkMachine first second)
        (renameConfiguration firstPipelineState
          (renameConfiguration rejectingHandoffState
            (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
              handoffFinal)))
        (renameConfiguration secondPipelineState
          (renameConfiguration simulationState
            (PipelineMachineSimulation.liftConfiguration second
              (startConfig second final.tape.outputBits) handoffFinal)))
        hLaunchStep'
      have hComplete := PipelineMachineSimulation.workRunExact?_compose
        (sequentialWorkMachine first second)
        (PipelineCompiler.bridgedWorkSteps input steps final.tape) 1
        (workStartConfiguration (sequentialWorkMachine first second)
          (rawInputWorkTape input))
        (renameConfiguration firstPipelineState
          (renameConfiguration rejectingHandoffState
            (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
              handoffFinal)))
        (renameConfiguration secondPipelineState
          (renameConfiguration simulationState
            (PipelineMachineSimulation.liftConfiguration second
              (startConfig second final.tape.outputBits) handoffFinal)))
        hFirst' hLaunch
      exact ⟨simulatorFinal, handoffFinal, hFinalRepresents,
        hHandoffRepresents, hComplete⟩

/-! ### Complete supplied sequential traces -/

/-- Supplied exact runs of both raw machines compose to the terminal accepting
configuration of the one literal sequential table. -/
theorem acceptingSequentialTrace_workRunExact_of_rawRunExact
    (first second : Machine) (firstSteps secondSteps : Nat)
    (input : BitString) (firstFinal secondFinal : Configuration)
    (hFirstRaw : PipelineMachineSimulation.rawRunExact? first firstSteps
      (startConfig first input) = some firstFinal)
    (hFirstFinal : firstFinal.state = first.acceptState ∨
      (firstFinal.state = first.rejectState ∧
        first.rejectState ≠ first.acceptState))
    (hSecondRaw : PipelineMachineSimulation.rawRunExact? second secondSteps
      (startConfig second firstFinal.tape.outputBits) = some secondFinal)
    (hSecondAccept : secondFinal.state = second.acceptState) :
    ∃ outsideLeft outsideRight,
      workRunExact? (sequentialWorkMachine first second)
          (sequentialWorkSteps input firstSteps firstFinal.tape
            secondSteps secondFinal.tape)
          (workStartConfiguration (sequentialWorkMachine first second)
            (rawInputWorkTape input)) =
        some (renameConfiguration secondPipelineState
          (renameConfiguration acceptingPackerState
            (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
              secondFinal.tape.outputBits outsideLeft outsideRight))) := by
  rcases firstTraceAndLaunch_workRunExact_of_rawRunExact
      first second firstSteps input firstFinal hFirstRaw hFirstFinal with
    ⟨_, firstHandoff, _, hFirstHandoffRepresents, hFirstComplete⟩
  have hSecondInput : PipelineTape.Represents
      (Tape.ofInput firstFinal.tape.outputBits) firstHandoff := by
    simpa [Tape.handoffTarget] using hFirstHandoffRepresents
  rcases secondAcceptingSuffix_workRunExact_of_rawRunExact
      second secondSteps firstFinal.tape.outputBits firstHandoff secondFinal
      hSecondInput hSecondRaw hSecondAccept with
    ⟨_, _, outsideLeft, outsideRight, _, _, _, hSecondLocal⟩
  have hSecond := second_workRunExact_of_exact first second
    (secondSuffixWorkSteps secondSteps secondFinal.tape)
    (renameConfiguration simulationState
      (PipelineMachineSimulation.liftConfiguration second
        (startConfig second firstFinal.tape.outputBits) firstHandoff))
    (renameConfiguration acceptingPackerState
      (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
        secondFinal.tape.outputBits outsideLeft outsideRight)) hSecondLocal
  have hComplete := PipelineMachineSimulation.workRunExact?_compose
    (sequentialWorkMachine first second)
    (PipelineCompiler.bridgedWorkSteps input firstSteps firstFinal.tape + 1)
    (secondSuffixWorkSteps secondSteps secondFinal.tape)
    (workStartConfiguration (sequentialWorkMachine first second)
      (rawInputWorkTape input))
    (renameConfiguration secondPipelineState
      (renameConfiguration simulationState
        (PipelineMachineSimulation.liftConfiguration second
          (startConfig second firstFinal.tape.outputBits) firstHandoff)))
    (renameConfiguration secondPipelineState
      (renameConfiguration acceptingPackerState
        (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
          secondFinal.tape.outputBits outsideLeft outsideRight)))
    hFirstComplete hSecond
  exact ⟨outsideLeft, outsideRight, by
    simpa [sequentialWorkSteps] using hComplete⟩

/-- The analogous complete trace ends in the disjoint terminal rejecting
configuration when the second raw machine rejects. -/
theorem rejectingSequentialTrace_workRunExact_of_rawRunExact
    (first second : Machine) (firstSteps secondSteps : Nat)
    (input : BitString) (firstFinal secondFinal : Configuration)
    (hFirstRaw : PipelineMachineSimulation.rawRunExact? first firstSteps
      (startConfig first input) = some firstFinal)
    (hFirstFinal : firstFinal.state = first.acceptState ∨
      (firstFinal.state = first.rejectState ∧
        first.rejectState ≠ first.acceptState))
    (hSecondDistinct : second.rejectState ≠ second.acceptState)
    (hSecondRaw : PipelineMachineSimulation.rawRunExact? second secondSteps
      (startConfig second firstFinal.tape.outputBits) = some secondFinal)
    (hSecondReject : secondFinal.state = second.rejectState) :
    ∃ outsideLeft outsideRight,
      workRunExact? (sequentialWorkMachine first second)
          (sequentialWorkSteps input firstSteps firstFinal.tape
            secondSteps secondFinal.tape)
          (workStartConfiguration (sequentialWorkMachine first second)
            (rawInputWorkTape input)) =
        some (renameConfiguration secondPipelineState
          (renameConfiguration rejectingPackerState
            (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
              secondFinal.tape.outputBits outsideLeft outsideRight))) := by
  rcases firstTraceAndLaunch_workRunExact_of_rawRunExact
      first second firstSteps input firstFinal hFirstRaw hFirstFinal with
    ⟨_, firstHandoff, _, hFirstHandoffRepresents, hFirstComplete⟩
  have hSecondInput : PipelineTape.Represents
      (Tape.ofInput firstFinal.tape.outputBits) firstHandoff := by
    simpa [Tape.handoffTarget] using hFirstHandoffRepresents
  rcases secondRejectingSuffix_workRunExact_of_rawRunExact
      second secondSteps firstFinal.tape.outputBits firstHandoff secondFinal
      hSecondDistinct hSecondInput hSecondRaw hSecondReject with
    ⟨_, _, outsideLeft, outsideRight, _, _, _, hSecondLocal⟩
  have hSecond := second_workRunExact_of_exact first second
    (secondSuffixWorkSteps secondSteps secondFinal.tape)
    (renameConfiguration simulationState
      (PipelineMachineSimulation.liftConfiguration second
        (startConfig second firstFinal.tape.outputBits) firstHandoff))
    (renameConfiguration rejectingPackerState
      (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
        secondFinal.tape.outputBits outsideLeft outsideRight)) hSecondLocal
  have hComplete := PipelineMachineSimulation.workRunExact?_compose
    (sequentialWorkMachine first second)
    (PipelineCompiler.bridgedWorkSteps input firstSteps firstFinal.tape + 1)
    (secondSuffixWorkSteps secondSteps secondFinal.tape)
    (workStartConfiguration (sequentialWorkMachine first second)
      (rawInputWorkTape input))
    (renameConfiguration secondPipelineState
      (renameConfiguration simulationState
        (PipelineMachineSimulation.liftConfiguration second
          (startConfig second firstFinal.tape.outputBits) firstHandoff)))
    (renameConfiguration secondPipelineState
      (renameConfiguration rejectingPackerState
        (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
          secondFinal.tape.outputBits outsideLeft outsideRight)))
    hFirstComplete hSecond
  exact ⟨outsideLeft, outsideRight, by
    simpa [sequentialWorkSteps] using hComplete⟩

theorem acceptingSequentialFinal_state_eq_accept
    (first second : Machine) (bits : BitString)
    (outsideLeft outsideRight : List WorkSymbol) :
    (renameConfiguration secondPipelineState
      (renameConfiguration acceptingPackerState
        (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
          bits outsideLeft outsideRight))).state =
      (sequentialWorkMachine first second).acceptState := by
  rfl

theorem rejectingSequentialFinal_state_eq_reject
    (first second : Machine) (bits : BitString)
    (outsideLeft outsideRight : List WorkSymbol) :
    (renameConfiguration secondPipelineState
      (renameConfiguration rejectingPackerState
        (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
          bits outsideLeft outsideRight))).state =
      (sequentialWorkMachine first second).rejectState := by
  rfl

theorem acceptingSequentialFinal_isHalted
    (first second : Machine) (bits : BitString)
    (outsideLeft outsideRight : List WorkSymbol) :
    (sequentialWorkMachine first second).isHalted
      (renameConfiguration secondPipelineState
        (renameConfiguration acceptingPackerState
          (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
            bits outsideLeft outsideRight))) = true := by
  unfold WorkMachine.isHalted
  rw [acceptingSequentialFinal_state_eq_accept first second bits
    outsideLeft outsideRight]
  rw [nat_beq_true_iff _ _ |>.mpr rfl]
  rfl

theorem rejectingSequentialFinal_isHalted
    (first second : Machine) (bits : BitString)
    (outsideLeft outsideRight : List WorkSymbol) :
    (sequentialWorkMachine first second).isHalted
      (renameConfiguration secondPipelineState
        (renameConfiguration rejectingPackerState
          (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
            bits outsideLeft outsideRight))) = true := by
  unfold WorkMachine.isHalted
  rw [rejectingSequentialFinal_state_eq_reject first second bits
    outsideLeft outsideRight]
  have hDistinct := sequentialWorkMachine_acceptState_ne_rejectState
    first second
  rw [nat_beq_false_of_ne _ _ hDistinct.symm,
    nat_beq_true_iff _ _ |>.mpr rfl]
  rfl

/-! ### External polynomial accounting -/

/-- The exact sequential raw cost is the two literal component-stage costs
plus the single first-to-second launch. -/
theorem sequentialRawSteps_eq_stage_costs
    (input : BitString) (firstSteps : Nat) (firstFinalTape : Tape)
    (secondSteps : Nat) (secondFinalTape : Tape) :
    sequentialRawSteps input firstSteps firstFinalTape secondSteps
        secondFinalTape =
      (6 * PipelineCompiler.bridgedWorkSteps input firstSteps firstFinalTape +
        6) + 6 * secondSuffixWorkSteps secondSteps secondFinalTape := by
  unfold sequentialRawSteps sequentialWorkSteps
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]

private theorem secondSuffixRawSteps_le_pipelineRawTimeBound
    (secondBound : NatPolynomial) (input : BitString)
    (steps : Nat) (finalTape : Tape)
    (hSteps : steps ≤ secondBound.eval (BitString.size input))
    (hOutput : finalTape.outputBits.length ≤
      (PipelineCompiler.pipelineOutputSizeBound secondBound).eval
        (BitString.size input)) :
    6 * secondSuffixWorkSteps steps finalTape ≤
      (PipelineCompiler.pipelineRawTimeBound secondBound).eval
        (BitString.size input) := by
  have hSimulation : 3 * steps ≤
      (PipelineInputFramer.totalInputFramerWorkSteps input + 1) +
        3 * steps :=
    Nat.le_add_left (3 * steps)
      (PipelineInputFramer.totalInputFramerWorkSteps input + 1)
  have hBridge : 3 * steps + 1 +
      PipelineOutputHandoff.framedOutputHandoffWorkSteps finalTape ≤
    ((PipelineInputFramer.totalInputFramerWorkSteps input + 1) +
      3 * steps) + 1 +
        PipelineOutputHandoff.framedOutputHandoffWorkSteps finalTape :=
    Nat.add_le_add_right (Nat.add_le_add_right hSimulation 1)
      (PipelineOutputHandoff.framedOutputHandoffWorkSteps finalTape)
  have hWork : secondSuffixWorkSteps steps finalTape ≤
      PipelineCompiler.suppliedTraceWorkSteps input steps finalTape := by
    unfold secondSuffixWorkSteps PipelineCompiler.suppliedTraceWorkSteps
      PipelineCompiler.bridgedWorkSteps
      PipelineCompiler.simulationPrefixWorkSteps
    exact Nat.add_le_add_right hBridge
      (terminalBridgeWorkSteps finalTape.outputBits)
  have hRaw : 6 * secondSuffixWorkSteps steps finalTape ≤
      PipelineCompiler.suppliedTraceRawSteps input steps finalTape := by
    unfold PipelineCompiler.suppliedTraceRawSteps
    exact Nat.mul_le_mul_left 6 hWork
  exact Nat.le_trans hRaw
    (PipelineCompiler.suppliedTraceRawSteps_le_pipelineRawTimeBound
      secondBound input steps finalTape hSteps hOutput)

/-- The complete exact trace is bounded by one polynomial evaluated only at
the original external input length.  Both later costs are transported through
explicit output-size polynomials. -/
theorem sequentialRawSteps_le_sequentialRawTimeBound
    (firstBound secondBound : NatPolynomial)
    (input : BitString) (firstSteps : Nat) (firstFinalTape : Tape)
    (secondSteps : Nat) (secondFinalTape : Tape)
    (hFirstSteps : firstSteps ≤ firstBound.eval (BitString.size input))
    (hFirstOutput : firstFinalTape.outputBits.length ≤
      (firstOutputSizeBound firstBound).eval (BitString.size input))
    (hSecondSteps : secondSteps ≤
      secondBound.eval firstFinalTape.outputBits.length)
    (hSecondOutput : secondFinalTape.outputBits.length ≤
      (PipelineCompiler.pipelineOutputSizeBound secondBound).eval
        firstFinalTape.outputBits.length) :
    sequentialRawSteps input firstSteps firstFinalTape secondSteps
        secondFinalTape ≤
      (sequentialRawTimeBound firstBound secondBound).eval
        (BitString.size input) := by
  let inputSize := BitString.size input
  let firstSize := (firstOutputSizeBound firstBound).eval inputSize
  have hFirstFull :=
    PipelineCompiler.suppliedTraceRawSteps_le_pipelineRawTimeBound
      firstBound input firstSteps firstFinalTape hFirstSteps hFirstOutput
  have hFirstStageToFull :
      6 * PipelineCompiler.bridgedWorkSteps input firstSteps firstFinalTape ≤
        PipelineCompiler.suppliedTraceRawSteps input firstSteps
          firstFinalTape := by
    unfold PipelineCompiler.suppliedTraceRawSteps
      PipelineCompiler.suppliedTraceWorkSteps
    exact Nat.mul_le_mul_left 6
      (Nat.le_add_right
        (PipelineCompiler.bridgedWorkSteps input firstSteps firstFinalTape)
        (terminalBridgeWorkSteps firstFinalTape.outputBits))
  have hFirstStage :
      6 * PipelineCompiler.bridgedWorkSteps input firstSteps firstFinalTape ≤
        (PipelineCompiler.pipelineRawTimeBound firstBound).eval inputSize :=
    Nat.le_trans hFirstStageToFull hFirstFull
  have hSecondLocal := secondSuffixRawSteps_le_pipelineRawTimeBound
    secondBound firstFinalTape.outputBits secondSteps secondFinalTape
    hSecondSteps hSecondOutput
  have hSecondMonotone := NatPolynomial.eval_mono
    (PipelineCompiler.pipelineRawTimeBound secondBound) hFirstOutput
  have hSecondStage : 6 * secondSuffixWorkSteps secondSteps secondFinalTape ≤
      (PipelineCompiler.pipelineRawTimeBound secondBound).eval firstSize :=
    Nat.le_trans hSecondLocal hSecondMonotone
  rw [sequentialRawSteps_eq_stage_costs]
  unfold sequentialRawTimeBound
  rw [NatPolynomial.eval_add, NatPolynomial.eval_add,
    NatPolynomial.eval_constant, NatPolynomial.eval_substitute]
  exact Nat.add_le_add (Nat.add_le_add hFirstStage (Nat.le_refl 6))
    hSecondStage

/-- Exact raw prefixes supply both output bounds required by the external
sequential polynomial; no caller provides an output certificate. -/
theorem sequentialRawSteps_le_of_rawRunExact
    (first second : Machine) (firstBound secondBound : NatPolynomial)
    (input : BitString) (firstSteps secondSteps : Nat)
    (firstFinal secondFinal : Configuration)
    (hFirstSteps : firstSteps ≤ firstBound.eval (BitString.size input))
    (hFirstRaw : PipelineMachineSimulation.rawRunExact? first firstSteps
      (startConfig first input) = some firstFinal)
    (hSecondSteps : secondSteps ≤
      secondBound.eval firstFinal.tape.outputBits.length)
    (hSecondRaw : PipelineMachineSimulation.rawRunExact? second secondSteps
      (startConfig second firstFinal.tape.outputBits) = some secondFinal) :
    sequentialRawSteps input firstSteps firstFinal.tape secondSteps
        secondFinal.tape ≤
      (sequentialRawTimeBound firstBound secondBound).eval
        (BitString.size input) := by
  have hFirstOutput :=
    PipelineCompiler.outputBits_length_le_pipelineOutputSizeBound_of_rawRunExact
      first firstBound firstSteps input firstFinal hFirstSteps hFirstRaw
  have hSecondOutput :=
    PipelineCompiler.outputBits_length_le_pipelineOutputSizeBound_of_rawRunExact
      second secondBound secondSteps firstFinal.tape.outputBits secondFinal
      hSecondSteps hSecondRaw
  exact sequentialRawSteps_le_sequentialRawTimeBound
    firstBound secondBound input firstSteps firstFinal.tape secondSteps
    secondFinal.tape hFirstSteps hFirstOutput hSecondSteps hSecondOutput

/-! ### Compiled raw execution at the external bound -/

/-- Supplied exact prefixes ending in second-machine acceptance reach the
compiled sequential machine's accept state at the external polynomial. -/
theorem run_sequential_accept_at_bound_of_rawRunExact
    (first second : Machine) (firstBound secondBound : NatPolynomial)
    (input : BitString) (firstSteps secondSteps : Nat)
    (firstFinal secondFinal : Configuration)
    (hFirstSteps : firstSteps ≤ firstBound.eval (BitString.size input))
    (hFirstRaw : PipelineMachineSimulation.rawRunExact? first firstSteps
      (startConfig first input) = some firstFinal)
    (hFirstFinal : firstFinal.state = first.acceptState ∨
      (firstFinal.state = first.rejectState ∧
        first.rejectState ≠ first.acceptState))
    (hSecondSteps : secondSteps ≤
      secondBound.eval firstFinal.tape.outputBits.length)
    (hSecondRaw : PipelineMachineSimulation.rawRunExact? second secondSteps
      (startConfig second firstFinal.tape.outputBits) = some secondFinal)
    (hSecondAccept : secondFinal.state = second.acceptState) :
    ∃ outsideLeft outsideRight,
      Configuration.BlankEquivalent
        (run (sequentialMachine first second)
          ((sequentialRawTimeBound firstBound secondBound).eval
            (BitString.size input))
          (startConfig (sequentialMachine first second) input))
        (encodeWorkConfiguration
          (renameConfiguration secondPipelineState
            (renameConfiguration acceptingPackerState
              (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
                secondFinal.tape.outputBits outsideLeft outsideRight)))) := by
  rcases acceptingSequentialTrace_workRunExact_of_rawRunExact
      first second firstSteps secondSteps input firstFinal secondFinal
      hFirstRaw hFirstFinal hSecondRaw hSecondAccept with
    ⟨outsideLeft, outsideRight, hExact⟩
  have hCost := sequentialRawSteps_le_of_rawRunExact first second
    firstBound secondBound input firstSteps secondSteps firstFinal secondFinal
    hFirstSteps hFirstRaw hSecondSteps hSecondRaw
  change 6 * sequentialWorkSteps input firstSteps firstFinal.tape secondSteps
      secondFinal.tape ≤
    (sequentialRawTimeBound firstBound secondBound).eval
      (BitString.size input) at hCost
  have hCompiled := run_compileWorkMachine_of_workRunExact_halted_le
    (sequentialWorkMachine first second)
    (sequentialWorkSteps input firstSteps firstFinal.tape secondSteps
      secondFinal.tape)
    ((sequentialRawTimeBound firstBound secondBound).eval
      (BitString.size input))
    (workStartConfiguration (sequentialWorkMachine first second)
      (rawInputWorkTape input))
    (renameConfiguration secondPipelineState
      (renameConfiguration acceptingPackerState
        (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
          secondFinal.tape.outputBits outsideLeft outsideRight)))
    hExact
    (acceptingSequentialFinal_isHalted first second secondFinal.tape.outputBits
      outsideLeft outsideRight)
    hCost
  have hStart := startConfig_compileWorkMachine_blankEquivalent
    (sequentialWorkMachine first second) input
  have hRun := run_blankEquivalent
    (compileWorkMachine (sequentialWorkMachine first second))
    ((sequentialRawTimeBound firstBound secondBound).eval
      (BitString.size input)) hStart
  rw [hCompiled] at hRun
  exact ⟨outsideLeft, outsideRight, by
    simpa [sequentialMachine] using hRun⟩

/-- Supplied exact prefixes ending in second-machine rejection reach the
disjoint compiled reject state at the same external polynomial. -/
theorem run_sequential_reject_at_bound_of_rawRunExact
    (first second : Machine) (firstBound secondBound : NatPolynomial)
    (input : BitString) (firstSteps secondSteps : Nat)
    (firstFinal secondFinal : Configuration)
    (hFirstSteps : firstSteps ≤ firstBound.eval (BitString.size input))
    (hFirstRaw : PipelineMachineSimulation.rawRunExact? first firstSteps
      (startConfig first input) = some firstFinal)
    (hFirstFinal : firstFinal.state = first.acceptState ∨
      (firstFinal.state = first.rejectState ∧
        first.rejectState ≠ first.acceptState))
    (hSecondDistinct : second.rejectState ≠ second.acceptState)
    (hSecondSteps : secondSteps ≤
      secondBound.eval firstFinal.tape.outputBits.length)
    (hSecondRaw : PipelineMachineSimulation.rawRunExact? second secondSteps
      (startConfig second firstFinal.tape.outputBits) = some secondFinal)
    (hSecondReject : secondFinal.state = second.rejectState) :
    ∃ outsideLeft outsideRight,
      Configuration.BlankEquivalent
        (run (sequentialMachine first second)
          ((sequentialRawTimeBound firstBound secondBound).eval
            (BitString.size input))
          (startConfig (sequentialMachine first second) input))
        (encodeWorkConfiguration
          (renameConfiguration secondPipelineState
            (renameConfiguration rejectingPackerState
              (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
                secondFinal.tape.outputBits outsideLeft outsideRight)))) := by
  rcases rejectingSequentialTrace_workRunExact_of_rawRunExact
      first second firstSteps secondSteps input firstFinal secondFinal
      hFirstRaw hFirstFinal hSecondDistinct hSecondRaw hSecondReject with
    ⟨outsideLeft, outsideRight, hExact⟩
  have hCost := sequentialRawSteps_le_of_rawRunExact first second
    firstBound secondBound input firstSteps secondSteps firstFinal secondFinal
    hFirstSteps hFirstRaw hSecondSteps hSecondRaw
  change 6 * sequentialWorkSteps input firstSteps firstFinal.tape secondSteps
      secondFinal.tape ≤
    (sequentialRawTimeBound firstBound secondBound).eval
      (BitString.size input) at hCost
  have hCompiled := run_compileWorkMachine_of_workRunExact_halted_le
    (sequentialWorkMachine first second)
    (sequentialWorkSteps input firstSteps firstFinal.tape secondSteps
      secondFinal.tape)
    ((sequentialRawTimeBound firstBound secondBound).eval
      (BitString.size input))
    (workStartConfiguration (sequentialWorkMachine first second)
      (rawInputWorkTape input))
    (renameConfiguration secondPipelineState
      (renameConfiguration rejectingPackerState
        (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
          secondFinal.tape.outputBits outsideLeft outsideRight)))
    hExact
    (rejectingSequentialFinal_isHalted first second secondFinal.tape.outputBits
      outsideLeft outsideRight)
    hCost
  have hStart := startConfig_compileWorkMachine_blankEquivalent
    (sequentialWorkMachine first second) input
  have hRun := run_blankEquivalent
    (compileWorkMachine (sequentialWorkMachine first second))
    ((sequentialRawTimeBound firstBound secondBound).eval
      (BitString.size input)) hStart
  rw [hCompiled] at hRun
  exact ⟨outsideLeft, outsideRight, by
    simpa [sequentialMachine] using hRun⟩

private theorem finalStateEvidence_of_ne_timeout
    (machine : Machine) (fuel : Nat) (input : BitString)
    (hHalts : boundedDecide machine fuel input ≠ .timeout) :
    (run machine fuel (startConfig machine input)).state =
        machine.acceptState ∨
      ((run machine fuel (startConfig machine input)).state =
          machine.rejectState ∧
        machine.rejectState ≠ machine.acceptState) := by
  cases hVerdict : boundedDecide machine fuel input with
  | accept =>
      exact Or.inl ((boundedDecide_accept_iff_final machine fuel input).1
        hVerdict)
  | reject =>
      have hFinal :=
        (boundedDecide_reject_iff_final machine fuel input).1 hVerdict
      refine Or.inr ⟨hFinal.2, ?_⟩
      intro hEqual
      exact hFinal.1 (hFinal.2.trans hEqual)
  | timeout =>
      exact False.elim (hHalts hVerdict)

/-- If both advertised bounded executions halt, the literal sequential
machine has exactly the second execution's verdict and ordinary raw output on
every input. -/
theorem sequential_correct
    (first second : Machine) (firstBound secondBound : NatPolynomial)
    (input : BitString)
    (hFirstHalts : boundedDecide first
      (firstBound.eval (BitString.size input)) input ≠ .timeout)
    (hSecondHalts : boundedDecide second
      (secondBound.eval (BitString.size
        (machineOutput first
          (firstBound.eval (BitString.size input)) input)))
      (machineOutput first
        (firstBound.eval (BitString.size input)) input) ≠ .timeout) :
    boundedDecide (sequentialMachine first second)
        ((sequentialRawTimeBound firstBound secondBound).eval
          (BitString.size input)) input =
      boundedDecide second
        (secondBound.eval (BitString.size
          (machineOutput first
            (firstBound.eval (BitString.size input)) input)))
        (machineOutput first
          (firstBound.eval (BitString.size input)) input) ∧
    machineOutput (sequentialMachine first second)
        ((sequentialRawTimeBound firstBound secondBound).eval
          (BitString.size input)) input =
      machineOutput second
        (secondBound.eval (BitString.size
          (machineOutput first
            (firstBound.eval (BitString.size input)) input)))
        (machineOutput first
          (firstBound.eval (BitString.size input)) input) := by
  let firstFuel := firstBound.eval (BitString.size input)
  let firstFinal := run first firstFuel (startConfig first input)
  rcases PipelineMachineSimulation.rawRunExact?_exists_le_run
      first firstFuel (startConfig first input) with
    ⟨firstSteps, hFirstSteps, hFirstRaw⟩
  have hFirstRaw' : PipelineMachineSimulation.rawRunExact? first firstSteps
      (startConfig first input) = some firstFinal := by
    simpa [firstFinal] using hFirstRaw
  have hFirstSteps' : firstSteps ≤
      firstBound.eval (BitString.size input) := by
    simpa [firstFuel] using hFirstSteps
  have hFirstFinal : firstFinal.state = first.acceptState ∨
      (firstFinal.state = first.rejectState ∧
        first.rejectState ≠ first.acceptState) := by
    simpa [firstFuel, firstFinal] using
      (finalStateEvidence_of_ne_timeout first firstFuel input
        (by simpa [firstFuel] using hFirstHalts))
  let secondInput := firstFinal.tape.outputBits
  let secondFuel := secondBound.eval (BitString.size secondInput)
  let secondFinal := run second secondFuel (startConfig second secondInput)
  rcases PipelineMachineSimulation.rawRunExact?_exists_le_run
      second secondFuel (startConfig second secondInput) with
    ⟨secondSteps, hSecondSteps, hSecondRaw⟩
  have hSecondRaw' : PipelineMachineSimulation.rawRunExact? second secondSteps
      (startConfig second firstFinal.tape.outputBits) = some secondFinal := by
    simpa [secondInput, secondFinal] using hSecondRaw
  have hSecondSteps' : secondSteps ≤
      secondBound.eval firstFinal.tape.outputBits.length := by
    simpa [secondInput, secondFuel, BitString.size] using hSecondSteps
  have hSecondHalts' : boundedDecide second secondFuel secondInput ≠
      .timeout := by
    simpa [firstFuel, firstFinal, secondInput, secondFuel, machineOutput]
      using hSecondHalts
  cases hSecondVerdict : boundedDecide second secondFuel secondInput with
  | accept =>
      have hSecondAccept : secondFinal.state = second.acceptState := by
        apply (boundedDecide_accept_iff_final second secondFuel secondInput).1
        exact hSecondVerdict
      rcases run_sequential_accept_at_bound_of_rawRunExact
          first second firstBound secondBound input firstSteps secondSteps
          firstFinal secondFinal hFirstSteps' hFirstRaw' hFirstFinal
          hSecondSteps' hSecondRaw' hSecondAccept with
        ⟨outsideLeft, outsideRight, hRun⟩
      let packedFinal := renameConfiguration secondPipelineState
        (renameConfiguration acceptingPackerState
          (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
            secondFinal.tape.outputBits outsideLeft outsideRight))
      have hPackedAccept : packedFinal.state =
          (sequentialWorkMachine first second).acceptState := by
        exact acceptingSequentialFinal_state_eq_accept first second
          secondFinal.tape.outputBits outsideLeft outsideRight
      have hEncodedAccept : (encodeWorkConfiguration packedFinal).state =
          (sequentialMachine first second).acceptState := by
        change (encodeWorkConfiguration packedFinal).state =
          (compileWorkMachine (sequentialWorkMachine first second)).acceptState
        exact (encodeWorkConfiguration_accept_iff
          (sequentialWorkMachine first second) packedFinal).2 hPackedAccept
      have hPipelineAccept :
          boundedDecide (sequentialMachine first second)
              ((sequentialRawTimeBound firstBound secondBound).eval
                (BitString.size input)) input = .accept := by
        apply (boundedDecide_accept_iff_final
          (sequentialMachine first second)
          ((sequentialRawTimeBound firstBound secondBound).eval
            (BitString.size input)) input).2
        exact hRun.1.trans hEncodedAccept
      constructor
      · simpa [firstFuel, firstFinal, secondInput, secondFuel,
          machineOutput] using
          hPipelineAccept.trans hSecondVerdict.symm
      · unfold machineOutput
        have hBlankOutput := Tape.outputBits_eq_of_blankEquivalent hRun.2
        have hOutput := acceptingTerminal_output_eq
          secondFinal.tape.outputBits outsideLeft outsideRight
        calc
          Tape.outputBits
              (run (sequentialMachine first second)
                ((sequentialRawTimeBound firstBound secondBound).eval
                  (BitString.size input))
                (startConfig (sequentialMachine first second) input)).tape =
              Tape.outputBits (encodeWorkConfiguration packedFinal).tape :=
            hBlankOutput
          _ = secondFinal.tape.outputBits := by
            simpa [packedFinal, renameConfiguration,
              encodeWorkConfiguration] using hOutput
          _ = Tape.outputBits
              (run second
                (secondBound.eval (BitString.size
                  (machineOutput first
                    (firstBound.eval (BitString.size input)) input)))
                (startConfig second
                  (machineOutput first
                    (firstBound.eval (BitString.size input)) input))).tape := by
            rfl
  | reject =>
      have hSecondFinal :=
        (boundedDecide_reject_iff_final second secondFuel secondInput).1
          hSecondVerdict
      have hSecondReject : secondFinal.state = second.rejectState :=
        hSecondFinal.2
      have hSecondDistinct : second.rejectState ≠ second.acceptState := by
        intro hEqual
        exact hSecondFinal.1 (hSecondReject.trans hEqual)
      rcases run_sequential_reject_at_bound_of_rawRunExact
          first second firstBound secondBound input firstSteps secondSteps
          firstFinal secondFinal hFirstSteps' hFirstRaw' hFirstFinal
          hSecondDistinct hSecondSteps' hSecondRaw' hSecondReject with
        ⟨outsideLeft, outsideRight, hRun⟩
      let packedFinal := renameConfiguration secondPipelineState
        (renameConfiguration rejectingPackerState
          (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
            secondFinal.tape.outputBits outsideLeft outsideRight))
      have hPackedReject : packedFinal.state =
          (sequentialWorkMachine first second).rejectState := by
        exact rejectingSequentialFinal_state_eq_reject first second
          secondFinal.tape.outputBits outsideLeft outsideRight
      have hPackedNotAccept : packedFinal.state ≠
          (sequentialWorkMachine first second).acceptState := by
        intro hAccept
        exact sequentialWorkMachine_acceptState_ne_rejectState first second
          (hAccept.symm.trans hPackedReject)
      have hEncodedReject : (encodeWorkConfiguration packedFinal).state =
          (sequentialMachine first second).rejectState := by
        change (encodeWorkConfiguration packedFinal).state =
          (compileWorkMachine (sequentialWorkMachine first second)).rejectState
        exact (encodeWorkConfiguration_reject_iff
          (sequentialWorkMachine first second) packedFinal).2 hPackedReject
      have hEncodedNotAccept : (encodeWorkConfiguration packedFinal).state ≠
          (sequentialMachine first second).acceptState := by
        intro hAccept
        have hWorkAccept := (encodeWorkConfiguration_accept_iff
          (sequentialWorkMachine first second) packedFinal).1 hAccept
        exact hPackedNotAccept hWorkAccept
      have hPipelineReject :
          boundedDecide (sequentialMachine first second)
              ((sequentialRawTimeBound firstBound secondBound).eval
                (BitString.size input)) input = .reject := by
        apply (boundedDecide_reject_iff_final
          (sequentialMachine first second)
          ((sequentialRawTimeBound firstBound secondBound).eval
            (BitString.size input)) input).2
        constructor
        · intro hAccept
          exact hEncodedNotAccept (hRun.1.symm.trans hAccept)
        · exact hRun.1.trans hEncodedReject
      constructor
      · simpa [firstFuel, firstFinal, secondInput, secondFuel,
          machineOutput] using
          hPipelineReject.trans hSecondVerdict.symm
      · unfold machineOutput
        have hBlankOutput := Tape.outputBits_eq_of_blankEquivalent hRun.2
        have hOutput := rejectingTerminal_output_eq
          secondFinal.tape.outputBits outsideLeft outsideRight
        calc
          Tape.outputBits
              (run (sequentialMachine first second)
                ((sequentialRawTimeBound firstBound secondBound).eval
                  (BitString.size input))
                (startConfig (sequentialMachine first second) input)).tape =
              Tape.outputBits (encodeWorkConfiguration packedFinal).tape :=
            hBlankOutput
          _ = secondFinal.tape.outputBits := by
            simpa [packedFinal, renameConfiguration,
              encodeWorkConfiguration] using hOutput
          _ = Tape.outputBits
              (run second
                (secondBound.eval (BitString.size
                  (machineOutput first
                    (firstBound.eval (BitString.size input)) input)))
                (startConfig second
                  (machineOutput first
                    (firstBound.eval (BitString.size input)) input))).tape := by
            rfl
  | timeout =>
      exact False.elim (hSecondHalts' hSecondVerdict)

/-- Exact verdict preservation for sequential composition of two
proof-bearing polynomial-time machines. -/
theorem sequential_boundedDecide_eq
    {firstLanguage secondLanguage : BitString → Prop}
    (first : PolynomialTimeMachine firstLanguage)
    (second : PolynomialTimeMachine secondLanguage) (input : BitString) :
    boundedDecide (sequentialMachine first.machine second.machine)
        ((sequentialRawTimeBound first.timeBound second.timeBound).eval
          (BitString.size input)) input =
      boundedDecide second.machine
        (second.timeBound.eval (BitString.size
          (machineOutput first.machine
            (first.timeBound.eval (BitString.size input)) input)))
        (machineOutput first.machine
          (first.timeBound.eval (BitString.size input)) input) := by
  exact (sequential_correct first.machine second.machine first.timeBound
    second.timeBound input (first.haltsWithin input)
    (second.haltsWithin (machineOutput first.machine
      (first.timeBound.eval (BitString.size input)) input))).1

/-- The same compiled run preserves the second execution's exact ordinary
blank-delimited output. -/
theorem sequential_machineOutput_eq
    {firstLanguage secondLanguage : BitString → Prop}
    (first : PolynomialTimeMachine firstLanguage)
    (second : PolynomialTimeMachine secondLanguage) (input : BitString) :
    machineOutput (sequentialMachine first.machine second.machine)
        ((sequentialRawTimeBound first.timeBound second.timeBound).eval
          (BitString.size input)) input =
      machineOutput second.machine
        (second.timeBound.eval (BitString.size
          (machineOutput first.machine
            (first.timeBound.eval (BitString.size input)) input)))
        (machineOutput first.machine
          (first.timeBound.eval (BitString.size input)) input) := by
  exact (sequential_correct first.machine second.machine first.timeBound
    second.timeBound input (first.haltsWithin input)
    (second.haltsWithin (machineOutput first.machine
      (first.timeBound.eval (BitString.size input)) input))).2

/-- The compiled sequential machine cannot time out at its external bound. -/
theorem sequential_ne_timeout
    {firstLanguage secondLanguage : BitString → Prop}
    (first : PolynomialTimeMachine firstLanguage)
    (second : PolynomialTimeMachine secondLanguage) (input : BitString) :
    boundedDecide (sequentialMachine first.machine second.machine)
        ((sequentialRawTimeBound first.timeBound second.timeBound).eval
          (BitString.size input)) input ≠ .timeout := by
  rw [sequential_boundedDecide_eq first second input]
  exact second.haltsWithin (machineOutput first.machine
    (first.timeBound.eval (BitString.size input)) input)

/-- Acceptance by the literal composition is exactly the second language on
the first machine's raw output. -/
theorem sequential_accepts_iff
    {firstLanguage secondLanguage : BitString → Prop}
    (first : PolynomialTimeMachine firstLanguage)
    (second : PolynomialTimeMachine secondLanguage) (input : BitString) :
    boundedDecide (sequentialMachine first.machine second.machine)
        ((sequentialRawTimeBound first.timeBound second.timeBound).eval
          (BitString.size input)) input = .accept ↔
      secondLanguage (machineOutput first.machine
        (first.timeBound.eval (BitString.size input)) input) := by
  rw [sequential_boundedDecide_eq first second input]
  exact second.accepts_iff (machineOutput first.machine
    (first.timeBound.eval (BitString.size input)) input)

/-! ### Fail-closed prefix behavior -/

/-- Before either designated first-machine endpoint launches the second
component, the global sequential machine reports timeout. -/
theorem firstSimulationPrefix_workBoundedDecide_timeout
    (first second : Machine) (steps : Nat) (input : BitString)
    (final : Configuration)
    (hRaw : PipelineMachineSimulation.rawRunExact? first steps
      (startConfig first input) = some final) :
    workBoundedDecide (sequentialWorkMachine first second)
        (PipelineCompiler.simulationPrefixWorkSteps input steps)
        (rawInputWorkTape input) = .timeout := by
  rcases PipelineCompiler.simulationPrefix_workRunExact_of_rawRunExact
      first steps input final hRaw with
    ⟨workFinal, hLocal, _⟩
  have hOuter := first_workRunExact_of_exact first second
    (PipelineCompiler.simulationPrefixWorkSteps input steps)
    (workStartConfiguration (bridgedMachine first) (rawInputWorkTape input))
    (renameConfiguration simulationState workFinal) hLocal
  have hOuter' : workRunExact? (sequentialWorkMachine first second)
      (PipelineCompiler.simulationPrefixWorkSteps input steps)
      (workStartConfiguration (sequentialWorkMachine first second)
        (rawInputWorkTape input)) =
    some (renameConfiguration firstPipelineState
      (renameConfiguration simulationState workFinal)) := by
    simpa [workStartConfiguration, sequentialWorkMachine,
      bridgedMachine, renameConfiguration] using hOuter
  have hRun := workRun_eq_of_workRunExact
    (sequentialWorkMachine first second)
    (PipelineCompiler.simulationPrefixWorkSteps input steps)
    (workStartConfiguration (sequentialWorkMachine first second)
      (rawInputWorkTape input))
    (renameConfiguration firstPipelineState
      (renameConfiguration simulationState workFinal)) hOuter'
  have hAccept :
      firstPipelineState (simulationState workFinal.state) ≠
        (sequentialWorkMachine first second).acceptState := by
    simpa only [sequentialWorkMachine] using
      (firstPipelineState_ne_secondPipelineState
        (simulationState workFinal.state)
        (terminalBridgeMachine second).acceptState)
  have hReject :
      firstPipelineState (simulationState workFinal.state) ≠
        (sequentialWorkMachine first second).rejectState := by
    simpa only [sequentialWorkMachine] using
      (firstPipelineState_ne_secondPipelineState
        (simulationState workFinal.state)
        (terminalBridgeMachine second).rejectState)
  unfold workBoundedDecide
  rw [hRun]
  change
    (if (firstPipelineState (simulationState workFinal.state) ==
        (sequentialWorkMachine first second).acceptState) = true then
      WorkVerdict.accept
     else if (firstPipelineState (simulationState workFinal.state) ==
        (sequentialWorkMachine first second).rejectState) = true then
      WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout
  rw [PipelineSequentialStateNamespace.nat_beq_false_of_ne _ _ hAccept,
    PipelineSequentialStateNamespace.nat_beq_false_of_ne _ _ hReject]
  rfl

/-- In particular, a stuck nonhalting first endpoint remains timeout and is
never promoted to rejection or allowed to launch the second machine. -/
theorem sequential_timeout_of_stuck_first_rawRunExact
    (first second : Machine) (steps : Nat) (input : BitString)
    (final : Configuration)
    (hRaw : PipelineMachineSimulation.rawRunExact? first steps
      (startConfig first input) = some final)
    (_hNonhalting : first.isHalted final = false)
    (_hStuck : step? first final = none) :
    workBoundedDecide (sequentialWorkMachine first second)
        (PipelineCompiler.simulationPrefixWorkSteps input steps)
        (rawInputWorkTape input) = .timeout := by
  exact firstSimulationPrefix_workBoundedDecide_timeout
    first second steps input final hRaw

/-- Package the literal sequential compiler as a polynomial-time machine for
the second language evaluated on the first machine's exact raw output. -/
def toPolynomialTimeMachine
    {firstLanguage secondLanguage : BitString → Prop}
    (first : PolynomialTimeMachine firstLanguage)
    (second : PolynomialTimeMachine secondLanguage) :
    PolynomialTimeMachine (fun input =>
      secondLanguage (machineOutput first.machine
        (first.timeBound.eval (BitString.size input)) input)) :=
  { machine := sequentialMachine first.machine second.machine
    timeBound := sequentialRawTimeBound first.timeBound second.timeBound
    haltsWithin := sequential_ne_timeout first second
    accepts_iff := sequential_accepts_iff first second }

/-!
## Exact boundary

This module proves an all-input two-machine sequential compiler with a literal
finite raw rule table, exact verdict/output preservation, and an external
input-size polynomial.  It does not yet define recursive
`FunctionProgram.RawRefinement` or `DecisionProgram.RawRefinement`
constructors and therefore does not discharge the concrete complexity
machine-link blocker.  It does not prove CNF-SAT in P, CNF-SAT
NP-completeness, `PNP.Main.p_eq_np`, or P = NP.  The publication gate remains
false.
-/

end PipelineSequentialCompiler

end PNP.Concrete
