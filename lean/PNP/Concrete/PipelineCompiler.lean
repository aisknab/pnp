/-
Copyright (c) 2026 PNP Labs.

Uniform all-input compilation of the literal four-stage work pipeline.

This module extends the canonical-pair result without changing the executable
rule table.  Every raw bitstring is framed, simulated by the supplied target,
handed off internally, and packed back into ordinary blank-delimited output.
The general FunctionProgram/DecisionProgram refinement constructors are a
separate milestone and are deliberately not claimed here.
-/

import PNP.Concrete.PipelinePairedCompiler

namespace PNP.Concrete

namespace PipelineCompiler

open PipelineStateNamespace PipelineStageBridges PipelineTerminalBridge

/-- The same literal compiled four-stage machine used by the paired compiler,
now proved correct from every ordinary raw input. -/
def pipelineMachine (target : Machine) : Machine :=
  compileWorkMachine (terminalBridgeMachine target)

theorem pipelineMachine_eq_pairedPipelineMachine (target : Machine) :
    pipelineMachine target =
      PipelinePairedCompiler.pairedPipelineMachine target := by
  rfl

/-- Exact work cost through framing, the first launch, and a supplied target
execution. -/
def simulationPrefixWorkSteps (input : BitString) (sourceSteps : Nat) : Nat :=
  PipelineInputFramer.totalInputFramerWorkSteps input + 1 + 3 * sourceSteps

/-- Exact work cost through the represented-output handoff. -/
def bridgedWorkSteps (input : BitString) (sourceSteps : Nat)
    (finalTape : Tape) : Nat :=
  simulationPrefixWorkSteps input sourceSteps + 1 +
    PipelineOutputHandoff.framedOutputHandoffWorkSteps finalTape

/-- Exact work cost through terminal raw-output packing. -/
def suppliedTraceWorkSteps (input : BitString) (sourceSteps : Nat)
    (finalTape : Tape) : Nat :=
  bridgedWorkSteps input sourceSteps finalTape +
    terminalBridgeWorkSteps finalTape.outputBits

/-- Six compiled raw transitions for every exact work transition. -/
def suppliedTraceRawSteps (input : BitString) (sourceSteps : Nat)
    (finalTape : Tape) : Nat :=
  6 * suppliedTraceWorkSteps input sourceSteps finalTape

/-- A target using `p(m)` steps can expose at most `m + p(m) + 1` output
bits. -/
def pipelineOutputSizeBound (targetBound : NatPolynomial) : NatPolynomial :=
  .add (.add .variable targetBound) (.constant 1)

/-- Complete all-input raw bound for the literal four-stage compiler. -/
def pipelineRawTimeBound (targetBound : NatPolynomial) : NatPolynomial :=
  .add
    (.add
      (.add
        (.add
          (.add PipelineInputFramer.totalInputFramerRawTimeBound
            (.constant 6))
          (.mul (.constant 18) targetBound))
        (.constant 6))
      (NatPolynomial.substitute
        PipelineOutputHandoff.framedOutputHandoffRawTimeBound
        (pipelineOutputSizeBound targetBound)))
    (NatPolynomial.substitute terminalBridgeRawTimeBound
      (pipelineOutputSizeBound targetBound))

/-- The total framer accept state launches the simulator on the unchanged raw
input. -/
theorem totalInputLaunch_workStep (machine : Machine) (input : BitString) :
    workStep? (bridgedMachine machine)
        (renameConfiguration inputState
          (PipelineInputFramer.totalInputFramerFinalConfiguration input)) =
      some (renameConfiguration simulationState
        (PipelineMachineSimulation.liftConfiguration machine
          (startConfig machine input)
          (PipelineInputFramer.totalInputFramerFinalTape input))) := by
  let final := PipelineInputFramer.totalInputFramerFinalConfiguration input
  have hHalted := bridgedMachine_isHalted_input_false
    machine final.state final.tape
  have hLaunch := findWorkRule_launchRules
    (inputState PipelineInputFramer.pairedInputFramer.acceptState)
    (simulationState
      (PipelineMachineSimulation.liftMachine machine).startState)
    final.tape.head
  have hInput : findWorkRule (inputLaunchRules machine)
      (inputState final.state) final.tape.head =
        some (launchRule
          (inputState PipelineInputFramer.pairedInputFramer.acceptState)
          (simulationState
            (PipelineMachineSimulation.liftMachine machine).startState)
          final.tape.head) := by
    simpa [inputLaunchRules, final,
      PipelineInputFramer.totalInputFramerFinalConfiguration] using hLaunch
  have hFind : findWorkRule (bridgedMachine machine).rules
      (inputState final.state) final.tape.head =
        some (launchRule
          (inputState PipelineInputFramer.pairedInputFramer.acceptState)
          (simulationState
            (PipelineMachineSimulation.liftMachine machine).startState)
          final.tape.head) := by
    unfold bridgedMachine PipelineStageBridges.bridgedRules
    exact findWorkRule_append_of_some _ _ _ _ _ hInput
  have hStep := workStep?_eq_apply_of_find (bridgedMachine machine)
    (renameConfiguration inputState final)
    (launchRule
      (inputState PipelineInputFramer.pairedInputFramer.acceptState)
      (simulationState
        (PipelineMachineSimulation.liftMachine machine).startState)
      final.tape.head) hHalted hFind
  simpa [final, launchRule, applyWorkRule, WorkTape.write, WorkTape.move,
    PipelineInputFramer.totalInputFramerFinalConfiguration,
    PipelineMachineSimulation.liftMachine,
    PipelineMachineSimulation.liftConfiguration, startConfig,
    renameConfiguration] using hStep

/-- The total framer trace, launch, and any supplied exact target trace form
one exact prefix in the literal bridged table. -/
theorem simulationPrefix_workRunExact_of_rawRunExact
    (machine : Machine) (steps : Nat) (input : BitString)
    (final : Configuration)
    (hRaw : PipelineMachineSimulation.rawRunExact? machine steps
      (startConfig machine input) = some final) :
    ∃ workFinal,
      workRunExact? (bridgedMachine machine)
          (simulationPrefixWorkSteps input steps)
          (workStartConfiguration (bridgedMachine machine)
            (rawInputWorkTape input)) =
        some (renameConfiguration simulationState workFinal) ∧
      PipelineMachineSimulation.RepresentsConfiguration
        machine final workFinal := by
  let framerSteps := PipelineInputFramer.totalInputFramerWorkSteps input
  let framerFinal :=
    PipelineInputFramer.totalInputFramerFinalConfiguration input
  let rawStart := startConfig machine input
  have hFramerLocal :=
    PipelineInputFramer.totalInputFramer_workRunExact input
  have hFramer := input_workRunExact_of_exact machine framerSteps
    (workStartConfiguration PipelineInputFramer.pairedInputFramer
      (rawInputWorkTape input)) framerFinal hFramerLocal
  change workRunExact? (bridgedMachine machine) framerSteps
      (workStartConfiguration (bridgedMachine machine)
        (rawInputWorkTape input)) =
    some (renameConfiguration inputState framerFinal) at hFramer
  have hInputStep := totalInputLaunch_workStep machine input
  have hInputBridge : workRunExact? (bridgedMachine machine) 1
      (renameConfiguration inputState framerFinal) =
        some (renameConfiguration simulationState
          (PipelineMachineSimulation.liftConfiguration machine rawStart
            (PipelineInputFramer.totalInputFramerFinalTape input))) := by
    change
      (match workStep? (bridgedMachine machine)
          (renameConfiguration inputState framerFinal) with
       | none => none
       | some next => workRunExact? (bridgedMachine machine) 0 next) = _
    rw [hInputStep]
    rfl
  have hFrameRepresents :=
    PipelineInputFramer.totalInputFramerFinal_represents input
  rcases PipelineMachineSimulation.workRunExact_three_mul_of_rawRunExact
      machine steps rawStart final
      (PipelineInputFramer.totalInputFramerFinalTape input)
      hRaw hFrameRepresents with
    ⟨workFinal, hSimulationLocal, hFinalRepresents⟩
  have hSimulation := simulation_workRunExact_of_exact machine (3 * steps)
    (PipelineMachineSimulation.liftConfiguration machine rawStart
      (PipelineInputFramer.totalInputFramerFinalTape input))
    workFinal hSimulationLocal
  have hFramerAndLaunch := PipelineMachineSimulation.workRunExact?_compose
    (bridgedMachine machine) framerSteps 1
    (workStartConfiguration (bridgedMachine machine)
      (rawInputWorkTape input))
    (renameConfiguration inputState framerFinal)
    (renameConfiguration simulationState
      (PipelineMachineSimulation.liftConfiguration machine rawStart
        (PipelineInputFramer.totalInputFramerFinalTape input)))
    hFramer hInputBridge
  have hPrefix := PipelineMachineSimulation.workRunExact?_compose
    (bridgedMachine machine) (framerSteps + 1) (3 * steps)
    (workStartConfiguration (bridgedMachine machine)
      (rawInputWorkTape input))
    (renameConfiguration simulationState
      (PipelineMachineSimulation.liftConfiguration machine rawStart
        (PipelineInputFramer.totalInputFramerFinalTape input)))
    (renameConfiguration simulationState workFinal)
    hFramerAndLaunch hSimulation
  refine ⟨workFinal, ?_, hFinalRepresents⟩
  simpa [simulationPrefixWorkSteps, framerSteps] using hPrefix

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

/-- An accepting target trace reaches the represented-output handoff endpoint
on every raw input. -/
theorem bridgedAccept_workRunExact_of_rawRunExact
    (machine : Machine) (steps : Nat) (input : BitString)
    (final : Configuration)
    (hRaw : PipelineMachineSimulation.rawRunExact? machine steps
      (startConfig machine input) = some final)
    (hAccept : final.state = machine.acceptState) :
    ∃ simulatorFinal handoffFinal,
      PipelineMachineSimulation.RepresentsConfiguration
          machine final simulatorFinal ∧
      PipelineTape.Represents final.tape.handoffTarget handoffFinal ∧
      workRunExact? (bridgedMachine machine)
          (bridgedWorkSteps input steps final.tape)
          (workStartConfiguration (bridgedMachine machine)
            (rawInputWorkTape input)) =
        some (renameConfiguration acceptingHandoffState
          (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
            handoffFinal)) := by
  rcases simulationPrefix_workRunExact_of_rawRunExact
      machine steps input final hRaw with
    ⟨simulatorFinal, hPrefix, hFinalRepresents⟩
  have hControl := controlState_eq_acceptSentinel_of_state_eq_accept
    machine final hAccept
  have hSimulatorState : simulatorFinal.state =
      PipelineMachineSimulation.acceptSentinel :=
    hFinalRepresents.1.trans hControl
  have hLaunchStep := acceptingLaunch_workStep machine simulatorFinal.tape
  have hSimulatorEq : simulatorFinal =
      { state := PipelineMachineSimulation.acceptSentinel,
        tape := simulatorFinal.tape } := by
    cases simulatorFinal with
    | mk state tape =>
        change state = PipelineMachineSimulation.acceptSentinel at hSimulatorState
        cases hSimulatorState
        rfl
  have hLaunchStep' : workStep? (bridgedMachine machine)
      (renameConfiguration simulationState simulatorFinal) =
        some (renameConfiguration acceptingHandoffState
          (workStartConfiguration
            PipelineOutputHandoff.framedOutputHandoff simulatorFinal.tape)) := by
    rw [hSimulatorEq]
    exact hLaunchStep
  have hLaunch : workRunExact? (bridgedMachine machine) 1
      (renameConfiguration simulationState simulatorFinal) =
        some (renameConfiguration acceptingHandoffState
          (workStartConfiguration
            PipelineOutputHandoff.framedOutputHandoff simulatorFinal.tape)) := by
    change
      (match workStep? (bridgedMachine machine)
          (renameConfiguration simulationState simulatorFinal) with
       | none => none
       | some next => workRunExact? (bridgedMachine machine) 0 next) = _
    rw [hLaunchStep']
    rfl
  rcases PipelineOutputHandoff.framedOutputHandoff_workRunExact_of_represents
      hFinalRepresents.2 with
    ⟨handoffFinal, hHandoffRepresents, hHandoffLocal⟩
  have hHandoff := acceptingHandoff_workRunExact_of_exact machine
    (PipelineOutputHandoff.framedOutputHandoffWorkSteps final.tape)
    (workStartConfiguration PipelineOutputHandoff.framedOutputHandoff
      simulatorFinal.tape)
    (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration handoffFinal)
    hHandoffLocal
  have hPrefixAndLaunch := PipelineMachineSimulation.workRunExact?_compose
    (bridgedMachine machine)
    (simulationPrefixWorkSteps input steps) 1
    (workStartConfiguration (bridgedMachine machine)
      (rawInputWorkTape input))
    (renameConfiguration simulationState simulatorFinal)
    (renameConfiguration acceptingHandoffState
      (workStartConfiguration PipelineOutputHandoff.framedOutputHandoff
        simulatorFinal.tape)) hPrefix hLaunch
  have hComplete := PipelineMachineSimulation.workRunExact?_compose
    (bridgedMachine machine)
    (simulationPrefixWorkSteps input steps + 1)
    (PipelineOutputHandoff.framedOutputHandoffWorkSteps final.tape)
    (workStartConfiguration (bridgedMachine machine)
      (rawInputWorkTape input))
    (renameConfiguration acceptingHandoffState
      (workStartConfiguration PipelineOutputHandoff.framedOutputHandoff
        simulatorFinal.tape))
    (renameConfiguration acceptingHandoffState
      (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
        handoffFinal)) hPrefixAndLaunch hHandoff
  exact ⟨simulatorFinal, handoffFinal, hFinalRepresents,
    hHandoffRepresents, by
      simpa [bridgedWorkSteps] using hComplete⟩

/-- A rejecting target trace uses the disjoint rejecting handoff copy on every
raw input. -/
theorem bridgedReject_workRunExact_of_rawRunExact
    (machine : Machine) (steps : Nat) (input : BitString)
    (final : Configuration)
    (hDistinct : machine.rejectState ≠ machine.acceptState)
    (hRaw : PipelineMachineSimulation.rawRunExact? machine steps
      (startConfig machine input) = some final)
    (hReject : final.state = machine.rejectState) :
    ∃ simulatorFinal handoffFinal,
      PipelineMachineSimulation.RepresentsConfiguration
          machine final simulatorFinal ∧
      PipelineTape.Represents final.tape.handoffTarget handoffFinal ∧
      workRunExact? (bridgedMachine machine)
          (bridgedWorkSteps input steps final.tape)
          (workStartConfiguration (bridgedMachine machine)
            (rawInputWorkTape input)) =
        some (renameConfiguration rejectingHandoffState
          (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
            handoffFinal)) := by
  rcases simulationPrefix_workRunExact_of_rawRunExact
      machine steps input final hRaw with
    ⟨simulatorFinal, hPrefix, hFinalRepresents⟩
  have hControl := controlState_eq_rejectSentinel_of_state_eq_reject
    machine final hReject hDistinct
  have hSimulatorState : simulatorFinal.state =
      PipelineMachineSimulation.rejectSentinel :=
    hFinalRepresents.1.trans hControl
  have hLaunchStep := rejectingLaunch_workStep machine simulatorFinal.tape
  have hSimulatorEq : simulatorFinal =
      { state := PipelineMachineSimulation.rejectSentinel,
        tape := simulatorFinal.tape } := by
    cases simulatorFinal with
    | mk state tape =>
        change state = PipelineMachineSimulation.rejectSentinel at hSimulatorState
        cases hSimulatorState
        rfl
  have hLaunchStep' : workStep? (bridgedMachine machine)
      (renameConfiguration simulationState simulatorFinal) =
        some (renameConfiguration rejectingHandoffState
          (workStartConfiguration
            PipelineOutputHandoff.framedOutputHandoff simulatorFinal.tape)) := by
    rw [hSimulatorEq]
    exact hLaunchStep
  have hLaunch : workRunExact? (bridgedMachine machine) 1
      (renameConfiguration simulationState simulatorFinal) =
        some (renameConfiguration rejectingHandoffState
          (workStartConfiguration
            PipelineOutputHandoff.framedOutputHandoff simulatorFinal.tape)) := by
    change
      (match workStep? (bridgedMachine machine)
          (renameConfiguration simulationState simulatorFinal) with
       | none => none
       | some next => workRunExact? (bridgedMachine machine) 0 next) = _
    rw [hLaunchStep']
    rfl
  rcases PipelineOutputHandoff.framedOutputHandoff_workRunExact_of_represents
      hFinalRepresents.2 with
    ⟨handoffFinal, hHandoffRepresents, hHandoffLocal⟩
  have hHandoff := rejectingHandoff_workRunExact_of_exact machine
    (PipelineOutputHandoff.framedOutputHandoffWorkSteps final.tape)
    (workStartConfiguration PipelineOutputHandoff.framedOutputHandoff
      simulatorFinal.tape)
    (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration handoffFinal)
    hHandoffLocal
  have hPrefixAndLaunch := PipelineMachineSimulation.workRunExact?_compose
    (bridgedMachine machine)
    (simulationPrefixWorkSteps input steps) 1
    (workStartConfiguration (bridgedMachine machine)
      (rawInputWorkTape input))
    (renameConfiguration simulationState simulatorFinal)
    (renameConfiguration rejectingHandoffState
      (workStartConfiguration PipelineOutputHandoff.framedOutputHandoff
        simulatorFinal.tape)) hPrefix hLaunch
  have hComplete := PipelineMachineSimulation.workRunExact?_compose
    (bridgedMachine machine)
    (simulationPrefixWorkSteps input steps + 1)
    (PipelineOutputHandoff.framedOutputHandoffWorkSteps final.tape)
    (workStartConfiguration (bridgedMachine machine)
      (rawInputWorkTape input))
    (renameConfiguration rejectingHandoffState
      (workStartConfiguration PipelineOutputHandoff.framedOutputHandoff
        simulatorFinal.tape))
    (renameConfiguration rejectingHandoffState
      (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
        handoffFinal)) hPrefixAndLaunch hHandoff
  exact ⟨simulatorFinal, handoffFinal, hFinalRepresents,
    hHandoffRepresents, by
      simpa [bridgedWorkSteps] using hComplete⟩

/-- A supplied accepting target execution continues through all four stages
on every raw input. -/
theorem acceptingSuppliedTrace_workRunExact_of_rawRunExact
    (machine : Machine) (steps : Nat) (input : BitString)
    (final : Configuration)
    (hRaw : PipelineMachineSimulation.rawRunExact? machine steps
      (startConfig machine input) = some final)
    (hAccept : final.state = machine.acceptState) :
    ∃ simulatorFinal handoffFinal outsideLeft outsideRight,
      PipelineMachineSimulation.RepresentsConfiguration
          machine final simulatorFinal ∧
      PipelineTape.Represents final.tape.handoffTarget handoffFinal ∧
      handoffFinal = TerminalOutputPacker.terminalOutputPackerInputTape
        final.tape.outputBits outsideLeft outsideRight ∧
      workRunExact? (terminalBridgeMachine machine)
          (suppliedTraceWorkSteps input steps final.tape)
          (workStartConfiguration (terminalBridgeMachine machine)
            (rawInputWorkTape input)) =
        some (renameConfiguration acceptingPackerState
          (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
            final.tape.outputBits outsideLeft outsideRight)) := by
  rcases bridgedAccept_workRunExact_of_rawRunExact
      machine steps input final hRaw hAccept with
    ⟨simulatorFinal, handoffFinal, hFinalRepresents,
      hHandoffRepresents, hBridgeExact⟩
  have hBridgeExtended := bridged_workRunExact_of_exact machine
    (bridgedWorkSteps input steps final.tape)
    (workStartConfiguration (bridgedMachine machine)
      (rawInputWorkTape input))
    (renameConfiguration acceptingHandoffState
      (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
        handoffFinal)) hBridgeExact
  have hBridgeExtended' : workRunExact? (terminalBridgeMachine machine)
      (bridgedWorkSteps input steps final.tape)
      (workStartConfiguration (terminalBridgeMachine machine)
        (rawInputWorkTape input)) =
      some (renameConfiguration acceptingHandoffState
        (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
          handoffFinal)) := by
    simpa [workStartConfiguration, bridgedMachine, terminalBridgeMachine]
      using hBridgeExtended
  rcases acceptingTerminal_workRunExact_of_represents
      machine hHandoffRepresents with
    ⟨outsideLeft, outsideRight, hInput, hTerminalExact⟩
  have hComplete := PipelineMachineSimulation.workRunExact?_compose
    (terminalBridgeMachine machine)
    (bridgedWorkSteps input steps final.tape)
    (terminalBridgeWorkSteps final.tape.outputBits)
    (workStartConfiguration (terminalBridgeMachine machine)
      (rawInputWorkTape input))
    (renameConfiguration acceptingHandoffState
      (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
        handoffFinal))
    (renameConfiguration acceptingPackerState
      (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
        final.tape.outputBits outsideLeft outsideRight))
    hBridgeExtended' hTerminalExact
  exact ⟨simulatorFinal, handoffFinal, outsideLeft, outsideRight,
    hFinalRepresents, hHandoffRepresents, hInput, by
      simpa [suppliedTraceWorkSteps] using hComplete⟩

/-- A supplied rejecting target execution uses the disjoint rejecting suffix
on every raw input. -/
theorem rejectingSuppliedTrace_workRunExact_of_rawRunExact
    (machine : Machine) (steps : Nat) (input : BitString)
    (final : Configuration)
    (hDistinct : machine.rejectState ≠ machine.acceptState)
    (hRaw : PipelineMachineSimulation.rawRunExact? machine steps
      (startConfig machine input) = some final)
    (hReject : final.state = machine.rejectState) :
    ∃ simulatorFinal handoffFinal outsideLeft outsideRight,
      PipelineMachineSimulation.RepresentsConfiguration
          machine final simulatorFinal ∧
      PipelineTape.Represents final.tape.handoffTarget handoffFinal ∧
      handoffFinal = TerminalOutputPacker.terminalOutputPackerInputTape
        final.tape.outputBits outsideLeft outsideRight ∧
      workRunExact? (terminalBridgeMachine machine)
          (suppliedTraceWorkSteps input steps final.tape)
          (workStartConfiguration (terminalBridgeMachine machine)
            (rawInputWorkTape input)) =
        some (renameConfiguration rejectingPackerState
          (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
            final.tape.outputBits outsideLeft outsideRight)) := by
  rcases bridgedReject_workRunExact_of_rawRunExact
      machine steps input final hDistinct hRaw hReject with
    ⟨simulatorFinal, handoffFinal, hFinalRepresents,
      hHandoffRepresents, hBridgeExact⟩
  have hBridgeExtended := bridged_workRunExact_of_exact machine
    (bridgedWorkSteps input steps final.tape)
    (workStartConfiguration (bridgedMachine machine)
      (rawInputWorkTape input))
    (renameConfiguration rejectingHandoffState
      (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
        handoffFinal)) hBridgeExact
  have hBridgeExtended' : workRunExact? (terminalBridgeMachine machine)
      (bridgedWorkSteps input steps final.tape)
      (workStartConfiguration (terminalBridgeMachine machine)
        (rawInputWorkTape input)) =
      some (renameConfiguration rejectingHandoffState
        (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
          handoffFinal)) := by
    simpa [workStartConfiguration, bridgedMachine, terminalBridgeMachine]
      using hBridgeExtended
  rcases rejectingTerminal_workRunExact_of_represents
      machine hHandoffRepresents with
    ⟨outsideLeft, outsideRight, hInput, hTerminalExact⟩
  have hComplete := PipelineMachineSimulation.workRunExact?_compose
    (terminalBridgeMachine machine)
    (bridgedWorkSteps input steps final.tape)
    (terminalBridgeWorkSteps final.tape.outputBits)
    (workStartConfiguration (terminalBridgeMachine machine)
      (rawInputWorkTape input))
    (renameConfiguration rejectingHandoffState
      (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
        handoffFinal))
    (renameConfiguration rejectingPackerState
      (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
        final.tape.outputBits outsideLeft outsideRight))
    hBridgeExtended' hTerminalExact
  exact ⟨simulatorFinal, handoffFinal, outsideLeft, outsideRight,
    hFinalRepresents, hHandoffRepresents, hInput, by
      simpa [suppliedTraceWorkSteps] using hComplete⟩

private theorem mulAssocSafe (left middle right : Nat) :
    (left * middle) * right = left * (middle * right) := by
  induction right with
  | zero =>
      rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]
  | succ right ih =>
      calc
        (left * middle) * Nat.succ right =
            (left * middle) * right + left * middle :=
          Nat.mul_succ _ _
        _ = left * (middle * right) + left * middle :=
          congrArg (fun value => value + left * middle) ih
        _ = left * (middle * right + middle) :=
          (Nat.mul_add _ _ _).symm
        _ = left * (middle * Nat.succ right) :=
          congrArg (Nat.mul left) (Nat.mul_succ middle right).symm

/-- Evaluation of the all-input output polynomial has the displayed closed
form. -/
theorem pipelineOutputSizeBound_eval (targetBound : NatPolynomial)
    (inputSize : Nat) :
    (pipelineOutputSizeBound targetBound).eval inputSize =
      inputSize + targetBound.eval inputSize + 1 := by
  rfl

/-- The exact all-input raw cost decomposes into the local compiled costs. -/
theorem suppliedTraceRawSteps_eq_components
    (input : BitString) (steps : Nat) (finalTape : Tape) :
    suppliedTraceRawSteps input steps finalTape =
      ((((6 * PipelineInputFramer.totalInputFramerWorkSteps input + 6) +
            18 * steps) + 6) +
          PipelineOutputHandoff.framedOutputHandoffRawTimeBound.eval
            finalTape.outputBits.length) +
        terminalBridgeRawSteps finalTape.outputBits := by
  unfold suppliedTraceRawSteps suppliedTraceWorkSteps bridgedWorkSteps
    simulationPrefixWorkSteps
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add,
    Nat.mul_add, ← mulAssocSafe 6 3 steps,
    ← PipelinePairedCompiler.framedOutputHandoffRawTimeBound_exact finalTape]
  change 6 * PipelineInputFramer.totalInputFramerWorkSteps input +
      6 * 1 + (6 * 3) * steps + 6 * 1 + _ +
      6 * terminalBridgeWorkSteps finalTape.outputBits = _
  rw [Nat.mul_one]
  change 6 * PipelineInputFramer.totalInputFramerWorkSteps input + 6 +
      18 * steps + 6 + _ + terminalBridgeRawSteps finalTape.outputBits = _
  rfl

/-- Every exact four-stage trace fits the explicit polynomial evaluated only
at the external raw input length. -/
theorem suppliedTraceRawSteps_le_pipelineRawTimeBound
    (targetBound : NatPolynomial) (input : BitString)
    (steps : Nat) (finalTape : Tape)
    (hSteps : steps ≤ targetBound.eval (BitString.size input))
    (hOutput : finalTape.outputBits.length ≤
      (pipelineOutputSizeBound targetBound).eval (BitString.size input)) :
    suppliedTraceRawSteps input steps finalTape ≤
      (pipelineRawTimeBound targetBound).eval (BitString.size input) := by
  let inputSize := BitString.size input
  have hFramer := PipelineInputFramer.totalInputFramerRawTimeBound_le input
  have hSimulation : 18 * steps ≤ 18 * targetBound.eval inputSize :=
    Nat.mul_le_mul_left 18 hSteps
  have hHandoff := NatPolynomial.eval_mono
    PipelineOutputHandoff.framedOutputHandoffRawTimeBound hOutput
  have hTerminalLocal := terminalBridge_runtime_le finalTape.outputBits
  have hTerminalMonotone := NatPolynomial.eval_mono
    terminalBridgeRawTimeBound hOutput
  have hTerminal : terminalBridgeRawSteps finalTape.outputBits ≤
      terminalBridgeRawTimeBound.eval
        ((pipelineOutputSizeBound targetBound).eval inputSize) :=
    Nat.le_trans hTerminalLocal hTerminalMonotone
  rw [suppliedTraceRawSteps_eq_components]
  unfold pipelineRawTimeBound
  simp only [NatPolynomial.eval_add, NatPolynomial.eval_constant,
    NatPolynomial.eval_mul, NatPolynomial.eval_substitute]
  exact Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add hFramer (Nat.le_refl 6)) hSimulation)
        (Nat.le_refl 6))
      hHandoff)
    hTerminal

/-- An exact target prefix inherits the uniform output-size polynomial from
the ordinary raw growth bound. -/
theorem outputBits_length_le_pipelineOutputSizeBound_of_rawRunExact
    (machine : Machine) (targetBound : NatPolynomial)
    (steps : Nat) (input : BitString) (final : Configuration)
    (hSteps : steps ≤ targetBound.eval (BitString.size input))
    (hRaw : PipelineMachineSimulation.rawRunExact? machine steps
      (startConfig machine input) = some final) :
    final.tape.outputBits.length ≤
      (pipelineOutputSizeBound targetBound).eval (BitString.size input) := by
  have hRun := PipelineMachineSimulation.run_eq_of_rawRunExact
    machine steps (startConfig machine input) final hRaw
  have hOutput :=
    PipelinePairedCompiler.machineOutput_length_le_input_add_fuel
      machine steps input
  unfold machineOutput at hOutput
  rw [hRun] at hOutput
  rw [pipelineOutputSizeBound_eval]
  exact Nat.le_trans hOutput
    (Nat.add_le_add_right
      (Nat.add_le_add_left hSteps (BitString.size input)) 1)

theorem suppliedTraceRawSteps_le_of_rawRunExact
    (machine : Machine) (targetBound : NatPolynomial)
    (steps : Nat) (input : BitString) (final : Configuration)
    (hSteps : steps ≤ targetBound.eval (BitString.size input))
    (hRaw : PipelineMachineSimulation.rawRunExact? machine steps
      (startConfig machine input) = some final) :
    suppliedTraceRawSteps input steps final.tape ≤
      (pipelineRawTimeBound targetBound).eval (BitString.size input) := by
  exact suppliedTraceRawSteps_le_pipelineRawTimeBound
    targetBound input steps final.tape hSteps
    (outputBits_length_le_pipelineOutputSizeBound_of_rawRunExact
      machine targetBound steps input final hSteps hRaw)

/-- A supplied accepting prefix reaches a terminal accepting configuration at
the external polynomial budget.  Ordinary and macro starts differ only by
finite materialization of exterior blanks. -/
theorem run_pipeline_accept_at_bound_of_rawRunExact
    (machine : Machine) (targetBound : NatPolynomial)
    (steps : Nat) (input : BitString) (final : Configuration)
    (hSteps : steps ≤ targetBound.eval (BitString.size input))
    (hRaw : PipelineMachineSimulation.rawRunExact? machine steps
      (startConfig machine input) = some final)
    (hAccept : final.state = machine.acceptState) :
    ∃ outsideLeft outsideRight,
      Configuration.BlankEquivalent
        (run (pipelineMachine machine)
          ((pipelineRawTimeBound targetBound).eval (BitString.size input))
          (startConfig (pipelineMachine machine) input))
        (encodeWorkConfiguration
          (renameConfiguration acceptingPackerState
            (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
              final.tape.outputBits outsideLeft outsideRight))) := by
  rcases acceptingSuppliedTrace_workRunExact_of_rawRunExact
      machine steps input final hRaw hAccept with
    ⟨_, _, outsideLeft, outsideRight, _, _, _, hExact⟩
  have hCost := suppliedTraceRawSteps_le_of_rawRunExact
    machine targetBound steps input final hSteps hRaw
  change 6 * suppliedTraceWorkSteps input steps final.tape ≤
    (pipelineRawTimeBound targetBound).eval (BitString.size input) at hCost
  have hCompiled := run_compileWorkMachine_of_workRunExact_halted_le
    (terminalBridgeMachine machine)
    (suppliedTraceWorkSteps input steps final.tape)
    ((pipelineRawTimeBound targetBound).eval (BitString.size input))
    (workStartConfiguration (terminalBridgeMachine machine)
      (rawInputWorkTape input))
    (renameConfiguration acceptingPackerState
      (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
        final.tape.outputBits outsideLeft outsideRight))
    hExact
    (acceptingTerminalFinal_isHalted machine final.tape.outputBits
      outsideLeft outsideRight)
    hCost
  have hStart := startConfig_compileWorkMachine_blankEquivalent
    (terminalBridgeMachine machine) input
  have hRun := run_blankEquivalent
    (compileWorkMachine (terminalBridgeMachine machine))
    ((pipelineRawTimeBound targetBound).eval (BitString.size input)) hStart
  rw [hCompiled] at hRun
  exact ⟨outsideLeft, outsideRight, by
    simpa [pipelineMachine] using hRun⟩

/-- The rejecting exact prefix reaches the disjoint terminal reject image at
the same all-input polynomial budget. -/
theorem run_pipeline_reject_at_bound_of_rawRunExact
    (machine : Machine) (targetBound : NatPolynomial)
    (steps : Nat) (input : BitString) (final : Configuration)
    (hDistinct : machine.rejectState ≠ machine.acceptState)
    (hSteps : steps ≤ targetBound.eval (BitString.size input))
    (hRaw : PipelineMachineSimulation.rawRunExact? machine steps
      (startConfig machine input) = some final)
    (hReject : final.state = machine.rejectState) :
    ∃ outsideLeft outsideRight,
      Configuration.BlankEquivalent
        (run (pipelineMachine machine)
          ((pipelineRawTimeBound targetBound).eval (BitString.size input))
          (startConfig (pipelineMachine machine) input))
        (encodeWorkConfiguration
          (renameConfiguration rejectingPackerState
            (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
              final.tape.outputBits outsideLeft outsideRight))) := by
  rcases rejectingSuppliedTrace_workRunExact_of_rawRunExact
      machine steps input final hDistinct hRaw hReject with
    ⟨_, _, outsideLeft, outsideRight, _, _, _, hExact⟩
  have hCost := suppliedTraceRawSteps_le_of_rawRunExact
    machine targetBound steps input final hSteps hRaw
  change 6 * suppliedTraceWorkSteps input steps final.tape ≤
    (pipelineRawTimeBound targetBound).eval (BitString.size input) at hCost
  have hCompiled := run_compileWorkMachine_of_workRunExact_halted_le
    (terminalBridgeMachine machine)
    (suppliedTraceWorkSteps input steps final.tape)
    ((pipelineRawTimeBound targetBound).eval (BitString.size input))
    (workStartConfiguration (terminalBridgeMachine machine)
      (rawInputWorkTape input))
    (renameConfiguration rejectingPackerState
      (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
        final.tape.outputBits outsideLeft outsideRight))
    hExact
    (rejectingTerminalFinal_isHalted machine final.tape.outputBits
      outsideLeft outsideRight)
    hCost
  have hStart := startConfig_compileWorkMachine_blankEquivalent
    (terminalBridgeMachine machine) input
  have hRun := run_blankEquivalent
    (compileWorkMachine (terminalBridgeMachine machine))
    ((pipelineRawTimeBound targetBound).eval (BitString.size input)) hStart
  rw [hCompiled] at hRun
  exact ⟨outsideLeft, outsideRight, by
    simpa [pipelineMachine] using hRun⟩

private theorem natBeqFalseOfNe (left right : Nat)
    (h : left ≠ right) : (left == right) = false := by
  cases hBool : (left == right) with
  | false => rfl
  | true => exact False.elim (h ((nat_beq_true_iff left right).mp hBool))

/-- At the exact end of a supplied target prefix the extended work machine is
still in the simulator namespace, hence reports timeout. -/
theorem simulationPrefix_workBoundedDecide_timeout
    (machine : Machine) (steps : Nat) (input : BitString)
    (final : Configuration)
    (hRaw : PipelineMachineSimulation.rawRunExact? machine steps
      (startConfig machine input) = some final) :
    workBoundedDecide (terminalBridgeMachine machine)
        (simulationPrefixWorkSteps input steps)
        (rawInputWorkTape input) = .timeout := by
  rcases simulationPrefix_workRunExact_of_rawRunExact
      machine steps input final hRaw with
    ⟨workFinal, hBridgeExact, _⟩
  have hExtended := bridged_workRunExact_of_exact machine
    (simulationPrefixWorkSteps input steps)
    (workStartConfiguration (bridgedMachine machine)
      (rawInputWorkTape input))
    (renameConfiguration simulationState workFinal) hBridgeExact
  have hExtended' : workRunExact? (terminalBridgeMachine machine)
      (simulationPrefixWorkSteps input steps)
      (workStartConfiguration (terminalBridgeMachine machine)
        (rawInputWorkTape input)) =
      some (renameConfiguration simulationState workFinal) := by
    simpa [workStartConfiguration, bridgedMachine, terminalBridgeMachine]
      using hExtended
  have hRun := workRun_eq_of_workRunExact
    (terminalBridgeMachine machine)
    (simulationPrefixWorkSteps input steps)
    (workStartConfiguration (terminalBridgeMachine machine)
      (rawInputWorkTape input))
    (renameConfiguration simulationState workFinal) hExtended'
  have hAccept : simulationState workFinal.state ≠
      (terminalBridgeMachine machine).acceptState := by
    simpa only [terminalBridgeMachine, acceptingPackerState] using
      (simulationState_ne_handoffState workFinal.state
        (acceptingHandoffState
          TerminalOutputPacker.terminalOutputPacker.acceptState))
  have hReject : simulationState workFinal.state ≠
      (terminalBridgeMachine machine).rejectState := by
    simpa only [terminalBridgeMachine, rejectingPackerState] using
      (simulationState_ne_handoffState workFinal.state
        (rejectingHandoffState
          TerminalOutputPacker.terminalOutputPacker.acceptState))
  unfold workBoundedDecide
  rw [hRun]
  change
    (if (simulationState workFinal.state ==
        (terminalBridgeMachine machine).acceptState) = true then
      WorkVerdict.accept
     else if (simulationState workFinal.state ==
        (terminalBridgeMachine machine).rejectState) = true then
      WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout
  rw [natBeqFalseOfNe _ _ hAccept,
    natBeqFalseOfNe _ _ hReject]
  rfl

/-- A stuck nonhalting target endpoint remains timeout and is never
reclassified as rejection. -/
theorem pipeline_timeout_of_stuck_rawRunExact
    (machine : Machine) (steps : Nat) (input : BitString)
    (final : Configuration)
    (hRaw : PipelineMachineSimulation.rawRunExact? machine steps
      (startConfig machine input) = some final)
    (_hNonhalting : machine.isHalted final = false)
    (_hStuck : step? machine final = none) :
    workBoundedDecide (terminalBridgeMachine machine)
        (simulationPrefixWorkSteps input steps)
        (rawInputWorkTape input) = .timeout := by
  exact simulationPrefix_workBoundedDecide_timeout
    machine steps input final hRaw

/-- If the target halts at its advertised budget, the one literal all-input
pipeline has exactly the same verdict and ordinary raw output. -/
theorem pipeline_correct
    (machine : Machine) (targetBound : NatPolynomial) (input : BitString)
    (hHalts : boundedDecide machine
      (targetBound.eval (BitString.size input)) input ≠ .timeout) :
    boundedDecide (pipelineMachine machine)
        ((pipelineRawTimeBound targetBound).eval (BitString.size input))
        input =
        boundedDecide machine
          (targetBound.eval (BitString.size input)) input ∧
      machineOutput (pipelineMachine machine)
        ((pipelineRawTimeBound targetBound).eval (BitString.size input))
        input =
        machineOutput machine
          (targetBound.eval (BitString.size input)) input := by
  let fuel := targetBound.eval (BitString.size input)
  let final := run machine fuel (startConfig machine input)
  rcases PipelineMachineSimulation.rawRunExact?_exists_le_run
      machine fuel (startConfig machine input) with
    ⟨steps, hSteps, hRaw⟩
  have hRaw' : PipelineMachineSimulation.rawRunExact? machine steps
      (startConfig machine input) = some final := by
    simpa [fuel, final] using hRaw
  have hSteps' : steps ≤ targetBound.eval (BitString.size input) := by
    simpa [fuel] using hSteps
  cases hVerdict : boundedDecide machine fuel input with
  | accept =>
      have hAccept : final.state = machine.acceptState := by
        apply (boundedDecide_accept_iff_final machine fuel input).1
        exact hVerdict
      rcases run_pipeline_accept_at_bound_of_rawRunExact
          machine targetBound steps input final hSteps' hRaw' hAccept with
        ⟨outsideLeft, outsideRight, hRun⟩
      let packedFinal := renameConfiguration acceptingPackerState
        (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
          final.tape.outputBits outsideLeft outsideRight)
      have hPackedAccept : packedFinal.state =
          (terminalBridgeMachine machine).acceptState := by
        exact acceptingTerminalFinal_state_eq_accept machine
          final.tape.outputBits outsideLeft outsideRight
      have hEncodedAccept :
          (encodeWorkConfiguration packedFinal).state =
            (pipelineMachine machine).acceptState := by
        change
          (encodeWorkConfiguration packedFinal).state =
            (compileWorkMachine (terminalBridgeMachine machine)).acceptState
        exact (encodeWorkConfiguration_accept_iff
          (terminalBridgeMachine machine) packedFinal).2 hPackedAccept
      have hPipelineAccept :
          boundedDecide (pipelineMachine machine)
              ((pipelineRawTimeBound targetBound).eval
                (BitString.size input)) input = .accept := by
        apply (boundedDecide_accept_iff_final
          (pipelineMachine machine)
          ((pipelineRawTimeBound targetBound).eval
            (BitString.size input)) input).2
        exact hRun.1.trans hEncodedAccept
      constructor
      · rw [hPipelineAccept]
      · unfold machineOutput
        have hBlankOutput := Tape.outputBits_eq_of_blankEquivalent hRun.2
        have hOutput := acceptingTerminal_output_eq final.tape.outputBits
          outsideLeft outsideRight
        change Tape.outputBits
            (run (pipelineMachine machine)
              ((pipelineRawTimeBound targetBound).eval
                (BitString.size input))
              (startConfig (pipelineMachine machine) input)).tape =
          Tape.outputBits
            (run machine (targetBound.eval (BitString.size input))
              (startConfig machine input)).tape
        calc
          Tape.outputBits
              (run (pipelineMachine machine)
                ((pipelineRawTimeBound targetBound).eval
                  (BitString.size input))
                (startConfig (pipelineMachine machine) input)).tape =
              Tape.outputBits (encodeWorkConfiguration packedFinal).tape :=
            hBlankOutput
          _ = final.tape.outputBits := by
            simpa [packedFinal, encodeWorkConfiguration] using hOutput
          _ = Tape.outputBits
              (run machine (targetBound.eval (BitString.size input))
                (startConfig machine input)).tape := by
            rfl
  | reject =>
      have hRejectFinal :=
        (boundedDecide_reject_iff_final machine fuel input).1 hVerdict
      have hReject : final.state = machine.rejectState := hRejectFinal.2
      have hDistinct : machine.rejectState ≠ machine.acceptState := by
        intro hEqual
        exact hRejectFinal.1 (hReject.trans hEqual)
      rcases run_pipeline_reject_at_bound_of_rawRunExact
          machine targetBound steps input final hDistinct hSteps' hRaw'
            hReject with
        ⟨outsideLeft, outsideRight, hRun⟩
      let packedFinal := renameConfiguration rejectingPackerState
        (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
          final.tape.outputBits outsideLeft outsideRight)
      have hPackedReject : packedFinal.state =
          (terminalBridgeMachine machine).rejectState := by
        exact rejectingTerminalFinal_state_eq_reject machine
          final.tape.outputBits outsideLeft outsideRight
      have hPackedNotAccept : packedFinal.state ≠
          (terminalBridgeMachine machine).acceptState := by
        intro hPackedAccept
        exact terminalBridgeMachine_acceptState_ne_rejectState machine
          (hPackedAccept.symm.trans hPackedReject)
      have hEncodedReject :
          (encodeWorkConfiguration packedFinal).state =
            (pipelineMachine machine).rejectState := by
        change
          (encodeWorkConfiguration packedFinal).state =
            (compileWorkMachine (terminalBridgeMachine machine)).rejectState
        exact (encodeWorkConfiguration_reject_iff
          (terminalBridgeMachine machine) packedFinal).2 hPackedReject
      have hEncodedNotAccept :
          (encodeWorkConfiguration packedFinal).state ≠
            (pipelineMachine machine).acceptState := by
        intro hEncodedAccept
        have hWorkAccept := (encodeWorkConfiguration_accept_iff
          (terminalBridgeMachine machine) packedFinal).1 hEncodedAccept
        exact hPackedNotAccept hWorkAccept
      have hPipelineReject :
          boundedDecide (pipelineMachine machine)
              ((pipelineRawTimeBound targetBound).eval
                (BitString.size input)) input = .reject := by
        apply (boundedDecide_reject_iff_final
          (pipelineMachine machine)
          ((pipelineRawTimeBound targetBound).eval
            (BitString.size input)) input).2
        constructor
        · intro hPipelineAccept
          exact hEncodedNotAccept (hRun.1.symm.trans hPipelineAccept)
        · exact hRun.1.trans hEncodedReject
      constructor
      · rw [hPipelineReject]
      · unfold machineOutput
        have hBlankOutput := Tape.outputBits_eq_of_blankEquivalent hRun.2
        have hOutput := rejectingTerminal_output_eq final.tape.outputBits
          outsideLeft outsideRight
        change Tape.outputBits
            (run (pipelineMachine machine)
              ((pipelineRawTimeBound targetBound).eval
                (BitString.size input))
              (startConfig (pipelineMachine machine) input)).tape =
          Tape.outputBits
            (run machine (targetBound.eval (BitString.size input))
              (startConfig machine input)).tape
        calc
          Tape.outputBits
              (run (pipelineMachine machine)
                ((pipelineRawTimeBound targetBound).eval
                  (BitString.size input))
                (startConfig (pipelineMachine machine) input)).tape =
              Tape.outputBits (encodeWorkConfiguration packedFinal).tape :=
            hBlankOutput
          _ = final.tape.outputBits := by
            simpa [packedFinal, encodeWorkConfiguration] using hOutput
          _ = Tape.outputBits
              (run machine (targetBound.eval (BitString.size input))
                (startConfig machine input)).tape := by
            rfl
  | timeout =>
      exact False.elim (hHalts (by simpa [fuel] using hVerdict))

/-- Exact verdict preservation for every input of a proof-bearing target. -/
theorem pipeline_boundedDecide_eq
    {language : BitString → Prop}
    (target : PolynomialTimeMachine language) (input : BitString) :
    boundedDecide (pipelineMachine target.machine)
        ((pipelineRawTimeBound target.timeBound).eval (BitString.size input))
        input =
      boundedDecide target.machine
        (target.timeBound.eval (BitString.size input)) input := by
  exact (pipeline_correct target.machine target.timeBound input
    (target.haltsWithin input)).1

/-- Exact ordinary blank-delimited output preservation for every input. -/
theorem pipeline_machineOutput_eq
    {language : BitString → Prop}
    (target : PolynomialTimeMachine language) (input : BitString) :
    machineOutput (pipelineMachine target.machine)
        ((pipelineRawTimeBound target.timeBound).eval (BitString.size input))
        input =
      machineOutput target.machine
        (target.timeBound.eval (BitString.size input)) input := by
  exact (pipeline_correct target.machine target.timeBound input
    (target.haltsWithin input)).2

/-- The all-input compiled run cannot time out at its external polynomial
budget. -/
theorem pipeline_ne_timeout
    {language : BitString → Prop}
    (target : PolynomialTimeMachine language) (input : BitString) :
    boundedDecide (pipelineMachine target.machine)
        ((pipelineRawTimeBound target.timeBound).eval (BitString.size input))
        input ≠ .timeout := by
  rw [pipeline_boundedDecide_eq target input]
  exact target.haltsWithin input

/-- Acceptance by the all-input compiler is exactly the target language. -/
theorem pipeline_accepts_iff
    {language : BitString → Prop}
    (target : PolynomialTimeMachine language) (input : BitString) :
    boundedDecide (pipelineMachine target.machine)
        ((pipelineRawTimeBound target.timeBound).eval (BitString.size input))
        input = .accept ↔ language input := by
  rw [pipeline_boundedDecide_eq target input]
  exact target.accepts_iff input

/-- Package the all-input compiler as another raw polynomial-time machine for
the same language. -/
def toPolynomialTimeMachine
    {language : BitString → Prop}
    (target : PolynomialTimeMachine language) :
    PolynomialTimeMachine language :=
  { machine := pipelineMachine target.machine
    timeBound := pipelineRawTimeBound target.timeBound
    haltsWithin := pipeline_ne_timeout target
    accepts_iff := pipeline_accepts_iff target }

/-!
## Exact boundary

This all-input compiler wraps one already raw `PolynomialTimeMachine`.
`PipelineRefinement` uses it together with the sequential compiler to close
the concrete complexity machine link, but this module does not establish
CNF-SAT in P, CNF-SAT NP-completeness, `PNP.Main.p_eq_np`, or P = NP.  The
publication gate remains false.
-/

end PipelineCompiler

end PNP.Concrete
