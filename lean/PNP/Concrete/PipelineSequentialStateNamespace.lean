/-
Copyright (c) 2026 PNP Labs.

Collision-free outer namespaces for literal sequential composition of two
already-audited pipeline work machines.

The first component is the all-input framer/simulator/represented-handoff
machine.  Its accepting and rejecting handoff endpoints both launch the
second component at the lifted simulator start.  The second component is the
existing simulator/handoff/terminal-packer machine.  Renaming the complete
component tables, rather than rebuilding their internal stages, preserves
all previously proved lookup isolation while making the two component images
disjoint.

This file proves only finite rule-table isolation, local-step transport, and
the two possible first-to-second launches.  It does not prove an end-to-end
trace, an external polynomial, a RawRefinement, CNFSAT in P, NP-completeness,
or P = NP.
-/

import PNP.Concrete.PipelineCompiler

namespace PNP.Concrete

namespace PipelineSequentialStateNamespace

open PipelineStateNamespace PipelineStageBridges PipelineTerminalBridge

/-! ### Two collision-free outer component images -/

/-- Outer image containing the all-input first framer, simulator, and
represented-output handoff. -/
def firstPipelineState (state : Nat) : Nat := inputState state

/-- Outer image containing the second simulator, represented-output handoff,
and terminal output packer. -/
def secondPipelineState (state : Nat) : Nat := simulationState state

theorem firstPipelineState_injective : Function.Injective firstPipelineState :=
  inputState_injective

theorem secondPipelineState_injective :
    Function.Injective secondPipelineState :=
  simulationState_injective

theorem firstPipelineState_ne_secondPipelineState (left right : Nat) :
    firstPipelineState left ≠ secondPipelineState right :=
  inputState_ne_simulationState left right

/-- The complete first component, injectively renamed into its outer image. -/
def renamedFirstPipeline (first : Machine) : WorkMachine :=
  renameMachine firstPipelineState (bridgedMachine first)

/-- The complete second component, injectively renamed into its outer image. -/
def renamedSecondPipeline (second : Machine) : WorkMachine :=
  renameMachine secondPipelineState (terminalBridgeMachine second)

/-! ### Literal first-to-second launch table -/

/-- A first-component accept launches the second lifted simulator.  The first
verdict is deliberately not retained: function composition uses the first
machine's output for both designated halts. -/
def firstAcceptLaunchRules (first second : Machine) : List WorkRule :=
  launchRules
    (firstPipelineState (bridgedMachine first).acceptState)
    (secondPipelineState
      (simulationState
        (PipelineMachineSimulation.liftMachine second).startState))

/-- A first-component reject launches the same second lifted simulator. -/
def firstRejectLaunchRules (first second : Machine) : List WorkRule :=
  launchRules
    (firstPipelineState (bridgedMachine first).rejectState)
    (secondPipelineState
      (simulationState
        (PipelineMachineSimulation.liftMachine second).startState))

/-- One literal finite table: both launch tables followed by the two renamed
component tables. -/
def sequentialRules (first second : Machine) : List WorkRule :=
  firstAcceptLaunchRules first second ++
    (firstRejectLaunchRules first second ++
      ((bridgedMachine first).rules.map (renameRule firstPipelineState) ++
        (terminalBridgeMachine second).rules.map
          (renameRule secondPipelineState)))

/-- The literal work machine for sequential execution.  Only the second
component's terminal packer endpoints are global halts. -/
def sequentialWorkMachine (first second : Machine) : WorkMachine :=
  { rules := sequentialRules first second
    startState := firstPipelineState (bridgedMachine first).startState
    acceptState := secondPipelineState
      (terminalBridgeMachine second).acceptState
    rejectState := secondPipelineState
      (terminalBridgeMachine second).rejectState }

theorem sequentialWorkMachine_acceptState_ne_rejectState
    (first second : Machine) :
    (sequentialWorkMachine first second).acceptState ≠
      (sequentialWorkMachine first second).rejectState := by
  intro h
  have hMapped :
      secondPipelineState (terminalBridgeMachine second).acceptState =
        secondPipelineState (terminalBridgeMachine second).rejectState := by
    simpa only [sequentialWorkMachine] using h
  have hInner := secondPipelineState_injective hMapped
  exact terminalBridgeMachine_acceptState_ne_rejectState second hInner

/-! ### Global halting classification -/

theorem state_ne_accept_of_isHalted_false (machine : WorkMachine)
    (config : WorkConfiguration)
    (hHalted : machine.isHalted config = false) :
    config.state ≠ machine.acceptState := by
  intro hState
  unfold WorkMachine.isHalted at hHalted
  rw [hState] at hHalted
  have hRefl : (machine.acceptState == machine.acceptState) = true :=
    (nat_beq_true_iff _ _).mpr rfl
  rw [hRefl] at hHalted
  contradiction

theorem state_ne_reject_of_isHalted_false (machine : WorkMachine)
    (config : WorkConfiguration)
    (hHalted : machine.isHalted config = false) :
    config.state ≠ machine.rejectState := by
  intro hState
  unfold WorkMachine.isHalted at hHalted
  rw [hState] at hHalted
  have hRefl : (machine.rejectState == machine.rejectState) = true :=
    (nat_beq_true_iff _ _).mpr rfl
  cases hAccept : (machine.rejectState == machine.acceptState) with
  | false =>
      rw [hAccept, hRefl] at hHalted
      contradiction
  | true =>
      rw [hAccept] at hHalted
      contradiction

theorem nat_beq_false_of_ne (left right : Nat) (hNe : left ≠ right) :
    (left == right) = false := by
  cases hEq : (left == right) with
  | false => rfl
  | true =>
      exact False.elim (hNe ((nat_beq_true_iff left right).mp hEq))

/-- No state in the first outer image is a global halt. -/
theorem sequentialWorkMachine_isHalted_first_false
    (first second : Machine) (config : WorkConfiguration) :
    (sequentialWorkMachine first second).isHalted
      (renameConfiguration firstPipelineState config) = false := by
  unfold WorkMachine.isHalted sequentialWorkMachine renameConfiguration
  rw [nat_beq_false_of_ne _ _
      (firstPipelineState_ne_secondPipelineState _ _),
    nat_beq_false_of_ne _ _
      (firstPipelineState_ne_secondPipelineState _ _)]
  rfl

/-- A locally nonhalting second-component state is also globally nonhalting. -/
theorem sequentialWorkMachine_isHalted_second_false_of_local
    (first second : Machine) (config : WorkConfiguration)
    (hLocal : (terminalBridgeMachine second).isHalted config = false) :
    (sequentialWorkMachine first second).isHalted
      (renameConfiguration secondPipelineState config) = false := by
  have hAccept := state_ne_accept_of_isHalted_false
    (terminalBridgeMachine second) config hLocal
  have hReject := state_ne_reject_of_isHalted_false
    (terminalBridgeMachine second) config hLocal
  have hGlobalAccept : secondPipelineState config.state ≠
      secondPipelineState (terminalBridgeMachine second).acceptState := by
    intro h
    exact hAccept (secondPipelineState_injective h)
  have hGlobalReject : secondPipelineState config.state ≠
      secondPipelineState (terminalBridgeMachine second).rejectState := by
    intro h
    exact hReject (secondPipelineState_injective h)
  unfold WorkMachine.isHalted sequentialWorkMachine renameConfiguration
  rw [nat_beq_false_of_ne _ _ hGlobalAccept,
    nat_beq_false_of_ne _ _ hGlobalReject]
  rfl

/-! ### First-match lookup isolation -/

/-- Away from its two designated endpoints, first-component lookup is exactly
the first renamed component lookup. -/
theorem findWorkRule_sequential_first_of_some
    (first second : Machine) (state : Nat) (symbol : WorkSymbol)
    (rule : WorkRule)
    (hAccept : state ≠ (bridgedMachine first).acceptState)
    (hReject : state ≠ (bridgedMachine first).rejectState)
    (hFind : findWorkRule (bridgedMachine first).rules state symbol =
      some rule) :
    findWorkRule (sequentialWorkMachine first second).rules
        (firstPipelineState state) symbol =
      some (renameRule firstPipelineState rule) := by
  have hAcceptLaunch : findWorkRule (firstAcceptLaunchRules first second)
      (firstPipelineState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    intro h
    exact hAccept (firstPipelineState_injective h).symm
  have hRejectLaunch : findWorkRule (firstRejectLaunchRules first second)
      (firstPipelineState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    intro h
    exact hReject (firstPipelineState_injective h).symm
  have hRenamed := findWorkRule_rename firstPipelineState
    firstPipelineState_injective (bridgedMachine first).rules state symbol
  rw [hFind] at hRenamed
  unfold sequentialWorkMachine sequentialRules
  rw [findWorkRule_append_of_none _ _ _ _ hAcceptLaunch,
    findWorkRule_append_of_none _ _ _ _ hRejectLaunch]
  exact findWorkRule_append_of_some _ _ _ _ _ hRenamed

/-- Second-component lookup is isolated from both first launch tables and the
entire first component. -/
theorem findWorkRule_sequential_second_of_some
    (first second : Machine) (state : Nat) (symbol : WorkSymbol)
    (rule : WorkRule)
    (hFind : findWorkRule (terminalBridgeMachine second).rules state symbol =
      some rule) :
    findWorkRule (sequentialWorkMachine first second).rules
        (secondPipelineState state) symbol =
      some (renameRule secondPipelineState rule) := by
  have hAcceptLaunch : findWorkRule (firstAcceptLaunchRules first second)
      (secondPipelineState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact firstPipelineState_ne_secondPipelineState _ _
  have hRejectLaunch : findWorkRule (firstRejectLaunchRules first second)
      (secondPipelineState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact firstPipelineState_ne_secondPipelineState _ _
  have hFirstRules : findWorkRule
      ((bridgedMachine first).rules.map (renameRule firstPipelineState))
      (secondPipelineState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact firstPipelineState_ne_secondPipelineState _ _
  have hRenamed := findWorkRule_rename secondPipelineState
    secondPipelineState_injective (terminalBridgeMachine second).rules
    state symbol
  rw [hFind] at hRenamed
  unfold sequentialWorkMachine sequentialRules
  rw [findWorkRule_append_of_none _ _ _ _ hAcceptLaunch,
    findWorkRule_append_of_none _ _ _ _ hRejectLaunch,
    findWorkRule_append_of_none _ _ _ _ hFirstRules]
  exact hRenamed

/-! ### Local transition and exact-trace transport -/

theorem first_workStep?_of_some (first second : Machine)
    (config next : WorkConfiguration)
    (hStep : workStep? (bridgedMachine first) config = some next) :
    workStep? (sequentialWorkMachine first second)
        (renameConfiguration firstPipelineState config) =
      some (renameConfiguration firstPipelineState next) := by
  rcases workStep?_some_exists (bridgedMachine first) config next hStep with
    ⟨rule, hHalted, hFind, hNext⟩
  have hAccept := state_ne_accept_of_isHalted_false
    (bridgedMachine first) config hHalted
  have hReject := state_ne_reject_of_isHalted_false
    (bridgedMachine first) config hHalted
  have hGlobalHalted := sequentialWorkMachine_isHalted_first_false
    first second config
  have hGlobalFind := findWorkRule_sequential_first_of_some
    first second config.state config.tape.head rule hAccept hReject hFind
  have hGlobalStep := workStep?_eq_apply_of_find
    (sequentialWorkMachine first second)
    (renameConfiguration firstPipelineState config)
    (renameRule firstPipelineState rule) hGlobalHalted hGlobalFind
  calc
    workStep? (sequentialWorkMachine first second)
        (renameConfiguration firstPipelineState config) =
        some (applyWorkRule (renameRule firstPipelineState rule)
          (renameConfiguration firstPipelineState config)) := hGlobalStep
    _ = some (renameConfiguration firstPipelineState
          (applyWorkRule rule config)) :=
      congrArg Option.some
        (applyWorkRule_rename firstPipelineState rule config)
    _ = some (renameConfiguration firstPipelineState next) :=
      congrArg (fun value => some
        (renameConfiguration firstPipelineState value)) hNext.symm

theorem second_workStep?_of_some (first second : Machine)
    (config next : WorkConfiguration)
    (hStep : workStep? (terminalBridgeMachine second) config = some next) :
    workStep? (sequentialWorkMachine first second)
        (renameConfiguration secondPipelineState config) =
      some (renameConfiguration secondPipelineState next) := by
  rcases workStep?_some_exists (terminalBridgeMachine second)
      config next hStep with ⟨rule, hHalted, hFind, hNext⟩
  have hGlobalHalted :=
    sequentialWorkMachine_isHalted_second_false_of_local
      first second config hHalted
  have hGlobalFind := findWorkRule_sequential_second_of_some
    first second config.state config.tape.head rule hFind
  have hGlobalStep := workStep?_eq_apply_of_find
    (sequentialWorkMachine first second)
    (renameConfiguration secondPipelineState config)
    (renameRule secondPipelineState rule) hGlobalHalted hGlobalFind
  calc
    workStep? (sequentialWorkMachine first second)
        (renameConfiguration secondPipelineState config) =
        some (applyWorkRule (renameRule secondPipelineState rule)
          (renameConfiguration secondPipelineState config)) := hGlobalStep
    _ = some (renameConfiguration secondPipelineState
          (applyWorkRule rule config)) :=
      congrArg Option.some
        (applyWorkRule_rename secondPipelineState rule config)
    _ = some (renameConfiguration secondPipelineState next) :=
      congrArg (fun value => some
        (renameConfiguration secondPipelineState value)) hNext.symm

theorem workRunExact?_transport
    (source target : WorkMachine) (encode : Nat → Nat)
    (hStep : ∀ config next,
      workStep? source config = some next →
      workStep? target (renameConfiguration encode config) =
        some (renameConfiguration encode next))
    (steps : Nat) (start final : WorkConfiguration)
    (hRun : workRunExact? source steps start = some final) :
    workRunExact? target steps (renameConfiguration encode start) =
      some (renameConfiguration encode final) := by
  induction steps generalizing start with
  | zero =>
      change some start = some final at hRun
      have hStart : start = final := Option.some.inj hRun
      rw [hStart]
      rfl
  | succ steps ih =>
      cases hLocalStep : workStep? source start with
      | none =>
          change
            (match workStep? source start with
             | none => none
             | some next => workRunExact? source steps next) =
              some final at hRun
          rw [hLocalStep] at hRun
          contradiction
      | some next =>
          have hTail : workRunExact? source steps next = some final := by
            change
              (match workStep? source start with
               | none => none
               | some next => workRunExact? source steps next) =
                some final at hRun
            rw [hLocalStep] at hRun
            exact hRun
          change
            (match workStep? target (renameConfiguration encode start) with
             | none => none
             | some next => workRunExact? target steps next) =
              some (renameConfiguration encode final)
          rw [hStep start next hLocalStep]
          exact ih next hTail

theorem first_workRunExact_of_exact (first second : Machine)
    (steps : Nat) (start final : WorkConfiguration)
    (hRun : workRunExact? (bridgedMachine first) steps start = some final) :
    workRunExact? (sequentialWorkMachine first second) steps
        (renameConfiguration firstPipelineState start) =
      some (renameConfiguration firstPipelineState final) := by
  exact workRunExact?_transport (bridgedMachine first)
    (sequentialWorkMachine first second) firstPipelineState
    (first_workStep?_of_some first second) steps start final hRun

theorem second_workRunExact_of_exact (first second : Machine)
    (steps : Nat) (start final : WorkConfiguration)
    (hRun : workRunExact? (terminalBridgeMachine second) steps start =
      some final) :
    workRunExact? (sequentialWorkMachine first second) steps
        (renameConfiguration secondPipelineState start) =
      some (renameConfiguration secondPipelineState final) := by
  exact workRunExact?_transport (terminalBridgeMachine second)
    (sequentialWorkMachine first second) secondPipelineState
    (second_workStep?_of_some first second) steps start final hRun

/-! ### Exact first-verdict launches -/

theorem firstAcceptLaunch_workStep (first second : Machine)
    (config : WorkConfiguration)
    (hState : config.state = (bridgedMachine first).acceptState) :
    workStep? (sequentialWorkMachine first second)
        (renameConfiguration firstPipelineState config) =
      some
        { state := secondPipelineState
            (simulationState
              (PipelineMachineSimulation.liftMachine second).startState)
          tape := config.tape } := by
  have hHalted := sequentialWorkMachine_isHalted_first_false
    first second config
  have hLaunch := findWorkRule_launchRules
    (firstPipelineState (bridgedMachine first).acceptState)
    (secondPipelineState
      (simulationState
        (PipelineMachineSimulation.liftMachine second).startState))
    config.tape.head
  have hFind : findWorkRule (sequentialWorkMachine first second).rules
      (firstPipelineState config.state) config.tape.head =
        some (launchRule
          (firstPipelineState (bridgedMachine first).acceptState)
          (secondPipelineState
            (simulationState
              (PipelineMachineSimulation.liftMachine second).startState))
          config.tape.head) := by
    unfold sequentialWorkMachine sequentialRules
    simpa [firstAcceptLaunchRules, hState] using
      (findWorkRule_append_of_some _ _ _ _ _ hLaunch)
  have hStep := workStep?_eq_apply_of_find
    (sequentialWorkMachine first second)
    (renameConfiguration firstPipelineState config)
    (launchRule
      (firstPipelineState (bridgedMachine first).acceptState)
      (secondPipelineState
        (simulationState
          (PipelineMachineSimulation.liftMachine second).startState))
      config.tape.head) hHalted hFind
  simpa [hState, launchRule, applyWorkRule, WorkTape.write, WorkTape.move,
    renameConfiguration] using hStep

theorem firstRejectLaunch_workStep (first second : Machine)
    (config : WorkConfiguration)
    (hState : config.state = (bridgedMachine first).rejectState) :
    workStep? (sequentialWorkMachine first second)
        (renameConfiguration firstPipelineState config) =
      some
        { state := secondPipelineState
            (simulationState
              (PipelineMachineSimulation.liftMachine second).startState)
          tape := config.tape } := by
  have hHalted := sequentialWorkMachine_isHalted_first_false
    first second config
  have hDistinct := bridgedMachine_acceptState_ne_rejectState first
  have hAcceptNone : findWorkRule (firstAcceptLaunchRules first second)
      (firstPipelineState config.state) config.tape.head = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    intro h
    have hInner := firstPipelineState_injective h
    exact hDistinct (hInner.trans hState)
  have hLaunch := findWorkRule_launchRules
    (firstPipelineState (bridgedMachine first).rejectState)
    (secondPipelineState
      (simulationState
        (PipelineMachineSimulation.liftMachine second).startState))
    config.tape.head
  have hFind : findWorkRule (sequentialWorkMachine first second).rules
      (firstPipelineState config.state) config.tape.head =
        some (launchRule
          (firstPipelineState (bridgedMachine first).rejectState)
          (secondPipelineState
            (simulationState
              (PipelineMachineSimulation.liftMachine second).startState))
          config.tape.head) := by
    unfold sequentialWorkMachine sequentialRules
    rw [findWorkRule_append_of_none _ _ _ _ hAcceptNone]
    simpa [firstRejectLaunchRules, hState] using
      (findWorkRule_append_of_some _ _ _ _ _ hLaunch)
  have hStep := workStep?_eq_apply_of_find
    (sequentialWorkMachine first second)
    (renameConfiguration firstPipelineState config)
    (launchRule
      (firstPipelineState (bridgedMachine first).rejectState)
      (secondPipelineState
        (simulationState
          (PipelineMachineSimulation.liftMachine second).startState))
      config.tape.head) hHalted hFind
  simpa [hState, launchRule, applyWorkRule, WorkTape.write, WorkTape.move,
    renameConfiguration] using hStep

/-!
The two component state images and every internal stage image are now
collision-free in one literal finite table.  End-to-end execution and
external polynomial accounting are intentionally deferred.
-/

end PipelineSequentialStateNamespace

end PNP.Concrete
