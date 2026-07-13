/-
Copyright (c) 2026 PNP Labs.

Literal launch transitions from the represented-output handoff into the
terminal raw-output packer.

The accepting and rejecting handoff copies launch two disjoint copies of the
same finite packer.  The exact local packer trace is transported through the
combined first-match rule table, retaining the target verdict in the final
control-state image.  Every represented canonical handoff endpoint therefore
has an exact launch-and-pack trace with the already-proved output and runtime.

The earlier framer/simulator/handoff trace is transported into this extended
machine and composed with the terminal suffix, but only from a supplied exact
target execution.  This module therefore does not construct a complete
pipeline RawRefinement, prove target termination, give a polynomial in
external encoded input length, prove CNFSAT in P or NP-completeness, or prove
P = NP.
-/

import PNP.Concrete.PipelineStageBridges
import PNP.Concrete.TerminalOutputPacker

namespace PNP.Concrete

namespace PipelineTerminalBridge

open PipelineStateNamespace PipelineStageBridges PipelineTape

/-! ### Verdict-indexed terminal-packer namespaces -/

/-- Terminal-packer state image following an accepting handoff. -/
def acceptingPackerState (state : Nat) : Nat :=
  handoffState (acceptingHandoffState state)

/-- Terminal-packer state image following a rejecting handoff. -/
def rejectingPackerState (state : Nat) : Nat :=
  handoffState (rejectingHandoffState state)

theorem acceptingPackerState_injective :
    Function.Injective acceptingPackerState := by
  intro left right h
  exact acceptingHandoffState_injective (handoffState_injective h)

theorem rejectingPackerState_injective :
    Function.Injective rejectingPackerState := by
  intro left right h
  exact rejectingHandoffState_injective (handoffState_injective h)

theorem acceptingPackerState_ne_rejectingPackerState
    (left right : Nat) :
    acceptingPackerState left ≠ rejectingPackerState right := by
  intro h
  exact acceptingHandoffState_ne_rejectingHandoffState left right
    (handoffState_injective h)

theorem acceptingHandoffState_ne_acceptingPackerState
    (left right : Nat) :
    acceptingHandoffState left ≠ acceptingPackerState right := by
  intro h
  have hInner := handoffState_injective h
  exact inputState_ne_handoffState left (inputState right)
    (by simpa [acceptingHandoffState] using hInner)

theorem acceptingHandoffState_ne_rejectingPackerState
    (left right : Nat) :
    acceptingHandoffState left ≠ rejectingPackerState right := by
  intro h
  have hInner := handoffState_injective h
  exact inputState_ne_handoffState left (simulationState right)
    (by simpa [rejectingHandoffState] using hInner)

theorem rejectingHandoffState_ne_acceptingPackerState
    (left right : Nat) :
    rejectingHandoffState left ≠ acceptingPackerState right := by
  intro h
  have hInner := handoffState_injective h
  exact simulationState_ne_handoffState left (inputState right)
    (by simpa [acceptingHandoffState] using hInner)

theorem rejectingHandoffState_ne_rejectingPackerState
    (left right : Nat) :
    rejectingHandoffState left ≠ rejectingPackerState right := by
  intro h
  have hInner := handoffState_injective h
  exact simulationState_ne_handoffState left (simulationState right)
    (by simpa [rejectingHandoffState] using hInner)

/-! ### Literal rule table and machine -/

def acceptingPackerLaunchRules : List WorkRule :=
  launchRules
    (acceptingHandoffState
      PipelineOutputHandoff.framedOutputHandoff.acceptState)
    (acceptingPackerState
      TerminalOutputPacker.terminalOutputPacker.startState)

def rejectingPackerLaunchRules : List WorkRule :=
  launchRules
    (rejectingHandoffState
      PipelineOutputHandoff.framedOutputHandoff.acceptState)
    (rejectingPackerState
      TerminalOutputPacker.terminalOutputPacker.startState)

def terminalBridgeRules (machine : Machine) : List WorkRule :=
  acceptingPackerLaunchRules ++
    (rejectingPackerLaunchRules ++
      (bridgedRules machine ++
        (TerminalOutputPacker.terminalOutputPacker.rules.map
            (renameRule acceptingPackerState) ++
          TerminalOutputPacker.terminalOutputPacker.rules.map
            (renameRule rejectingPackerState))))

/-- The finite extended machine.  Its only designated final states are the
accepting and rejecting copies of the terminal packer's accept state. -/
def terminalBridgeMachine (machine : Machine) : WorkMachine :=
  { rules := terminalBridgeRules machine
    startState := inputState PipelineInputFramer.pairedInputFramer.startState
    acceptState := acceptingPackerState
      TerminalOutputPacker.terminalOutputPacker.acceptState
    rejectState := rejectingPackerState
      TerminalOutputPacker.terminalOutputPacker.acceptState }

def terminalBridgeWorkSteps (bits : BitString) : Nat :=
  1 + TerminalOutputPacker.terminalOutputPackerWorkSteps bits

def terminalBridgeRawSteps (bits : BitString) : Nat :=
  6 * terminalBridgeWorkSteps bits

/-- Exact work cost of the complete literal trace induced by a supplied exact
target run.  This is not yet a polynomial in external encoded input length. -/
def suppliedTraceTerminalWorkSteps (left right : BitString)
    (sourceSteps : Nat) (finalTape : Tape) : Nat :=
  bridgedWorkSteps left right sourceSteps finalTape +
    terminalBridgeWorkSteps finalTape.outputBits

/-- Six raw transitions for every work transition in the supplied complete
trace. -/
def suppliedTraceTerminalRawSteps (left right : BitString)
    (sourceSteps : Nat) (finalTape : Tape) : Nat :=
  6 * suppliedTraceTerminalWorkSteps left right sourceSteps finalTape

/-- Raw bound for the one launch followed by the compiled terminal packer. -/
def terminalBridgeRawTimeBound : NatPolynomial :=
  .add TerminalOutputPacker.terminalOutputPackerRawTimeBound (.linear 0 6)

theorem terminalBridge_runtime_le (bits : BitString) :
    terminalBridgeRawSteps bits ≤
      terminalBridgeRawTimeBound.eval bits.length := by
  have hPacker := TerminalOutputPacker.terminalOutputPacker_runtime_le bits
  calc
    terminalBridgeRawSteps bits =
        6 + 6 * TerminalOutputPacker.terminalOutputPackerWorkSteps bits := by
      unfold terminalBridgeRawSteps terminalBridgeWorkSteps
      rw [Nat.mul_add, Nat.mul_one]
    _ ≤ 6 + TerminalOutputPacker.terminalOutputPackerRawTimeBound.eval
          bits.length := Nat.add_le_add_left hPacker 6
    _ = TerminalOutputPacker.terminalOutputPackerRawTimeBound.eval
          bits.length + 6 := Nat.add_comm _ _
    _ = terminalBridgeRawTimeBound.eval bits.length := by
      unfold terminalBridgeRawTimeBound
      rw [NatPolynomial.eval_add, NatPolynomial.eval_linear,
        Nat.zero_mul, Nat.zero_add]

/-! ### First-match isolation from the prior bridge table -/

private theorem findWorkRule_bridgedRules_none_acceptingPacker
    (machine : Machine) (state : Nat) (symbol : WorkSymbol) :
    findWorkRule (bridgedRules machine) (acceptingPackerState state) symbol =
      none := by
  have hInputLaunch : findWorkRule (inputLaunchRules machine)
      (acceptingPackerState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact inputState_ne_handoffState _ _
  have hAcceptLaunch : findWorkRule acceptingLaunchRules
      (acceptingPackerState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact simulationState_ne_handoffState _ _
  have hRejectLaunch : findWorkRule rejectingLaunchRules
      (acceptingPackerState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact simulationState_ne_handoffState _ _
  have hInputRules : findWorkRule
      (PipelineInputFramer.pairedInputFramer.rules.map
        (renameRule inputState)) (acceptingPackerState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact inputState_ne_handoffState _ _
  have hSimulationRules : findWorkRule
      ((PipelineMachineSimulation.liftMachine machine).rules.map
        (renameRule simulationState)) (acceptingPackerState state) symbol =
        none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact simulationState_ne_handoffState _ _
  have hAcceptingRules : findWorkRule
      (PipelineOutputHandoff.framedOutputHandoff.rules.map
        (renameRule acceptingHandoffState))
      (acceptingPackerState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact acceptingHandoffState_ne_acceptingPackerState _ _
  have hRejectingRules : findWorkRule
      (PipelineOutputHandoff.framedOutputHandoff.rules.map
        (renameRule rejectingHandoffState))
      (acceptingPackerState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact rejectingHandoffState_ne_acceptingPackerState _ _
  unfold bridgedRules
  rw [findWorkRule_append_of_none _ _ _ _ hInputLaunch,
    findWorkRule_append_of_none _ _ _ _ hAcceptLaunch,
    findWorkRule_append_of_none _ _ _ _ hRejectLaunch,
    findWorkRule_append_of_none _ _ _ _ hInputRules,
    findWorkRule_append_of_none _ _ _ _ hSimulationRules,
    findWorkRule_append_of_none _ _ _ _ hAcceptingRules]
  exact hRejectingRules

private theorem findWorkRule_bridgedRules_none_rejectingPacker
    (machine : Machine) (state : Nat) (symbol : WorkSymbol) :
    findWorkRule (bridgedRules machine) (rejectingPackerState state) symbol =
      none := by
  have hInputLaunch : findWorkRule (inputLaunchRules machine)
      (rejectingPackerState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact inputState_ne_handoffState _ _
  have hAcceptLaunch : findWorkRule acceptingLaunchRules
      (rejectingPackerState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact simulationState_ne_handoffState _ _
  have hRejectLaunch : findWorkRule rejectingLaunchRules
      (rejectingPackerState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact simulationState_ne_handoffState _ _
  have hInputRules : findWorkRule
      (PipelineInputFramer.pairedInputFramer.rules.map
        (renameRule inputState)) (rejectingPackerState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact inputState_ne_handoffState _ _
  have hSimulationRules : findWorkRule
      ((PipelineMachineSimulation.liftMachine machine).rules.map
        (renameRule simulationState)) (rejectingPackerState state) symbol =
        none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact simulationState_ne_handoffState _ _
  have hAcceptingRules : findWorkRule
      (PipelineOutputHandoff.framedOutputHandoff.rules.map
        (renameRule acceptingHandoffState))
      (rejectingPackerState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact acceptingHandoffState_ne_rejectingPackerState _ _
  have hRejectingRules : findWorkRule
      (PipelineOutputHandoff.framedOutputHandoff.rules.map
        (renameRule rejectingHandoffState))
      (rejectingPackerState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact rejectingHandoffState_ne_rejectingPackerState _ _
  unfold bridgedRules
  rw [findWorkRule_append_of_none _ _ _ _ hInputLaunch,
    findWorkRule_append_of_none _ _ _ _ hAcceptLaunch,
    findWorkRule_append_of_none _ _ _ _ hRejectLaunch,
    findWorkRule_append_of_none _ _ _ _ hInputRules,
    findWorkRule_append_of_none _ _ _ _ hSimulationRules,
    findWorkRule_append_of_none _ _ _ _ hAcceptingRules]
  exact hRejectingRules

theorem findWorkRule_terminalBridge_acceptingPacker_of_some
    (machine : Machine) (state : Nat) (symbol : WorkSymbol)
    (rule : WorkRule)
    (hFind : findWorkRule TerminalOutputPacker.terminalOutputPacker.rules
      state symbol = some rule) :
    findWorkRule (terminalBridgeMachine machine).rules
        (acceptingPackerState state) symbol =
      some (renameRule acceptingPackerState rule) := by
  have hAcceptLaunch : findWorkRule acceptingPackerLaunchRules
      (acceptingPackerState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact acceptingHandoffState_ne_acceptingPackerState _ _
  have hRejectLaunch : findWorkRule rejectingPackerLaunchRules
      (acceptingPackerState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact rejectingHandoffState_ne_acceptingPackerState _ _
  have hBridge := findWorkRule_bridgedRules_none_acceptingPacker
    machine state symbol
  have hRenamed := findWorkRule_rename acceptingPackerState
    acceptingPackerState_injective
    TerminalOutputPacker.terminalOutputPacker.rules state symbol
  rw [hFind] at hRenamed
  unfold terminalBridgeMachine terminalBridgeRules
  rw [findWorkRule_append_of_none _ _ _ _ hAcceptLaunch,
    findWorkRule_append_of_none _ _ _ _ hRejectLaunch,
    findWorkRule_append_of_none _ _ _ _ hBridge]
  exact findWorkRule_append_of_some _ _ _ _ _ hRenamed

theorem findWorkRule_terminalBridge_rejectingPacker_of_some
    (machine : Machine) (state : Nat) (symbol : WorkSymbol)
    (rule : WorkRule)
    (hFind : findWorkRule TerminalOutputPacker.terminalOutputPacker.rules
      state symbol = some rule) :
    findWorkRule (terminalBridgeMachine machine).rules
        (rejectingPackerState state) symbol =
      some (renameRule rejectingPackerState rule) := by
  have hAcceptLaunch : findWorkRule acceptingPackerLaunchRules
      (rejectingPackerState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact acceptingHandoffState_ne_rejectingPackerState _ _
  have hRejectLaunch : findWorkRule rejectingPackerLaunchRules
      (rejectingPackerState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact rejectingHandoffState_ne_rejectingPackerState _ _
  have hBridge := findWorkRule_bridgedRules_none_rejectingPacker
    machine state symbol
  have hAcceptingRules : findWorkRule
      (TerminalOutputPacker.terminalOutputPacker.rules.map
        (renameRule acceptingPackerState))
      (rejectingPackerState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact acceptingPackerState_ne_rejectingPackerState _ _
  have hRenamed := findWorkRule_rename rejectingPackerState
    rejectingPackerState_injective
    TerminalOutputPacker.terminalOutputPacker.rules state symbol
  rw [hFind] at hRenamed
  unfold terminalBridgeMachine terminalBridgeRules
  rw [findWorkRule_append_of_none _ _ _ _ hAcceptLaunch,
    findWorkRule_append_of_none _ _ _ _ hRejectLaunch,
    findWorkRule_append_of_none _ _ _ _ hBridge,
    findWorkRule_append_of_none _ _ _ _ hAcceptingRules]
  exact hRenamed

/-! ### Halt separation and exact local packer steps -/

private theorem state_ne_accept_of_not_halted
    (machine : WorkMachine) (config : WorkConfiguration)
    (hHalted : machine.isHalted config = false) :
    config.state ≠ machine.acceptState := by
  intro hState
  unfold WorkMachine.isHalted at hHalted
  rw [hState] at hHalted
  have hRefl : (machine.acceptState == machine.acceptState) = true :=
    (nat_beq_true_iff _ _).mpr rfl
  rw [hRefl] at hHalted
  contradiction

private theorem state_ne_reject_of_not_halted
    (machine : WorkMachine) (config : WorkConfiguration)
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
      rw [hAccept, hRefl] at hHalted
      contradiction

private theorem nat_beq_false_of_ne (left right : Nat)
    (h : left ≠ right) : (left == right) = false := by
  cases hBool : (left == right) with
  | false => rfl
  | true => exact False.elim (h ((nat_beq_true_iff left right).mp hBool))

/-! ### Transport of the prior literal bridge table -/

/-- Every successful step of the prior three-stage bridge remains literally
the same successful step in the extended terminal rule table.  The two new
launch tables cannot shadow such a step because their sources were the prior
machine's designated halts. -/
theorem bridged_workStep?_of_some (machine : Machine)
    (config next : WorkConfiguration)
    (hStep : workStep? (bridgedMachine machine) config = some next) :
    workStep? (terminalBridgeMachine machine) config = some next := by
  rcases workStep?_some_exists (bridgedMachine machine) config next hStep with
    ⟨rule, hBridgeHalted, hBridgeFind, hNext⟩
  have hNotBridgeAccept := state_ne_accept_of_not_halted
    (bridgedMachine machine) config hBridgeHalted
  have hNotBridgeReject := state_ne_reject_of_not_halted
    (bridgedMachine machine) config hBridgeHalted
  have hAcceptSource :
      acceptingHandoffState
          PipelineOutputHandoff.framedOutputHandoff.acceptState ≠
        config.state := by
    intro hState
    apply hNotBridgeAccept
    simpa [bridgedMachine] using hState.symm
  have hRejectSource :
      rejectingHandoffState
          PipelineOutputHandoff.framedOutputHandoff.acceptState ≠
        config.state := by
    intro hState
    apply hNotBridgeReject
    simpa [bridgedMachine] using hState.symm
  have hAcceptLaunch : findWorkRule acceptingPackerLaunchRules
      config.state config.tape.head = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact hAcceptSource
  have hRejectLaunch : findWorkRule rejectingPackerLaunchRules
      config.state config.tape.head = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact hRejectSource
  have hNotTerminalAccept : config.state ≠
      (terminalBridgeMachine machine).acceptState := by
    intro hState
    have hNone := findWorkRule_bridgedRules_none_acceptingPacker
      machine TerminalOutputPacker.terminalOutputPacker.acceptState
        config.tape.head
    have hState' : config.state = acceptingPackerState
        TerminalOutputPacker.terminalOutputPacker.acceptState := by
      simpa [terminalBridgeMachine] using hState
    have hBridgeFind' : findWorkRule (bridgedRules machine)
        (acceptingPackerState
          TerminalOutputPacker.terminalOutputPacker.acceptState)
        config.tape.head = some rule := by
      simpa [bridgedMachine, hState'] using hBridgeFind
    rw [hNone] at hBridgeFind'
    cases hBridgeFind'
  have hNotTerminalReject : config.state ≠
      (terminalBridgeMachine machine).rejectState := by
    intro hState
    have hNone := findWorkRule_bridgedRules_none_rejectingPacker
      machine TerminalOutputPacker.terminalOutputPacker.acceptState
        config.tape.head
    have hState' : config.state = rejectingPackerState
        TerminalOutputPacker.terminalOutputPacker.acceptState := by
      simpa [terminalBridgeMachine] using hState
    have hBridgeFind' : findWorkRule (bridgedRules machine)
        (rejectingPackerState
          TerminalOutputPacker.terminalOutputPacker.acceptState)
        config.tape.head = some rule := by
      simpa [bridgedMachine, hState'] using hBridgeFind
    rw [hNone] at hBridgeFind'
    cases hBridgeFind'
  have hTerminalHalted : (terminalBridgeMachine machine).isHalted config =
      false := by
    unfold WorkMachine.isHalted
    rw [nat_beq_false_of_ne _ _ hNotTerminalAccept,
      nat_beq_false_of_ne _ _ hNotTerminalReject]
    rfl
  have hTerminalFind : findWorkRule (terminalBridgeMachine machine).rules
      config.state config.tape.head = some rule := by
    unfold terminalBridgeMachine terminalBridgeRules
    rw [findWorkRule_append_of_none _ _ _ _ hAcceptLaunch,
      findWorkRule_append_of_none _ _ _ _ hRejectLaunch]
    exact findWorkRule_append_of_some _ _ _ _ _ hBridgeFind
  have hTerminalStep := workStep?_eq_apply_of_find
    (terminalBridgeMachine machine) config rule hTerminalHalted hTerminalFind
  calc
    workStep? (terminalBridgeMachine machine) config =
        some (applyWorkRule rule config) := hTerminalStep
    _ = some next := congrArg Option.some hNext.symm

/-- Every finite exact trace in the prior bridge table is preserved exactly
in the extended terminal machine. -/
theorem bridged_workRunExact_of_exact (machine : Machine)
    (steps : Nat) (start final : WorkConfiguration)
    (hRun : workRunExact? (bridgedMachine machine) steps start = some final) :
    workRunExact? (terminalBridgeMachine machine) steps start = some final := by
  have hTransport := workRunExact?_transport
    (bridgedMachine machine) (terminalBridgeMachine machine) id
    (fun config next hStep => by
      simpa [renameConfiguration] using
        (bridged_workStep?_of_some machine config next hStep))
    steps start final hRun
  simpa [renameConfiguration] using hTransport

theorem terminalBridgeMachine_isHalted_acceptingHandoff_false
    (machine : Machine) (state : Nat) (tape : WorkTape) :
    (terminalBridgeMachine machine).isHalted
      (renameConfiguration acceptingHandoffState
        { state := state, tape := tape }) = false := by
  unfold WorkMachine.isHalted terminalBridgeMachine renameConfiguration
  rw [nat_beq_false_of_ne _ _
      (acceptingHandoffState_ne_acceptingPackerState _ _),
    nat_beq_false_of_ne _ _
      (acceptingHandoffState_ne_rejectingPackerState _ _)]
  rfl

theorem terminalBridgeMachine_isHalted_rejectingHandoff_false
    (machine : Machine) (state : Nat) (tape : WorkTape) :
    (terminalBridgeMachine machine).isHalted
      (renameConfiguration rejectingHandoffState
        { state := state, tape := tape }) = false := by
  unfold WorkMachine.isHalted terminalBridgeMachine renameConfiguration
  rw [nat_beq_false_of_ne _ _
      (rejectingHandoffState_ne_acceptingPackerState _ _),
    nat_beq_false_of_ne _ _
      (rejectingHandoffState_ne_rejectingPackerState _ _)]
  rfl

theorem terminalBridgeMachine_isHalted_acceptingPacker_false_of_local
    (machine : Machine) (config : WorkConfiguration)
    (hLocal : TerminalOutputPacker.terminalOutputPacker.isHalted config =
      false) :
    (terminalBridgeMachine machine).isHalted
      (renameConfiguration acceptingPackerState config) = false := by
  have hAccept : config.state ≠
      TerminalOutputPacker.terminalOutputPacker.acceptState :=
    state_ne_accept_of_not_halted
      TerminalOutputPacker.terminalOutputPacker config hLocal
  have hGlobalAccept : acceptingPackerState config.state ≠
      acceptingPackerState
        TerminalOutputPacker.terminalOutputPacker.acceptState := by
    intro h
    exact hAccept (acceptingPackerState_injective h)
  unfold WorkMachine.isHalted terminalBridgeMachine renameConfiguration
  rw [nat_beq_false_of_ne _ _ hGlobalAccept,
    nat_beq_false_of_ne _ _
      (acceptingPackerState_ne_rejectingPackerState _ _)]
  rfl

theorem terminalBridgeMachine_isHalted_rejectingPacker_false_of_local
    (machine : Machine) (config : WorkConfiguration)
    (hLocal : TerminalOutputPacker.terminalOutputPacker.isHalted config =
      false) :
    (terminalBridgeMachine machine).isHalted
      (renameConfiguration rejectingPackerState config) = false := by
  have hAccept : config.state ≠
      TerminalOutputPacker.terminalOutputPacker.acceptState :=
    state_ne_accept_of_not_halted
      TerminalOutputPacker.terminalOutputPacker config hLocal
  have hGlobalReject : rejectingPackerState config.state ≠
      rejectingPackerState
        TerminalOutputPacker.terminalOutputPacker.acceptState := by
    intro h
    exact hAccept (rejectingPackerState_injective h)
  unfold WorkMachine.isHalted terminalBridgeMachine renameConfiguration
  rw [nat_beq_false_of_ne _ _
      (fun h => acceptingPackerState_ne_rejectingPackerState _ _ h.symm),
    nat_beq_false_of_ne _ _ hGlobalReject]
  rfl

theorem acceptingPacker_workStep?_of_some (machine : Machine)
    (config next : WorkConfiguration)
    (hStep : workStep? TerminalOutputPacker.terminalOutputPacker config =
      some next) :
    workStep? (terminalBridgeMachine machine)
        (renameConfiguration acceptingPackerState config) =
      some (renameConfiguration acceptingPackerState next) := by
  rcases workStep?_some_exists TerminalOutputPacker.terminalOutputPacker
      config next hStep with ⟨rule, hHalted, hFind, hNext⟩
  have hGlobalHalted :=
    terminalBridgeMachine_isHalted_acceptingPacker_false_of_local
      machine config hHalted
  have hGlobalFind := findWorkRule_terminalBridge_acceptingPacker_of_some
    machine config.state config.tape.head rule hFind
  have hGlobalStep := workStep?_eq_apply_of_find
    (terminalBridgeMachine machine)
    (renameConfiguration acceptingPackerState config)
    (renameRule acceptingPackerState rule) hGlobalHalted hGlobalFind
  calc
    workStep? (terminalBridgeMachine machine)
        (renameConfiguration acceptingPackerState config) =
        some (applyWorkRule (renameRule acceptingPackerState rule)
          (renameConfiguration acceptingPackerState config)) := hGlobalStep
    _ = some (renameConfiguration acceptingPackerState
          (applyWorkRule rule config)) :=
      congrArg Option.some
        (applyWorkRule_rename acceptingPackerState rule config)
    _ = some (renameConfiguration acceptingPackerState next) :=
      congrArg
        (fun value => some (renameConfiguration acceptingPackerState value))
        hNext.symm

theorem rejectingPacker_workStep?_of_some (machine : Machine)
    (config next : WorkConfiguration)
    (hStep : workStep? TerminalOutputPacker.terminalOutputPacker config =
      some next) :
    workStep? (terminalBridgeMachine machine)
        (renameConfiguration rejectingPackerState config) =
      some (renameConfiguration rejectingPackerState next) := by
  rcases workStep?_some_exists TerminalOutputPacker.terminalOutputPacker
      config next hStep with ⟨rule, hHalted, hFind, hNext⟩
  have hGlobalHalted :=
    terminalBridgeMachine_isHalted_rejectingPacker_false_of_local
      machine config hHalted
  have hGlobalFind := findWorkRule_terminalBridge_rejectingPacker_of_some
    machine config.state config.tape.head rule hFind
  have hGlobalStep := workStep?_eq_apply_of_find
    (terminalBridgeMachine machine)
    (renameConfiguration rejectingPackerState config)
    (renameRule rejectingPackerState rule) hGlobalHalted hGlobalFind
  calc
    workStep? (terminalBridgeMachine machine)
        (renameConfiguration rejectingPackerState config) =
        some (applyWorkRule (renameRule rejectingPackerState rule)
          (renameConfiguration rejectingPackerState config)) := hGlobalStep
    _ = some (renameConfiguration rejectingPackerState
          (applyWorkRule rule config)) :=
      congrArg Option.some
        (applyWorkRule_rename rejectingPackerState rule config)
    _ = some (renameConfiguration rejectingPackerState next) :=
      congrArg
        (fun value => some (renameConfiguration rejectingPackerState value))
        hNext.symm

theorem acceptingPacker_workRunExact_of_exact (machine : Machine)
    (steps : Nat) (start final : WorkConfiguration)
    (hRun : workRunExact? TerminalOutputPacker.terminalOutputPacker steps
      start = some final) :
    workRunExact? (terminalBridgeMachine machine) steps
        (renameConfiguration acceptingPackerState start) =
      some (renameConfiguration acceptingPackerState final) := by
  exact workRunExact?_transport TerminalOutputPacker.terminalOutputPacker
    (terminalBridgeMachine machine) acceptingPackerState
    (acceptingPacker_workStep?_of_some machine) steps start final hRun

theorem rejectingPacker_workRunExact_of_exact (machine : Machine)
    (steps : Nat) (start final : WorkConfiguration)
    (hRun : workRunExact? TerminalOutputPacker.terminalOutputPacker steps
      start = some final) :
    workRunExact? (terminalBridgeMachine machine) steps
        (renameConfiguration rejectingPackerState start) =
      some (renameConfiguration rejectingPackerState final) := by
  exact workRunExact?_transport TerminalOutputPacker.terminalOutputPacker
    (terminalBridgeMachine machine) rejectingPackerState
    (rejectingPacker_workStep?_of_some machine) steps start final hRun

/-! ### Exact handoff-to-packer launches -/

theorem acceptingPackerLaunch_workStep (machine : Machine)
    (tape : WorkTape) :
    workStep? (terminalBridgeMachine machine)
        (renameConfiguration acceptingHandoffState
          (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
            tape)) =
      some (renameConfiguration acceptingPackerState
        (workStartConfiguration TerminalOutputPacker.terminalOutputPacker
          tape)) := by
  let final := PipelineOutputHandoff.framedOutputHandoffFinalConfiguration tape
  have hHalted := terminalBridgeMachine_isHalted_acceptingHandoff_false
    machine final.state final.tape
  have hLaunch := findWorkRule_launchRules
    (acceptingHandoffState
      PipelineOutputHandoff.framedOutputHandoff.acceptState)
    (acceptingPackerState
      TerminalOutputPacker.terminalOutputPacker.startState)
    final.tape.head
  have hFind : findWorkRule (terminalBridgeMachine machine).rules
      (acceptingHandoffState final.state) final.tape.head =
        some (launchRule
          (acceptingHandoffState
            PipelineOutputHandoff.framedOutputHandoff.acceptState)
          (acceptingPackerState
            TerminalOutputPacker.terminalOutputPacker.startState)
          final.tape.head) := by
    unfold terminalBridgeMachine terminalBridgeRules
    simpa [acceptingPackerLaunchRules, final,
      PipelineOutputHandoff.framedOutputHandoffFinalConfiguration] using
        (findWorkRule_append_of_some _ _ _ _ _ hLaunch)
  have hStep := workStep?_eq_apply_of_find (terminalBridgeMachine machine)
    (renameConfiguration acceptingHandoffState final)
    (launchRule
      (acceptingHandoffState
        PipelineOutputHandoff.framedOutputHandoff.acceptState)
      (acceptingPackerState
        TerminalOutputPacker.terminalOutputPacker.startState)
      final.tape.head) hHalted hFind
  simpa [final, launchRule, applyWorkRule, WorkTape.write, WorkTape.move,
    PipelineOutputHandoff.framedOutputHandoffFinalConfiguration,
    workStartConfiguration, renameConfiguration] using hStep

theorem rejectingPackerLaunch_workStep (machine : Machine)
    (tape : WorkTape) :
    workStep? (terminalBridgeMachine machine)
        (renameConfiguration rejectingHandoffState
          (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
            tape)) =
      some (renameConfiguration rejectingPackerState
        (workStartConfiguration TerminalOutputPacker.terminalOutputPacker
          tape)) := by
  let final := PipelineOutputHandoff.framedOutputHandoffFinalConfiguration tape
  have hHalted := terminalBridgeMachine_isHalted_rejectingHandoff_false
    machine final.state final.tape
  have hAcceptNone : findWorkRule acceptingPackerLaunchRules
      (rejectingHandoffState final.state) final.tape.head = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    intro h
    exact acceptingHandoffState_ne_rejectingHandoffState _ _ h
  have hLaunch := findWorkRule_launchRules
    (rejectingHandoffState
      PipelineOutputHandoff.framedOutputHandoff.acceptState)
    (rejectingPackerState
      TerminalOutputPacker.terminalOutputPacker.startState)
    final.tape.head
  have hFind : findWorkRule (terminalBridgeMachine machine).rules
      (rejectingHandoffState final.state) final.tape.head =
        some (launchRule
          (rejectingHandoffState
            PipelineOutputHandoff.framedOutputHandoff.acceptState)
          (rejectingPackerState
            TerminalOutputPacker.terminalOutputPacker.startState)
          final.tape.head) := by
    unfold terminalBridgeMachine terminalBridgeRules
    rw [findWorkRule_append_of_none _ _ _ _ hAcceptNone]
    simpa [rejectingPackerLaunchRules, final,
      PipelineOutputHandoff.framedOutputHandoffFinalConfiguration] using
        (findWorkRule_append_of_some _ _ _ _ _ hLaunch)
  have hStep := workStep?_eq_apply_of_find (terminalBridgeMachine machine)
    (renameConfiguration rejectingHandoffState final)
    (launchRule
      (rejectingHandoffState
        PipelineOutputHandoff.framedOutputHandoff.acceptState)
      (rejectingPackerState
        TerminalOutputPacker.terminalOutputPacker.startState)
      final.tape.head) hHalted hFind
  simpa [final, launchRule, applyWorkRule, WorkTape.write, WorkTape.move,
    PipelineOutputHandoff.framedOutputHandoffFinalConfiguration,
    workStartConfiguration, renameConfiguration] using hStep

/-! ### Exact launch-and-pack traces from represented handoff endpoints -/

private theorem workRunExact_one (machine : WorkMachine)
    (start next : WorkConfiguration)
    (hStep : workStep? machine start = some next) :
    workRunExact? machine 1 start = some next := by
  change (match workStep? machine start with
    | none => none
    | some result => some result) = some next
  rw [hStep]

theorem acceptingTerminal_workRunExact_of_represents
    (machine : Machine) {raw : Tape} {work : WorkTape}
    (hRepresents : Represents raw.handoffTarget work) :
    ∃ outsideLeft outsideRight,
      work = TerminalOutputPacker.terminalOutputPackerInputTape
        raw.outputBits outsideLeft outsideRight ∧
      workRunExact? (terminalBridgeMachine machine)
          (terminalBridgeWorkSteps raw.outputBits)
          (renameConfiguration acceptingHandoffState
            (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
              work)) =
        some (renameConfiguration acceptingPackerState
          (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
            raw.outputBits outsideLeft outsideRight)) := by
  rcases hRepresents with ⟨outsideLeft, outsideRight, hWork⟩
  have hInput : work =
      TerminalOutputPacker.terminalOutputPackerInputTape
        raw.outputBits outsideLeft outsideRight := by
    simpa [TerminalOutputPacker.terminalOutputPackerInputTape,
      Tape.handoffTarget] using hWork
  have hLaunchStep := acceptingPackerLaunch_workStep machine work
  have hLaunch := workRunExact_one (terminalBridgeMachine machine)
    (renameConfiguration acceptingHandoffState
      (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration work))
    (renameConfiguration acceptingPackerState
      (workStartConfiguration TerminalOutputPacker.terminalOutputPacker work))
    hLaunchStep
  have hLocal := TerminalOutputPacker.terminalOutputPacker_workRunExact
    raw.outputBits outsideLeft outsideRight
  have hPacked : workRunExact? (terminalBridgeMachine machine)
      (TerminalOutputPacker.terminalOutputPackerWorkSteps raw.outputBits)
      (renameConfiguration acceptingPackerState
        (workStartConfiguration TerminalOutputPacker.terminalOutputPacker
          work)) =
      some (renameConfiguration acceptingPackerState
        (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
          raw.outputBits outsideLeft outsideRight)) := by
    rw [hInput]
    exact acceptingPacker_workRunExact_of_exact machine _ _ _ hLocal
  have hComplete := PipelineMachineSimulation.workRunExact?_compose
    (terminalBridgeMachine machine) 1
    (TerminalOutputPacker.terminalOutputPackerWorkSteps raw.outputBits)
    (renameConfiguration acceptingHandoffState
      (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration work))
    (renameConfiguration acceptingPackerState
      (workStartConfiguration TerminalOutputPacker.terminalOutputPacker work))
    (renameConfiguration acceptingPackerState
      (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
        raw.outputBits outsideLeft outsideRight)) hLaunch hPacked
  exact ⟨outsideLeft, outsideRight, hInput, by
    simpa [terminalBridgeWorkSteps] using hComplete⟩

theorem rejectingTerminal_workRunExact_of_represents
    (machine : Machine) {raw : Tape} {work : WorkTape}
    (hRepresents : Represents raw.handoffTarget work) :
    ∃ outsideLeft outsideRight,
      work = TerminalOutputPacker.terminalOutputPackerInputTape
        raw.outputBits outsideLeft outsideRight ∧
      workRunExact? (terminalBridgeMachine machine)
          (terminalBridgeWorkSteps raw.outputBits)
          (renameConfiguration rejectingHandoffState
            (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
              work)) =
        some (renameConfiguration rejectingPackerState
          (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
            raw.outputBits outsideLeft outsideRight)) := by
  rcases hRepresents with ⟨outsideLeft, outsideRight, hWork⟩
  have hInput : work =
      TerminalOutputPacker.terminalOutputPackerInputTape
        raw.outputBits outsideLeft outsideRight := by
    simpa [TerminalOutputPacker.terminalOutputPackerInputTape,
      Tape.handoffTarget] using hWork
  have hLaunchStep := rejectingPackerLaunch_workStep machine work
  have hLaunch := workRunExact_one (terminalBridgeMachine machine)
    (renameConfiguration rejectingHandoffState
      (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration work))
    (renameConfiguration rejectingPackerState
      (workStartConfiguration TerminalOutputPacker.terminalOutputPacker work))
    hLaunchStep
  have hLocal := TerminalOutputPacker.terminalOutputPacker_workRunExact
    raw.outputBits outsideLeft outsideRight
  have hPacked : workRunExact? (terminalBridgeMachine machine)
      (TerminalOutputPacker.terminalOutputPackerWorkSteps raw.outputBits)
      (renameConfiguration rejectingPackerState
        (workStartConfiguration TerminalOutputPacker.terminalOutputPacker
          work)) =
      some (renameConfiguration rejectingPackerState
        (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
          raw.outputBits outsideLeft outsideRight)) := by
    rw [hInput]
    exact rejectingPacker_workRunExact_of_exact machine _ _ _ hLocal
  have hComplete := PipelineMachineSimulation.workRunExact?_compose
    (terminalBridgeMachine machine) 1
    (TerminalOutputPacker.terminalOutputPackerWorkSteps raw.outputBits)
    (renameConfiguration rejectingHandoffState
      (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration work))
    (renameConfiguration rejectingPackerState
      (workStartConfiguration TerminalOutputPacker.terminalOutputPacker work))
    (renameConfiguration rejectingPackerState
      (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
        raw.outputBits outsideLeft outsideRight)) hLaunch hPacked
  exact ⟨outsideLeft, outsideRight, hInput, by
    simpa [terminalBridgeWorkSteps] using hComplete⟩

/-! ### Complete literal traces induced by supplied exact target executions -/

/-- A supplied accepting target execution now continues through framing,
simulation, represented handoff, terminal launch, and raw-output packing in
one literal finite work machine. -/
theorem acceptingSuppliedTrace_workRunExact_of_rawRunExact
    (machine : Machine) (steps : Nat) (left right : BitString)
    (final : Configuration)
    (hRaw : PipelineMachineSimulation.rawRunExact? machine steps
      (startConfig machine (BitString.pair left right)) = some final)
    (hAccept : final.state = machine.acceptState) :
    ∃ simulatorFinal handoffFinal outsideLeft outsideRight,
      PipelineMachineSimulation.RepresentsConfiguration
          machine final simulatorFinal ∧
      Represents final.tape.handoffTarget handoffFinal ∧
      handoffFinal = TerminalOutputPacker.terminalOutputPackerInputTape
        final.tape.outputBits outsideLeft outsideRight ∧
      workRunExact? (terminalBridgeMachine machine)
          (suppliedTraceTerminalWorkSteps left right steps final.tape)
          (workStartConfiguration (terminalBridgeMachine machine)
            (pairedWorkTape left right)) =
        some (renameConfiguration acceptingPackerState
          (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
            final.tape.outputBits outsideLeft outsideRight)) := by
  rcases bridgedAccept_workRunExact_of_rawRunExact
      machine steps left right final hRaw hAccept with
    ⟨simulatorFinal, handoffFinal, hFinalRepresents,
      hHandoffRepresents, hBridgeExact⟩
  have hBridgeExtended := bridged_workRunExact_of_exact machine
    (bridgedWorkSteps left right steps final.tape)
    (workStartConfiguration (bridgedMachine machine)
      (pairedWorkTape left right))
    (renameConfiguration acceptingHandoffState
      (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
        handoffFinal)) hBridgeExact
  have hBridgeExtended' : workRunExact? (terminalBridgeMachine machine)
      (bridgedWorkSteps left right steps final.tape)
      (workStartConfiguration (terminalBridgeMachine machine)
        (pairedWorkTape left right)) =
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
    (bridgedWorkSteps left right steps final.tape)
    (terminalBridgeWorkSteps final.tape.outputBits)
    (workStartConfiguration (terminalBridgeMachine machine)
      (pairedWorkTape left right))
    (renameConfiguration acceptingHandoffState
      (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
        handoffFinal))
    (renameConfiguration acceptingPackerState
      (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
        final.tape.outputBits outsideLeft outsideRight))
    hBridgeExtended' hTerminalExact
  exact ⟨simulatorFinal, handoffFinal, outsideLeft, outsideRight,
    hFinalRepresents, hHandoffRepresents, hInput, by
      simpa [suppliedTraceTerminalWorkSteps] using hComplete⟩

/-- The rejecting target endpoint uses the disjoint rejecting handoff and
terminal-packer copies in the same literal machine. -/
theorem rejectingSuppliedTrace_workRunExact_of_rawRunExact
    (machine : Machine) (steps : Nat) (left right : BitString)
    (final : Configuration)
    (hDistinct : machine.rejectState ≠ machine.acceptState)
    (hRaw : PipelineMachineSimulation.rawRunExact? machine steps
      (startConfig machine (BitString.pair left right)) = some final)
    (hReject : final.state = machine.rejectState) :
    ∃ simulatorFinal handoffFinal outsideLeft outsideRight,
      PipelineMachineSimulation.RepresentsConfiguration
          machine final simulatorFinal ∧
      Represents final.tape.handoffTarget handoffFinal ∧
      handoffFinal = TerminalOutputPacker.terminalOutputPackerInputTape
        final.tape.outputBits outsideLeft outsideRight ∧
      workRunExact? (terminalBridgeMachine machine)
          (suppliedTraceTerminalWorkSteps left right steps final.tape)
          (workStartConfiguration (terminalBridgeMachine machine)
            (pairedWorkTape left right)) =
        some (renameConfiguration rejectingPackerState
          (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
            final.tape.outputBits outsideLeft outsideRight)) := by
  rcases bridgedReject_workRunExact_of_rawRunExact
      machine steps left right final hDistinct hRaw hReject with
    ⟨simulatorFinal, handoffFinal, hFinalRepresents,
      hHandoffRepresents, hBridgeExact⟩
  have hBridgeExtended := bridged_workRunExact_of_exact machine
    (bridgedWorkSteps left right steps final.tape)
    (workStartConfiguration (bridgedMachine machine)
      (pairedWorkTape left right))
    (renameConfiguration rejectingHandoffState
      (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
        handoffFinal)) hBridgeExact
  have hBridgeExtended' : workRunExact? (terminalBridgeMachine machine)
      (bridgedWorkSteps left right steps final.tape)
      (workStartConfiguration (terminalBridgeMachine machine)
        (pairedWorkTape left right)) =
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
    (bridgedWorkSteps left right steps final.tape)
    (terminalBridgeWorkSteps final.tape.outputBits)
    (workStartConfiguration (terminalBridgeMachine machine)
      (pairedWorkTape left right))
    (renameConfiguration rejectingHandoffState
      (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
        handoffFinal))
    (renameConfiguration rejectingPackerState
      (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
        final.tape.outputBits outsideLeft outsideRight))
    hBridgeExtended' hTerminalExact
  exact ⟨simulatorFinal, handoffFinal, outsideLeft, outsideRight,
    hFinalRepresents, hHandoffRepresents, hInput, by
      simpa [suppliedTraceTerminalWorkSteps] using hComplete⟩

theorem acceptingTerminalFinal_state_eq_accept (machine : Machine)
    (bits : BitString) (outsideLeft outsideRight : List WorkSymbol) :
    (renameConfiguration acceptingPackerState
      (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
        bits outsideLeft outsideRight)).state =
      (terminalBridgeMachine machine).acceptState := by
  rfl

theorem rejectingTerminalFinal_state_eq_reject (machine : Machine)
    (bits : BitString) (outsideLeft outsideRight : List WorkSymbol) :
    (renameConfiguration rejectingPackerState
      (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
        bits outsideLeft outsideRight)).state =
      (terminalBridgeMachine machine).rejectState := by
  rfl

theorem terminalBridgeMachine_acceptState_ne_rejectState
    (machine : Machine) :
    (terminalBridgeMachine machine).acceptState ≠
      (terminalBridgeMachine machine).rejectState := by
  simpa only [terminalBridgeMachine,
    TerminalOutputPacker.terminalOutputPacker] using
      (acceptingPackerState_ne_rejectingPackerState
        TerminalOutputPacker.acceptState TerminalOutputPacker.acceptState)

theorem acceptingTerminalFinal_isHalted (machine : Machine)
    (bits : BitString) (outsideLeft outsideRight : List WorkSymbol) :
    (terminalBridgeMachine machine).isHalted
      (renameConfiguration acceptingPackerState
        (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
          bits outsideLeft outsideRight)) = true := by
  unfold WorkMachine.isHalted
  rw [acceptingTerminalFinal_state_eq_accept machine bits
    outsideLeft outsideRight]
  have hRefl :
      ((terminalBridgeMachine machine).acceptState ==
        (terminalBridgeMachine machine).acceptState) = true :=
    (nat_beq_true_iff _ _).mpr rfl
  rw [hRefl]
  rfl

theorem rejectingTerminalFinal_isHalted (machine : Machine)
    (bits : BitString) (outsideLeft outsideRight : List WorkSymbol) :
    (terminalBridgeMachine machine).isHalted
      (renameConfiguration rejectingPackerState
        (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
          bits outsideLeft outsideRight)) = true := by
  unfold WorkMachine.isHalted
  rw [rejectingTerminalFinal_state_eq_reject machine bits
    outsideLeft outsideRight]
  have hNotAccept : (terminalBridgeMachine machine).rejectState ≠
      (terminalBridgeMachine machine).acceptState :=
    (terminalBridgeMachine_acceptState_ne_rejectState machine).symm
  rw [nat_beq_false_of_ne _ _ hNotAccept]
  have hRefl :
      ((terminalBridgeMachine machine).rejectState ==
        (terminalBridgeMachine machine).rejectState) = true :=
    (nat_beq_true_iff _ _).mpr rfl
  rw [hRefl]
  rfl

theorem suppliedTraceTerminalWorkSteps_eq (left right : BitString)
    (sourceSteps : Nat) (finalTape : Tape) :
    suppliedTraceTerminalWorkSteps left right sourceSteps finalTape =
      (PipelineInputFramer.inputFramerWorkSteps
          (PipelineInputFramer.packedPairCount left right) +
        1 + 3 * sourceSteps + 1 +
        PipelineOutputHandoff.framedOutputHandoffWorkSteps finalTape) +
      (1 + TerminalOutputPacker.terminalOutputPackerWorkSteps
        finalTape.outputBits) := by
  rfl

/-- At the exact end of any supplied target prefix, the extended terminal
machine still reports timeout.  No terminal launch fires from a simulator
state. -/
theorem simulationPrefix_terminalBridge_workBoundedDecide_timeout
    (machine : Machine) (steps : Nat) (left right : BitString)
    (final : Configuration)
    (hRaw : PipelineMachineSimulation.rawRunExact? machine steps
      (startConfig machine (BitString.pair left right)) = some final) :
    workBoundedDecide (terminalBridgeMachine machine)
        (simulationPrefixWorkSteps left right steps)
        (pairedWorkTape left right) = .timeout := by
  rcases simulationPrefix_workRunExact_of_rawRunExact
      machine steps left right final hRaw with
    ⟨workFinal, hBridgeExact, _⟩
  have hExtended := bridged_workRunExact_of_exact machine
    (simulationPrefixWorkSteps left right steps)
    (workStartConfiguration (bridgedMachine machine)
      (pairedWorkTape left right))
    (renameConfiguration simulationState workFinal) hBridgeExact
  have hExtended' : workRunExact? (terminalBridgeMachine machine)
      (simulationPrefixWorkSteps left right steps)
      (workStartConfiguration (terminalBridgeMachine machine)
        (pairedWorkTape left right)) =
      some (renameConfiguration simulationState workFinal) := by
    simpa [workStartConfiguration, bridgedMachine, terminalBridgeMachine]
      using hExtended
  have hRun := workRun_eq_of_workRunExact
    (terminalBridgeMachine machine)
    (simulationPrefixWorkSteps left right steps)
    (workStartConfiguration (terminalBridgeMachine machine)
      (pairedWorkTape left right))
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
  rw [nat_beq_false_of_ne _ _ hAccept,
    nat_beq_false_of_ne _ _ hReject]
  rfl

/-- Explicit stuck-endpoint corollary: a supplied stuck nonhalting target
endpoint remains timeout in the extended machine, never rejection. -/
theorem workBoundedDecide_terminalBridge_timeout_of_stuck_rawRunExact
    (machine : Machine) (steps : Nat) (left right : BitString)
    (final : Configuration)
    (hRaw : PipelineMachineSimulation.rawRunExact? machine steps
      (startConfig machine (BitString.pair left right)) = some final)
    (_hNonhalting : machine.isHalted final = false)
    (_hStuck : step? machine final = none) :
    workBoundedDecide (terminalBridgeMachine machine)
        (simulationPrefixWorkSteps left right steps)
        (pairedWorkTape left right) = .timeout := by
  exact simulationPrefix_terminalBridge_workBoundedDecide_timeout
    machine steps left right final hRaw

/-- At the exact cumulative supplied-trace budget, a target accept remains an
accept verdict after terminal packing. -/
theorem workBoundedDecide_terminalBridge_accept_of_rawRunExact
    (machine : Machine) (steps : Nat) (left right : BitString)
    (final : Configuration)
    (hRaw : PipelineMachineSimulation.rawRunExact? machine steps
      (startConfig machine (BitString.pair left right)) = some final)
    (hAccept : final.state = machine.acceptState) :
    workBoundedDecide (terminalBridgeMachine machine)
        (suppliedTraceTerminalWorkSteps left right steps final.tape)
        (pairedWorkTape left right) = .accept := by
  rcases acceptingSuppliedTrace_workRunExact_of_rawRunExact
      machine steps left right final hRaw hAccept with
    ⟨_, _, outsideLeft, outsideRight, _, _, _, hExact⟩
  have hRun := workRun_eq_of_workRunExact
    (terminalBridgeMachine machine)
    (suppliedTraceTerminalWorkSteps left right steps final.tape)
    (workStartConfiguration (terminalBridgeMachine machine)
      (pairedWorkTape left right))
    (renameConfiguration acceptingPackerState
      (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
        final.tape.outputBits outsideLeft outsideRight)) hExact
  apply (workBoundedDecide_accept_iff_final
    (terminalBridgeMachine machine)
    (suppliedTraceTerminalWorkSteps left right steps final.tape)
    (pairedWorkTape left right)).2
  rw [hRun]
  exact acceptingTerminalFinal_state_eq_accept machine
    final.tape.outputBits outsideLeft outsideRight

/-- A supplied rejecting target execution remains the distinct reject verdict
after terminal packing. -/
theorem workBoundedDecide_terminalBridge_reject_of_rawRunExact
    (machine : Machine) (steps : Nat) (left right : BitString)
    (final : Configuration)
    (hDistinct : machine.rejectState ≠ machine.acceptState)
    (hRaw : PipelineMachineSimulation.rawRunExact? machine steps
      (startConfig machine (BitString.pair left right)) = some final)
    (hReject : final.state = machine.rejectState) :
    workBoundedDecide (terminalBridgeMachine machine)
        (suppliedTraceTerminalWorkSteps left right steps final.tape)
        (pairedWorkTape left right) = .reject := by
  rcases rejectingSuppliedTrace_workRunExact_of_rawRunExact
      machine steps left right final hDistinct hRaw hReject with
    ⟨_, _, outsideLeft, outsideRight, _, _, _, hExact⟩
  have hRun := workRun_eq_of_workRunExact
    (terminalBridgeMachine machine)
    (suppliedTraceTerminalWorkSteps left right steps final.tape)
    (workStartConfiguration (terminalBridgeMachine machine)
      (pairedWorkTape left right))
    (renameConfiguration rejectingPackerState
      (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
        final.tape.outputBits outsideLeft outsideRight)) hExact
  apply (workBoundedDecide_reject_iff_final
    (terminalBridgeMachine machine)
    (suppliedTraceTerminalWorkSteps left right steps final.tape)
    (pairedWorkTape left right)).2
  constructor
  · rw [hRun]
    intro hEqual
    exact terminalBridgeMachine_acceptState_ne_rejectState machine
      hEqual.symm
  · rw [hRun]
    exact rejectingTerminalFinal_state_eq_reject machine
      final.tape.outputBits outsideLeft outsideRight

/-- The accepting supplied work trace compiles from ordinary external paired
input at exactly six raw transitions per work transition. -/
theorem run_compileTerminalBridge_accept_of_rawRunExact
    (machine : Machine) (steps : Nat) (left right : BitString)
    (final : Configuration)
    (hRaw : PipelineMachineSimulation.rawRunExact? machine steps
      (startConfig machine (BitString.pair left right)) = some final)
    (hAccept : final.state = machine.acceptState) :
    ∃ outsideLeft outsideRight,
      run (compileWorkMachine (terminalBridgeMachine machine))
          (suppliedTraceTerminalRawSteps left right steps final.tape)
          (startConfig (compileWorkMachine (terminalBridgeMachine machine))
            (BitString.pair left right)) =
        encodeWorkConfiguration
          (renameConfiguration acceptingPackerState
            (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
              final.tape.outputBits outsideLeft outsideRight)) := by
  rcases acceptingSuppliedTrace_workRunExact_of_rawRunExact
      machine steps left right final hRaw hAccept with
    ⟨_, _, outsideLeft, outsideRight, _, _, _, hExact⟩
  have hCompiled := run_compileWorkMachine_mul_of_workRunExact
    (terminalBridgeMachine machine)
    (suppliedTraceTerminalWorkSteps left right steps final.tape)
    (workStartConfiguration (terminalBridgeMachine machine)
      (pairedWorkTape left right))
    (renameConfiguration acceptingPackerState
      (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
        final.tape.outputBits outsideLeft outsideRight)) hExact
  rw [← startConfig_compileWorkMachine_paired
    (terminalBridgeMachine machine) left right] at hCompiled
  exact ⟨outsideLeft, outsideRight, by
    simpa [suppliedTraceTerminalRawSteps] using hCompiled⟩

/-- The rejecting supplied trace has the same exact compiled cost and reaches
the distinct terminal reject image. -/
theorem run_compileTerminalBridge_reject_of_rawRunExact
    (machine : Machine) (steps : Nat) (left right : BitString)
    (final : Configuration)
    (hDistinct : machine.rejectState ≠ machine.acceptState)
    (hRaw : PipelineMachineSimulation.rawRunExact? machine steps
      (startConfig machine (BitString.pair left right)) = some final)
    (hReject : final.state = machine.rejectState) :
    ∃ outsideLeft outsideRight,
      run (compileWorkMachine (terminalBridgeMachine machine))
          (suppliedTraceTerminalRawSteps left right steps final.tape)
          (startConfig (compileWorkMachine (terminalBridgeMachine machine))
            (BitString.pair left right)) =
        encodeWorkConfiguration
          (renameConfiguration rejectingPackerState
            (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
              final.tape.outputBits outsideLeft outsideRight)) := by
  rcases rejectingSuppliedTrace_workRunExact_of_rawRunExact
      machine steps left right final hDistinct hRaw hReject with
    ⟨_, _, outsideLeft, outsideRight, _, _, _, hExact⟩
  have hCompiled := run_compileWorkMachine_mul_of_workRunExact
    (terminalBridgeMachine machine)
    (suppliedTraceTerminalWorkSteps left right steps final.tape)
    (workStartConfiguration (terminalBridgeMachine machine)
      (pairedWorkTape left right))
    (renameConfiguration rejectingPackerState
      (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
        final.tape.outputBits outsideLeft outsideRight)) hExact
  rw [← startConfig_compileWorkMachine_paired
    (terminalBridgeMachine machine) left right] at hCompiled
  exact ⟨outsideLeft, outsideRight, by
    simpa [suppliedTraceTerminalRawSteps] using hCompiled⟩

/-- The exact accepting launch-and-pack trace compiles at six raw steps per
work transition.  The input here is an encoded internal handoff endpoint, not
ordinary external `startConfig`. -/
theorem run_compileTerminalBridge_accepting_of_represents
    (machine : Machine) {raw : Tape} {work : WorkTape}
    (hRepresents : Represents raw.handoffTarget work) :
    ∃ outsideLeft outsideRight,
      work = TerminalOutputPacker.terminalOutputPackerInputTape
        raw.outputBits outsideLeft outsideRight ∧
      run (compileWorkMachine (terminalBridgeMachine machine))
          (terminalBridgeRawSteps raw.outputBits)
          (encodeWorkConfiguration
            (renameConfiguration acceptingHandoffState
              (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
                work))) =
        encodeWorkConfiguration
          (renameConfiguration acceptingPackerState
            (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
              raw.outputBits outsideLeft outsideRight)) := by
  rcases acceptingTerminal_workRunExact_of_represents machine hRepresents with
    ⟨outsideLeft, outsideRight, hWork, hExact⟩
  have hCompiled := run_compileWorkMachine_mul_of_workRunExact
    (terminalBridgeMachine machine)
    (terminalBridgeWorkSteps raw.outputBits)
    (renameConfiguration acceptingHandoffState
      (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration work))
    (renameConfiguration acceptingPackerState
      (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
        raw.outputBits outsideLeft outsideRight)) hExact
  exact ⟨outsideLeft, outsideRight, hWork, by
    simpa [terminalBridgeRawSteps] using hCompiled⟩

/-- The rejecting copy has the same exact compiled cost and reaches the
distinct global reject image. -/
theorem run_compileTerminalBridge_rejecting_of_represents
    (machine : Machine) {raw : Tape} {work : WorkTape}
    (hRepresents : Represents raw.handoffTarget work) :
    ∃ outsideLeft outsideRight,
      work = TerminalOutputPacker.terminalOutputPackerInputTape
        raw.outputBits outsideLeft outsideRight ∧
      run (compileWorkMachine (terminalBridgeMachine machine))
          (terminalBridgeRawSteps raw.outputBits)
          (encodeWorkConfiguration
            (renameConfiguration rejectingHandoffState
              (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
                work))) =
        encodeWorkConfiguration
          (renameConfiguration rejectingPackerState
            (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
              raw.outputBits outsideLeft outsideRight)) := by
  rcases rejectingTerminal_workRunExact_of_represents machine hRepresents with
    ⟨outsideLeft, outsideRight, hWork, hExact⟩
  have hCompiled := run_compileWorkMachine_mul_of_workRunExact
    (terminalBridgeMachine machine)
    (terminalBridgeWorkSteps raw.outputBits)
    (renameConfiguration rejectingHandoffState
      (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration work))
    (renameConfiguration rejectingPackerState
      (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
        raw.outputBits outsideLeft outsideRight)) hExact
  exact ⟨outsideLeft, outsideRight, hWork, by
    simpa [terminalBridgeRawSteps] using hCompiled⟩

/-- Padding the accepting local trace to its output-length polynomial leaves
the compiled machine at the same accepting terminal configuration. -/
theorem run_compileTerminalBridge_accepting_of_represents_at_bound
    (machine : Machine) {raw : Tape} {work : WorkTape}
    (hRepresents : Represents raw.handoffTarget work) :
    ∃ outsideLeft outsideRight,
      work = TerminalOutputPacker.terminalOutputPackerInputTape
        raw.outputBits outsideLeft outsideRight ∧
      run (compileWorkMachine (terminalBridgeMachine machine))
          (terminalBridgeRawTimeBound.eval raw.outputBits.length)
          (encodeWorkConfiguration
            (renameConfiguration acceptingHandoffState
              (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
                work))) =
        encodeWorkConfiguration
          (renameConfiguration acceptingPackerState
            (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
              raw.outputBits outsideLeft outsideRight)) := by
  rcases acceptingTerminal_workRunExact_of_represents machine hRepresents with
    ⟨outsideLeft, outsideRight, hWork, hExact⟩
  have hCompiled := run_compileWorkMachine_of_workRunExact_halted_le
    (terminalBridgeMachine machine)
    (terminalBridgeWorkSteps raw.outputBits)
    (terminalBridgeRawTimeBound.eval raw.outputBits.length)
    (renameConfiguration acceptingHandoffState
      (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration work))
    (renameConfiguration acceptingPackerState
      (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
        raw.outputBits outsideLeft outsideRight)) hExact
    (acceptingTerminalFinal_isHalted machine raw.outputBits
      outsideLeft outsideRight)
    (terminalBridge_runtime_le raw.outputBits)
  exact ⟨outsideLeft, outsideRight, hWork, hCompiled⟩

/-- The rejecting local trace is stable through the same advertised
output-length polynomial budget. -/
theorem run_compileTerminalBridge_rejecting_of_represents_at_bound
    (machine : Machine) {raw : Tape} {work : WorkTape}
    (hRepresents : Represents raw.handoffTarget work) :
    ∃ outsideLeft outsideRight,
      work = TerminalOutputPacker.terminalOutputPackerInputTape
        raw.outputBits outsideLeft outsideRight ∧
      run (compileWorkMachine (terminalBridgeMachine machine))
          (terminalBridgeRawTimeBound.eval raw.outputBits.length)
          (encodeWorkConfiguration
            (renameConfiguration rejectingHandoffState
              (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
                work))) =
        encodeWorkConfiguration
          (renameConfiguration rejectingPackerState
            (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
              raw.outputBits outsideLeft outsideRight)) := by
  rcases rejectingTerminal_workRunExact_of_represents machine hRepresents with
    ⟨outsideLeft, outsideRight, hWork, hExact⟩
  have hCompiled := run_compileWorkMachine_of_workRunExact_halted_le
    (terminalBridgeMachine machine)
    (terminalBridgeWorkSteps raw.outputBits)
    (terminalBridgeRawTimeBound.eval raw.outputBits.length)
    (renameConfiguration rejectingHandoffState
      (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration work))
    (renameConfiguration rejectingPackerState
      (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
        raw.outputBits outsideLeft outsideRight)) hExact
    (rejectingTerminalFinal_isHalted machine raw.outputBits
      outsideLeft outsideRight)
    (terminalBridge_runtime_le raw.outputBits)
  exact ⟨outsideLeft, outsideRight, hWork, hCompiled⟩

theorem acceptingTerminal_output_eq (bits : BitString)
    (outsideLeft outsideRight : List WorkSymbol) :
    Tape.outputBits
        (encodeWorkTape
          (renameConfiguration acceptingPackerState
            (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
              bits outsideLeft outsideRight)).tape) = bits := by
  exact TerminalOutputPacker.terminalOutputPacker_output_eq
    bits outsideLeft outsideRight

theorem rejectingTerminal_output_eq (bits : BitString)
    (outsideLeft outsideRight : List WorkSymbol) :
    Tape.outputBits
        (encodeWorkTape
          (renameConfiguration rejectingPackerState
            (TerminalOutputPacker.terminalOutputPackerFinalConfiguration
              bits outsideLeft outsideRight)).tape) = bits := by
  exact TerminalOutputPacker.terminalOutputPacker_output_eq
    bits outsideLeft outsideRight

/-- Ordinary raw-machine output after the supplied accepting trace is exactly
the target execution's logical output. -/
theorem machineOutput_compileTerminalBridge_accept_of_rawRunExact
    (machine : Machine) (steps : Nat) (left right : BitString)
    (final : Configuration)
    (hRaw : PipelineMachineSimulation.rawRunExact? machine steps
      (startConfig machine (BitString.pair left right)) = some final)
    (hAccept : final.state = machine.acceptState) :
    machineOutput (compileWorkMachine (terminalBridgeMachine machine))
        (suppliedTraceTerminalRawSteps left right steps final.tape)
        (BitString.pair left right) = final.tape.outputBits := by
  rcases run_compileTerminalBridge_accept_of_rawRunExact
      machine steps left right final hRaw hAccept with
    ⟨outsideLeft, outsideRight, hRun⟩
  unfold machineOutput
  rw [hRun]
  exact acceptingTerminal_output_eq final.tape.outputBits
    outsideLeft outsideRight

/-- Ordinary raw-machine output after the supplied rejecting trace is the
same target output while the control state remains rejecting. -/
theorem machineOutput_compileTerminalBridge_reject_of_rawRunExact
    (machine : Machine) (steps : Nat) (left right : BitString)
    (final : Configuration)
    (hDistinct : machine.rejectState ≠ machine.acceptState)
    (hRaw : PipelineMachineSimulation.rawRunExact? machine steps
      (startConfig machine (BitString.pair left right)) = some final)
    (hReject : final.state = machine.rejectState) :
    machineOutput (compileWorkMachine (terminalBridgeMachine machine))
        (suppliedTraceTerminalRawSteps left right steps final.tape)
        (BitString.pair left right) = final.tape.outputBits := by
  rcases run_compileTerminalBridge_reject_of_rawRunExact
      machine steps left right final hDistinct hRaw hReject with
    ⟨outsideLeft, outsideRight, hRun⟩
  unfold machineOutput
  rw [hRun]
  exact rejectingTerminal_output_eq final.tape.outputBits
    outsideLeft outsideRight

/-- At the advertised local bound, ordinary raw blank-delimited observation
of the accepting terminal trace is exactly the represented logical output. -/
theorem outputBits_compileTerminalBridge_accepting_of_represents
    (machine : Machine) {raw : Tape} {work : WorkTape}
    (hRepresents : Represents raw.handoffTarget work) :
    Tape.outputBits
        (run (compileWorkMachine (terminalBridgeMachine machine))
          (terminalBridgeRawTimeBound.eval raw.outputBits.length)
          (encodeWorkConfiguration
            (renameConfiguration acceptingHandoffState
              (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
                work)))).tape = raw.outputBits := by
  rcases run_compileTerminalBridge_accepting_of_represents_at_bound
      machine hRepresents with
    ⟨outsideLeft, outsideRight, _hWork, hRun⟩
  rw [hRun]
  exact acceptingTerminal_output_eq raw.outputBits outsideLeft outsideRight

/-- The rejecting terminal copy exposes the same exact logical output while
ending in its distinct global reject state. -/
theorem outputBits_compileTerminalBridge_rejecting_of_represents
    (machine : Machine) {raw : Tape} {work : WorkTape}
    (hRepresents : Represents raw.handoffTarget work) :
    Tape.outputBits
        (run (compileWorkMachine (terminalBridgeMachine machine))
          (terminalBridgeRawTimeBound.eval raw.outputBits.length)
          (encodeWorkConfiguration
            (renameConfiguration rejectingHandoffState
              (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
                work)))).tape = raw.outputBits := by
  rcases run_compileTerminalBridge_rejecting_of_represents_at_bound
      machine hRepresents with
    ⟨outsideLeft, outsideRight, _hWork, hRun⟩
  rw [hRun]
  exact rejectingTerminal_output_eq raw.outputBits outsideLeft outsideRight

end PipelineTerminalBridge

end PNP.Concrete
