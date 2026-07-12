/-
Copyright (c) 2026 PNP Labs.

Explicit launch transitions for the finite pipeline work machines.

This module extends the collision-free state namespace with literal one-step
bridges from the paired-input framer to the lifted simulator and from the
simulator's accept/reject sentinels to two verdict-indexed copies of the
represented-output handoff.  The two handoff copies retain the target
classification while sharing the already-proved tape transformation.

The result remains an internal represented-output pipeline.  It does not
pack the two-track work tape into ordinary raw `machineOutput`, prove a
pipeline `RawRefinement`, supply an external-input-size polynomial, establish
CNFSAT in P or NP-completeness, or establish P = NP.
-/

import PNP.Concrete.PipelineStateNamespace

namespace PNP.Concrete

namespace PipelineStageBridges

open PipelineStateNamespace

/-! ### Verdict-indexed handoff namespaces -/

/-- Handoff-state image used after a simulated accept halt. -/
def acceptingHandoffState (state : Nat) : Nat :=
  handoffState (inputState state)

/-- Handoff-state image used after a simulated reject halt. -/
def rejectingHandoffState (state : Nat) : Nat :=
  handoffState (simulationState state)

theorem acceptingHandoffState_injective :
    Function.Injective acceptingHandoffState := by
  intro left right h
  exact inputState_injective (handoffState_injective h)

theorem rejectingHandoffState_injective :
    Function.Injective rejectingHandoffState := by
  intro left right h
  exact simulationState_injective (handoffState_injective h)

theorem acceptingHandoffState_ne_rejectingHandoffState
    (left right : Nat) :
    acceptingHandoffState left ≠ rejectingHandoffState right := by
  intro h
  exact inputState_ne_simulationState left right
    (handoffState_injective h)

/-! ### Literal one-step launch tables -/

/-- One symbol-preserving, head-preserving stage launch. -/
def launchRule (source target : Nat) (symbol : WorkSymbol) : WorkRule :=
  { sourceState := source
    readSymbol := symbol
    targetState := target
    writeSymbol := symbol
    move := .stay }

/-- A total finite launch table over all nine work symbols. -/
def launchRules (source target : Nat) : List WorkRule :=
  PipelineMachineSimulation.allWorkSymbols.map
    (launchRule source target)

private theorem findWorkRule_launchRulesFrom_of_mem
    (symbols : List WorkSymbol) (source target : Nat)
    (symbol : WorkSymbol) (hMem : symbol ∈ symbols) :
    findWorkRule (symbols.map (launchRule source target)) source symbol =
      some (launchRule source target symbol) := by
  induction symbols with
  | nil => contradiction
  | cons first rest ih =>
      by_cases hFirst : first = symbol
      · subst first
        exact findWorkRule_cons_of_matches _ _ _ _ ⟨rfl, rfl⟩
      · have hRest : symbol ∈ rest := by
          cases hMem with
          | head => exact False.elim (hFirst rfl)
          | tail _ hTail => exact hTail
        change findWorkRule
          (launchRule source target first ::
            rest.map (launchRule source target)) source symbol = _
        rw [findWorkRule_cons_of_not_matches]
        · exact ih hRest
        · intro hMatch
          exact hFirst (by simpa [launchRule] using hMatch.2)

theorem findWorkRule_launchRules (source target : Nat)
    (symbol : WorkSymbol) :
    findWorkRule (launchRules source target) source symbol =
      some (launchRule source target symbol) := by
  exact findWorkRule_launchRulesFrom_of_mem
    PipelineMachineSimulation.allWorkSymbols source target symbol
    (PipelineMachineSimulation.allWorkSymbols_mem symbol)

theorem findWorkRule_launchRules_none_of_source_ne
    (source target state : Nat) (symbol : WorkSymbol)
    (hSource : source ≠ state) :
    findWorkRule (launchRules source target) state symbol = none := by
  unfold launchRules
  apply PipelineMachineSimulation.findWorkRule_map_none_of_source_ne
  intro item
  simpa [launchRule] using hSource

theorem findWorkRule_renamedRules_none
    (encode : Nat -> Nat) (rules : List WorkRule)
    (state : Nat) (symbol : WorkSymbol)
    (hSource : forall source, encode source ≠ state) :
    findWorkRule (rules.map (renameRule encode)) state symbol = none := by
  apply PipelineMachineSimulation.findWorkRule_map_none_of_source_ne
  intro rule
  simpa [renameRule] using hSource rule.sourceState

/-- Launch the completed paired-input frame as the lifted target start. -/
def inputLaunchRules (machine : Machine) : List WorkRule :=
  launchRules
    (inputState PipelineInputFramer.pairedInputFramer.acceptState)
    (simulationState
      (PipelineMachineSimulation.liftMachine machine).startState)

/-- Launch represented-output handoff while remembering target acceptance. -/
def acceptingLaunchRules : List WorkRule :=
  launchRules
    (simulationState PipelineMachineSimulation.acceptSentinel)
    (acceptingHandoffState
      PipelineOutputHandoff.framedOutputHandoff.startState)

/-- Launch represented-output handoff while remembering target rejection. -/
def rejectingLaunchRules : List WorkRule :=
  launchRules
    (simulationState PipelineMachineSimulation.rejectSentinel)
    (rejectingHandoffState
      PipelineOutputHandoff.framedOutputHandoff.startState)

/-- The represented-output handoff in the accepting verdict image. -/
def acceptingOutputHandoff : WorkMachine :=
  renameMachine acceptingHandoffState
    PipelineOutputHandoff.framedOutputHandoff

/-- The represented-output handoff in the rejecting verdict image. -/
def rejectingOutputHandoff : WorkMachine :=
  renameMachine rejectingHandoffState
    PipelineOutputHandoff.framedOutputHandoff

/-- Literal bridge-first rule table.  Bridge priority is harmless away from
the three exact launch states and makes terminal dispatch explicit. -/
def bridgedRules (machine : Machine) : List WorkRule :=
  inputLaunchRules machine ++
    (acceptingLaunchRules ++
      (rejectingLaunchRules ++
        (PipelineInputFramer.pairedInputFramer.rules.map
            (renameRule inputState) ++
          ((PipelineMachineSimulation.liftMachine machine).rules.map
              (renameRule simulationState) ++
            (PipelineOutputHandoff.framedOutputHandoff.rules.map
                (renameRule acceptingHandoffState) ++
              PipelineOutputHandoff.framedOutputHandoff.rules.map
                (renameRule rejectingHandoffState))))))

/-- One finite work machine containing both bridge transitions and all four
verdict-safe stage tables. -/
def bridgedMachine (machine : Machine) : WorkMachine :=
  { rules := bridgedRules machine
    startState := inputState PipelineInputFramer.pairedInputFramer.startState
    acceptState := acceptingHandoffState
      PipelineOutputHandoff.framedOutputHandoff.acceptState
    rejectState := rejectingHandoffState
      PipelineOutputHandoff.framedOutputHandoff.acceptState }

/-! ### Exact displayed costs -/

/-- Work transitions through the simulator launch, excluding output handoff. -/
def simulationPrefixWorkSteps (left right : BitString)
    (sourceSteps : Nat) : Nat :=
  PipelineInputFramer.inputFramerWorkSteps
      (PipelineInputFramer.packedPairCount left right) +
    1 + 3 * sourceSteps

/-- Work transitions through represented-output handoff. -/
def bridgedWorkSteps (left right : BitString) (sourceSteps : Nat)
    (finalTape : Tape) : Nat :=
  simulationPrefixWorkSteps left right sourceSteps + 1 +
    PipelineOutputHandoff.framedOutputHandoffWorkSteps finalTape

/-- Raw transitions used by compilation of the displayed work trace. -/
def bridgedRawSteps (left right : BitString) (sourceSteps : Nat)
    (finalTape : Tape) : Nat :=
  6 * bridgedWorkSteps left right sourceSteps finalTape

/-! ### Generic exact-run transport -/

theorem workRunExact?_transport
    (source target : WorkMachine) (encode : Nat -> Nat)
    (hStep : forall config next,
      workStep? source config = some next ->
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
  | true =>
      exact False.elim (h ((nat_beq_true_iff left right).mp hBool))

/-! ### Global halt separation -/

theorem bridgedMachine_isHalted_input_false (machine : Machine)
    (state : Nat) (tape : WorkTape) :
    (bridgedMachine machine).isHalted
      (renameConfiguration inputState { state := state, tape := tape }) =
        false := by
  unfold WorkMachine.isHalted bridgedMachine renameConfiguration
  change
    ((inputState state == acceptingHandoffState
        PipelineOutputHandoff.framedOutputHandoff.acceptState) ||
      (inputState state == rejectingHandoffState
        PipelineOutputHandoff.framedOutputHandoff.acceptState)) = false
  unfold acceptingHandoffState rejectingHandoffState
  rw [nat_beq_false_of_ne _ _
      (inputState_ne_handoffState state
        (inputState PipelineOutputHandoff.framedOutputHandoff.acceptState)),
    nat_beq_false_of_ne _ _
      (inputState_ne_handoffState state
        (simulationState
          PipelineOutputHandoff.framedOutputHandoff.acceptState))]
  rfl

theorem bridgedMachine_isHalted_simulation_false (machine : Machine)
    (state : Nat) (tape : WorkTape) :
    (bridgedMachine machine).isHalted
      (renameConfiguration simulationState { state := state, tape := tape }) =
        false := by
  unfold WorkMachine.isHalted bridgedMachine renameConfiguration
  change
    ((simulationState state == acceptingHandoffState
        PipelineOutputHandoff.framedOutputHandoff.acceptState) ||
      (simulationState state == rejectingHandoffState
        PipelineOutputHandoff.framedOutputHandoff.acceptState)) = false
  unfold acceptingHandoffState rejectingHandoffState
  rw [nat_beq_false_of_ne _ _
      (simulationState_ne_handoffState state
        (inputState PipelineOutputHandoff.framedOutputHandoff.acceptState)),
    nat_beq_false_of_ne _ _
      (simulationState_ne_handoffState state
        (simulationState
          PipelineOutputHandoff.framedOutputHandoff.acceptState))]
  rfl

theorem bridgedMachine_isHalted_accepting_false_of_local
    (machine : Machine) (config : WorkConfiguration)
    (hLocal : PipelineOutputHandoff.framedOutputHandoff.isHalted config =
      false) :
    (bridgedMachine machine).isHalted
      (renameConfiguration acceptingHandoffState config) = false := by
  have hAccept : config.state ≠
      PipelineOutputHandoff.framedOutputHandoff.acceptState :=
    state_ne_accept_of_not_halted
      PipelineOutputHandoff.framedOutputHandoff config hLocal
  have hGlobalAccept : acceptingHandoffState config.state ≠
      acceptingHandoffState
        PipelineOutputHandoff.framedOutputHandoff.acceptState := by
    intro h
    exact hAccept (acceptingHandoffState_injective h)
  have hGlobalReject : acceptingHandoffState config.state ≠
      rejectingHandoffState
        PipelineOutputHandoff.framedOutputHandoff.acceptState :=
    acceptingHandoffState_ne_rejectingHandoffState _ _
  unfold WorkMachine.isHalted bridgedMachine renameConfiguration
  rw [nat_beq_false_of_ne _ _ hGlobalAccept,
    nat_beq_false_of_ne _ _ hGlobalReject]
  rfl

theorem bridgedMachine_isHalted_rejecting_false_of_local
    (machine : Machine) (config : WorkConfiguration)
    (hLocal : PipelineOutputHandoff.framedOutputHandoff.isHalted config =
      false) :
    (bridgedMachine machine).isHalted
      (renameConfiguration rejectingHandoffState config) = false := by
  have hAccept : config.state ≠
      PipelineOutputHandoff.framedOutputHandoff.acceptState :=
    state_ne_accept_of_not_halted
      PipelineOutputHandoff.framedOutputHandoff config hLocal
  have hGlobalAccept : rejectingHandoffState config.state ≠
      acceptingHandoffState
        PipelineOutputHandoff.framedOutputHandoff.acceptState := by
    intro h
    exact acceptingHandoffState_ne_rejectingHandoffState _ _ h.symm
  have hGlobalReject : rejectingHandoffState config.state ≠
      rejectingHandoffState
        PipelineOutputHandoff.framedOutputHandoff.acceptState := by
    intro h
    exact hAccept (rejectingHandoffState_injective h)
  unfold WorkMachine.isHalted bridgedMachine renameConfiguration
  rw [nat_beq_false_of_ne _ _ hGlobalAccept,
    nat_beq_false_of_ne _ _ hGlobalReject]
  rfl

/-! ### First-match isolation in the bridge-first table -/

theorem findWorkRule_bridged_input_of_some
    (machine : Machine) (state : Nat) (symbol : WorkSymbol)
    (rule : WorkRule)
    (hAccept : state ≠ PipelineInputFramer.pairedInputFramer.acceptState)
    (hFind : findWorkRule PipelineInputFramer.pairedInputFramer.rules
      state symbol = some rule) :
    findWorkRule (bridgedMachine machine).rules (inputState state) symbol =
      some (renameRule inputState rule) := by
  have hInputLaunch : findWorkRule (inputLaunchRules machine)
      (inputState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    intro h
    exact hAccept (inputState_injective h).symm
  have hAcceptLaunch : findWorkRule acceptingLaunchRules
      (inputState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    intro h
    exact inputState_ne_simulationState state
      PipelineMachineSimulation.acceptSentinel h.symm
  have hRejectLaunch : findWorkRule rejectingLaunchRules
      (inputState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    intro h
    exact inputState_ne_simulationState state
      PipelineMachineSimulation.rejectSentinel h.symm
  have hRenamed := findWorkRule_rename inputState inputState_injective
    PipelineInputFramer.pairedInputFramer.rules state symbol
  rw [hFind] at hRenamed
  unfold bridgedMachine bridgedRules
  rw [findWorkRule_append_of_none _ _ _ _ hInputLaunch,
    findWorkRule_append_of_none _ _ _ _ hAcceptLaunch,
    findWorkRule_append_of_none _ _ _ _ hRejectLaunch]
  exact findWorkRule_append_of_some _ _ _ _ _ hRenamed

theorem findWorkRule_bridged_simulation_of_some
    (machine : Machine) (state : Nat) (symbol : WorkSymbol)
    (rule : WorkRule)
    (hAccept : state ≠ PipelineMachineSimulation.acceptSentinel)
    (hReject : state ≠ PipelineMachineSimulation.rejectSentinel)
    (hFind : findWorkRule
      (PipelineMachineSimulation.liftMachine machine).rules
      state symbol = some rule) :
    findWorkRule (bridgedMachine machine).rules
      (simulationState state) symbol =
        some (renameRule simulationState rule) := by
  have hInputLaunch : findWorkRule (inputLaunchRules machine)
      (simulationState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact inputState_ne_simulationState _ _
  have hAcceptLaunch : findWorkRule acceptingLaunchRules
      (simulationState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    intro h
    exact hAccept (simulationState_injective h).symm
  have hRejectLaunch : findWorkRule rejectingLaunchRules
      (simulationState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    intro h
    exact hReject (simulationState_injective h).symm
  have hInputRules : findWorkRule
      (PipelineInputFramer.pairedInputFramer.rules.map
        (renameRule inputState)) (simulationState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact inputState_ne_simulationState source state
  have hRenamed := findWorkRule_rename simulationState
    simulationState_injective
    (PipelineMachineSimulation.liftMachine machine).rules state symbol
  rw [hFind] at hRenamed
  unfold bridgedMachine bridgedRules
  rw [findWorkRule_append_of_none _ _ _ _ hInputLaunch,
    findWorkRule_append_of_none _ _ _ _ hAcceptLaunch,
    findWorkRule_append_of_none _ _ _ _ hRejectLaunch,
    findWorkRule_append_of_none _ _ _ _ hInputRules]
  exact findWorkRule_append_of_some _ _ _ _ _ hRenamed

theorem findWorkRule_bridged_acceptingHandoff_of_some
    (machine : Machine) (state : Nat) (symbol : WorkSymbol)
    (rule : WorkRule)
    (hFind : findWorkRule
      PipelineOutputHandoff.framedOutputHandoff.rules state symbol =
        some rule) :
    findWorkRule (bridgedMachine machine).rules
      (acceptingHandoffState state) symbol =
        some (renameRule acceptingHandoffState rule) := by
  have hInputLaunch : findWorkRule (inputLaunchRules machine)
      (acceptingHandoffState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact inputState_ne_handoffState _ _
  have hAcceptLaunch : findWorkRule acceptingLaunchRules
      (acceptingHandoffState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact simulationState_ne_handoffState _ _
  have hRejectLaunch : findWorkRule rejectingLaunchRules
      (acceptingHandoffState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact simulationState_ne_handoffState _ _
  have hInputRules : findWorkRule
      (PipelineInputFramer.pairedInputFramer.rules.map
        (renameRule inputState)) (acceptingHandoffState state) symbol =
        none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact inputState_ne_handoffState _ _
  have hSimulationRules : findWorkRule
      ((PipelineMachineSimulation.liftMachine machine).rules.map
        (renameRule simulationState)) (acceptingHandoffState state) symbol =
        none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact simulationState_ne_handoffState _ _
  have hRenamed := findWorkRule_rename acceptingHandoffState
    acceptingHandoffState_injective
    PipelineOutputHandoff.framedOutputHandoff.rules state symbol
  rw [hFind] at hRenamed
  unfold bridgedMachine bridgedRules
  rw [findWorkRule_append_of_none _ _ _ _ hInputLaunch,
    findWorkRule_append_of_none _ _ _ _ hAcceptLaunch,
    findWorkRule_append_of_none _ _ _ _ hRejectLaunch,
    findWorkRule_append_of_none _ _ _ _ hInputRules,
    findWorkRule_append_of_none _ _ _ _ hSimulationRules]
  exact findWorkRule_append_of_some _ _ _ _ _ hRenamed

theorem findWorkRule_bridged_rejectingHandoff_of_some
    (machine : Machine) (state : Nat) (symbol : WorkSymbol)
    (rule : WorkRule)
    (hFind : findWorkRule
      PipelineOutputHandoff.framedOutputHandoff.rules state symbol =
        some rule) :
    findWorkRule (bridgedMachine machine).rules
      (rejectingHandoffState state) symbol =
        some (renameRule rejectingHandoffState rule) := by
  have hInputLaunch : findWorkRule (inputLaunchRules machine)
      (rejectingHandoffState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact inputState_ne_handoffState _ _
  have hAcceptLaunch : findWorkRule acceptingLaunchRules
      (rejectingHandoffState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact simulationState_ne_handoffState _ _
  have hRejectLaunch : findWorkRule rejectingLaunchRules
      (rejectingHandoffState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact simulationState_ne_handoffState _ _
  have hInputRules : findWorkRule
      (PipelineInputFramer.pairedInputFramer.rules.map
        (renameRule inputState)) (rejectingHandoffState state) symbol =
        none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact inputState_ne_handoffState _ _
  have hSimulationRules : findWorkRule
      ((PipelineMachineSimulation.liftMachine machine).rules.map
        (renameRule simulationState)) (rejectingHandoffState state) symbol =
        none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact simulationState_ne_handoffState _ _
  have hAcceptingRules : findWorkRule
      (PipelineOutputHandoff.framedOutputHandoff.rules.map
        (renameRule acceptingHandoffState))
      (rejectingHandoffState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact acceptingHandoffState_ne_rejectingHandoffState source state
  have hRenamed := findWorkRule_rename rejectingHandoffState
    rejectingHandoffState_injective
    PipelineOutputHandoff.framedOutputHandoff.rules state symbol
  rw [hFind] at hRenamed
  unfold bridgedMachine bridgedRules
  rw [findWorkRule_append_of_none _ _ _ _ hInputLaunch,
    findWorkRule_append_of_none _ _ _ _ hAcceptLaunch,
    findWorkRule_append_of_none _ _ _ _ hRejectLaunch,
    findWorkRule_append_of_none _ _ _ _ hInputRules,
    findWorkRule_append_of_none _ _ _ _ hSimulationRules,
    findWorkRule_append_of_none _ _ _ _ hAcceptingRules]
  exact hRenamed

/-! ### Ordinary stage steps survive bridge priority -/

theorem input_workStep?_of_some (machine : Machine)
    (config next : WorkConfiguration)
    (hStep : workStep? PipelineInputFramer.pairedInputFramer config =
      some next) :
    workStep? (bridgedMachine machine)
        (renameConfiguration inputState config) =
      some (renameConfiguration inputState next) := by
  rcases workStep?_some_exists PipelineInputFramer.pairedInputFramer
      config next hStep with ⟨rule, hHalted, hFind, hNext⟩
  have hAccept := state_ne_accept_of_not_halted
    PipelineInputFramer.pairedInputFramer config hHalted
  have hGlobalHalted := bridgedMachine_isHalted_input_false
    machine config.state config.tape
  have hGlobalFind := findWorkRule_bridged_input_of_some
    machine config.state config.tape.head rule hAccept hFind
  have hGlobalStep := workStep?_eq_apply_of_find
    (bridgedMachine machine) (renameConfiguration inputState config)
    (renameRule inputState rule) hGlobalHalted hGlobalFind
  calc
    workStep? (bridgedMachine machine)
        (renameConfiguration inputState config) =
        some (applyWorkRule (renameRule inputState rule)
          (renameConfiguration inputState config)) := hGlobalStep
    _ = some (renameConfiguration inputState
          (applyWorkRule rule config)) :=
      congrArg Option.some (applyWorkRule_rename inputState rule config)
    _ = some (renameConfiguration inputState next) :=
      congrArg (fun value => some (renameConfiguration inputState value))
        hNext.symm

theorem simulation_workStep?_of_some (machine : Machine)
    (config next : WorkConfiguration)
    (hStep : workStep? (PipelineMachineSimulation.liftMachine machine)
      config = some next) :
    workStep? (bridgedMachine machine)
        (renameConfiguration simulationState config) =
      some (renameConfiguration simulationState next) := by
  rcases workStep?_some_exists
      (PipelineMachineSimulation.liftMachine machine)
      config next hStep with ⟨rule, hHalted, hFind, hNext⟩
  have hAccept := state_ne_accept_of_not_halted
    (PipelineMachineSimulation.liftMachine machine) config hHalted
  have hReject := state_ne_reject_of_not_halted
    (PipelineMachineSimulation.liftMachine machine) config hHalted
  have hGlobalHalted := bridgedMachine_isHalted_simulation_false
    machine config.state config.tape
  have hGlobalFind := findWorkRule_bridged_simulation_of_some
    machine config.state config.tape.head rule hAccept hReject hFind
  have hGlobalStep := workStep?_eq_apply_of_find
    (bridgedMachine machine) (renameConfiguration simulationState config)
    (renameRule simulationState rule) hGlobalHalted hGlobalFind
  calc
    workStep? (bridgedMachine machine)
        (renameConfiguration simulationState config) =
        some (applyWorkRule (renameRule simulationState rule)
          (renameConfiguration simulationState config)) := hGlobalStep
    _ = some (renameConfiguration simulationState
          (applyWorkRule rule config)) :=
      congrArg Option.some (applyWorkRule_rename simulationState rule config)
    _ = some (renameConfiguration simulationState next) :=
      congrArg (fun value => some (renameConfiguration simulationState value))
        hNext.symm

theorem acceptingHandoff_workStep?_of_some (machine : Machine)
    (config next : WorkConfiguration)
    (hStep : workStep? PipelineOutputHandoff.framedOutputHandoff config =
      some next) :
    workStep? (bridgedMachine machine)
        (renameConfiguration acceptingHandoffState config) =
      some (renameConfiguration acceptingHandoffState next) := by
  rcases workStep?_some_exists PipelineOutputHandoff.framedOutputHandoff
      config next hStep with ⟨rule, hHalted, hFind, hNext⟩
  have hGlobalHalted :=
    bridgedMachine_isHalted_accepting_false_of_local machine config hHalted
  have hGlobalFind := findWorkRule_bridged_acceptingHandoff_of_some
    machine config.state config.tape.head rule hFind
  have hGlobalStep := workStep?_eq_apply_of_find
    (bridgedMachine machine)
    (renameConfiguration acceptingHandoffState config)
    (renameRule acceptingHandoffState rule) hGlobalHalted hGlobalFind
  calc
    workStep? (bridgedMachine machine)
        (renameConfiguration acceptingHandoffState config) =
        some (applyWorkRule (renameRule acceptingHandoffState rule)
          (renameConfiguration acceptingHandoffState config)) := hGlobalStep
    _ = some (renameConfiguration acceptingHandoffState
          (applyWorkRule rule config)) :=
      congrArg Option.some
        (applyWorkRule_rename acceptingHandoffState rule config)
    _ = some (renameConfiguration acceptingHandoffState next) :=
      congrArg
        (fun value => some (renameConfiguration acceptingHandoffState value))
        hNext.symm

theorem rejectingHandoff_workStep?_of_some (machine : Machine)
    (config next : WorkConfiguration)
    (hStep : workStep? PipelineOutputHandoff.framedOutputHandoff config =
      some next) :
    workStep? (bridgedMachine machine)
        (renameConfiguration rejectingHandoffState config) =
      some (renameConfiguration rejectingHandoffState next) := by
  rcases workStep?_some_exists PipelineOutputHandoff.framedOutputHandoff
      config next hStep with ⟨rule, hHalted, hFind, hNext⟩
  have hGlobalHalted :=
    bridgedMachine_isHalted_rejecting_false_of_local machine config hHalted
  have hGlobalFind := findWorkRule_bridged_rejectingHandoff_of_some
    machine config.state config.tape.head rule hFind
  have hGlobalStep := workStep?_eq_apply_of_find
    (bridgedMachine machine)
    (renameConfiguration rejectingHandoffState config)
    (renameRule rejectingHandoffState rule) hGlobalHalted hGlobalFind
  calc
    workStep? (bridgedMachine machine)
        (renameConfiguration rejectingHandoffState config) =
        some (applyWorkRule (renameRule rejectingHandoffState rule)
          (renameConfiguration rejectingHandoffState config)) := hGlobalStep
    _ = some (renameConfiguration rejectingHandoffState
          (applyWorkRule rule config)) :=
      congrArg Option.some
        (applyWorkRule_rename rejectingHandoffState rule config)
    _ = some (renameConfiguration rejectingHandoffState next) :=
      congrArg
        (fun value => some (renameConfiguration rejectingHandoffState value))
        hNext.symm

/-! ### Exact one-step stage launches -/

theorem simulationAcceptState_ne_simulationRejectState :
    simulationState PipelineMachineSimulation.acceptSentinel ≠
      simulationState PipelineMachineSimulation.rejectSentinel := by
  intro h
  have hSentinel := simulationState_injective h
  exact PipelineMachineSimulation.taggedState_ne_of_phase_ne
    (leftPayload := 0) (rightPayload := 0)
    (leftPhase := .accept) (rightPhase := .reject)
    (by intro impossible; contradiction) hSentinel

theorem inputLaunch_workStep (machine : Machine)
    (left right : BitString) :
    workStep? (bridgedMachine machine)
        (renameConfiguration inputState
          (PipelineInputFramer.pairedInputFramerFinalConfiguration
            left right)) =
      some (renameConfiguration simulationState
        (PipelineMachineSimulation.liftConfiguration machine
          (startConfig machine (BitString.pair left right))
          (PipelineInputFramer.pairedInputFramerFinalTape left right))) := by
  let final := PipelineInputFramer.pairedInputFramerFinalConfiguration
    left right
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
      PipelineInputFramer.pairedInputFramerFinalConfiguration] using hLaunch
  have hFind : findWorkRule (bridgedMachine machine).rules
      (inputState final.state) final.tape.head =
        some (launchRule
          (inputState PipelineInputFramer.pairedInputFramer.acceptState)
          (simulationState
            (PipelineMachineSimulation.liftMachine machine).startState)
          final.tape.head) := by
    unfold bridgedMachine bridgedRules
    exact findWorkRule_append_of_some _ _ _ _ _ hInput
  have hStep := workStep?_eq_apply_of_find (bridgedMachine machine)
    (renameConfiguration inputState final)
    (launchRule
      (inputState PipelineInputFramer.pairedInputFramer.acceptState)
      (simulationState
        (PipelineMachineSimulation.liftMachine machine).startState)
      final.tape.head) hHalted hFind
  simpa [final, launchRule, applyWorkRule, WorkTape.write, WorkTape.move,
    PipelineInputFramer.pairedInputFramerFinalConfiguration,
    PipelineMachineSimulation.liftMachine,
    PipelineMachineSimulation.liftConfiguration, startConfig,
    renameConfiguration] using hStep

theorem acceptingLaunch_workStep (machine : Machine) (tape : WorkTape) :
    workStep? (bridgedMachine machine)
        (renameConfiguration simulationState
          { state := PipelineMachineSimulation.acceptSentinel,
            tape := tape }) =
      some (renameConfiguration acceptingHandoffState
        (workStartConfiguration
          PipelineOutputHandoff.framedOutputHandoff tape)) := by
  have hHalted := bridgedMachine_isHalted_simulation_false
    machine PipelineMachineSimulation.acceptSentinel tape
  have hInputNone : findWorkRule (inputLaunchRules machine)
      (simulationState PipelineMachineSimulation.acceptSentinel)
      tape.head = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact inputState_ne_simulationState _ _
  have hAccept := findWorkRule_launchRules
    (simulationState PipelineMachineSimulation.acceptSentinel)
    (acceptingHandoffState
      PipelineOutputHandoff.framedOutputHandoff.startState) tape.head
  have hFind : findWorkRule (bridgedMachine machine).rules
      (simulationState PipelineMachineSimulation.acceptSentinel)
      tape.head =
        some (launchRule
          (simulationState PipelineMachineSimulation.acceptSentinel)
          (acceptingHandoffState
            PipelineOutputHandoff.framedOutputHandoff.startState)
          tape.head) := by
    unfold bridgedMachine bridgedRules
    rw [findWorkRule_append_of_none _ _ _ _ hInputNone]
    exact findWorkRule_append_of_some _ _ _ _ _ hAccept
  have hStep := workStep?_eq_apply_of_find (bridgedMachine machine)
    (renameConfiguration simulationState
      { state := PipelineMachineSimulation.acceptSentinel, tape := tape })
    (launchRule
      (simulationState PipelineMachineSimulation.acceptSentinel)
      (acceptingHandoffState
        PipelineOutputHandoff.framedOutputHandoff.startState)
      tape.head) hHalted hFind
  simpa [launchRule, applyWorkRule, WorkTape.write, WorkTape.move,
    workStartConfiguration, renameConfiguration] using hStep

theorem rejectingLaunch_workStep (machine : Machine) (tape : WorkTape) :
    workStep? (bridgedMachine machine)
        (renameConfiguration simulationState
          { state := PipelineMachineSimulation.rejectSentinel,
            tape := tape }) =
      some (renameConfiguration rejectingHandoffState
        (workStartConfiguration
          PipelineOutputHandoff.framedOutputHandoff tape)) := by
  have hHalted := bridgedMachine_isHalted_simulation_false
    machine PipelineMachineSimulation.rejectSentinel tape
  have hInputNone : findWorkRule (inputLaunchRules machine)
      (simulationState PipelineMachineSimulation.rejectSentinel)
      tape.head = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact inputState_ne_simulationState _ _
  have hAcceptNone : findWorkRule acceptingLaunchRules
      (simulationState PipelineMachineSimulation.rejectSentinel)
      tape.head = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact simulationAcceptState_ne_simulationRejectState
  have hReject := findWorkRule_launchRules
    (simulationState PipelineMachineSimulation.rejectSentinel)
    (rejectingHandoffState
      PipelineOutputHandoff.framedOutputHandoff.startState) tape.head
  have hFind : findWorkRule (bridgedMachine machine).rules
      (simulationState PipelineMachineSimulation.rejectSentinel)
      tape.head =
        some (launchRule
          (simulationState PipelineMachineSimulation.rejectSentinel)
          (rejectingHandoffState
            PipelineOutputHandoff.framedOutputHandoff.startState)
          tape.head) := by
    unfold bridgedMachine bridgedRules
    rw [findWorkRule_append_of_none _ _ _ _ hInputNone,
      findWorkRule_append_of_none _ _ _ _ hAcceptNone]
    exact findWorkRule_append_of_some _ _ _ _ _ hReject
  have hStep := workStep?_eq_apply_of_find (bridgedMachine machine)
    (renameConfiguration simulationState
      { state := PipelineMachineSimulation.rejectSentinel, tape := tape })
    (launchRule
      (simulationState PipelineMachineSimulation.rejectSentinel)
      (rejectingHandoffState
        PipelineOutputHandoff.framedOutputHandoff.startState)
      tape.head) hHalted hFind
  simpa [launchRule, applyWorkRule, WorkTape.write, WorkTape.move,
    workStartConfiguration, renameConfiguration] using hStep

/-! ### Exact local traces inside the bridged machine -/

theorem input_workRunExact_of_exact (machine : Machine)
    (steps : Nat) (start final : WorkConfiguration)
    (hRun : workRunExact? PipelineInputFramer.pairedInputFramer steps
      start = some final) :
    workRunExact? (bridgedMachine machine) steps
        (renameConfiguration inputState start) =
      some (renameConfiguration inputState final) := by
  exact workRunExact?_transport
    PipelineInputFramer.pairedInputFramer (bridgedMachine machine)
    inputState (input_workStep?_of_some machine) steps start final hRun

theorem simulation_workRunExact_of_exact (machine : Machine)
    (steps : Nat) (start final : WorkConfiguration)
    (hRun : workRunExact?
      (PipelineMachineSimulation.liftMachine machine) steps start =
        some final) :
    workRunExact? (bridgedMachine machine) steps
        (renameConfiguration simulationState start) =
      some (renameConfiguration simulationState final) := by
  exact workRunExact?_transport
    (PipelineMachineSimulation.liftMachine machine) (bridgedMachine machine)
    simulationState (simulation_workStep?_of_some machine)
    steps start final hRun

theorem acceptingHandoff_workRunExact_of_exact (machine : Machine)
    (steps : Nat) (start final : WorkConfiguration)
    (hRun : workRunExact? PipelineOutputHandoff.framedOutputHandoff steps
      start = some final) :
    workRunExact? (bridgedMachine machine) steps
        (renameConfiguration acceptingHandoffState start) =
      some (renameConfiguration acceptingHandoffState final) := by
  exact workRunExact?_transport
    PipelineOutputHandoff.framedOutputHandoff (bridgedMachine machine)
    acceptingHandoffState (acceptingHandoff_workStep?_of_some machine)
    steps start final hRun

theorem rejectingHandoff_workRunExact_of_exact (machine : Machine)
    (steps : Nat) (start final : WorkConfiguration)
    (hRun : workRunExact? PipelineOutputHandoff.framedOutputHandoff steps
      start = some final) :
    workRunExact? (bridgedMachine machine) steps
        (renameConfiguration rejectingHandoffState start) =
      some (renameConfiguration rejectingHandoffState final) := by
  exact workRunExact?_transport
    PipelineOutputHandoff.framedOutputHandoff (bridgedMachine machine)
    rejectingHandoffState (rejectingHandoff_workStep?_of_some machine)
    steps start final hRun

/-! ### Cumulative executable traces -/

/-- Framing, the first launch, and every supplied exact target execution form
one exact prefix in the literal bridged rule table. -/
theorem simulationPrefix_workRunExact_of_rawRunExact
    (machine : Machine) (steps : Nat) (left right : BitString)
    (final : Configuration)
    (hRaw : PipelineMachineSimulation.rawRunExact? machine steps
      (startConfig machine (BitString.pair left right)) = some final) :
    ∃ workFinal,
      workRunExact? (bridgedMachine machine)
          (simulationPrefixWorkSteps left right steps)
          (workStartConfiguration (bridgedMachine machine)
            (pairedWorkTape left right)) =
        some (renameConfiguration simulationState workFinal) ∧
      PipelineMachineSimulation.RepresentsConfiguration
        machine final workFinal := by
  let framerSteps := PipelineInputFramer.inputFramerWorkSteps
    (PipelineInputFramer.packedPairCount left right)
  let framerFinal :=
    PipelineInputFramer.pairedInputFramerFinalConfiguration left right
  let rawStart := startConfig machine (BitString.pair left right)
  have hFramerLocal :=
    PipelineInputFramer.pairedInputFramer_workRunExact left right
  have hFramer := input_workRunExact_of_exact machine framerSteps
    (workStartConfiguration PipelineInputFramer.pairedInputFramer
      (pairedWorkTape left right)) framerFinal hFramerLocal
  change workRunExact? (bridgedMachine machine) framerSteps
      (workStartConfiguration (bridgedMachine machine)
        (pairedWorkTape left right)) =
    some (renameConfiguration inputState framerFinal) at hFramer
  have hInputStep := inputLaunch_workStep machine left right
  have hInputBridge : workRunExact? (bridgedMachine machine) 1
      (renameConfiguration inputState framerFinal) =
        some (renameConfiguration simulationState
          (PipelineMachineSimulation.liftConfiguration machine rawStart
            (PipelineInputFramer.pairedInputFramerFinalTape left right))) := by
    change
      (match workStep? (bridgedMachine machine)
          (renameConfiguration inputState framerFinal) with
       | none => none
       | some next => workRunExact? (bridgedMachine machine) 0 next) = _
    rw [hInputStep]
    rfl
  have hFrameRepresents :=
    PipelineInputFramer.pairedInputFramerFinal_represents left right
  rcases PipelineMachineSimulation.workRunExact_three_mul_of_rawRunExact
      machine steps rawStart final
      (PipelineInputFramer.pairedInputFramerFinalTape left right)
      hRaw hFrameRepresents with
    ⟨workFinal, hSimulationLocal, hFinalRepresents⟩
  have hSimulation := simulation_workRunExact_of_exact machine (3 * steps)
    (PipelineMachineSimulation.liftConfiguration machine rawStart
      (PipelineInputFramer.pairedInputFramerFinalTape left right))
    workFinal hSimulationLocal
  have hFramerAndLaunch := PipelineMachineSimulation.workRunExact?_compose
    (bridgedMachine machine) framerSteps 1
    (workStartConfiguration (bridgedMachine machine)
      (pairedWorkTape left right))
    (renameConfiguration inputState framerFinal)
    (renameConfiguration simulationState
      (PipelineMachineSimulation.liftConfiguration machine rawStart
        (PipelineInputFramer.pairedInputFramerFinalTape left right)))
    hFramer hInputBridge
  have hPrefix := PipelineMachineSimulation.workRunExact?_compose
    (bridgedMachine machine) (framerSteps + 1) (3 * steps)
    (workStartConfiguration (bridgedMachine machine)
      (pairedWorkTape left right))
    (renameConfiguration simulationState
      (PipelineMachineSimulation.liftConfiguration machine rawStart
        (PipelineInputFramer.pairedInputFramerFinalTape left right)))
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

/-- A target accept trace launches the accepting handoff copy and reaches its
represented-output endpoint at the displayed cumulative work cost. -/
theorem bridgedAccept_workRunExact_of_rawRunExact
    (machine : Machine) (steps : Nat) (left right : BitString)
    (final : Configuration)
    (hRaw : PipelineMachineSimulation.rawRunExact? machine steps
      (startConfig machine (BitString.pair left right)) = some final)
    (hAccept : final.state = machine.acceptState) :
    ∃ simulatorFinal handoffFinal,
      PipelineMachineSimulation.RepresentsConfiguration
          machine final simulatorFinal ∧
      PipelineTape.Represents final.tape.handoffTarget handoffFinal ∧
      workRunExact? (bridgedMachine machine)
          (bridgedWorkSteps left right steps final.tape)
          (workStartConfiguration (bridgedMachine machine)
            (pairedWorkTape left right)) =
        some (renameConfiguration acceptingHandoffState
          (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
            handoffFinal)) := by
  rcases simulationPrefix_workRunExact_of_rawRunExact
      machine steps left right final hRaw with
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
    (simulationPrefixWorkSteps left right steps) 1
    (workStartConfiguration (bridgedMachine machine)
      (pairedWorkTape left right))
    (renameConfiguration simulationState simulatorFinal)
    (renameConfiguration acceptingHandoffState
      (workStartConfiguration PipelineOutputHandoff.framedOutputHandoff
        simulatorFinal.tape)) hPrefix hLaunch
  have hComplete := PipelineMachineSimulation.workRunExact?_compose
    (bridgedMachine machine)
    (simulationPrefixWorkSteps left right steps + 1)
    (PipelineOutputHandoff.framedOutputHandoffWorkSteps final.tape)
    (workStartConfiguration (bridgedMachine machine)
      (pairedWorkTape left right))
    (renameConfiguration acceptingHandoffState
      (workStartConfiguration PipelineOutputHandoff.framedOutputHandoff
        simulatorFinal.tape))
    (renameConfiguration acceptingHandoffState
      (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
        handoffFinal)) hPrefixAndLaunch hHandoff
  exact ⟨simulatorFinal, handoffFinal, hFinalRepresents,
    hHandoffRepresents, by
      simpa [bridgedWorkSteps] using hComplete⟩

/-- A target reject trace uses the disjoint rejecting handoff copy and reaches
the global rejecting endpoint at the same cumulative work cost. -/
theorem bridgedReject_workRunExact_of_rawRunExact
    (machine : Machine) (steps : Nat) (left right : BitString)
    (final : Configuration)
    (hDistinct : machine.rejectState ≠ machine.acceptState)
    (hRaw : PipelineMachineSimulation.rawRunExact? machine steps
      (startConfig machine (BitString.pair left right)) = some final)
    (hReject : final.state = machine.rejectState) :
    ∃ simulatorFinal handoffFinal,
      PipelineMachineSimulation.RepresentsConfiguration
          machine final simulatorFinal ∧
      PipelineTape.Represents final.tape.handoffTarget handoffFinal ∧
      workRunExact? (bridgedMachine machine)
          (bridgedWorkSteps left right steps final.tape)
          (workStartConfiguration (bridgedMachine machine)
            (pairedWorkTape left right)) =
        some (renameConfiguration rejectingHandoffState
          (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
            handoffFinal)) := by
  rcases simulationPrefix_workRunExact_of_rawRunExact
      machine steps left right final hRaw with
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
    (simulationPrefixWorkSteps left right steps) 1
    (workStartConfiguration (bridgedMachine machine)
      (pairedWorkTape left right))
    (renameConfiguration simulationState simulatorFinal)
    (renameConfiguration rejectingHandoffState
      (workStartConfiguration PipelineOutputHandoff.framedOutputHandoff
        simulatorFinal.tape)) hPrefix hLaunch
  have hComplete := PipelineMachineSimulation.workRunExact?_compose
    (bridgedMachine machine)
    (simulationPrefixWorkSteps left right steps + 1)
    (PipelineOutputHandoff.framedOutputHandoffWorkSteps final.tape)
    (workStartConfiguration (bridgedMachine machine)
      (pairedWorkTape left right))
    (renameConfiguration rejectingHandoffState
      (workStartConfiguration PipelineOutputHandoff.framedOutputHandoff
        simulatorFinal.tape))
    (renameConfiguration rejectingHandoffState
      (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
        handoffFinal)) hPrefixAndLaunch hHandoff
  exact ⟨simulatorFinal, handoffFinal, hFinalRepresents,
    hHandoffRepresents, by
      simpa [bridgedWorkSteps] using hComplete⟩

/-! ### Verdict and compiled-raw endpoints -/

theorem acceptingHandoffFinal_state_eq_accept (machine : Machine)
    (tape : WorkTape) :
    (renameConfiguration acceptingHandoffState
      (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration tape)).state =
        (bridgedMachine machine).acceptState := by
  rfl

theorem rejectingHandoffFinal_state_eq_reject (machine : Machine)
    (tape : WorkTape) :
    (renameConfiguration rejectingHandoffState
      (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration tape)).state =
        (bridgedMachine machine).rejectState := by
  rfl

theorem acceptingHandoffFinal_isHalted (machine : Machine)
    (tape : WorkTape) :
    (bridgedMachine machine).isHalted
      (renameConfiguration acceptingHandoffState
        (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration tape)) =
      true := by
  unfold WorkMachine.isHalted
  rw [acceptingHandoffFinal_state_eq_accept machine tape]
  have hRefl :
      ((bridgedMachine machine).acceptState ==
        (bridgedMachine machine).acceptState) = true :=
    (nat_beq_true_iff _ _).mpr rfl
  rw [hRefl]
  rfl

theorem rejectingHandoffFinal_isHalted (machine : Machine)
    (tape : WorkTape) :
    (bridgedMachine machine).isHalted
      (renameConfiguration rejectingHandoffState
        (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration tape)) =
      true := by
  unfold WorkMachine.isHalted
  rw [rejectingHandoffFinal_state_eq_reject machine tape]
  have hNotAccept : (bridgedMachine machine).rejectState ≠
      (bridgedMachine machine).acceptState := by
    intro h
    exact acceptingHandoffState_ne_rejectingHandoffState _ _ h.symm
  have hRejectFalse := nat_beq_false_of_ne
    (bridgedMachine machine).rejectState
    (bridgedMachine machine).acceptState hNotAccept
  have hRefl :
      ((bridgedMachine machine).rejectState ==
        (bridgedMachine machine).rejectState) = true :=
    (nat_beq_true_iff _ _).mpr rfl
  rw [hRejectFalse, hRefl]
  rfl

theorem bridgedMachine_acceptState_ne_rejectState (machine : Machine) :
    (bridgedMachine machine).acceptState ≠
      (bridgedMachine machine).rejectState := by
  exact acceptingHandoffState_ne_rejectingHandoffState _ _

/-- The cumulative cost definition exposes exactly two launch transitions,
the three-for-one simulator cost, and the existing handoff cost. -/
theorem bridgedWorkSteps_eq (left right : BitString) (sourceSteps : Nat)
    (finalTape : Tape) :
    bridgedWorkSteps left right sourceSteps finalTape =
      PipelineInputFramer.inputFramerWorkSteps
          (PipelineInputFramer.packedPairCount left right) +
        1 + 3 * sourceSteps + 1 +
        PipelineOutputHandoff.framedOutputHandoffWorkSteps finalTape := by
  rfl

/-- Exact target acceptance remains acceptance after both launches and the
internal represented-output handoff. -/
theorem workBoundedDecide_bridged_accept_of_rawRunExact
    (machine : Machine) (steps : Nat) (left right : BitString)
    (final : Configuration)
    (hRaw : PipelineMachineSimulation.rawRunExact? machine steps
      (startConfig machine (BitString.pair left right)) = some final)
    (hAccept : final.state = machine.acceptState) :
    workBoundedDecide (bridgedMachine machine)
        (bridgedWorkSteps left right steps final.tape)
        (pairedWorkTape left right) = .accept := by
  rcases bridgedAccept_workRunExact_of_rawRunExact
      machine steps left right final hRaw hAccept with
    ⟨_, handoffFinal, _, _, hExact⟩
  have hRun := workRun_eq_of_workRunExact
    (bridgedMachine machine) (bridgedWorkSteps left right steps final.tape)
    (workStartConfiguration (bridgedMachine machine)
      (pairedWorkTape left right))
    (renameConfiguration acceptingHandoffState
      (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
        handoffFinal)) hExact
  apply (workBoundedDecide_accept_iff_final
    (bridgedMachine machine) (bridgedWorkSteps left right steps final.tape)
    (pairedWorkTape left right)).2
  rw [hRun]
  exact acceptingHandoffFinal_state_eq_accept machine handoffFinal

/-- Exact target rejection remains rejection; the explicit distinctness
premise matches the interpreter's accept-before-reject convention. -/
theorem workBoundedDecide_bridged_reject_of_rawRunExact
    (machine : Machine) (steps : Nat) (left right : BitString)
    (final : Configuration)
    (hDistinct : machine.rejectState ≠ machine.acceptState)
    (hRaw : PipelineMachineSimulation.rawRunExact? machine steps
      (startConfig machine (BitString.pair left right)) = some final)
    (hReject : final.state = machine.rejectState) :
    workBoundedDecide (bridgedMachine machine)
        (bridgedWorkSteps left right steps final.tape)
        (pairedWorkTape left right) = .reject := by
  rcases bridgedReject_workRunExact_of_rawRunExact
      machine steps left right final hDistinct hRaw hReject with
    ⟨_, handoffFinal, _, _, hExact⟩
  have hRun := workRun_eq_of_workRunExact
    (bridgedMachine machine) (bridgedWorkSteps left right steps final.tape)
    (workStartConfiguration (bridgedMachine machine)
      (pairedWorkTape left right))
    (renameConfiguration rejectingHandoffState
      (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
        handoffFinal)) hExact
  apply (workBoundedDecide_reject_iff_final
    (bridgedMachine machine) (bridgedWorkSteps left right steps final.tape)
    (pairedWorkTape left right)).2
  constructor
  · rw [hRun]
    intro hEqual
    exact bridgedMachine_acceptState_ne_rejectState machine hEqual.symm
  · rw [hRun]
    exact rejectingHandoffFinal_state_eq_reject machine handoffFinal

/-- At the exact end of any supplied target prefix, a nonterminal simulator
state is still reported as timeout.  In particular, no stuck nonhalting raw
endpoint is converted into rejection by a launch rule. -/
theorem simulationPrefix_workBoundedDecide_timeout
    (machine : Machine) (steps : Nat) (left right : BitString)
    (final : Configuration)
    (hRaw : PipelineMachineSimulation.rawRunExact? machine steps
      (startConfig machine (BitString.pair left right)) = some final) :
    workBoundedDecide (bridgedMachine machine)
        (simulationPrefixWorkSteps left right steps)
        (pairedWorkTape left right) = .timeout := by
  rcases simulationPrefix_workRunExact_of_rawRunExact
      machine steps left right final hRaw with
    ⟨workFinal, hExact, _⟩
  have hRun := workRun_eq_of_workRunExact
    (bridgedMachine machine) (simulationPrefixWorkSteps left right steps)
    (workStartConfiguration (bridgedMachine machine)
      (pairedWorkTape left right))
    (renameConfiguration simulationState workFinal) hExact
  have hAccept : simulationState workFinal.state ≠
      (bridgedMachine machine).acceptState := by
    exact simulationState_ne_handoffState _ _
  have hReject : simulationState workFinal.state ≠
      (bridgedMachine machine).rejectState := by
    exact simulationState_ne_handoffState _ _
  unfold workBoundedDecide
  rw [hRun]
  change
    (if (simulationState workFinal.state ==
        (bridgedMachine machine).acceptState) = true then WorkVerdict.accept
     else if (simulationState workFinal.state ==
        (bridgedMachine machine).rejectState) = true then WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout
  rw [nat_beq_false_of_ne _ _ hAccept,
    nat_beq_false_of_ne _ _ hReject]
  rfl

/-- Explicit stuck-endpoint corollary: a raw endpoint with no successor that
is not designated halting is timeout at the exact cumulative prefix budget,
never rejection. -/
theorem workBoundedDecide_bridged_timeout_of_stuck_rawRunExact
    (machine : Machine) (steps : Nat) (left right : BitString)
    (final : Configuration)
    (hRaw : PipelineMachineSimulation.rawRunExact? machine steps
      (startConfig machine (BitString.pair left right)) = some final)
    (_hNonhalting : machine.isHalted final = false)
    (_hStuck : step? machine final = none) :
    workBoundedDecide (bridgedMachine machine)
        (simulationPrefixWorkSteps left right steps)
        (pairedWorkTape left right) = .timeout := by
  exact simulationPrefix_workBoundedDecide_timeout
    machine steps left right final hRaw

/-- The exact accepting work trace compiles to six raw transitions per work
transition from ordinary canonical paired input. -/
theorem run_compileBridgedMachine_accept_of_rawRunExact
    (machine : Machine) (steps : Nat) (left right : BitString)
    (final : Configuration)
    (hRaw : PipelineMachineSimulation.rawRunExact? machine steps
      (startConfig machine (BitString.pair left right)) = some final)
    (hAccept : final.state = machine.acceptState) :
    ∃ simulatorFinal handoffFinal,
      PipelineMachineSimulation.RepresentsConfiguration
          machine final simulatorFinal ∧
      PipelineTape.Represents final.tape.handoffTarget handoffFinal ∧
      run (compileWorkMachine (bridgedMachine machine))
          (bridgedRawSteps left right steps final.tape)
          (startConfig (compileWorkMachine (bridgedMachine machine))
            (BitString.pair left right)) =
        encodeWorkConfiguration
          (renameConfiguration acceptingHandoffState
            (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
              handoffFinal)) := by
  rcases bridgedAccept_workRunExact_of_rawRunExact
      machine steps left right final hRaw hAccept with
    ⟨simulatorFinal, handoffFinal, hFinalRepresents,
      hHandoffRepresents, hExact⟩
  have hCompiled := run_compileWorkMachine_mul_of_workRunExact
    (bridgedMachine machine)
    (bridgedWorkSteps left right steps final.tape)
    (workStartConfiguration (bridgedMachine machine)
      (pairedWorkTape left right))
    (renameConfiguration acceptingHandoffState
      (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
        handoffFinal)) hExact
  rw [← startConfig_compileWorkMachine_paired
    (bridgedMachine machine) left right] at hCompiled
  exact ⟨simulatorFinal, handoffFinal, hFinalRepresents,
    hHandoffRepresents, by
      simpa [bridgedRawSteps] using hCompiled⟩

/-- The exact rejecting work trace has the same six-for-one compiled raw
cost and ends in the distinct global reject image. -/
theorem run_compileBridgedMachine_reject_of_rawRunExact
    (machine : Machine) (steps : Nat) (left right : BitString)
    (final : Configuration)
    (hDistinct : machine.rejectState ≠ machine.acceptState)
    (hRaw : PipelineMachineSimulation.rawRunExact? machine steps
      (startConfig machine (BitString.pair left right)) = some final)
    (hReject : final.state = machine.rejectState) :
    ∃ simulatorFinal handoffFinal,
      PipelineMachineSimulation.RepresentsConfiguration
          machine final simulatorFinal ∧
      PipelineTape.Represents final.tape.handoffTarget handoffFinal ∧
      run (compileWorkMachine (bridgedMachine machine))
          (bridgedRawSteps left right steps final.tape)
          (startConfig (compileWorkMachine (bridgedMachine machine))
            (BitString.pair left right)) =
        encodeWorkConfiguration
          (renameConfiguration rejectingHandoffState
            (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
              handoffFinal)) := by
  rcases bridgedReject_workRunExact_of_rawRunExact
      machine steps left right final hDistinct hRaw hReject with
    ⟨simulatorFinal, handoffFinal, hFinalRepresents,
      hHandoffRepresents, hExact⟩
  have hCompiled := run_compileWorkMachine_mul_of_workRunExact
    (bridgedMachine machine)
    (bridgedWorkSteps left right steps final.tape)
    (workStartConfiguration (bridgedMachine machine)
      (pairedWorkTape left right))
    (renameConfiguration rejectingHandoffState
      (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
        handoffFinal)) hExact
  rw [← startConfig_compileWorkMachine_paired
    (bridgedMachine machine) left right] at hCompiled
  exact ⟨simulatorFinal, handoffFinal, hFinalRepresents,
    hHandoffRepresents, by
      simpa [bridgedRawSteps] using hCompiled⟩

end PipelineStageBridges

end PNP.Concrete
