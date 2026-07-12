/-
Copyright (c) 2026 PNP Labs.

Collision-free state namespaces for composing the finite pipeline work
machines.

The input framer, lifted raw-machine simulator, and represented-output handoff
were previously proved as separate finite machines.  This module supplies the
missing state-renaming calculus and one three-way rule-table namespace.  Every
stage is mapped injectively into a disjoint control-state image; first-match
rule lookup, halting status, one-step execution, exact execution, bounded
execution, and verdicts are preserved by injective renaming.  The concatenated
rule table is proved lookup-isolated at every stage image.

This is a composition prerequisite, not an end-to-end pipeline compiler.  It
does not connect a framer halt to a simulator start, connect simulator halts
to the handoff machine, construct terminal raw output, prove a pipeline
RawRefinement, establish an external input-size polynomial, prove CNFSAT in P
or NP-completeness, or establish P = NP.
-/

import PNP.Concrete.PipelineInputFramer
import PNP.Concrete.PipelineMachineSimulation
import PNP.Concrete.PipelineOutputHandoff

namespace PNP.Concrete

namespace PipelineStateNamespace

/-! ### General injective work-machine state renaming -/

/-- Rename both control-state endpoints of one finite work rule. -/
def renameRule (encode : Nat → Nat) (rule : WorkRule) : WorkRule :=
  { sourceState := encode rule.sourceState
    readSymbol := rule.readSymbol
    targetState := encode rule.targetState
    writeSymbol := rule.writeSymbol
    move := rule.move }

/-- Rename only the control state of one work configuration. -/
def renameConfiguration (encode : Nat → Nat)
    (config : WorkConfiguration) : WorkConfiguration :=
  { state := encode config.state
    tape := config.tape }

/-- Injectively rename every state named by a finite work machine. -/
def renameMachine (encode : Nat → Nat) (machine : WorkMachine) : WorkMachine :=
  { rules := machine.rules.map (renameRule encode)
    startState := encode machine.startState
    acceptState := encode machine.acceptState
    rejectState := encode machine.rejectState }

/-- First-match rule lookup commutes with injective state renaming. -/
theorem findWorkRule_rename (encode : Nat → Nat)
    (hInjective : Function.Injective encode) (rules : List WorkRule)
    (state : Nat) (symbol : WorkSymbol) :
    findWorkRule (rules.map (renameRule encode)) (encode state) symbol =
      Option.map (renameRule encode) (findWorkRule rules state symbol) := by
  induction rules with
  | nil => rfl
  | cons first rest ih =>
      change findWorkRule
        (renameRule encode first :: rest.map (renameRule encode))
          (encode state) symbol =
        Option.map (renameRule encode)
          (findWorkRule (first :: rest) state symbol)
      by_cases hFirst : first.sourceState = state ∧
          first.readSymbol = symbol
      · have hRenamed :
            (renameRule encode first).sourceState = encode state ∧
              (renameRule encode first).readSymbol = symbol :=
          ⟨congrArg encode hFirst.1, hFirst.2⟩
        rw [findWorkRule_cons_of_matches first rest state symbol hFirst]
        rw [findWorkRule_cons_of_matches (renameRule encode first)
          (rest.map (renameRule encode)) (encode state) symbol hRenamed]
        rfl
      · have hRenamed : ¬((renameRule encode first).sourceState = encode state ∧
            (renameRule encode first).readSymbol = symbol) := by
          intro hMatch
          exact hFirst ⟨hInjective hMatch.1, hMatch.2⟩
        rw [findWorkRule_cons_of_not_matches first rest state symbol hFirst]
        rw [findWorkRule_cons_of_not_matches (renameRule encode first)
          (rest.map (renameRule encode)) (encode state) symbol hRenamed]
        exact ih

/-- Designated halt status is invariant under injective renaming. -/
theorem renameMachine_isHalted (encode : Nat → Nat)
    (hInjective : Function.Injective encode) (machine : WorkMachine)
    (config : WorkConfiguration) :
    (renameMachine encode machine).isHalted
        (renameConfiguration encode config) = machine.isHalted config := by
  unfold WorkMachine.isHalted renameMachine renameConfiguration
  rw [nat_beq_map_of_injective encode hInjective]
  rw [nat_beq_map_of_injective encode hInjective]

/-- Applying a renamed rule to a renamed configuration is exactly the renamed
source transition. -/
theorem applyWorkRule_rename (encode : Nat → Nat) (rule : WorkRule)
    (config : WorkConfiguration) :
    applyWorkRule (renameRule encode rule) (renameConfiguration encode config) =
      renameConfiguration encode (applyWorkRule rule config) := by
  rfl


private def guardStep {α : Type} (halted : Bool)
    (next : Option α) : Option α :=
  if halted then none else next

private theorem guardStep_map {α β : Type} (function : α → β)
    (halted : Bool) (next : Option α) :
    guardStep halted (Option.map function next) =
      Option.map function (guardStep halted next) := by
  cases halted <;> rfl

/-- One work transition commutes with injective state renaming. -/
theorem workStep?_rename (encode : Nat → Nat)
    (hInjective : Function.Injective encode) (machine : WorkMachine)
    (config : WorkConfiguration) :
    workStep? (renameMachine encode machine) (renameConfiguration encode config) =
      Option.map (renameConfiguration encode) (workStep? machine config) := by
  let sourceNext :=
    match findWorkRule machine.rules config.state config.tape.head with
    | none => none
    | some rule => some (applyWorkRule rule config)
  let renamedNext :=
    match findWorkRule (renameMachine encode machine).rules
        (renameConfiguration encode config).state
        (renameConfiguration encode config).tape.head with
    | none => none
    | some rule =>
        some (applyWorkRule rule (renameConfiguration encode config))
  have hNext : renamedNext =
      Option.map (renameConfiguration encode) sourceNext := by
    cases hSourceFind : findWorkRule machine.rules config.state
        config.tape.head with
    | none =>
        have hRenamedFind := findWorkRule_rename encode hInjective
          machine.rules config.state config.tape.head
        rw [hSourceFind] at hRenamedFind
        dsimp [sourceNext, renamedNext]
        unfold renameMachine renameConfiguration
        rw [hSourceFind]
        change
          (match findWorkRule (machine.rules.map (renameRule encode))
              (encode config.state) config.tape.head with
           | none => none
           | some rule =>
               some (applyWorkRule rule
                 (renameConfiguration encode config))) = none
        rw [hRenamedFind]
        rfl
    | some rule =>
        have hRenamedFind := findWorkRule_rename encode hInjective
          machine.rules config.state config.tape.head
        rw [hSourceFind] at hRenamedFind
        dsimp [sourceNext, renamedNext]
        unfold renameMachine renameConfiguration
        rw [hSourceFind]
        change
          (match findWorkRule (machine.rules.map (renameRule encode))
              (encode config.state) config.tape.head with
           | none => none
           | some selected =>
               some (applyWorkRule selected
                 (renameConfiguration encode config))) =
            some (renameConfiguration encode
              (applyWorkRule rule config))
        rw [hRenamedFind]
        exact congrArg Option.some
          (applyWorkRule_rename encode rule config)
  have hHalted := renameMachine_isHalted encode hInjective machine config
  change guardStep
      ((renameMachine encode machine).isHalted
        (renameConfiguration encode config)) renamedNext =
    Option.map (renameConfiguration encode)
      (guardStep (machine.isHalted config) sourceNext)
  calc
    guardStep
        ((renameMachine encode machine).isHalted
          (renameConfiguration encode config)) renamedNext =
      guardStep (machine.isHalted config) renamedNext :=
        congrArg (fun halted => guardStep halted renamedNext) hHalted
    _ = guardStep (machine.isHalted config)
        (Option.map (renameConfiguration encode) sourceNext) :=
      congrArg (guardStep (machine.isHalted config)) hNext
    _ = Option.map (renameConfiguration encode)
        (guardStep (machine.isHalted config) sourceNext) :=
      guardStep_map (renameConfiguration encode)
        (machine.isHalted config) sourceNext

/-- At-most execution commutes with injective state renaming. -/
theorem workRun_rename (encode : Nat → Nat)
    (hInjective : Function.Injective encode) (machine : WorkMachine)
    (fuel : Nat) (config : WorkConfiguration) :
    workRun (renameMachine encode machine) fuel
        (renameConfiguration encode config) =
      renameConfiguration encode (workRun machine fuel config) := by
  induction fuel generalizing config with
  | zero => rfl
  | succ fuel ih =>
      change
        (match workStep? (renameMachine encode machine)
            (renameConfiguration encode config) with
         | none => renameConfiguration encode config
         | some next => workRun (renameMachine encode machine) fuel next) =
        renameConfiguration encode
          (match workStep? machine config with
           | none => config
           | some next => workRun machine fuel next)
      rw [workStep?_rename encode hInjective machine config]
      cases hStep : workStep? machine config with
      | none => rfl
      | some next => exact ih next

/-- Exact successful execution commutes with injective state renaming. -/
theorem workRunExact?_rename (encode : Nat → Nat)
    (hInjective : Function.Injective encode) (machine : WorkMachine)
    (steps : Nat) (config : WorkConfiguration) :
    workRunExact? (renameMachine encode machine) steps
        (renameConfiguration encode config) =
      Option.map (renameConfiguration encode)
        (workRunExact? machine steps config) := by
  induction steps generalizing config with
  | zero => rfl
  | succ steps ih =>
      change
        (match workStep? (renameMachine encode machine)
            (renameConfiguration encode config) with
         | none => none
         | some next =>
             workRunExact? (renameMachine encode machine) steps next) =
        Option.map (renameConfiguration encode)
          (match workStep? machine config with
           | none => none
           | some next => workRunExact? machine steps next)
      rw [workStep?_rename encode hInjective machine config]
      cases hStep : workStep? machine config with
      | none => rfl
      | some next => exact ih next

/-- Renaming the source start configuration yields the renamed machine's start
configuration on the same work tape. -/
theorem workStartConfiguration_rename (encode : Nat → Nat)
    (machine : WorkMachine) (tape : WorkTape) :
    renameConfiguration encode (workStartConfiguration machine tape) =
      workStartConfiguration (renameMachine encode machine) tape := by
  rfl

/-- The bounded work verdict is invariant under injective state renaming. -/
theorem workBoundedDecide_rename (encode : Nat → Nat)
    (hInjective : Function.Injective encode) (machine : WorkMachine)
    (fuel : Nat) (tape : WorkTape) :
    workBoundedDecide (renameMachine encode machine) fuel tape =
      workBoundedDecide machine fuel tape := by
  unfold workBoundedDecide
  rw [← workStartConfiguration_rename encode machine tape]
  rw [workRun_rename encode hInjective machine fuel
    (workStartConfiguration machine tape)]
  change
    (if encode (workRun machine fuel
          (workStartConfiguration machine tape)).state ==
        encode machine.acceptState then
      WorkVerdict.accept
    else if encode (workRun machine fuel
          (workStartConfiguration machine tape)).state ==
        encode machine.rejectState then
      WorkVerdict.reject
    else WorkVerdict.timeout) =
    (if (workRun machine fuel
          (workStartConfiguration machine tape)).state ==
        machine.acceptState then
      WorkVerdict.accept
    else if (workRun machine fuel
          (workStartConfiguration machine tape)).state ==
        machine.rejectState then
      WorkVerdict.reject
    else WorkVerdict.timeout)
  rw [nat_beq_map_of_injective encode hInjective]
  rw [nat_beq_map_of_injective encode hInjective]

/-! ### Three disjoint public pipeline stages -/

/-- The three finite control-state namespaces required by the pipeline. -/
inductive Stage where
  | input
  | simulation
  | handoff
deriving DecidableEq, Repr

/-- Advance one payload layer while retaining a three-way stage tag. -/
def stageStep (value : Nat) : Nat :=
  Nat.succ (Nat.succ (Nat.succ value))

/-- Encode a payload state in one of three pairwise disjoint stage images. -/
def stageState : Nat → Stage → Nat
  | 0, .input => 0
  | 0, .simulation => 1
  | 0, .handoff => 2
  | payload + 1, stage => stageStep (stageState payload stage)

/-- One payload-layer step is injective. -/
theorem stageStep_injective {left right : Nat}
    (h : stageStep left = stageStep right) : left = right := by
  exact Nat.succ.inj (Nat.succ.inj (Nat.succ.inj h))

/-- A zero-payload stage code never collides with a positive-payload code. -/
theorem stageState_zero_ne_succ (leftStage rightStage : Stage)
    (payload : Nat) :
    stageState 0 leftStage ≠ stageState (payload + 1) rightStage := by
  intro h
  cases leftStage with
  | input => contradiction
  | simulation =>
      have hOne := Nat.succ.inj h
      contradiction
  | handoff =>
      have hOne := Nat.succ.inj h
      have hTwo := Nat.succ.inj hOne
      contradiction

/-- The combined payload-and-stage encoding is injective. -/
theorem stageState_injective {leftPayload rightPayload : Nat}
    {leftStage rightStage : Stage}
    (h : stageState leftPayload leftStage =
      stageState rightPayload rightStage) :
    leftPayload = rightPayload ∧ leftStage = rightStage := by
  induction leftPayload generalizing rightPayload with
  | zero =>
      cases rightPayload with
      | zero =>
          cases leftStage <;> cases rightStage <;>
            first | exact ⟨rfl, rfl⟩ | contradiction
      | succ rightPayload =>
          exact False.elim
            (stageState_zero_ne_succ leftStage rightStage rightPayload h)
  | succ leftPayload ih =>
      cases rightPayload with
      | zero =>
          exact False.elim
            (stageState_zero_ne_succ rightStage leftStage leftPayload h.symm)
      | succ rightPayload =>
          have hInner := stageStep_injective h
          have hParts := ih hInner
          exact ⟨congrArg Nat.succ hParts.1, hParts.2⟩

/-- Distinct stage tags have disjoint state images. -/
theorem stageState_ne_of_stage_ne {leftPayload rightPayload : Nat}
    {leftStage rightStage : Stage} (hStage : leftStage ≠ rightStage) :
    stageState leftPayload leftStage ≠
      stageState rightPayload rightStage := by
  intro h
  exact hStage (stageState_injective h).2

/-- Input-framer state image. -/
def inputState (state : Nat) : Nat := stageState state .input

/-- Lifted-simulator state image. -/
def simulationState (state : Nat) : Nat := stageState state .simulation

/-- Represented-output-handoff state image. -/
def handoffState (state : Nat) : Nat := stageState state .handoff

/-- Input-stage renaming is injective. -/
theorem inputState_injective : Function.Injective inputState := by
  intro left right h
  exact (stageState_injective h).1

/-- Simulation-stage renaming is injective. -/
theorem simulationState_injective : Function.Injective simulationState := by
  intro left right h
  exact (stageState_injective h).1

/-- Handoff-stage renaming is injective. -/
theorem handoffState_injective : Function.Injective handoffState := by
  intro left right h
  exact (stageState_injective h).1

/-- Input and simulation states never collide. -/
theorem inputState_ne_simulationState (left right : Nat) :
    inputState left ≠ simulationState right := by
  exact stageState_ne_of_stage_ne (by intro h; contradiction)

/-- Input and handoff states never collide. -/
theorem inputState_ne_handoffState (left right : Nat) :
    inputState left ≠ handoffState right := by
  exact stageState_ne_of_stage_ne (by intro h; contradiction)

/-- Simulation and handoff states never collide. -/
theorem simulationState_ne_handoffState (left right : Nat) :
    simulationState left ≠ handoffState right := by
  exact stageState_ne_of_stage_ne (by intro h; contradiction)

/-- Rename one finite rule list into a selected pipeline stage. -/
def stageRules (stage : Stage) (rules : List WorkRule) : List WorkRule :=
  rules.map (renameRule (fun state => stageState state stage))

/-- Concatenate the three collision-free stage rule tables in execution order. -/
def composedRules (input simulation handoff : WorkMachine) : List WorkRule :=
  stageRules .input input.rules ++
    (stageRules .simulation simulation.rules ++
      stageRules .handoff handoff.rules)

/-- A renamed rule list has no matching source in another stage image. -/
theorem findWorkRule_stageRules_none_of_stage_ne
    (leftStage rightStage : Stage) (hStage : leftStage ≠ rightStage)
    (rules : List WorkRule) (state : Nat) (symbol : WorkSymbol) :
    findWorkRule (stageRules leftStage rules)
        (stageState state rightStage) symbol = none := by
  induction rules with
  | nil => rfl
  | cons first rest ih =>
      change findWorkRule
        (renameRule (fun value => stageState value leftStage) first ::
          stageRules leftStage rest)
        (stageState state rightStage) symbol = none
      rw [findWorkRule_cons_of_not_matches]
      · exact ih
      · intro hMatch
        exact hStage (stageState_injective hMatch.1).2

/-- At an input-stage state, the combined table selects exactly the input
stage's first matching rule. -/
theorem findWorkRule_composedRules_input
    (input simulation handoff : WorkMachine) (state : Nat)
    (symbol : WorkSymbol) :
    findWorkRule (composedRules input simulation handoff)
        (inputState state) symbol =
      findWorkRule (stageRules .input input.rules)
        (inputState state) symbol := by
  unfold composedRules
  cases hInput : findWorkRule (stageRules .input input.rules)
      (inputState state) symbol with
  | some selected =>
      exact findWorkRule_append_of_some _ _ _ _ _ hInput
  | none =>
      rw [findWorkRule_append_of_none _ _ _ _ hInput]
      have hSimulation : findWorkRule
          (stageRules .simulation simulation.rules)
          (inputState state) symbol = none := by
        simpa [inputState] using
          (findWorkRule_stageRules_none_of_stage_ne
            .simulation .input (by intro h; contradiction)
            simulation.rules state symbol)
      rw [findWorkRule_append_of_none _ _ _ _ hSimulation]
      simpa [inputState] using
        (findWorkRule_stageRules_none_of_stage_ne
          .handoff .input (by intro h; contradiction)
          handoff.rules state symbol)

/-- At a simulation-stage state, the combined table selects exactly the
simulator's first matching rule. -/
theorem findWorkRule_composedRules_simulation
    (input simulation handoff : WorkMachine) (state : Nat)
    (symbol : WorkSymbol) :
    findWorkRule (composedRules input simulation handoff)
        (simulationState state) symbol =
      findWorkRule (stageRules .simulation simulation.rules)
        (simulationState state) symbol := by
  unfold composedRules
  have hInput : findWorkRule (stageRules .input input.rules)
      (simulationState state) symbol = none := by
    simpa [simulationState] using
      (findWorkRule_stageRules_none_of_stage_ne
        .input .simulation (by intro h; contradiction)
        input.rules state symbol)
  rw [findWorkRule_append_of_none _ _ _ _ hInput]
  cases hSimulation : findWorkRule
      (stageRules .simulation simulation.rules)
      (simulationState state) symbol with
  | some selected =>
      exact findWorkRule_append_of_some _ _ _ _ _ hSimulation
  | none =>
      rw [findWorkRule_append_of_none _ _ _ _ hSimulation]
      simpa [simulationState] using
        (findWorkRule_stageRules_none_of_stage_ne
          .handoff .simulation (by intro h; contradiction)
          handoff.rules state symbol)

/-- At a handoff-stage state, the combined table selects exactly the handoff
stage's first matching rule. -/
theorem findWorkRule_composedRules_handoff
    (input simulation handoff : WorkMachine) (state : Nat)
    (symbol : WorkSymbol) :
    findWorkRule (composedRules input simulation handoff)
        (handoffState state) symbol =
      findWorkRule (stageRules .handoff handoff.rules)
        (handoffState state) symbol := by
  unfold composedRules
  have hInput : findWorkRule (stageRules .input input.rules)
      (handoffState state) symbol = none := by
    simpa [handoffState] using
      (findWorkRule_stageRules_none_of_stage_ne
        .input .handoff (by intro h; contradiction)
        input.rules state symbol)
  rw [findWorkRule_append_of_none _ _ _ _ hInput]
  have hSimulation : findWorkRule
      (stageRules .simulation simulation.rules)
      (handoffState state) symbol = none := by
    simpa [handoffState] using
      (findWorkRule_stageRules_none_of_stage_ne
        .simulation .handoff (by intro h; contradiction)
        simulation.rules state symbol)
  rw [findWorkRule_append_of_none _ _ _ _ hSimulation]

/-! ### The three existing machines in the collision-free namespace -/

/-- The canonical paired-input framer in the input-stage image. -/
def renamedInputFramer : WorkMachine :=
  renameMachine inputState PipelineInputFramer.pairedInputFramer

/-- A lifted raw machine in the simulation-stage image. -/
def renamedLiftMachine (machine : Machine) : WorkMachine :=
  renameMachine simulationState
    (PipelineMachineSimulation.liftMachine machine)

/-- The internal represented-output handoff in the handoff-stage image. -/
def renamedOutputHandoff : WorkMachine :=
  renameMachine handoffState PipelineOutputHandoff.framedOutputHandoff

/-- The exact canonical framer trace survives input-stage renaming. -/
theorem renamedInputFramer_workRunExact (left right : BitString) :
    workRunExact? renamedInputFramer
        (PipelineInputFramer.inputFramerWorkSteps
          (PipelineInputFramer.packedPairCount left right))
        (workStartConfiguration renamedInputFramer
          (pairedWorkTape left right)) =
      some (renameConfiguration inputState
        (PipelineInputFramer.pairedInputFramerFinalConfiguration left right)) := by
  have hRename := workRunExact?_rename inputState inputState_injective
    PipelineInputFramer.pairedInputFramer
    (PipelineInputFramer.inputFramerWorkSteps
      (PipelineInputFramer.packedPairCount left right))
    (workStartConfiguration PipelineInputFramer.pairedInputFramer
      (pairedWorkTape left right))
  rw [PipelineInputFramer.pairedInputFramer_workRunExact left right] at hRename
  change workRunExact? renamedInputFramer _
      (renameConfiguration inputState
        (workStartConfiguration PipelineInputFramer.pairedInputFramer
          (pairedWorkTape left right))) = _ at hRename
  rw [workStartConfiguration_rename inputState
    PipelineInputFramer.pairedInputFramer (pairedWorkTape left right)] at hRename
  exact hRename

/-- Every exact source run retains its exact three-for-one simulator trace
inside the simulation-stage image. -/
theorem renamedLiftMachine_workRunExact_of_rawRunExact
    (machine : Machine) (steps : Nat) (start final : Configuration)
    (workTape : WorkTape)
    (hRun : PipelineMachineSimulation.rawRunExact? machine steps start =
      some final)
    (hRepresents : PipelineTape.Represents start.tape workTape) :
    ∃ workFinal,
      workRunExact? (renamedLiftMachine machine) (3 * steps)
          (renameConfiguration simulationState
            (PipelineMachineSimulation.liftConfiguration machine start workTape)) =
        some (renameConfiguration simulationState workFinal) ∧
      PipelineMachineSimulation.RepresentsConfiguration
        machine final workFinal := by
  rcases PipelineMachineSimulation.workRunExact_three_mul_of_rawRunExact
      machine steps start final workTape hRun hRepresents with
    ⟨workFinal, hExact, hFinalRepresents⟩
  refine ⟨workFinal, ?_, hFinalRepresents⟩
  have hRename := workRunExact?_rename simulationState
    simulationState_injective
    (PipelineMachineSimulation.liftMachine machine) (3 * steps)
    (PipelineMachineSimulation.liftConfiguration machine start workTape)
  rw [hExact] at hRename
  exact hRename

/-- The exact represented-output handoff trace survives handoff-stage
renaming. -/
theorem renamedOutputHandoff_workRunExact_of_represents
    (raw : Tape) (work : WorkTape)
    (hRepresents : PipelineTape.Represents raw work) :
    ∃ finalTape,
      PipelineTape.Represents raw.handoffTarget finalTape ∧
      workRunExact? renamedOutputHandoff
          (PipelineOutputHandoff.framedOutputHandoffWorkSteps raw)
          (workStartConfiguration renamedOutputHandoff work) =
        some (renameConfiguration handoffState
          (PipelineOutputHandoff.framedOutputHandoffFinalConfiguration
            finalTape)) := by
  rcases PipelineOutputHandoff.framedOutputHandoff_workRunExact_of_represents
      hRepresents with ⟨finalTape, hFinalRepresents, hExact⟩
  refine ⟨finalTape, hFinalRepresents, ?_⟩
  have hRename := workRunExact?_rename handoffState
    handoffState_injective PipelineOutputHandoff.framedOutputHandoff
    (PipelineOutputHandoff.framedOutputHandoffWorkSteps raw)
    (workStartConfiguration PipelineOutputHandoff.framedOutputHandoff work)
  rw [hExact] at hRename
  change workRunExact? renamedOutputHandoff _
      (renameConfiguration handoffState
        (workStartConfiguration PipelineOutputHandoff.framedOutputHandoff work)) = _
      at hRename
  rw [workStartConfiguration_rename handoffState
    PipelineOutputHandoff.framedOutputHandoff work] at hRename
  exact hRename

end PipelineStateNamespace

end PNP.Concrete
