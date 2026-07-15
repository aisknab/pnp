/-
Copyright (c) 2026 PNP Labs.

Literal composition of the all-input framer and the Cook--Levin unary
input-length tally.

The machine in this file starts from an ordinary raw bitstring, executes the
existing total finite framer, takes one symbol-preserving launch transition,
and executes the existing fixed 19-rule tally stage.  It is only an executable
input-preparation prefix.  It emits no formula bit and supplies no formula
builder, raw refinement, polynomial reduction, complexity-class result, or
P = NP theorem.
-/

import PNP.Concrete.CookLevinBuilderInputLength
import PNP.Concrete.PipelineStageBridges

namespace PNP.Concrete

namespace CookLevin

namespace BuilderInputPrefix

open PipelineStateNamespace PipelineStageBridges

/-! ### Collision-free stage images and literal rule table -/

/-- State image containing the existing total raw-input framer. -/
def framerState (state : Nat) : Nat := inputState state

/-- State image containing the existing unary input-length tally. -/
def tallyState (state : Nat) : Nat := simulationState state

theorem framerState_injective : Function.Injective framerState :=
  inputState_injective

theorem tallyState_injective : Function.Injective tallyState :=
  simulationState_injective

theorem framerState_ne_tallyState (left right : Nat) :
    framerState left ≠ tallyState right :=
  inputState_ne_simulationState left right

/-- The complete framer table in its builder-prefix state image. -/
def renamedFramer : WorkMachine :=
  renameMachine framerState PipelineInputFramer.pairedInputFramer

/-- The complete input-length table in its builder-prefix state image. -/
def renamedTally : WorkMachine :=
  renameMachine tallyState BuilderInputLength.machine

/-- Total symbol-preserving launch from the framer accept endpoint to the
input-length tally start state. -/
def launchRules : List WorkRule :=
  PipelineStageBridges.launchRules
    (framerState PipelineInputFramer.pairedInputFramer.acceptState)
    (tallyState BuilderInputLength.machine.startState)

/-- One literal bridge-first table containing both renamed finite stages. -/
def rules : List WorkRule :=
  launchRules ++
    (PipelineInputFramer.pairedInputFramer.rules.map
      (renameRule framerState) ++
    BuilderInputLength.machine.rules.map (renameRule tallyState))

/-- The executable two-stage input-preparation prefix.  Only the tally's
designated endpoints are global halts. -/
def machine : WorkMachine :=
  { rules := rules
    startState := framerState PipelineInputFramer.pairedInputFramer.startState
    acceptState := tallyState BuilderInputLength.machine.acceptState
    rejectState := tallyState BuilderInputLength.machine.rejectState }

theorem machine_acceptState_ne_rejectState :
    machine.acceptState ≠ machine.rejectState := by
  intro h
  have hInner := tallyState_injective h
  contradiction

/-! ### Exact endpoint and displayed costs -/

/-- Exact work-transition count through framing, launch, and tally. -/
def workSteps (input : BitString) : Nat :=
  PipelineInputFramer.totalInputFramerWorkSteps input + 1 +
    BuilderInputLength.workSteps input.length

/-- Explicit raw-transition polynomial in the external encoded input length. -/
def rawTimeBound : NatPolynomial :=
  .add (.quadratic 18 93) (.linear 63 0)

/-- The final tape preserves the raw source and contains its exact unary
length tally in the fresh right workspace. -/
def finalTape (input : BitString) : WorkTape :=
  BuilderInputLength.finalTape input
    (PipelineInputFramer.totalInputFramerOutsideLeft input)

def finalConfiguration (input : BitString) : WorkConfiguration :=
  { state := machine.acceptState
    tape := finalTape input }

theorem finalTape_represents (input : BitString) :
    PipelineTape.Represents (Tape.ofInput input) (finalTape input) := by
  exact BuilderInputLength.finalTape_represents input _

theorem finalTape_tally_length (input : BitString) :
    (List.replicate input.length BuilderInputLength.tallySymbol).length =
      input.length := by
  exact BuilderInputLength.finalTape_tally_length input
    (PipelineInputFramer.totalInputFramerOutsideLeft input)

/-! ### Global halt separation -/

private theorem nat_beq_false_of_ne (left right : Nat)
    (h : left ≠ right) : (left == right) = false := by
  cases hBool : (left == right) with
  | false => rfl
  | true =>
      exact False.elim (h ((nat_beq_true_iff left right).mp hBool))

private theorem state_ne_accept_of_not_halted
    (source : WorkMachine) (config : WorkConfiguration)
    (hHalted : source.isHalted config = false) :
    config.state ≠ source.acceptState := by
  intro hState
  unfold WorkMachine.isHalted at hHalted
  rw [hState] at hHalted
  have hRefl : (source.acceptState == source.acceptState) = true :=
    (nat_beq_true_iff _ _).mpr rfl
  rw [hRefl] at hHalted
  contradiction

private theorem state_ne_reject_of_not_halted
    (source : WorkMachine) (config : WorkConfiguration)
    (hHalted : source.isHalted config = false) :
    config.state ≠ source.rejectState := by
  intro hState
  unfold WorkMachine.isHalted at hHalted
  rw [hState] at hHalted
  have hRefl : (source.rejectState == source.rejectState) = true :=
    (nat_beq_true_iff _ _).mpr rfl
  cases hAccept : (source.rejectState == source.acceptState) with
  | false =>
      rw [hAccept, hRefl] at hHalted
      contradiction
  | true =>
      rw [hAccept, hRefl] at hHalted
      contradiction

/-- Every framer-image state is globally nonhalting, including the local
framer accept state which must execute the launch. -/
theorem machine_isHalted_framer_false (config : WorkConfiguration) :
    machine.isHalted (renameConfiguration framerState config) = false := by
  unfold WorkMachine.isHalted machine renameConfiguration
  rw [nat_beq_false_of_ne _ _
      (framerState_ne_tallyState config.state
        BuilderInputLength.machine.acceptState),
    nat_beq_false_of_ne _ _
      (framerState_ne_tallyState config.state
        BuilderInputLength.machine.rejectState)]
  rfl

/-- A locally nonhalting tally state remains globally nonhalting. -/
theorem machine_isHalted_tally_false_of_local
    (config : WorkConfiguration)
    (hLocal : BuilderInputLength.machine.isHalted config = false) :
    machine.isHalted (renameConfiguration tallyState config) = false := by
  have hAccept := state_ne_accept_of_not_halted
    BuilderInputLength.machine config hLocal
  have hReject := state_ne_reject_of_not_halted
    BuilderInputLength.machine config hLocal
  have hGlobalAccept : tallyState config.state ≠
      tallyState BuilderInputLength.machine.acceptState := by
    intro h
    exact hAccept (tallyState_injective h)
  have hGlobalReject : tallyState config.state ≠
      tallyState BuilderInputLength.machine.rejectState := by
    intro h
    exact hReject (tallyState_injective h)
  unfold WorkMachine.isHalted machine renameConfiguration
  rw [nat_beq_false_of_ne _ _ hGlobalAccept,
    nat_beq_false_of_ne _ _ hGlobalReject]
  rfl

/-! ### First-match lookup isolation -/

theorem findWorkRule_framer_of_some
    (state : Nat) (symbol : WorkSymbol) (rule : WorkRule)
    (hAccept : state ≠ PipelineInputFramer.pairedInputFramer.acceptState)
    (hFind : findWorkRule PipelineInputFramer.pairedInputFramer.rules
      state symbol = some rule) :
    findWorkRule machine.rules (framerState state) symbol =
      some (renameRule framerState rule) := by
  have hLaunch : findWorkRule launchRules
      (framerState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    intro h
    exact hAccept (framerState_injective h).symm
  have hRenamed := findWorkRule_rename framerState framerState_injective
    PipelineInputFramer.pairedInputFramer.rules state symbol
  rw [hFind] at hRenamed
  unfold machine rules
  rw [findWorkRule_append_of_none _ _ _ _ hLaunch]
  exact findWorkRule_append_of_some _ _ _ _ _ hRenamed

theorem findWorkRule_tally_of_some
    (state : Nat) (symbol : WorkSymbol) (rule : WorkRule)
    (hFind : findWorkRule BuilderInputLength.machine.rules
      state symbol = some rule) :
    findWorkRule machine.rules (tallyState state) symbol =
      some (renameRule tallyState rule) := by
  have hLaunch : findWorkRule launchRules
      (tallyState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact framerState_ne_tallyState _ _
  have hFramer : findWorkRule
      (PipelineInputFramer.pairedInputFramer.rules.map
        (renameRule framerState)) (tallyState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact framerState_ne_tallyState source state
  have hRenamed := findWorkRule_rename tallyState tallyState_injective
    BuilderInputLength.machine.rules state symbol
  rw [hFind] at hRenamed
  unfold machine rules
  rw [findWorkRule_append_of_none _ _ _ _ hLaunch,
    findWorkRule_append_of_none _ _ _ _ hFramer]
  exact hRenamed

/-! ### Local transition and exact-trace transport -/

theorem framer_workStep?_of_some
    (config next : WorkConfiguration)
    (hStep : workStep? PipelineInputFramer.pairedInputFramer config =
      some next) :
    workStep? machine (renameConfiguration framerState config) =
      some (renameConfiguration framerState next) := by
  rcases workStep?_some_exists PipelineInputFramer.pairedInputFramer
      config next hStep with ⟨rule, hHalted, hFind, hNext⟩
  have hAccept := state_ne_accept_of_not_halted
    PipelineInputFramer.pairedInputFramer config hHalted
  have hGlobalHalted := machine_isHalted_framer_false config
  have hGlobalFind := findWorkRule_framer_of_some
    config.state config.tape.head rule hAccept hFind
  have hGlobalStep := workStep?_eq_apply_of_find machine
    (renameConfiguration framerState config)
    (renameRule framerState rule) hGlobalHalted hGlobalFind
  calc
    workStep? machine (renameConfiguration framerState config) =
        some (applyWorkRule (renameRule framerState rule)
          (renameConfiguration framerState config)) := hGlobalStep
    _ = some (renameConfiguration framerState
          (applyWorkRule rule config)) :=
      congrArg Option.some (applyWorkRule_rename framerState rule config)
    _ = some (renameConfiguration framerState next) :=
      congrArg (fun value => some (renameConfiguration framerState value))
        hNext.symm

theorem tally_workStep?_of_some
    (config next : WorkConfiguration)
    (hStep : workStep? BuilderInputLength.machine config = some next) :
    workStep? machine (renameConfiguration tallyState config) =
      some (renameConfiguration tallyState next) := by
  rcases workStep?_some_exists BuilderInputLength.machine
      config next hStep with ⟨rule, hHalted, hFind, hNext⟩
  have hGlobalHalted := machine_isHalted_tally_false_of_local config hHalted
  have hGlobalFind := findWorkRule_tally_of_some
    config.state config.tape.head rule hFind
  have hGlobalStep := workStep?_eq_apply_of_find machine
    (renameConfiguration tallyState config)
    (renameRule tallyState rule) hGlobalHalted hGlobalFind
  calc
    workStep? machine (renameConfiguration tallyState config) =
        some (applyWorkRule (renameRule tallyState rule)
          (renameConfiguration tallyState config)) := hGlobalStep
    _ = some (renameConfiguration tallyState
          (applyWorkRule rule config)) :=
      congrArg Option.some (applyWorkRule_rename tallyState rule config)
    _ = some (renameConfiguration tallyState next) :=
      congrArg (fun value => some (renameConfiguration tallyState value))
        hNext.symm

theorem framer_workRunExact (input : BitString) :
    workRunExact? machine
        (PipelineInputFramer.totalInputFramerWorkSteps input)
        (workStartConfiguration machine
          (rawInputWorkTape input)) =
      some (renameConfiguration framerState
        (PipelineInputFramer.totalInputFramerFinalConfiguration input)) := by
  have hTransport := workRunExact?_transport
    PipelineInputFramer.pairedInputFramer machine framerState
    framer_workStep?_of_some
    (PipelineInputFramer.totalInputFramerWorkSteps input)
    (workStartConfiguration PipelineInputFramer.pairedInputFramer
      (rawInputWorkTape input))
    (PipelineInputFramer.totalInputFramerFinalConfiguration input)
    (PipelineInputFramer.totalInputFramer_workRunExact input)
  simpa [machine, workStartConfiguration, renameConfiguration] using hTransport

/-- The literal launch preserves the framed tape and head. -/
theorem launch_workStep (input : BitString) :
    workStep? machine
        (renameConfiguration framerState
          (PipelineInputFramer.totalInputFramerFinalConfiguration input)) =
      some (renameConfiguration tallyState
        (workStartConfiguration BuilderInputLength.machine
          (PipelineInputFramer.totalInputFramerFinalTape input))) := by
  let final := PipelineInputFramer.totalInputFramerFinalConfiguration input
  have hHalted := machine_isHalted_framer_false final
  have hLaunch := findWorkRule_launchRules
    (framerState PipelineInputFramer.pairedInputFramer.acceptState)
    (tallyState BuilderInputLength.machine.startState)
    final.tape.head
  have hFind : findWorkRule machine.rules
      (framerState final.state) final.tape.head =
        some (PipelineStageBridges.launchRule
          (framerState PipelineInputFramer.pairedInputFramer.acceptState)
          (tallyState BuilderInputLength.machine.startState)
          final.tape.head) := by
    unfold machine rules
    simpa [launchRules, final,
      PipelineInputFramer.totalInputFramerFinalConfiguration] using
      (findWorkRule_append_of_some _ _ _ _ _ hLaunch)
  have hStep := workStep?_eq_apply_of_find machine
    (renameConfiguration framerState final)
    (PipelineStageBridges.launchRule
      (framerState PipelineInputFramer.pairedInputFramer.acceptState)
      (tallyState BuilderInputLength.machine.startState)
      final.tape.head) hHalted hFind
  simpa [final, PipelineStageBridges.launchRule, applyWorkRule,
    WorkTape.write, WorkTape.move, workStartConfiguration,
    renameConfiguration,
    PipelineInputFramer.totalInputFramerFinalConfiguration] using hStep

theorem tally_workRunExact (input : BitString) :
    workRunExact? machine (BuilderInputLength.workSteps input.length)
        (renameConfiguration tallyState
          (workStartConfiguration BuilderInputLength.machine
            (PipelineInputFramer.totalInputFramerFinalTape input))) =
      some (finalConfiguration input) := by
  have hLocal := BuilderInputLength.workRunExact_after_totalInputFramer input
  have hTransport := workRunExact?_transport
    BuilderInputLength.machine machine tallyState
    tally_workStep?_of_some (BuilderInputLength.workSteps input.length)
    (workStartConfiguration BuilderInputLength.machine
      (PipelineInputFramer.totalInputFramerFinalTape input))
    (BuilderInputLength.finalConfiguration input
      (PipelineInputFramer.totalInputFramerOutsideLeft input)) hLocal
  simpa [finalConfiguration, finalTape, machine,
    BuilderInputLength.finalConfiguration, renameConfiguration] using hTransport

/-- Every ordinary raw bitstring executes both literal stages and the launch
in exactly the displayed number of successful work transitions. -/
theorem workRunExact (input : BitString) :
    workRunExact? machine (workSteps input)
        (workStartConfiguration machine
          (rawInputWorkTape input)) =
      some (finalConfiguration input) := by
  have hLaunch : workRunExact? machine 1
      (renameConfiguration framerState
        (PipelineInputFramer.totalInputFramerFinalConfiguration input)) =
      some (renameConfiguration tallyState
        (workStartConfiguration BuilderInputLength.machine
          (PipelineInputFramer.totalInputFramerFinalTape input))) := by
    change
      (match workStep? machine
          (renameConfiguration framerState
            (PipelineInputFramer.totalInputFramerFinalConfiguration input)) with
       | none => none
       | some next => workRunExact? machine 0 next) = _
    rw [launch_workStep input]
    rfl
  have hFramerLaunch := PipelineMachineSimulation.workRunExact?_compose
    machine (PipelineInputFramer.totalInputFramerWorkSteps input) 1
    (workStartConfiguration machine
      (rawInputWorkTape input))
    (renameConfiguration framerState
      (PipelineInputFramer.totalInputFramerFinalConfiguration input))
    (renameConfiguration tallyState
      (workStartConfiguration BuilderInputLength.machine
        (PipelineInputFramer.totalInputFramerFinalTape input)))
    (framer_workRunExact input) hLaunch
  have hComplete := PipelineMachineSimulation.workRunExact?_compose
    machine (PipelineInputFramer.totalInputFramerWorkSteps input + 1)
    (BuilderInputLength.workSteps input.length)
    (workStartConfiguration machine
      (rawInputWorkTape input))
    (renameConfiguration tallyState
      (workStartConfiguration BuilderInputLength.machine
        (PipelineInputFramer.totalInputFramerFinalTape input)))
    (finalConfiguration input) hFramerLaunch (tally_workRunExact input)
  simpa [workSteps] using hComplete

theorem finalConfiguration_isHalted (input : BitString) :
    machine.isHalted (finalConfiguration input) = true := by
  rfl

/-! ### Compiled execution and the external polynomial -/

theorem rawTimeBound_eval (input : BitString) :
    rawTimeBound.eval (BitString.size input) =
      18 * input.length * input.length + 63 * input.length + 93 := by
  simp [rawTimeBound, NatPolynomial.quadratic, NatPolynomial.linear,
    BitString.size]
  omega

theorem rawTimeBound_le (input : BitString) :
    6 * workSteps input ≤ rawTimeBound.eval (BitString.size input) := by
  have hFramer := PipelineInputFramer.totalInputFramerRawTimeBound_le input
  rw [rawTimeBound_eval]
  change 6 *
      (PipelineInputFramer.totalInputFramerWorkSteps input + 1 +
        BuilderInputLength.workSteps input.length) ≤ _
  have hFramerClosed :
      6 * PipelineInputFramer.totalInputFramerWorkSteps input ≤
        6 * input.length * input.length +
          (75 + 39 * input.length) := by
    simpa [PipelineInputFramer.totalInputFramerRawTimeBound,
      NatPolynomial.quadratic, NatPolynomial.linear, BitString.size,
      Nat.add_assoc] using hFramer
  unfold BuilderInputLength.workSteps
  simp only [Nat.mul_add, Nat.mul_one, Nat.mul_assoc] at *
  omega

/-- Exact six-for-one compilation of the complete successful work trace. -/
theorem run_compile_exact (input : BitString) :
    run (compileWorkMachine machine) (6 * workSteps input)
        (encodeWorkConfiguration
          (workStartConfiguration machine
            (rawInputWorkTape input))) =
      encodeWorkConfiguration (finalConfiguration input) := by
  exact run_compileWorkMachine_mul_of_workRunExact machine
    (workSteps input)
    (workStartConfiguration machine
      (rawInputWorkTape input))
    (finalConfiguration input) (workRunExact input)

/-- The compiled prefix reaches the same endpoint within the single explicit
external-input-size polynomial. -/
theorem run_compile_rawTimeBound (input : BitString) :
    run (compileWorkMachine machine)
        (rawTimeBound.eval (BitString.size input))
        (encodeWorkConfiguration
          (workStartConfiguration machine
            (rawInputWorkTape input))) =
      encodeWorkConfiguration (finalConfiguration input) := by
  exact run_compileWorkMachine_of_workRunExact_halted_le
    machine (workSteps input)
    (rawTimeBound.eval (BitString.size input))
    (workStartConfiguration machine
      (rawInputWorkTape input))
    (finalConfiguration input) (workRunExact input)
    (finalConfiguration_isHalted input) (rawTimeBound_le input)

/-- Ordinary raw `startConfig` differs only by materialized exterior blanks,
and that equivalence survives the complete polynomial-budget execution. -/
theorem run_compile_rawTimeBound_blankEquivalent (input : BitString) :
    Configuration.BlankEquivalent
      (run (compileWorkMachine machine)
        (rawTimeBound.eval (BitString.size input))
        (startConfig (compileWorkMachine machine) input))
      (encodeWorkConfiguration (finalConfiguration input)) := by
  have hStart := startConfig_compileWorkMachine_blankEquivalent machine input
  have hRun := run_blankEquivalent (compileWorkMachine machine)
    (rawTimeBound.eval (BitString.size input)) hStart
  rw [run_compile_rawTimeBound input] at hRun
  exact hRun

theorem boundedDecide_compile_accept (input : BitString) :
    boundedDecide (compileWorkMachine machine)
        (rawTimeBound.eval (BitString.size input)) input = .accept := by
  apply (boundedDecide_accept_iff_final
    (compileWorkMachine machine)
    (rawTimeBound.eval (BitString.size input)) input).mpr
  exact (run_compile_rawTimeBound_blankEquivalent input).1

theorem boundedDecide_compile_ne_timeout (input : BitString) :
    boundedDecide (compileWorkMachine machine)
        (rawTimeBound.eval (BitString.size input)) input ≠ .timeout := by
  rw [boundedDecide_compile_accept]
  intro impossible
  contradiction

/-! ### Fail-closed negative behavior -/

def malformedTallyConfiguration (left right : List WorkSymbol) :
    WorkConfiguration :=
  { state := tallyState BuilderInputLength.scanState
    tape :=
      { left := left
        head := WorkSymbol.zeroOne
        right := right } }

theorem malformedTallyScanSymbol_isHalted_false
    (left right : List WorkSymbol) :
    machine.isHalted (malformedTallyConfiguration left right) = false := by
  rfl

theorem malformedTallyScanSymbol_workStep_none
    (left right : List WorkSymbol) :
    workStep? machine (malformedTallyConfiguration left right) = none := by
  rfl

/-- The unused tally scan symbol remains stuck and nonhalting for every fuel
budget in the combined machine, so it cannot fall through to a verdict. -/
theorem malformedTallyScanSymbol_timeout (fuel : Nat)
    (left right : List WorkSymbol) :
    (let result := workRun machine fuel
        (malformedTallyConfiguration left right)
     if result.state == machine.acceptState then WorkVerdict.accept
     else if result.state == machine.rejectState then WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  have hRun := workRun_eq_self_of_workStep?_eq_none machine
    (malformedTallyConfiguration left right) fuel
    (malformedTallyScanSymbol_workStep_none left right)
  rw [hRun]
  rfl

private theorem workRunExact_succ_split_last :
    ∀ (steps : Nat) (initial final : WorkConfiguration),
      workRunExact? machine (steps + 1) initial = some final →
      ∃ before,
        workRunExact? machine steps initial = some before ∧
        workStep? machine before = some final := by
  intro steps
  induction steps with
  | zero =>
      intro initial final hRun
      cases hStep : workStep? machine initial with
      | none =>
          change
            (match workStep? machine initial with
             | none => none
             | some next => some next) = some final at hRun
          rw [hStep] at hRun
          contradiction
      | some next =>
          have hNext : next = final := by
            change
              (match workStep? machine initial with
               | none => none
               | some result => some result) = some final at hRun
            rw [hStep] at hRun
            exact Option.some.inj hRun
          subst final
          exact ⟨initial, rfl, hStep⟩
  | succ steps ih =>
      intro initial final hRun
      cases hStep : workStep? machine initial with
      | none =>
          change
            (match workStep? machine initial with
             | none => none
             | some next => workRunExact? machine (steps + 1) next) =
              some final at hRun
          rw [hStep] at hRun
          contradiction
      | some next =>
          have hTail : workRunExact? machine (steps + 1) next =
              some final := by
            change
              (match workStep? machine initial with
               | none => none
               | some result => workRunExact? machine (steps + 1) result) =
                some final at hRun
            rw [hStep] at hRun
            exact hRun
          rcases ih next final hTail with ⟨before, hPrefix, hLast⟩
          refine ⟨before, ?_, hLast⟩
          change
            (match workStep? machine initial with
             | none => none
             | some result => workRunExact? machine steps result) =
              some before
          rw [hStep]
          exact hPrefix

private theorem isHalted_false_of_workStep_some
    (config next : WorkConfiguration)
    (hStep : workStep? machine config = some next) :
    machine.isHalted config = false := by
  cases hHalted : machine.isHalted config with
  | false => rfl
  | true =>
      unfold workStep? at hStep
      rw [hHalted] at hStep
      contradiction

private theorem workSteps_positive (input : BitString) :
    0 < workSteps input := by
  unfold workSteps
  omega

/-- Removing exactly one successful transition from the complete prefix leaves
a nonhalting state and therefore reports timeout. -/
theorem work_one_step_short_timeout (input : BitString) :
    workBoundedDecide machine (workSteps input - 1)
        (rawInputWorkTape input) = .timeout := by
  let short := workSteps input - 1
  let initial := workStartConfiguration machine
    (rawInputWorkTape input)
  let final := finalConfiguration input
  have hSucc : short + 1 = workSteps input := by
    dsimp [short]
    have hPositive := workSteps_positive input
    omega
  have hExact := workRunExact input
  change workRunExact? machine (workSteps input) initial = some final at hExact
  rw [← hSucc] at hExact
  rcases workRunExact_succ_split_last short initial final hExact with
    ⟨before, hPrefix, hLast⟩
  have hRun : workRun machine short initial = before :=
    workRun_eq_of_workRunExact machine short initial before hPrefix
  have hNotHalted := isHalted_false_of_workStep_some before final hLast
  unfold workBoundedDecide
  change
    (let result := workRun machine short initial
     if result.state == machine.acceptState then WorkVerdict.accept
     else if result.state == machine.rejectState then WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout
  rw [hRun]
  cases hAccept : (before.state == machine.acceptState) with
  | true =>
      unfold WorkMachine.isHalted at hNotHalted
      rw [hAccept] at hNotHalted
      contradiction
  | false =>
      cases hReject : (before.state == machine.rejectState) with
      | true =>
          unfold WorkMachine.isHalted at hNotHalted
          rw [hAccept, hReject] at hNotHalted
          contradiction
      | false => simp [hAccept, hReject]

end BuilderInputPrefix

end CookLevin

end PNP.Concrete
