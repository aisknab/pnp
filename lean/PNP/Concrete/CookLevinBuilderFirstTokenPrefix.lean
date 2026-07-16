/-
Copyright (c) 2026 PNP Labs.

Literal composition of the complete raw-input preparation prefix with the
fixed first Cook--Levin header-token appender.

The finite work machine in this file executes an ordinary raw bitstring
through the total framer, constructs its exact unary input-length tally,
takes one symbol-preserving launch transition, and emits the first canonical
formula token `CNFToken.t`.  It therefore materializes exactly the first two
bits of the encoded formula.  It does not compute the remaining width header,
interpret a dynamic formula cursor, construct the complete formula, provide a
RawRefinement or polynomial reduction, prove CNF-SAT is in P, or establish
P = NP.
-/

import PNP.Concrete.CookLevinBuilderTokenAppender

namespace PNP.Concrete

namespace CookLevin

namespace BuilderFirstTokenPrefix

open PipelineStateNamespace PipelineStageBridges

/-! ### Collision-free component images and literal rule table -/

/-- Outer state image containing the complete raw-input/tally prefix. -/
def prefixState (state : Nat) : Nat := inputState state

/-- Outer state image containing the complete fixed token appender. -/
def appenderState (state : Nat) : Nat := simulationState state

theorem prefixState_injective : Function.Injective prefixState :=
  inputState_injective

theorem appenderState_injective : Function.Injective appenderState :=
  simulationState_injective

theorem prefixState_ne_appenderState (left right : Nat) :
    prefixState left ≠ appenderState right :=
  inputState_ne_simulationState left right

/-- The complete 116-rule input prefix in its outer state image. -/
def renamedPrefix : WorkMachine :=
  renameMachine prefixState BuilderInputPrefix.machine

/-- The complete 59-rule token appender in its disjoint outer image. -/
def renamedAppender : WorkMachine :=
  renameMachine appenderState BuilderTokenAppender.machine

/-- Nine symbol-preserving rules launch the appender from the completed
input-prefix endpoint. -/
def launchRules : List WorkRule :=
  PipelineStageBridges.launchRules
    (prefixState BuilderInputPrefix.machine.acceptState)
    (appenderState BuilderTokenAppender.machine.startState)

/-- One literal bridge-first table containing both complete renamed
components. -/
def rules : List WorkRule :=
  launchRules ++
    (BuilderInputPrefix.machine.rules.map (renameRule prefixState) ++
      BuilderTokenAppender.machine.rules.map (renameRule appenderState))

/-- The executable raw-input-to-first-token work machine.  Only the token
appender's accept and reject images are global halts. -/
def machine : WorkMachine :=
  { rules := rules
    startState := prefixState BuilderInputPrefix.machine.startState
    acceptState := appenderState BuilderTokenAppender.machine.acceptState
    rejectState := appenderState BuilderTokenAppender.machine.rejectState }

theorem rules_length : rules.length = 184 := by rfl

theorem rules_pairwise_query_distinct :
    rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  set_option maxRecDepth 10000 in
    decide

theorem machine_acceptState_ne_rejectState :
    machine.acceptState ≠ machine.rejectState := by
  intro h
  exact BuilderTokenAppender.machine_acceptState_ne_rejectState
    (appenderState_injective h)

/-! ### Exact endpoint and displayed costs -/

/-- Exact work-transition count through the complete input prefix, the new
launch, and the distinguished first-token append. -/
def workSteps (input : BitString) : Nat :=
  BuilderInputPrefix.workSteps input + 1 +
    BuilderTokenAppender.workSteps input []

/-- Sum of the two reviewed external raw bounds and the six raw transitions
implementing the new work-level launch. -/
def rawTimeBound : NatPolynomial :=
  .add
    (.add BuilderInputPrefix.rawTimeBound (.constant 6))
    BuilderTokenAppender.firstTokenRawTimeBound

/-- Preserved represented input and unary tally with output `[CNFToken.t]`. -/
def finalTape (input : BitString) : WorkTape :=
  BuilderTokenAppender.workspaceTape input
    (PipelineInputFramer.totalInputFramerOutsideLeft input) [.t]

def finalConfiguration (input : BitString) : WorkConfiguration :=
  { state := machine.acceptState
    tape := finalTape input }

theorem finalTape_represents (input : BitString) :
    PipelineTape.Represents (Tape.ofInput input) (finalTape input) := by
  exact BuilderTokenAppender.workspaceTape_represents input
    (PipelineInputFramer.totalInputFramerOutsideLeft input) [.t]

/-! ### Private halt-separation and transport infrastructure -/

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

private theorem machine_isHalted_prefix_false
    (config : WorkConfiguration) :
    machine.isHalted (renameConfiguration prefixState config) = false := by
  unfold WorkMachine.isHalted machine renameConfiguration
  rw [nat_beq_false_of_ne _ _
      (prefixState_ne_appenderState config.state
        BuilderTokenAppender.machine.acceptState),
    nat_beq_false_of_ne _ _
      (prefixState_ne_appenderState config.state
        BuilderTokenAppender.machine.rejectState)]
  rfl

private theorem machine_isHalted_appender_false_of_local
    (config : WorkConfiguration)
    (hLocal : BuilderTokenAppender.machine.isHalted config = false) :
    machine.isHalted (renameConfiguration appenderState config) = false := by
  have hAccept := state_ne_accept_of_not_halted
    BuilderTokenAppender.machine config hLocal
  have hReject := state_ne_reject_of_not_halted
    BuilderTokenAppender.machine config hLocal
  have hGlobalAccept : appenderState config.state ≠
      appenderState BuilderTokenAppender.machine.acceptState := by
    intro h
    exact hAccept (appenderState_injective h)
  have hGlobalReject : appenderState config.state ≠
      appenderState BuilderTokenAppender.machine.rejectState := by
    intro h
    exact hReject (appenderState_injective h)
  unfold WorkMachine.isHalted machine renameConfiguration
  rw [nat_beq_false_of_ne _ _ hGlobalAccept,
    nat_beq_false_of_ne _ _ hGlobalReject]
  rfl

/-! ### First-match lookup isolation -/

theorem findWorkRule_prefix_of_some
    (state : Nat) (symbol : WorkSymbol) (rule : WorkRule)
    (hAccept : state ≠ BuilderInputPrefix.machine.acceptState)
    (hFind : findWorkRule BuilderInputPrefix.machine.rules state symbol =
      some rule) :
    findWorkRule machine.rules (prefixState state) symbol =
      some (renameRule prefixState rule) := by
  have hLaunch : findWorkRule launchRules
      (prefixState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    intro h
    exact hAccept (prefixState_injective h).symm
  have hRenamed := findWorkRule_rename prefixState prefixState_injective
    BuilderInputPrefix.machine.rules state symbol
  rw [hFind] at hRenamed
  unfold machine rules
  rw [findWorkRule_append_of_none _ _ _ _ hLaunch]
  exact findWorkRule_append_of_some _ _ _ _ _ hRenamed

theorem findWorkRule_appender_of_some
    (state : Nat) (symbol : WorkSymbol) (rule : WorkRule)
    (hFind : findWorkRule BuilderTokenAppender.machine.rules state symbol =
      some rule) :
    findWorkRule machine.rules (appenderState state) symbol =
      some (renameRule appenderState rule) := by
  have hLaunch : findWorkRule launchRules
      (appenderState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact prefixState_ne_appenderState _ _
  have hPrefix : findWorkRule
      (BuilderInputPrefix.machine.rules.map (renameRule prefixState))
      (appenderState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact prefixState_ne_appenderState source state
  have hRenamed := findWorkRule_rename appenderState appenderState_injective
    BuilderTokenAppender.machine.rules state symbol
  rw [hFind] at hRenamed
  unfold machine rules
  rw [findWorkRule_append_of_none _ _ _ _ hLaunch,
    findWorkRule_append_of_none _ _ _ _ hPrefix]
  exact hRenamed

private theorem prefix_workStep?_of_some
    (config next : WorkConfiguration)
    (hStep : workStep? BuilderInputPrefix.machine config = some next) :
    workStep? machine (renameConfiguration prefixState config) =
      some (renameConfiguration prefixState next) := by
  rcases workStep?_some_exists BuilderInputPrefix.machine config next hStep with
    ⟨rule, hHalted, hFind, hNext⟩
  have hAccept := state_ne_accept_of_not_halted
    BuilderInputPrefix.machine config hHalted
  have hGlobalHalted := machine_isHalted_prefix_false config
  have hGlobalFind := findWorkRule_prefix_of_some
    config.state config.tape.head rule hAccept hFind
  have hGlobalStep := workStep?_eq_apply_of_find machine
    (renameConfiguration prefixState config)
    (renameRule prefixState rule) hGlobalHalted hGlobalFind
  calc
    workStep? machine (renameConfiguration prefixState config) =
        some (applyWorkRule (renameRule prefixState rule)
          (renameConfiguration prefixState config)) := hGlobalStep
    _ = some (renameConfiguration prefixState
          (applyWorkRule rule config)) :=
      congrArg Option.some (applyWorkRule_rename prefixState rule config)
    _ = some (renameConfiguration prefixState next) :=
      congrArg (fun value => some (renameConfiguration prefixState value))
        hNext.symm

private theorem appender_workStep?_of_some
    (config next : WorkConfiguration)
    (hStep : workStep? BuilderTokenAppender.machine config = some next) :
    workStep? machine (renameConfiguration appenderState config) =
      some (renameConfiguration appenderState next) := by
  rcases workStep?_some_exists BuilderTokenAppender.machine
      config next hStep with ⟨rule, hHalted, hFind, hNext⟩
  have hGlobalHalted :=
    machine_isHalted_appender_false_of_local config hHalted
  have hGlobalFind := findWorkRule_appender_of_some
    config.state config.tape.head rule hFind
  have hGlobalStep := workStep?_eq_apply_of_find machine
    (renameConfiguration appenderState config)
    (renameRule appenderState rule) hGlobalHalted hGlobalFind
  calc
    workStep? machine (renameConfiguration appenderState config) =
        some (applyWorkRule (renameRule appenderState rule)
          (renameConfiguration appenderState config)) := hGlobalStep
    _ = some (renameConfiguration appenderState
          (applyWorkRule rule config)) :=
      congrArg Option.some (applyWorkRule_rename appenderState rule config)
    _ = some (renameConfiguration appenderState next) :=
      congrArg (fun value => some (renameConfiguration appenderState value))
        hNext.symm

/-! ### Literal launch and exact all-input trace -/

/-- The outer launch preserves the completed input/tally tape and its head. -/
theorem launch_workStep (input : BitString) :
    workStep? machine
        (renameConfiguration prefixState
          (BuilderInputPrefix.finalConfiguration input)) =
      some (renameConfiguration appenderState
        (workStartConfiguration BuilderTokenAppender.machine
          (BuilderInputPrefix.finalTape input))) := by
  let final := BuilderInputPrefix.finalConfiguration input
  have hHalted := machine_isHalted_prefix_false final
  have hLaunch := findWorkRule_launchRules
    (prefixState BuilderInputPrefix.machine.acceptState)
    (appenderState BuilderTokenAppender.machine.startState)
    final.tape.head
  have hFind : findWorkRule machine.rules
      (prefixState final.state) final.tape.head =
        some (PipelineStageBridges.launchRule
          (prefixState BuilderInputPrefix.machine.acceptState)
          (appenderState BuilderTokenAppender.machine.startState)
          final.tape.head) := by
    unfold machine rules
    simpa [launchRules, final, BuilderInputPrefix.finalConfiguration] using
      (findWorkRule_append_of_some _ _ _ _ _ hLaunch)
  have hStep := workStep?_eq_apply_of_find machine
    (renameConfiguration prefixState final)
    (PipelineStageBridges.launchRule
      (prefixState BuilderInputPrefix.machine.acceptState)
      (appenderState BuilderTokenAppender.machine.startState)
      final.tape.head) hHalted hFind
  simpa [final, PipelineStageBridges.launchRule, applyWorkRule,
    WorkTape.write, WorkTape.move, workStartConfiguration,
    renameConfiguration, BuilderInputPrefix.finalConfiguration] using hStep

theorem prefix_workRunExact (input : BitString) :
    workRunExact? machine (BuilderInputPrefix.workSteps input)
        (workStartConfiguration machine (rawInputWorkTape input)) =
      some (renameConfiguration prefixState
        (BuilderInputPrefix.finalConfiguration input)) := by
  have hTransport := PipelineStageBridges.workRunExact?_transport
    BuilderInputPrefix.machine machine prefixState
    prefix_workStep?_of_some (BuilderInputPrefix.workSteps input)
    (workStartConfiguration BuilderInputPrefix.machine
      (rawInputWorkTape input))
    (BuilderInputPrefix.finalConfiguration input)
    (BuilderInputPrefix.workRunExact input)
  simpa [machine, workStartConfiguration, renameConfiguration] using hTransport

theorem appender_workRunExact (input : BitString) :
    workRunExact? machine (BuilderTokenAppender.workSteps input [])
        (renameConfiguration appenderState
          (workStartConfiguration BuilderTokenAppender.machine
            (BuilderInputPrefix.finalTape input))) =
      some (finalConfiguration input) := by
  have hLocal :=
    BuilderTokenAppender.firstHeaderToken_after_builderInputPrefix input
  have hTransport := PipelineStageBridges.workRunExact?_transport
    BuilderTokenAppender.machine machine appenderState
    appender_workStep?_of_some (BuilderTokenAppender.workSteps input [])
    (workStartConfiguration BuilderTokenAppender.machine
      (BuilderInputPrefix.finalTape input))
    (BuilderTokenAppender.firstHeaderFinalConfiguration input
      (PipelineInputFramer.totalInputFramerOutsideLeft input)) hLocal
  simpa [finalConfiguration, finalTape, machine,
    BuilderTokenAppender.firstHeaderFinalConfiguration,
    BuilderTokenAppender.finalConfiguration, renameConfiguration] using
      hTransport

/-- Every raw bitstring follows one exact successful trace through all 184
literal rules and reaches the tape containing the first header token. -/
theorem workRunExact (input : BitString) :
    workRunExact? machine (workSteps input)
        (workStartConfiguration machine (rawInputWorkTape input)) =
      some (finalConfiguration input) := by
  have hLaunch : workRunExact? machine 1
      (renameConfiguration prefixState
        (BuilderInputPrefix.finalConfiguration input)) =
      some (renameConfiguration appenderState
        (workStartConfiguration BuilderTokenAppender.machine
          (BuilderInputPrefix.finalTape input))) := by
    change
      (match workStep? machine
          (renameConfiguration prefixState
            (BuilderInputPrefix.finalConfiguration input)) with
       | none => none
       | some next => workRunExact? machine 0 next) = _
    rw [launch_workStep input]
    rfl
  have hPrefixLaunch := PipelineMachineSimulation.workRunExact?_compose
    machine (BuilderInputPrefix.workSteps input) 1
    (workStartConfiguration machine (rawInputWorkTape input))
    (renameConfiguration prefixState
      (BuilderInputPrefix.finalConfiguration input))
    (renameConfiguration appenderState
      (workStartConfiguration BuilderTokenAppender.machine
        (BuilderInputPrefix.finalTape input)))
    (prefix_workRunExact input) hLaunch
  have hComplete := PipelineMachineSimulation.workRunExact?_compose
    machine (BuilderInputPrefix.workSteps input + 1)
    (BuilderTokenAppender.workSteps input [])
    (workStartConfiguration machine (rawInputWorkTape input))
    (renameConfiguration appenderState
      (workStartConfiguration BuilderTokenAppender.machine
        (BuilderInputPrefix.finalTape input)))
    (finalConfiguration input) hPrefixLaunch (appender_workRunExact input)
  simpa [workSteps] using hComplete

private theorem finalConfiguration_isHalted (input : BitString) :
    machine.isHalted (finalConfiguration input) = true := by
  rfl

/-! ### Formula prefix and compiled external polynomial -/

/-- The emitted token's two bits are the first two bits of every concrete
Cook--Levin formula. -/
theorem finalTokenBits_eq_encodedFormula_take_two
    {language : Language} (problem : VerifierTableauProblem language) :
    CNFToken.t.bits = problem.encodedFormula.take 2 := by
  exact BuilderTokenAppender.firstHeaderToken_bits_eq_encodedFormula_take_two
    problem

theorem rawTimeBound_eval (input : BitString) :
    rawTimeBound.eval (BitString.size input) =
      18 * input.length * input.length + 87 * input.length + 147 := by
  rw [rawTimeBound, NatPolynomial.eval_add, NatPolynomial.eval_add,
    NatPolynomial.eval_constant,
    BuilderInputPrefix.rawTimeBound_eval,
    BuilderTokenAppender.firstTokenRawTimeBound_eval]
  omega

theorem rawTimeBound_le (input : BitString) :
    6 * workSteps input ≤ rawTimeBound.eval (BitString.size input) := by
  have hPrefix := BuilderInputPrefix.rawTimeBound_le input
  have hAppender := BuilderTokenAppender.firstTokenRawTimeBound_le input
  rw [rawTimeBound_eval]
  rw [BuilderInputPrefix.rawTimeBound_eval] at hPrefix
  rw [BuilderTokenAppender.firstTokenRawTimeBound_eval] at hAppender
  unfold workSteps
  omega

/-- Exact six-for-one compilation of the complete successful work trace. -/
theorem run_compile_exact (input : BitString) :
    run (compileWorkMachine machine) (6 * workSteps input)
        (encodeWorkConfiguration
          (workStartConfiguration machine (rawInputWorkTape input))) =
      encodeWorkConfiguration (finalConfiguration input) := by
  exact run_compileWorkMachine_mul_of_workRunExact machine
    (workSteps input)
    (workStartConfiguration machine (rawInputWorkTape input))
    (finalConfiguration input) (workRunExact input)

/-- The compiled composed machine reaches the exact endpoint within
`18*n^2 + 87*n + 147` raw transitions. -/
theorem run_compile_rawTimeBound (input : BitString) :
    run (compileWorkMachine machine)
        (rawTimeBound.eval (BitString.size input))
        (encodeWorkConfiguration
          (workStartConfiguration machine (rawInputWorkTape input))) =
      encodeWorkConfiguration (finalConfiguration input) := by
  exact run_compileWorkMachine_of_workRunExact_halted_le
    machine (workSteps input)
    (rawTimeBound.eval (BitString.size input))
    (workStartConfiguration machine (rawInputWorkTape input))
    (finalConfiguration input) (workRunExact input)
    (finalConfiguration_isHalted input) (rawTimeBound_le input)

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

private theorem verdict_timeout_of_not_halted
    (config : WorkConfiguration)
    (hHalted : machine.isHalted config = false) :
    (if config.state == machine.acceptState then WorkVerdict.accept
     else if config.state == machine.rejectState then WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  unfold WorkMachine.isHalted at hHalted
  cases hAccept : (config.state == machine.acceptState) with
  | true =>
      rw [hAccept] at hHalted
      contradiction
  | false =>
      cases hReject : (config.state == machine.rejectState) with
      | true =>
          rw [hAccept, hReject] at hHalted
          contradiction
      | false => rfl

private theorem stuck_timeout (fuel : Nat) (config : WorkConfiguration)
    (hHalted : machine.isHalted config = false)
    (hStep : workStep? machine config = none) :
    (let result := workRun machine fuel config
     if result.state == machine.acceptState then WorkVerdict.accept
     else if result.state == machine.rejectState then WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  have hRun := workRun_eq_self_of_workStep?_eq_none machine config fuel hStep
  rw [hRun]
  exact verdict_timeout_of_not_halted config hHalted

/-- The exact prefix endpoint is nonhalting until the ninth-symbol-total
launch table executes one further transition. -/
theorem prefixEndpoint_before_launch_timeout (input : BitString) :
    workBoundedDecide machine (BuilderInputPrefix.workSteps input)
        (rawInputWorkTape input) = .timeout := by
  unfold workBoundedDecide
  rw [workRun_eq_of_workRunExact machine
    (BuilderInputPrefix.workSteps input)
    (workStartConfiguration machine (rawInputWorkTape input))
    (renameConfiguration prefixState
      (BuilderInputPrefix.finalConfiguration input))
    (prefix_workRunExact input)]
  exact verdict_timeout_of_not_halted _
    (machine_isHalted_prefix_false
      (BuilderInputPrefix.finalConfiguration input))

private theorem findWorkRule_none_of_workStep_none
    (source : WorkMachine) (config : WorkConfiguration)
    (hHalted : source.isHalted config = false)
    (hStep : workStep? source config = none) :
    findWorkRule source.rules config.state config.tape.head = none := by
  unfold workStep? at hStep
  rw [hHalted] at hStep
  cases hFind : findWorkRule source.rules config.state config.tape.head with
  | none => rfl
  | some rule =>
      rw [hFind] at hStep
      contradiction

private theorem findWorkRule_prefix_of_none
    (state : Nat) (symbol : WorkSymbol)
    (hAccept : state ≠ BuilderInputPrefix.machine.acceptState)
    (hFind : findWorkRule BuilderInputPrefix.machine.rules state symbol =
      none) :
    findWorkRule machine.rules (prefixState state) symbol = none := by
  have hLaunch : findWorkRule launchRules (prefixState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    intro h
    exact hAccept (prefixState_injective h).symm
  have hRenamed := findWorkRule_rename prefixState prefixState_injective
    BuilderInputPrefix.machine.rules state symbol
  rw [hFind] at hRenamed
  have hAppender : findWorkRule
      (BuilderTokenAppender.machine.rules.map (renameRule appenderState))
      (prefixState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact (prefixState_ne_appenderState state source).symm
  unfold machine rules
  rw [findWorkRule_append_of_none _ _ _ _ hLaunch,
    findWorkRule_append_of_none _ _ _ _ hRenamed]
  exact hAppender

private theorem findWorkRule_appender_of_none
    (state : Nat) (symbol : WorkSymbol)
    (hFind : findWorkRule BuilderTokenAppender.machine.rules state symbol =
      none) :
    findWorkRule machine.rules (appenderState state) symbol = none := by
  have hLaunch : findWorkRule launchRules
      (appenderState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact prefixState_ne_appenderState _ _
  have hPrefix : findWorkRule
      (BuilderInputPrefix.machine.rules.map (renameRule prefixState))
      (appenderState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact prefixState_ne_appenderState source state
  have hRenamed := findWorkRule_rename appenderState appenderState_injective
    BuilderTokenAppender.machine.rules state symbol
  rw [hFind] at hRenamed
  unfold machine rules
  rw [findWorkRule_append_of_none _ _ _ _ hLaunch,
    findWorkRule_append_of_none _ _ _ _ hPrefix]
  exact hRenamed

private theorem prefix_workStep_none_of_local
    (config : WorkConfiguration)
    (hAccept : config.state ≠ BuilderInputPrefix.machine.acceptState)
    (hLocalHalted : BuilderInputPrefix.machine.isHalted config = false)
    (hLocalStep : workStep? BuilderInputPrefix.machine config = none) :
    workStep? machine (renameConfiguration prefixState config) = none := by
  have hFind := findWorkRule_none_of_workStep_none
    BuilderInputPrefix.machine config hLocalHalted hLocalStep
  have hGlobalFind := findWorkRule_prefix_of_none
    config.state config.tape.head hAccept hFind
  unfold workStep?
  rw [machine_isHalted_prefix_false config]
  change
    (match findWorkRule machine.rules (prefixState config.state)
        config.tape.head with
     | none => none
     | some rule =>
         some (applyWorkRule rule
           (renameConfiguration prefixState config))) = none
  rw [hGlobalFind]

private theorem appender_workStep_none_of_local
    (config : WorkConfiguration)
    (hLocalHalted : BuilderTokenAppender.machine.isHalted config = false)
    (hLocalStep : workStep? BuilderTokenAppender.machine config = none) :
    workStep? machine (renameConfiguration appenderState config) = none := by
  have hFind := findWorkRule_none_of_workStep_none
    BuilderTokenAppender.machine config hLocalHalted hLocalStep
  have hGlobalFind := findWorkRule_appender_of_none
    config.state config.tape.head hFind
  unfold workStep?
  rw [machine_isHalted_appender_false_of_local config hLocalHalted]
  change
    (match findWorkRule machine.rules (appenderState config.state)
        config.tape.head with
     | none => none
     | some rule =>
         some (applyWorkRule rule
           (renameConfiguration appenderState config))) = none
  rw [hGlobalFind]

/-- An invalid symbol in the inner prefix tally remains stuck and globally
nonhalting for every fuel budget. -/
theorem malformedPrefixTally_timeout (fuel : Nat)
    (left right : List WorkSymbol) :
    (let config := renameConfiguration prefixState
        (BuilderInputPrefix.malformedTallyConfiguration left right)
     let result := workRun machine fuel config
     if result.state == machine.acceptState then WorkVerdict.accept
     else if result.state == machine.rejectState then WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  let bad := BuilderInputPrefix.malformedTallyConfiguration left right
  have hLocalHalted :=
    BuilderInputPrefix.malformedTallyScanSymbol_isHalted_false left right
  have hLocalStep :=
    BuilderInputPrefix.malformedTallyScanSymbol_workStep_none left right
  have hAccept : bad.state ≠ BuilderInputPrefix.machine.acceptState := by
    change BuilderInputPrefix.tallyState BuilderInputLength.scanState ≠
      BuilderInputPrefix.tallyState BuilderInputLength.machine.acceptState
    intro h
    have hInner := BuilderInputPrefix.tallyState_injective h
    exact (by decide : BuilderInputLength.scanState ≠
      BuilderInputLength.machine.acceptState) hInner
  have hStep := prefix_workStep_none_of_local bad hAccept
    hLocalHalted hLocalStep
  exact stuck_timeout fuel (renameConfiguration prefixState bad)
    (machine_isHalted_prefix_false bad) hStep

/-- An invalid tally-phase symbol in the appender cannot fall through to a
global accept or reject endpoint. -/
theorem malformedAppenderTally_timeout (fuel : Nat) (request : CNFToken)
    (left right : List WorkSymbol) :
    (let config := renameConfiguration appenderState
        (BuilderTokenAppender.malformedTallyConfiguration request left right)
     let result := workRun machine fuel config
     if result.state == machine.acceptState then WorkVerdict.accept
     else if result.state == machine.rejectState then WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  let bad :=
    BuilderTokenAppender.malformedTallyConfiguration request left right
  have hLocalHalted :=
    BuilderTokenAppender.malformedTallySymbol_isHalted_false
      request left right
  have hLocalStep := BuilderTokenAppender.malformedTallySymbol_workStep_none
    request left right
  have hStep := appender_workStep_none_of_local bad
    hLocalHalted hLocalStep
  exact stuck_timeout fuel (renameConfiguration appenderState bad)
    (machine_isHalted_appender_false_of_local bad hLocalHalted) hStep

/-- An invalid output-phase symbol in the appender also remains timeout. -/
theorem malformedAppenderOutput_timeout (fuel : Nat) (request : CNFToken)
    (left right : List WorkSymbol) :
    (let config := renameConfiguration appenderState
        (BuilderTokenAppender.malformedOutputConfiguration request left right)
     let result := workRun machine fuel config
     if result.state == machine.acceptState then WorkVerdict.accept
     else if result.state == machine.rejectState then WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  let bad :=
    BuilderTokenAppender.malformedOutputConfiguration request left right
  have hLocalHalted :=
    BuilderTokenAppender.malformedOutputSymbol_isHalted_false
      request left right
  have hLocalStep := BuilderTokenAppender.malformedOutputSymbol_workStep_none
    request left right
  have hStep := appender_workStep_none_of_local bad
    hLocalHalted hLocalStep
  exact stuck_timeout fuel (renameConfiguration appenderState bad)
    (machine_isHalted_appender_false_of_local bad hLocalHalted) hStep

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

/-- Removing exactly the final successful transition leaves a nonhalting
state and therefore reports timeout. -/
theorem work_one_step_short_timeout (input : BitString) :
    workBoundedDecide machine (workSteps input - 1)
        (rawInputWorkTape input) = .timeout := by
  let short := workSteps input - 1
  let initial := workStartConfiguration machine (rawInputWorkTape input)
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
  exact verdict_timeout_of_not_halted before hNotHalted

end BuilderFirstTokenPrefix

end CookLevin

end PNP.Concrete
