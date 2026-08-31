/-
Copyright (c) 2026 PNP Labs.

A literal request-coded handoff into the Cook--Levin token appender.

One fixed finite machine reads a physical request cell immediately to the
left of the canonical builder workspace.  The five request symbols encode
padding or one of the four CNF tokens.  The dispatch transition restores the
left boundary and either accepts without changing the output or enters the
existing fixed token-appender state selected by the physical token symbol.

The canonical specialization derives the request at every post-header
coordinate from M215/M216.  This module does not construct that request cell
from the raw coordinate classifier, iterate one physical loop, construct the
complete raw formula builder, prove its RawRefinement, or package the
Cook--Levin reduction.
-/

import PNP.Concrete.CookLevinBuilderCompleteScheduleIteration

namespace PNP.Concrete

namespace CookLevin

namespace BuilderPhysicalOptionalTokenDispatch

open PipelineTape PipelineStateNamespace
open BuilderPostDividerSelectedTokenLaunch

abbrev appenderMachine : WorkMachine := BuilderTokenAppender.machine

def dispatchState : Nat := inputState 0
def appenderState (state : Nat) : Nat := simulationState state

theorem appenderState_injective : Function.Injective appenderState :=
  simulationState_injective

theorem dispatchState_ne_appenderState (state : Nat) :
    dispatchState ≠ appenderState state :=
  inputState_ne_simulationState 0 state

/-- The padding request uses the fifth symbol outside the four two-bit token
symbols. -/
def requestSymbol : Option CNFToken -> WorkSymbol
  | none => rightMarker
  | some token => BuilderTokenAppender.tokenSymbol token

theorem requestSymbol_injective : Function.Injective requestSymbol := by
  intro left right h
  cases left with
  | none =>
      cases right with
      | none => rfl
      | some token =>
          cases token <;>
            contradiction
  | some leftToken =>
      cases right with
      | none =>
          cases leftToken <;>
            contradiction
      | some rightToken =>
          congr
          exact BuilderTokenAppender.tokenSymbol_injective h

def requestOrder : List (Option CNFToken) :=
  [none, some .f, some .t, some .sep, some .finish]

def dispatchTarget : Option CNFToken -> Nat
  | none => appenderState appenderMachine.acceptState
  | some token => appenderState (BuilderTokenAppender.seekInputState token)

def dispatchRule (request : Option CNFToken) : WorkRule :=
  { sourceState := dispatchState
    readSymbol := requestSymbol request
    targetState := dispatchTarget request
    writeSymbol := leftMarker
    move := .right }

def dispatchRules : List WorkRule := requestOrder.map dispatchRule

def rules : List WorkRule :=
  dispatchRules ++ appenderMachine.rules.map (renameRule appenderState)

/-- One fixed 64-rule machine.  Five request rules feed one renamed copy of
the existing 59-rule appender. -/
def machine : WorkMachine :=
  { rules := rules
    startState := dispatchState
    acceptState := appenderState appenderMachine.acceptState
    rejectState := appenderState appenderMachine.rejectState }

theorem dispatchRules_length : dispatchRules.length = 5 := by rfl

theorem rules_length : rules.length = 64 := by rfl

theorem rules_pairwise_query_distinct :
    rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  decide

theorem machine_acceptState_ne_rejectState :
    machine.acceptState ≠ machine.rejectState := by
  intro h
  exact BuilderTokenAppender.machine_acceptState_ne_rejectState
    (appenderState_injective h)

/-- Output after interpreting one optional token request. -/
def nextOutput (output : List CNFToken) : Option CNFToken -> List CNFToken
  | none => output
  | some token => output ++ [token]

/-- The request cell replaces the canonical left boundary and is focused one
physical work cell before the ordinary appender workspace. -/
def requestTape (input : BitString) (outsideLeft : List WorkSymbol)
    (output : List CNFToken) (request : Option CNFToken) : WorkTape :=
  let workspace := BuilderTokenAppender.workspaceTape input outsideLeft output
  { left := outsideLeft
    head := requestSymbol request
    right := workspace.head :: workspace.right }

def entryConfiguration (input : BitString)
    (outsideLeft : List WorkSymbol) (output : List CNFToken)
    (request : Option CNFToken) : WorkConfiguration :=
  { state := machine.startState
    tape := requestTape input outsideLeft output request }

def finalConfiguration (input : BitString)
    (outsideLeft : List WorkSymbol) (output : List CNFToken)
    (request : Option CNFToken) : WorkConfiguration :=
  renameConfiguration appenderState
    (BuilderTokenAppender.finalConfiguration input outsideLeft
      (nextOutput output request))

def workSteps (input : BitString) (output : List CNFToken) :
    Option CNFToken -> Nat
  | none => 1
  | some _ => 1 + BuilderTokenAppender.workSteps input output

theorem requestTape_dispatch_restores_workspace (input : BitString)
    (outsideLeft : List WorkSymbol) (output : List CNFToken)
    (request : Option CNFToken) :
    ((requestTape input outsideLeft output request).write leftMarker).move
        .right =
      BuilderTokenAppender.workspaceTape input outsideLeft output := by
  cases input <;> rfl

/-- The literal first transition is selected solely by the tape-resident
request symbol. -/
theorem dispatch_workStep (input : BitString)
    (outsideLeft : List WorkSymbol) (output : List CNFToken)
    (request : Option CNFToken) :
    workStep? machine (entryConfiguration input outsideLeft output request) =
      some
        (match request with
        | none => finalConfiguration input outsideLeft output none
        | some token =>
            renameConfiguration appenderState
              (BuilderTokenAppender.entryConfiguration token
                (BuilderTokenAppender.workspaceTape input outsideLeft
                  output))) := by
  cases input with
  | nil =>
      cases request with
      | none => rfl
      | some token =>
          cases token <;> rfl
  | cons bit rest =>
      cases request with
      | none => rfl
      | some token =>
          cases token <;> rfl

private theorem state_ne_accept_of_not_halted
    (source : WorkMachine) (config : WorkConfiguration)
    (hHalted : source.isHalted config = false) :
    config.state ≠ source.acceptState := by
  intro hState
  unfold WorkMachine.isHalted at hHalted
  rw [hState, (nat_beq_true_iff _ _).mpr rfl] at hHalted
  contradiction

private theorem state_ne_reject_of_not_halted
    (source : WorkMachine) (config : WorkConfiguration)
    (hHalted : source.isHalted config = false) :
    config.state ≠ source.rejectState := by
  intro hState
  unfold WorkMachine.isHalted at hHalted
  rw [hState, (nat_beq_true_iff _ _).mpr rfl] at hHalted
  simp at hHalted

private theorem nat_beq_false_of_ne (left right : Nat)
    (h : left ≠ right) : (left == right) = false := by
  cases hBool : (left == right) with
  | false => rfl
  | true => exact False.elim (h ((nat_beq_true_iff left right).mp hBool))

theorem machine_isHalted_appender_false_of_local
    (config : WorkConfiguration)
    (hLocal : appenderMachine.isHalted config = false) :
    machine.isHalted (renameConfiguration appenderState config) = false := by
  have hAccept := state_ne_accept_of_not_halted appenderMachine config hLocal
  have hReject := state_ne_reject_of_not_halted appenderMachine config hLocal
  unfold WorkMachine.isHalted machine renameConfiguration
  rw [nat_beq_false_of_ne _ _
      (fun h => hAccept (appenderState_injective h)),
    nat_beq_false_of_ne _ _
      (fun h => hReject (appenderState_injective h))]
  rfl

theorem findWorkRule_dispatchRules_appender_none
    (state : Nat) (symbol : WorkSymbol) :
    findWorkRule dispatchRules (appenderState state) symbol = none := by
  have hSource : dispatchState ≠ appenderState state :=
    dispatchState_ne_appenderState state
  unfold dispatchRules requestOrder
  simp only [List.map_cons, List.map_nil]
  rw [findWorkRule_cons_of_not_matches _ _ _ _ (by
    intro h; exact hSource h.1)]
  rw [findWorkRule_cons_of_not_matches _ _ _ _ (by
    intro h; exact hSource h.1)]
  rw [findWorkRule_cons_of_not_matches _ _ _ _ (by
    intro h; exact hSource h.1)]
  rw [findWorkRule_cons_of_not_matches _ _ _ _ (by
    intro h; exact hSource h.1)]
  rw [findWorkRule_cons_of_not_matches _ _ _ _ (by
    intro h; exact hSource h.1)]
  rfl

theorem findWorkRule_appender_of_some (state : Nat)
    (symbol : WorkSymbol) (rule : WorkRule)
    (hFind : findWorkRule appenderMachine.rules state symbol = some rule) :
    findWorkRule machine.rules (appenderState state) symbol =
      some (renameRule appenderState rule) := by
  have hRenamed := findWorkRule_rename appenderState appenderState_injective
    appenderMachine.rules state symbol
  rw [hFind] at hRenamed
  unfold machine rules
  rw [findWorkRule_append_of_none _ _ _ _
    (findWorkRule_dispatchRules_appender_none state symbol)]
  exact hRenamed

theorem appender_workStep_of_some (config next : WorkConfiguration)
    (hStep : workStep? appenderMachine config = some next) :
    workStep? machine (renameConfiguration appenderState config) =
      some (renameConfiguration appenderState next) := by
  rcases workStep?_some_exists appenderMachine config next hStep with
    ⟨rule, hHalted, hFind, hNext⟩
  have hGlobalHalted := machine_isHalted_appender_false_of_local config hHalted
  have hGlobalFind := findWorkRule_appender_of_some config.state
    config.tape.head rule hFind
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

theorem appender_workRunExact (steps : Nat)
    (start final : WorkConfiguration)
    (hRun : workRunExact? appenderMachine steps start = some final) :
    workRunExact? machine steps (renameConfiguration appenderState start) =
      some (renameConfiguration appenderState final) := by
  exact PipelineStageBridges.workRunExact?_transport appenderMachine machine
    appenderState appender_workStep_of_some steps start final hRun

/-- Every valid physical request has one exact literal-machine execution. -/
theorem workRunExact (input : BitString)
    (outsideLeft : List WorkSymbol) (output : List CNFToken)
    (request : Option CNFToken) :
    workRunExact? machine (workSteps input output request)
        (entryConfiguration input outsideLeft output request) =
      some (finalConfiguration input outsideLeft output request) := by
  cases request with
  | none =>
      change
        (match workStep? machine
            (entryConfiguration input outsideLeft output none) with
        | none => none
        | some next => some next) =
          some (finalConfiguration input outsideLeft output none)
      rw [dispatch_workStep]
  | some token =>
      let initial := BuilderTokenAppender.entryConfiguration token
        (BuilderTokenAppender.workspaceTape input outsideLeft output)
      let final := BuilderTokenAppender.finalConfiguration input outsideLeft
        (output ++ [token])
      have hLaunch :
          workRunExact? machine 1
              (entryConfiguration input outsideLeft output (some token)) =
            some (renameConfiguration appenderState initial) := by
        change
          (match workStep? machine
              (entryConfiguration input outsideLeft output (some token)) with
          | none => none
          | some next => some next) =
            some (renameConfiguration appenderState initial)
        rw [dispatch_workStep]
      have hLocal :
          workRunExact? appenderMachine
              (BuilderTokenAppender.workSteps input output) initial =
            some final := by
        exact BuilderTokenAppender.appendToken_workRunExact input outsideLeft
          output token
      have hTail := appender_workRunExact
        (BuilderTokenAppender.workSteps input output) initial final hLocal
      have hCombined := PipelineMachineSimulation.workRunExact?_compose machine
        1 (BuilderTokenAppender.workSteps input output)
        (entryConfiguration input outsideLeft output (some token))
        (renameConfiguration appenderState initial)
        (renameConfiguration appenderState final) hLaunch hTail
      simpa [workSteps, finalConfiguration, nextOutput, initial, final] using
        hCombined

theorem run_compile_exact (input : BitString)
    (outsideLeft : List WorkSymbol) (output : List CNFToken)
    (request : Option CNFToken) :
    run (compileWorkMachine machine) (6 * workSteps input output request)
        (encodeWorkConfiguration
          (entryConfiguration input outsideLeft output request)) =
      encodeWorkConfiguration
        (finalConfiguration input outsideLeft output request) := by
  exact run_compileWorkMachine_mul_of_workRunExact machine
    (workSteps input output request)
    (entryConfiguration input outsideLeft output request)
    (finalConfiguration input outsideLeft output request)
    (workRunExact input outsideLeft output request)

private theorem workRunExact_succ_split_last (selectedMachine : WorkMachine) :
    forall (steps : Nat) (initial final : WorkConfiguration),
      workRunExact? selectedMachine (steps + 1) initial = some final ->
      exists before,
        workRunExact? selectedMachine steps initial = some before /\
          workStep? selectedMachine before = some final := by
  intro steps
  induction steps with
  | zero =>
      intro initial final hRun
      cases hStep : workStep? selectedMachine initial with
      | none =>
          change
            (match workStep? selectedMachine initial with
            | none => none
            | some next => some next) = some final at hRun
          rw [hStep] at hRun
          contradiction
      | some next =>
          have hNext : next = final := by
            change
              (match workStep? selectedMachine initial with
              | none => none
              | some result => some result) = some final at hRun
            rw [hStep] at hRun
            exact Option.some.inj hRun
          subst final
          exact ⟨initial, rfl, hStep⟩
  | succ steps ih =>
      intro initial final hRun
      cases hStep : workStep? selectedMachine initial with
      | none =>
          change
            (match workStep? selectedMachine initial with
            | none => none
            | some next => workRunExact? selectedMachine (steps + 1) next) =
              some final at hRun
          rw [hStep] at hRun
          contradiction
      | some next =>
          have hTail : workRunExact? selectedMachine (steps + 1) next =
              some final := by
            change
              (match workStep? selectedMachine initial with
              | none => none
              | some result =>
                  workRunExact? selectedMachine (steps + 1) result) =
                some final at hRun
            rw [hStep] at hRun
            exact hRun
          rcases ih next final hTail with ⟨before, hPrefix, hLast⟩
          refine ⟨before, ?_, hLast⟩
          change
            (match workStep? selectedMachine initial with
            | none => none
            | some result => workRunExact? selectedMachine steps result) =
              some before
          rw [hStep]
          exact hPrefix

private theorem isHalted_false_of_workStep_some
    (selectedMachine : WorkMachine) (configuration next : WorkConfiguration)
    (hStep : workStep? selectedMachine configuration = some next) :
    selectedMachine.isHalted configuration = false := by
  cases hHalted : selectedMachine.isHalted configuration with
  | false => rfl
  | true =>
      unfold workStep? at hStep
      rw [hHalted] at hStep
      contradiction

private theorem one_step_short_not_halted_of_exact
    (selectedMachine : WorkMachine) (steps : Nat)
    (initial final : WorkConfiguration) (hPositive : 0 < steps)
    (hExact : workRunExact? selectedMachine steps initial = some final) :
    selectedMachine.isHalted
        (workRun selectedMachine (steps - 1) initial) = false := by
  let short := steps - 1
  have hSucc : short + 1 = steps := by
    dsimp [short]
    omega
  rw [← hSucc] at hExact
  rcases workRunExact_succ_split_last selectedMachine short initial final
      hExact with ⟨before, hPrefix, hLast⟩
  have hRun : workRun selectedMachine short initial = before :=
    workRun_eq_of_workRunExact selectedMachine short initial before hPrefix
  rw [hRun]
  exact isHalted_false_of_workStep_some selectedMachine before final hLast

theorem workSteps_positive (input : BitString) (output : List CNFToken)
    (request : Option CNFToken) : 0 < workSteps input output request := by
  cases request with
  | none =>
      change 0 < 1
      exact Nat.zero_lt_one
  | some token =>
      change 0 < 1 + BuilderTokenAppender.workSteps input output
      omega

theorem one_step_short_not_halted (input : BitString)
    (outsideLeft : List WorkSymbol) (output : List CNFToken)
    (request : Option CNFToken) :
    machine.isHalted
        (workRun machine (workSteps input output request - 1)
          (entryConfiguration input outsideLeft output request)) = false := by
  exact one_step_short_not_halted_of_exact machine
    (workSteps input output request)
    (entryConfiguration input outsideLeft output request)
    (finalConfiguration input outsideLeft output request)
    (workSteps_positive input output request)
    (workRunExact input outsideLeft output request)

def malformedRequestTape (input : BitString)
    (outsideLeft : List WorkSymbol) (output : List CNFToken) : WorkTape :=
  let workspace := BuilderTokenAppender.workspaceTape input outsideLeft output
  { left := outsideLeft
    head := WorkSymbol.blank
    right := workspace.head :: workspace.right }


def malformedRequestConfiguration (input : BitString)
    (outsideLeft : List WorkSymbol) (output : List CNFToken) :
    WorkConfiguration :=
  { state := machine.startState
    tape := malformedRequestTape input outsideLeft output }

theorem malformedRequest_workStep_none (input : BitString)
    (outsideLeft : List WorkSymbol) (output : List CNFToken) :
    workStep? machine
      (malformedRequestConfiguration input outsideLeft output) = none := by
  rfl

theorem malformedRequest_workRun (fuel : Nat) (input : BitString)
    (outsideLeft : List WorkSymbol) (output : List CNFToken) :
    workRun machine fuel
        (malformedRequestConfiguration input outsideLeft output) =
      malformedRequestConfiguration input outsideLeft output := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      change
        (match workStep? machine
            (malformedRequestConfiguration input outsideLeft output) with
        | none => malformedRequestConfiguration input outsideLeft output
        | some next => workRun machine fuel next) = _
      rw [malformedRequest_workStep_none]

theorem malformedRequest_timeout (fuel : Nat) (input : BitString)
    (outsideLeft : List WorkSymbol) (output : List CNFToken) :
    workBoundedDecide machine fuel
        (malformedRequestTape input outsideLeft output) = .timeout := by
  unfold workBoundedDecide
  have hStart : workStartConfiguration machine
      (malformedRequestTape input outsideLeft output) =
        malformedRequestConfiguration input outsideLeft output := rfl
  rw [hStart, malformedRequest_workRun]
  rfl

def canonicalRequest {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    Option CNFToken :=
  scheduleEntry problem index

def canonicalWorkSteps {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    Nat :=
  workSteps problem.input (emittedPrefix problem index.val)
    (canonicalRequest problem index)

theorem canonical_nextOutput {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    nextOutput (emittedPrefix problem index.val)
        (canonicalRequest problem index) =
      emittedPrefix problem (index.val + 1) := by
  change
    (match scheduleEntry problem index with
    | none => emittedPrefix problem index.val
    | some token => emittedPrefix problem index.val ++ [token]) = _
  exact (emittedPrefix_succ problem index).symm

theorem canonical_workRunExact {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (outsideLeft : List WorkSymbol) :
    workRunExact? machine (canonicalWorkSteps problem index)
        (entryConfiguration problem.input outsideLeft
          (emittedPrefix problem index.val) (canonicalRequest problem index)) =
      some
        (renameConfiguration appenderState
          (BuilderTokenAppender.finalConfiguration problem.input outsideLeft
            (emittedPrefix problem (index.val + 1)))) := by
  have hRun := workRunExact problem.input outsideLeft
    (emittedPrefix problem index.val) (canonicalRequest problem index)
  rw [← canonical_nextOutput problem index]
  simpa [canonicalWorkSteps, finalConfiguration] using hRun

theorem canonical_run_compile_exact {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (outsideLeft : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * canonicalWorkSteps problem index)
        (encodeWorkConfiguration
          (entryConfiguration problem.input outsideLeft
            (emittedPrefix problem index.val)
            (canonicalRequest problem index))) =
      encodeWorkConfiguration
        (renameConfiguration appenderState
          (BuilderTokenAppender.finalConfiguration problem.input outsideLeft
            (emittedPrefix problem (index.val + 1)))) := by
  have hRun := run_compile_exact problem.input outsideLeft
    (emittedPrefix problem index.val) (canonicalRequest problem index)
  rw [← canonical_nextOutput problem index]
  simpa [canonicalWorkSteps, finalConfiguration] using hRun

def rawTimeBound {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (.constant 6)
    (BuilderPostDividerSelectedTokenLaunch.appenderRawTimeBound verifier)

theorem rawTimeBound_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (rawTimeBound problem.verifier).eval problem.input.length =
      6 +
        (BuilderPostDividerSelectedTokenLaunch.appenderRawTimeBound
          problem.verifier).eval problem.input.length := by
  rfl

theorem canonicalCompiledSteps_le_rawTimeBound {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    6 * canonicalWorkSteps problem index ≤
      (rawTimeBound problem.verifier).eval problem.input.length := by
  have hAppender :=
    BuilderPostDividerSelectedTokenLaunch.appenderCompiledSteps_le problem
      index.val
  rw [rawTimeBound_eval]
  unfold canonicalWorkSteps canonicalRequest workSteps
  cases hRequest : scheduleEntry problem index with
  | none => simp
  | some token =>
      simp only
      omega

def CanonicalDispatchHolds {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (outsideLeft : List WorkSymbol) : Prop :=
  workRunExact? machine (canonicalWorkSteps problem index)
      (entryConfiguration problem.input outsideLeft
        (emittedPrefix problem index.val) (canonicalRequest problem index)) =
        some
          (renameConfiguration appenderState
            (BuilderTokenAppender.finalConfiguration problem.input outsideLeft
              (emittedPrefix problem (index.val + 1)))) ∧
    run (compileWorkMachine machine) (6 * canonicalWorkSteps problem index)
      (encodeWorkConfiguration
        (entryConfiguration problem.input outsideLeft
          (emittedPrefix problem index.val) (canonicalRequest problem index))) =
        encodeWorkConfiguration
          (renameConfiguration appenderState
            (BuilderTokenAppender.finalConfiguration problem.input outsideLeft
              (emittedPrefix problem (index.val + 1)))) ∧
    machine.isHalted
      (workRun machine (canonicalWorkSteps problem index - 1)
        (entryConfiguration problem.input outsideLeft
          (emittedPrefix problem index.val) (canonicalRequest problem index))) =
        false

theorem canonicalDispatchHolds {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (outsideLeft : List WorkSymbol) :
    CanonicalDispatchHolds problem index outsideLeft := by
  exact ⟨canonical_workRunExact problem index outsideLeft,
    canonical_run_compile_exact problem index outsideLeft,
    one_step_short_not_halted problem.input outsideLeft
      (emittedPrefix problem index.val) (canonicalRequest problem index)⟩

/-- M217 closes the literal request-cell-to-appender boundary for the full
optional-token alphabet and every canonical post-header coordinate.  The
request remains a canonical input to this stage; producing it from the raw
classifier and iterating one physical loop remain open. -/
theorem cook_levin_builder_physical_optional_token_dispatch_checked_complete
    {language : Language} (problem : VerifierTableauProblem language) :
    Function.Injective requestSymbol ∧
    rules.length = 64 ∧
    rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) ∧
    (forall index outsideLeft,
      CanonicalDispatchHolds problem index outsideLeft) ∧
    (forall index,
      6 * canonicalWorkSteps problem index ≤
        (rawTimeBound problem.verifier).eval problem.input.length) ∧
    (forall fuel outsideLeft output,
      workBoundedDecide machine fuel
          (malformedRequestTape problem.input outsideLeft output) =
        .timeout) := by
  exact ⟨requestSymbol_injective, rules_length,
    rules_pairwise_query_distinct, canonicalDispatchHolds problem,
    canonicalCompiledSteps_le_rawTimeBound problem,
    fun fuel outsideLeft output =>
      malformedRequest_timeout fuel problem.input outsideLeft output⟩

end BuilderPhysicalOptionalTokenDispatch

end CookLevin

end PNP.Concrete
