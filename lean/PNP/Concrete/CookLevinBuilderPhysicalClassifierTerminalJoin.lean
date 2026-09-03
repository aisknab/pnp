/-
Copyright (c) 2026 PNP Labs.

One fixed literal wrapper around the complete Cook--Levin post-header
classifier.  The wrapper preserves the body terminal and redirects the unique
Finish terminal through one total symbol-preserving launch table, so every
valid post-header coordinate reaches one common continuation-ready state.

This module normalizes physical control flow only.  It does not synthesize a
body-token request, dispatch a token, connect successive coordinates, build the
complete formula, construct a RawRefinement, or package a polynomial reduction.
-/

import PNP.Concrete.CookLevinBuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch

namespace PNP.Concrete.CookLevin

namespace BuilderPhysicalClassifierTerminalJoin

open PipelineStateNamespace PipelineStageBridges

abbrev classifierMachine : WorkMachine :=
  BuilderPhysicalClassifierPipeline.machine

def sourceState (state : Nat) : Nat := inputState state

def terminalRejectState : Nat := simulationState 0

theorem sourceState_injective : Function.Injective sourceState :=
  inputState_injective

theorem sourceState_ne_terminalRejectState (state : Nat) :
    sourceState state ≠ terminalRejectState :=
  inputState_ne_simulationState state 0

def redirectRules : List WorkRule :=
  launchRules (sourceState classifierMachine.rejectState)
    (sourceState classifierMachine.acceptState)

def rules : List WorkRule :=
  redirectRules ++ classifierMachine.rules.map (renameRule sourceState)

/-- The classifier's accepting body terminal is retained.  Its rejecting
`Finish` terminal is no longer a halt: the total redirect table sends it to
the same accepting state without changing the focused tape. -/
def machine : WorkMachine :=
  { rules := rules
    startState := sourceState classifierMachine.startState
    acceptState := sourceState classifierMachine.acceptState
    rejectState := terminalRejectState }

def QueryDistinct (left right : WorkRule) : Prop :=
  (left.sourceState, left.readSymbol) ≠
    (right.sourceState, right.readSymbol)

private theorem queryDistinct_of_source_ne (left right : WorkRule)
    (hSource : left.sourceState ≠ right.sourceState) :
    QueryDistinct left right := by
  intro hQuery
  exact hSource (congrArg Prod.fst hQuery)

private theorem renameRules_pairwise (encode : Nat -> Nat)
    (hInjective : Function.Injective encode) (localRules : List WorkRule)
    (hPairwise : localRules.Pairwise QueryDistinct) :
    (localRules.map (renameRule encode)).Pairwise QueryDistinct := by
  exact List.Pairwise.map (renameRule encode) (fun left right hDistinct => by
    intro hEqual
    apply hDistinct
    apply Prod.ext
    · exact hInjective (by
        simpa [renameRule] using congrArg Prod.fst hEqual)
    · simpa [renameRule] using congrArg Prod.snd hEqual) hPairwise

private theorem launchRules_pairwise (source target : Nat) :
    (launchRules source target).Pairwise QueryDistinct := by
  unfold launchRules PipelineMachineSimulation.allWorkSymbols
  simp [QueryDistinct, launchRule, WorkSymbol.blank,
    WorkSymbol.blankZero, WorkSymbol.blankOne, WorkSymbol.zeroBlank,
    WorkSymbol.zeroZero, WorkSymbol.zeroOne, WorkSymbol.oneBlank,
    WorkSymbol.oneZero, WorkSymbol.oneOne]

private theorem launchRules_source_eq {source target : Nat}
    {rule : WorkRule} (hMem : rule ∈ launchRules source target) :
    rule.sourceState = source := by
  rcases List.mem_map.mp hMem with ⟨symbol, _hSymbol, hRule⟩
  rw [← hRule]
  rfl

private theorem renamedRules_source {encode : Nat -> Nat}
    {localRules : List WorkRule} {rule : WorkRule}
    (hMem : rule ∈ localRules.map (renameRule encode)) :
    ∃ localRule ∈ localRules,
      rule.sourceState = encode localRule.sourceState := by
  rcases List.mem_map.mp hMem with ⟨localRule, hLocal, hRule⟩
  exact ⟨localRule, hLocal, by rw [← hRule]; rfl⟩

private theorem launchRenamed_cross (source target : Nat)
    (encode : Nat -> Nat) (localRules : List WorkRule)
    (hSource : ∀ localRule ∈ localRules,
      source ≠ encode localRule.sourceState) :
    ∀ bridgeRule ∈ launchRules source target,
      ∀ componentRule ∈ localRules.map (renameRule encode),
        QueryDistinct bridgeRule componentRule := by
  intro bridgeRule hBridge componentRule hComponent
  rcases renamedRules_source hComponent with
    ⟨localRule, hLocal, hComponentSource⟩
  apply queryDistinct_of_source_ne
  rw [launchRules_source_eq hBridge, hComponentSource]
  exact hSource localRule hLocal

set_option maxRecDepth 1000000 in
private theorem classifier_noRuleAtAccept :
    WorkMachineChain.NoRuleAtAccept classifierMachine := by
  intro rule hRule
  change rule.sourceState ≠ classifierMachine.acceptState
  change rule ∈ classifierMachine.rules at hRule
  decide +revert

set_option maxRecDepth 1000000 in
private theorem classifier_noRuleAtReject :
    ∀ rule, rule ∈ classifierMachine.rules →
      rule.sourceState ≠ classifierMachine.rejectState := by
  intro rule hRule
  change rule.sourceState ≠ classifierMachine.rejectState
  change rule ∈ classifierMachine.rules at hRule
  decide +revert

theorem redirectRules_length : redirectRules.length = 9 := by rfl

set_option maxRecDepth 1000000 in
theorem rules_length : rules.length = 720 := by rfl

theorem rules_pairwise_query_distinct :
    rules.Pairwise QueryDistinct := by
  have hRedirect := launchRules_pairwise
    (sourceState classifierMachine.rejectState)
    (sourceState classifierMachine.acceptState)
  have hClassifier := renameRules_pairwise sourceState sourceState_injective
    classifierMachine.rules
    BuilderPhysicalClassifierPipeline.rules_pairwise_query_distinct
  have hCross := launchRenamed_cross
    (sourceState classifierMachine.rejectState)
    (sourceState classifierMachine.acceptState)
    sourceState classifierMachine.rules (by
      intro localRule hLocal hEqual
      exact classifier_noRuleAtReject localRule hLocal
        (sourceState_injective hEqual).symm)
  unfold rules redirectRules
  rw [List.pairwise_append]
  exact ⟨hRedirect, hClassifier, hCross⟩

theorem machine_acceptState_ne_rejectState :
    machine.acceptState ≠ machine.rejectState :=
  sourceState_ne_terminalRejectState classifierMachine.acceptState

theorem noRuleAtAccept : WorkMachineChain.NoRuleAtAccept machine := by
  intro rule hRule
  simp only [machine, rules, List.mem_append] at hRule
  rcases hRule with hRedirect | hClassifier
  · intro hEqual
    have hSource := launchRules_source_eq hRedirect
    rw [hSource] at hEqual
    have hEqual' :
        sourceState classifierMachine.rejectState =
          sourceState classifierMachine.acceptState := by
      simpa [machine] using hEqual
    exact BuilderPhysicalClassifierPipeline.machine_acceptState_ne_rejectState
      (sourceState_injective hEqual').symm
  · rcases renamedRules_source hClassifier with
      ⟨localRule, hLocal, hSource⟩
    intro hEqual
    rw [hSource] at hEqual
    have hEqual' : sourceState localRule.sourceState =
        sourceState classifierMachine.acceptState := by
      simpa [machine] using hEqual
    exact classifier_noRuleAtAccept localRule hLocal
      (sourceState_injective hEqual')

private theorem nat_beq_false_of_ne (left right : Nat)
    (h : left ≠ right) : (left == right) = false := by
  cases hBool : (left == right) with
  | false => rfl
  | true => exact False.elim (h ((nat_beq_true_iff left right).mp hBool))

private theorem state_ne_accept_of_not_halted
    (source : WorkMachine) (configuration : WorkConfiguration)
    (hHalted : source.isHalted configuration = false) :
    configuration.state ≠ source.acceptState := by
  intro hState
  unfold WorkMachine.isHalted at hHalted
  rw [hState, (nat_beq_true_iff _ _).mpr rfl] at hHalted
  contradiction

private theorem state_ne_reject_of_not_halted
    (source : WorkMachine) (configuration : WorkConfiguration)
    (hHalted : source.isHalted configuration = false) :
    configuration.state ≠ source.rejectState := by
  intro hState
  unfold WorkMachine.isHalted at hHalted
  rw [hState, (nat_beq_true_iff _ _).mpr rfl] at hHalted
  simp at hHalted

theorem machine_isHalted_source_false_of_local
    (configuration : WorkConfiguration)
    (hLocal : classifierMachine.isHalted configuration = false) :
    machine.isHalted (renameConfiguration sourceState configuration) = false := by
  have hAccept := state_ne_accept_of_not_halted classifierMachine
    configuration hLocal
  unfold WorkMachine.isHalted machine renameConfiguration
  rw [nat_beq_false_of_ne _ _
      (fun h => hAccept (sourceState_injective h)),
    nat_beq_false_of_ne _ _
      (sourceState_ne_terminalRejectState configuration.state)]
  rfl

theorem findWorkRule_source_of_some (state : Nat) (symbol : WorkSymbol)
    (rule : WorkRule) (hReject : state ≠ classifierMachine.rejectState)
    (hFind : findWorkRule classifierMachine.rules state symbol = some rule) :
    findWorkRule machine.rules (sourceState state) symbol =
      some (renameRule sourceState rule) := by
  have hRedirect : findWorkRule redirectRules (sourceState state) symbol =
      none := by
    apply findWorkRule_launchRules_none_of_source_ne
    intro hEqual
    exact hReject (sourceState_injective hEqual).symm
  have hRenamed := findWorkRule_rename sourceState sourceState_injective
    classifierMachine.rules state symbol
  rw [hFind] at hRenamed
  unfold machine rules
  rw [findWorkRule_append_of_none _ _ _ _ hRedirect]
  exact hRenamed

theorem source_workStep_of_some (configuration next : WorkConfiguration)
    (hStep : workStep? classifierMachine configuration = some next) :
    workStep? machine (renameConfiguration sourceState configuration) =
      some (renameConfiguration sourceState next) := by
  rcases workStep?_some_exists classifierMachine configuration next hStep with
    ⟨rule, hHalted, hFind, hNext⟩
  have hReject := state_ne_reject_of_not_halted classifierMachine
    configuration hHalted
  have hGlobalHalted := machine_isHalted_source_false_of_local
    configuration hHalted
  have hGlobalFind := findWorkRule_source_of_some configuration.state
    configuration.tape.head rule hReject hFind
  have hGlobalStep := workStep?_eq_apply_of_find machine
    (renameConfiguration sourceState configuration)
    (renameRule sourceState rule) hGlobalHalted hGlobalFind
  calc
    workStep? machine (renameConfiguration sourceState configuration) =
        some (applyWorkRule (renameRule sourceState rule)
          (renameConfiguration sourceState configuration)) := hGlobalStep
    _ = some (renameConfiguration sourceState
          (applyWorkRule rule configuration)) :=
      congrArg Option.some
        (applyWorkRule_rename sourceState rule configuration)
    _ = some (renameConfiguration sourceState next) :=
      congrArg (fun value => some (renameConfiguration sourceState value))
        hNext.symm

theorem source_workRunExact (steps : Nat)
    (initial final : WorkConfiguration)
    (hRun : workRunExact? classifierMachine steps initial = some final) :
    workRunExact? machine steps (renameConfiguration sourceState initial) =
      some (renameConfiguration sourceState final) := by
  exact PipelineStageBridges.workRunExact?_transport classifierMachine machine
    sourceState source_workStep_of_some steps initial final hRun

theorem redirect_workStep (tape : WorkTape) :
    workStep? machine
        (renameConfiguration sourceState
          { state := classifierMachine.rejectState, tape := tape }) =
      some (renameConfiguration sourceState
        { state := classifierMachine.acceptState, tape := tape }) := by
  let initial : WorkConfiguration :=
    { state := classifierMachine.rejectState, tape := tape }
  have hAccept : sourceState classifierMachine.rejectState ≠
      sourceState classifierMachine.acceptState := by
    intro hEqual
    exact BuilderPhysicalClassifierPipeline.machine_acceptState_ne_rejectState
      (sourceState_injective hEqual).symm
  have hHalted : machine.isHalted
      (renameConfiguration sourceState initial) = false := by
    unfold WorkMachine.isHalted machine renameConfiguration initial
    rw [nat_beq_false_of_ne _ _ hAccept,
      nat_beq_false_of_ne _ _
        (sourceState_ne_terminalRejectState classifierMachine.rejectState)]
    rfl
  have hRedirect := findWorkRule_launchRules
    (sourceState classifierMachine.rejectState)
    (sourceState classifierMachine.acceptState) tape.head
  have hFind : findWorkRule machine.rules
      (sourceState classifierMachine.rejectState) tape.head =
        some (launchRule
          (sourceState classifierMachine.rejectState)
          (sourceState classifierMachine.acceptState) tape.head) := by
    unfold machine rules redirectRules
    exact findWorkRule_append_of_some _ _ _ _ _ hRedirect
  have hStep := workStep?_eq_apply_of_find machine
    (renameConfiguration sourceState initial)
    (launchRule (sourceState classifierMachine.rejectState)
      (sourceState classifierMachine.acceptState) tape.head) hHalted hFind
  simpa [initial, launchRule, applyWorkRule, WorkTape.write, WorkTape.move,
    renameConfiguration] using hStep

theorem reject_workRunExact (steps : Nat)
    (initial final : WorkConfiguration)
    (hRun : workRunExact? classifierMachine steps initial = some final)
    (hReject : final.state = classifierMachine.rejectState) :
    workRunExact? machine (steps + 1)
        (renameConfiguration sourceState initial) =
      some (renameConfiguration sourceState
        { state := classifierMachine.acceptState, tape := final.tape }) := by
  have hTransport := source_workRunExact steps initial final hRun
  have hFinal : final =
      { state := classifierMachine.rejectState, tape := final.tape } := by
    cases final with
    | mk state tape =>
        simp only at hReject ⊢
        exact congrArg (fun nextState =>
          ({ state := nextState, tape := tape } : WorkConfiguration)) hReject
  have hRedirect : workRunExact? machine 1
      (renameConfiguration sourceState final) =
        some (renameConfiguration sourceState
          { state := classifierMachine.acceptState, tape := final.tape }) := by
    rw [hFinal]
    change
      (match workStep? machine
          (renameConfiguration sourceState
            { state := classifierMachine.rejectState, tape := final.tape }) with
       | none => none
       | some next => workRunExact? machine 0 next) = _
    rw [redirect_workStep]
    rfl
  have hAll := PipelineMachineSimulation.workRunExact?_compose machine
    steps 1 (renameConfiguration sourceState initial)
    (renameConfiguration sourceState final)
    (renameConfiguration sourceState
      { state := classifierMachine.acceptState, tape := final.tape })
    hTransport hRedirect
  simpa using hAll

def entryConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol) : WorkConfiguration :=
  renameConfiguration sourceState
    (BuilderPhysicalClassifierPipeline.entryConfiguration problem index workspace)

def finalConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol) : WorkConfiguration :=
  renameConfiguration sourceState
    { state := classifierMachine.acceptState
      tape := (BuilderPhysicalClassifierPipeline.finalConfiguration
        problem index workspace).tape }

def terminalStepCount {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    Nat :=
  match BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute
      problem index.val with
  | .finish => 1
  | .body _ _ => 0
  | .outOfRange => 0

def workSteps {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    Nat :=
  BuilderPhysicalClassifierPipeline.workSteps problem index +
    terminalStepCount problem index

theorem workRunExact {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol) :
    workRunExact? machine (workSteps problem index)
        (entryConfiguration problem index workspace) =
      some (finalConfiguration problem index workspace) := by
  let classifierFinal := BuilderPhysicalClassifierPipeline.finalConfiguration
    problem index workspace
  have hClassifier := BuilderPhysicalClassifierPipeline.workRunExact
    problem index workspace
  have hRoute := BuilderPhysicalClassifierPipeline.routeAgreement
    problem index workspace
  cases hDecoded : BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute
      problem index.val with
  | body clauseCoordinate tokenCoordinate =>
      have hAccept : classifierFinal.state = classifierMachine.acceptState := by
        simpa only [BuilderPhysicalClassifierPipeline.RouteAgreement,
          hDecoded, classifierFinal, classifierMachine] using hRoute
      have hTransport := source_workRunExact
        (BuilderPhysicalClassifierPipeline.workSteps problem index)
        (BuilderPhysicalClassifierPipeline.entryConfiguration
          problem index workspace)
        classifierFinal hClassifier
      have hFinal : renameConfiguration sourceState classifierFinal =
          finalConfiguration problem index workspace := by
        have hShape : classifierFinal =
            { state := classifierMachine.acceptState
              tape := classifierFinal.tape } := by
          cases hFinalEq : classifierFinal with
          | mk state tape =>
              have hState : state = classifierMachine.acceptState := by
                simpa [hFinalEq] using hAccept
              simp [hState]
        rw [hShape]
        rfl
      rw [hFinal] at hTransport
      simpa [workSteps, terminalStepCount, hDecoded, entryConfiguration] using
        hTransport
  | finish =>
      have hReject : classifierFinal.state = classifierMachine.rejectState := by
        simpa only [BuilderPhysicalClassifierPipeline.RouteAgreement,
          hDecoded, classifierFinal, classifierMachine] using hRoute
      have hJoined := reject_workRunExact
        (BuilderPhysicalClassifierPipeline.workSteps problem index)
        (BuilderPhysicalClassifierPipeline.entryConfiguration
          problem index workspace)
        classifierFinal hClassifier hReject
      simpa [workSteps, terminalStepCount, hDecoded, entryConfiguration,
        finalConfiguration, classifierFinal] using hJoined
  | outOfRange =>
      simp only [BuilderPhysicalClassifierPipeline.RouteAgreement,
        hDecoded] at hRoute

theorem run_compile_exact {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps problem index)
        (encodeWorkConfiguration (entryConfiguration problem index workspace)) =
      encodeWorkConfiguration (finalConfiguration problem index workspace) := by
  exact run_compileWorkMachine_mul_of_workRunExact machine
    (workSteps problem index) (entryConfiguration problem index workspace)
    (finalConfiguration problem index workspace)
    (workRunExact problem index workspace)

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
  | succ steps inductionHypothesis =>
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
          rcases inductionHypothesis next final hTail with
            ⟨before, hPrefix, hLast⟩
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

theorem workSteps_positive {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    0 < workSteps problem index := by
  have hClassifier := BuilderPhysicalClassifierPipeline.workSteps_positive
    problem index
  unfold workSteps
  omega

theorem one_step_short_not_halted {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol) :
    machine.isHalted
      (workRun machine (workSteps problem index - 1)
        (entryConfiguration problem index workspace)) = false := by
  have hPositive := workSteps_positive problem index
  let short := workSteps problem index - 1
  have hStepCount : short + 1 = workSteps problem index := by
    unfold short
    omega
  have hExact := workRunExact problem index workspace
  rw [← hStepCount] at hExact
  rcases workRunExact_succ_split_last machine short
      (entryConfiguration problem index workspace)
      (finalConfiguration problem index workspace) hExact with
    ⟨previous, hPrefix, hLast⟩
  have hRun : workRun machine short
      (entryConfiguration problem index workspace) = previous :=
    workRun_eq_of_workRunExact machine short
      (entryConfiguration problem index workspace) previous hPrefix
  rw [hRun]
  exact isHalted_false_of_workStep_some machine previous
    (finalConfiguration problem index workspace) hLast

def rawTimeBound {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderPhysicalClassifierPipeline.rawTimeBound verifier) (.constant 6)

theorem rawTimeBound_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (rawTimeBound problem.verifier).eval problem.input.length =
      (BuilderPhysicalClassifierPipeline.rawTimeBound
        problem.verifier).eval problem.input.length + 6 := by
  rfl

theorem compiledSteps_le_rawTimeBound {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    6 * workSteps problem index ≤
      (rawTimeBound problem.verifier).eval problem.input.length := by
  have hClassifier :=
    BuilderPhysicalClassifierPipeline.compiledSteps_le_rawTimeBound problem index
  have hTerminal : terminalStepCount problem index ≤ 1 := by
    unfold terminalStepCount
    cases BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute problem index.val <;>
      simp
  rw [rawTimeBound_eval]
  unfold workSteps
  omega

def TerminalJoinHolds {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol) : Prop :=
  BuilderPhysicalClassifierPipeline.RouteAgreement problem index workspace /\
    workRunExact? machine (workSteps problem index)
        (entryConfiguration problem index workspace) =
      some (finalConfiguration problem index workspace) /\
    (finalConfiguration problem index workspace).state = machine.acceptState /\
    run (compileWorkMachine machine) (6 * workSteps problem index)
        (encodeWorkConfiguration (entryConfiguration problem index workspace)) =
      encodeWorkConfiguration (finalConfiguration problem index workspace) /\
    machine.isHalted
      (workRun machine (workSteps problem index - 1)
        (entryConfiguration problem index workspace)) = false /\
    6 * workSteps problem index ≤
      (rawTimeBound problem.verifier).eval problem.input.length

theorem terminalJoinHolds {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol) :
    TerminalJoinHolds problem index workspace := by
  exact ⟨BuilderPhysicalClassifierPipeline.routeAgreement problem index workspace,
    workRunExact problem index workspace, rfl,
    run_compile_exact problem index workspace,
    one_step_short_not_halted problem index workspace,
    compiledSteps_le_rawTimeBound problem index⟩

/-- M226 gives every verifier-derived post-header coordinate one literal
continuation-ready classifier endpoint.  Body coordinates retain M220's
accepting terminal, while the unique `Finish` coordinate takes one of nine
symbol-preserving redirect rules from M220's rejecting terminal to that same
accepting state.  The one fixed 720-rule table works for arbitrary protected
workspace and carries exact work, compiled, one-step-short and source-size
polynomial evidence.  It does not synthesize or dispatch a request, connect
successive coordinates, construct the complete builder `RawRefinement`, or
package the Cook--Levin reduction. -/
theorem cook_levin_builder_physical_classifier_terminal_join_checked_complete
    {language : Language} (problem : VerifierTableauProblem language) :
    redirectRules.length = 9 /\
    rules.length = 720 /\
    rules.Pairwise QueryDistinct /\
    machine.acceptState ≠ machine.rejectState /\
    WorkMachineChain.NoRuleAtAccept machine /\
    (forall index workspace, TerminalJoinHolds problem index workspace) := by
  exact ⟨redirectRules_length, rules_length, rules_pairwise_query_distinct,
    machine_acceptState_ne_rejectState, noRuleAtAccept,
    terminalJoinHolds problem⟩

end BuilderPhysicalClassifierTerminalJoin

end PNP.Concrete.CookLevin
