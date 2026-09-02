/-
Copyright (c) 2026 PNP Labs.

The full physical classifier's unique Finish path, continued through a
spatially reflected copy of the fixed optional-token dispatcher.

M222 reaches exactly the mirror of M217's canonical Finish-request entry.
This module defines the syntactic reflection of a finite work machine, proves
that reflection transports every exact execution, and uses it to append the
final token after the complete classifier and workspace-orientation pass.  The
result is one fixed literal machine whose final output is the complete
canonical CNF token stream.

This is still only the unique Finish path.  It does not derive body-token or
padding requests, connect every classifier outcome to the dispatcher, iterate
one physical schedule loop, prove builder `RawRefinement`, or package the
Cook--Levin reduction.
-/

import PNP.Concrete.CookLevinBuilderPhysicalClassifierFinishWorkspaceOrientation

namespace PNP.Concrete.CookLevin

namespace BuilderPhysicalClassifierFinishMirroredDispatch

open PipelineStateNamespace


/-! ## Generic spatial reflection for literal work machines -/

def mirrorMove : HeadMove -> HeadMove
  | .left => .right
  | .stay => .stay
  | .right => .left

def mirrorTape : WorkTape -> WorkTape := BuilderPhysicalClassifierFinishWorkspaceOrientation.mirrorTape

def mirrorRule (rule : WorkRule) : WorkRule :=
  { rule with move := mirrorMove rule.move }

def mirrorConfiguration (configuration : WorkConfiguration) :
    WorkConfiguration :=
  { state := configuration.state
    tape := mirrorTape configuration.tape }

def mirrorMachine (source : WorkMachine) : WorkMachine :=
  { rules := source.rules.map mirrorRule
    startState := source.startState
    acceptState := source.acceptState
    rejectState := source.rejectState }

private theorem workConfiguration_ext {left right : WorkConfiguration}
    (hState : left.state = right.state)
    (hTape : left.tape = right.tape) : left = right := by
  cases left
  cases right
  simp_all

@[simp] theorem mirrorMove_mirrorMove (move : HeadMove) :
    mirrorMove (mirrorMove move) = move := by
  cases move <;> rfl

@[simp] theorem mirrorTape_mirrorTape (tape : WorkTape) :
    mirrorTape (mirrorTape tape) = tape := by
  cases tape
  rfl

@[simp] theorem mirrorTape_write (tape : WorkTape) (symbol : WorkSymbol) :
    mirrorTape (tape.write symbol) = (mirrorTape tape).write symbol := by
  cases tape
  rfl

@[simp] theorem mirrorTape_moveLeft (tape : WorkTape) :
    mirrorTape tape.moveLeft = (mirrorTape tape).moveRight := by
  rcases tape with ⟨left, head, right⟩
  cases left <;> rfl

@[simp] theorem mirrorTape_moveRight (tape : WorkTape) :
    mirrorTape tape.moveRight = (mirrorTape tape).moveLeft := by
  rcases tape with ⟨left, head, right⟩
  cases right <;> rfl

@[simp] theorem mirrorTape_move (tape : WorkTape) (move : HeadMove) :
    mirrorTape (tape.move move) =
      (mirrorTape tape).move (mirrorMove move) := by
  cases move <;> simp [mirrorMove, WorkTape.move]

@[simp] theorem mirrorRule_mirrorRule (rule : WorkRule) :
    mirrorRule (mirrorRule rule) = rule := by
  cases rule
  simp [mirrorRule]

@[simp] theorem mirrorConfiguration_mirrorConfiguration
    (configuration : WorkConfiguration) :
    mirrorConfiguration (mirrorConfiguration configuration) =
      configuration := by
  cases configuration
  simp [mirrorConfiguration]

theorem findWorkRule_mirrorRules (rules : List WorkRule)
    (state : Nat) (symbol : WorkSymbol) :
    findWorkRule (rules.map mirrorRule) state symbol =
      (findWorkRule rules state symbol).map mirrorRule := by
  induction rules with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.map_cons]
      by_cases hMatch :
          first.sourceState = state /\ first.readSymbol = symbol
      · have hMirror :
            (mirrorRule first).sourceState = state /\
              (mirrorRule first).readSymbol = symbol := by
          simpa [mirrorRule] using hMatch
        rw [findWorkRule_cons_of_matches first rest state symbol hMatch,
          findWorkRule_cons_of_matches (mirrorRule first)
            (rest.map mirrorRule) state symbol hMirror]
        rfl
      · have hMirror :
            ¬((mirrorRule first).sourceState = state /\
              (mirrorRule first).readSymbol = symbol) := by
          intro h
          exact hMatch (by simpa [mirrorRule] using h)
        rw [findWorkRule_cons_of_not_matches first rest state symbol hMatch,
          findWorkRule_cons_of_not_matches (mirrorRule first)
            (rest.map mirrorRule) state symbol hMirror]
        exact ih

@[simp] theorem mirrorMachine_isHalted (source : WorkMachine)
    (configuration : WorkConfiguration) :
    (mirrorMachine source).isHalted
        (mirrorConfiguration configuration) =
      source.isHalted configuration := by
  rfl

@[simp] theorem applyWorkRule_mirror (rule : WorkRule)
    (configuration : WorkConfiguration) :
    applyWorkRule (mirrorRule rule) (mirrorConfiguration configuration) =
      mirrorConfiguration (applyWorkRule rule configuration) := by
  rcases rule with ⟨sourceState, readSymbol, targetState, writeSymbol, move⟩
  cases move <;>
    simp [applyWorkRule, mirrorRule, mirrorConfiguration, mirrorMove]

theorem workStep?_mirror (source : WorkMachine)
    (configuration : WorkConfiguration) :
    workStep? (mirrorMachine source) (mirrorConfiguration configuration) =
      (workStep? source configuration).map mirrorConfiguration := by
  cases hHalted : source.isHalted configuration with
  | true =>
      simp [workStep?, hHalted, mirrorMachine_isHalted]
  | false =>
      simp only [workStep?, mirrorMachine_isHalted, hHalted,
        Bool.false_eq_true, if_false]
      change
        (match findWorkRule (source.rules.map mirrorRule)
            configuration.state configuration.tape.head with
        | none => none
        | some rule =>
            some (applyWorkRule rule (mirrorConfiguration configuration))) =
          (match findWorkRule source.rules configuration.state
              configuration.tape.head with
          | none => none
          | some rule => some (applyWorkRule rule configuration)).map
            mirrorConfiguration
      rw [findWorkRule_mirrorRules]
      cases hFind : findWorkRule source.rules configuration.state
          configuration.tape.head with
      | none => simp
      | some rule =>
          simp [applyWorkRule_mirror]

theorem workRunExact?_mirror (source : WorkMachine) :
    forall (steps : Nat) (initial : WorkConfiguration),
      workRunExact? (mirrorMachine source) steps
          (mirrorConfiguration initial) =
        (workRunExact? source steps initial).map mirrorConfiguration := by
  intro steps
  induction steps with
  | zero =>
      intro initial
      rfl
  | succ steps ih =>
      intro initial
      simp only [workRunExact?]
      rw [workStep?_mirror]
      cases hStep : workStep? source initial with
      | none => simp
      | some next =>
          simp only [Option.map_some]
          exact ih next

theorem workRunExact?_mirror_of_some (source : WorkMachine)
    (steps : Nat) (initial final : WorkConfiguration)
    (hRun : workRunExact? source steps initial = some final) :
    workRunExact? (mirrorMachine source) steps
        (mirrorConfiguration initial) =
      some (mirrorConfiguration final) := by
  rw [workRunExact?_mirror, hRun]
  rfl

theorem mirrorRules_pairwise_query_distinct (source : WorkMachine)
    (hPairwise : source.rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol))) :
    (mirrorMachine source).rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  exact List.Pairwise.map mirrorRule (fun left right hDistinct => by
    intro hEqual
    apply hDistinct
    apply Prod.ext
    · simpa [mirrorRule] using congrArg Prod.fst hEqual
    · simpa [mirrorRule] using congrArg Prod.snd hEqual) hPairwise

theorem mirrorMachine_acceptState_ne_rejectState (source : WorkMachine)
    (hDistinct : source.acceptState ≠ source.rejectState) :
    (mirrorMachine source).acceptState ≠
      (mirrorMachine source).rejectState := by
  exact hDistinct

/-! ## Reflected M217 Finish dispatcher -/

abbrev sourceDispatchMachine : WorkMachine := BuilderPhysicalOptionalTokenDispatch.machine

def dispatchMachine : WorkMachine := mirrorMachine sourceDispatchMachine

def dispatchEntryConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  mirrorConfiguration
    (BuilderPhysicalOptionalTokenDispatch.entryConfiguration problem.input
      (BuilderPhysicalClassifierFinishWorkspaceOrientation.dispatchOutsideLeft problem) (BuilderPhysicalClassifierFinishWorkspaceOrientation.output problem)
      (some .finish))

def dispatchFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  mirrorConfiguration
    (renameConfiguration BuilderPhysicalOptionalTokenDispatch.appenderState
      (BuilderTokenAppender.finalConfiguration problem.input
        (BuilderPhysicalClassifierFinishWorkspaceOrientation.dispatchOutsideLeft problem)
        (encodeCNFTokens problem.formula)))

def dispatchWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderPhysicalOptionalTokenDispatch.canonicalWorkSteps problem (BuilderPhysicalClassifierFinishWorkspaceOrientation.finishIndex problem)

theorem finishIndex_succ_eq_bodySlotCount {language : Language}
    (problem : VerifierTableauProblem language) :
    (BuilderPhysicalClassifierFinishWorkspaceOrientation.finishIndex problem).val + 1 =
      BuilderFullScheduleCursorController.bodySlotCount problem := by
  simp [BuilderPhysicalClassifierFinishWorkspaceOrientation.finishIndex,
    BuilderPhysicalClassifierFinishRequest.finishIndex,
    BuilderPhysicalFinishRequest.finishIndex,
    BuilderFullScheduleCursorController.bodySlotCount_eq]

theorem dispatch_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? dispatchMachine (dispatchWorkSteps problem)
        (dispatchEntryConfiguration problem) =
      some (dispatchFinalConfiguration problem) := by
  have hRun := BuilderPhysicalOptionalTokenDispatch.canonical_workRunExact problem
    (BuilderPhysicalClassifierFinishWorkspaceOrientation.finishIndex problem) (BuilderPhysicalClassifierFinishWorkspaceOrientation.dispatchOutsideLeft problem)
  have hRequest :
      BuilderPhysicalOptionalTokenDispatch.canonicalRequest problem
          (BuilderPhysicalClassifierFinishWorkspaceOrientation.finishIndex problem) =
        some .finish :=
    BuilderPhysicalClassifierFinishRequest.finishIndex_scheduleEntry problem
  rw [hRequest] at hRun
  rw [finishIndex_succ_eq_bodySlotCount problem,
    BuilderCompleteScheduleIteration.emittedPrefix_bodySlotCount_eq_encodeCNFTokens] at hRun
  exact workRunExact?_mirror_of_some sourceDispatchMachine
    (dispatchWorkSteps problem)
    (BuilderPhysicalOptionalTokenDispatch.entryConfiguration problem.input
      (BuilderPhysicalClassifierFinishWorkspaceOrientation.dispatchOutsideLeft problem) (BuilderPhysicalClassifierFinishWorkspaceOrientation.output problem)
      (some .finish))
    (renameConfiguration BuilderPhysicalOptionalTokenDispatch.appenderState
      (BuilderTokenAppender.finalConfiguration problem.input
        (BuilderPhysicalClassifierFinishWorkspaceOrientation.dispatchOutsideLeft problem)
        (encodeCNFTokens problem.formula))) (by
      simpa [dispatchWorkSteps,
        BuilderPhysicalClassifierFinishWorkspaceOrientation.output] using hRun)

theorem dispatch_run_compile_exact {language : Language}
    (problem : VerifierTableauProblem language) :
    run (compileWorkMachine dispatchMachine) (6 * dispatchWorkSteps problem)
        (encodeWorkConfiguration (dispatchEntryConfiguration problem)) =
      encodeWorkConfiguration (dispatchFinalConfiguration problem) := by
  exact run_compileWorkMachine_mul_of_workRunExact dispatchMachine
    (dispatchWorkSteps problem) (dispatchEntryConfiguration problem)
    (dispatchFinalConfiguration problem) (dispatch_workRunExact problem)

theorem dispatchRules_length : dispatchMachine.rules.length = 64 := by
  rfl

theorem dispatchRules_pairwise_query_distinct :
    dispatchMachine.rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  exact mirrorRules_pairwise_query_distinct sourceDispatchMachine
    BuilderPhysicalOptionalTokenDispatch.rules_pairwise_query_distinct

theorem dispatchMachine_acceptState_ne_rejectState :
    dispatchMachine.acceptState ≠ dispatchMachine.rejectState := by
  exact mirrorMachine_acceptState_ne_rejectState sourceDispatchMachine
    BuilderPhysicalOptionalTokenDispatch.machine_acceptState_ne_rejectState

theorem classifierFinal_tape_eq_dispatchEntry {language : Language}
    (problem : VerifierTableauProblem language) :
    (BuilderPhysicalClassifierFinishWorkspaceOrientation.composedFinalConfiguration problem).tape =
      (dispatchEntryConfiguration problem).tape := by
  exact BuilderPhysicalClassifierFinishWorkspaceOrientation.composedFinal_tape_eq_mirrored_dispatch_entry problem

/-! ## Full classifier/orienter/reflected-dispatcher composition -/

abbrev classifierMachine : WorkMachine := BuilderPhysicalClassifierFinishWorkspaceOrientation.composedMachine

def machine : WorkMachine :=
  WorkMachineChain.machine classifierMachine dispatchMachine

def entryConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.firstState
    (BuilderPhysicalClassifierFinishWorkspaceOrientation.composedEntryConfiguration problem)

def finalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.secondState
    (dispatchFinalConfiguration problem)

def workSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderPhysicalClassifierFinishWorkspaceOrientation.composedWorkSteps problem + 1 + dispatchWorkSteps problem

theorem workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? machine (workSteps problem) (entryConfiguration problem) =
      some (finalConfiguration problem) := by
  have hFirst := BuilderPhysicalClassifierFinishWorkspaceOrientation.composed_workRunExact problem
  have hEntry :
      ({ state := dispatchMachine.startState
         tape := (BuilderPhysicalClassifierFinishWorkspaceOrientation.composedFinalConfiguration problem).tape } :
        WorkConfiguration) = dispatchEntryConfiguration problem := by
    apply workConfiguration_ext
    · rfl
    · exact classifierFinal_tape_eq_dispatchEntry problem
  have hSecond : workRunExact? dispatchMachine
      (dispatchWorkSteps problem)
      { state := dispatchMachine.startState
        tape := (BuilderPhysicalClassifierFinishWorkspaceOrientation.composedFinalConfiguration problem).tape } =
      some (dispatchFinalConfiguration problem) := by
    rw [hEntry]
    exact dispatch_workRunExact problem
  have hAll := WorkMachineChain.workRunExact classifierMachine dispatchMachine
    (BuilderPhysicalClassifierFinishWorkspaceOrientation.composedWorkSteps problem) (dispatchWorkSteps problem)
    (BuilderPhysicalClassifierFinishWorkspaceOrientation.composedEntryConfiguration problem)
    (BuilderPhysicalClassifierFinishWorkspaceOrientation.composedFinalConfiguration problem)
    (dispatchFinalConfiguration problem) hFirst rfl hSecond
  simpa [machine, workSteps, entryConfiguration, finalConfiguration] using hAll

set_option maxRecDepth 1000000 in
theorem rules_length : machine.rules.length = 813 := by
  rfl

private theorem orient_noRuleAtAccept :
    WorkMachineChain.NoRuleAtAccept BuilderPhysicalClassifierFinishWorkspaceOrientation.orientMachine := by
  intro rule hRule
  change rule ∈ BuilderPhysicalClassifierFinishWorkspaceOrientation.orientMachine.rules at hRule
  change rule.sourceState ≠ BuilderPhysicalClassifierFinishWorkspaceOrientation.orientMachine.acceptState
  decide +revert

private theorem classifier_noRuleAtAccept :
    WorkMachineChain.NoRuleAtAccept classifierMachine := by
  exact WorkMachineChain.noRuleAtAccept BuilderPhysicalClassifierFinishWorkspaceOrientation.classifierWriterMachine
    BuilderPhysicalClassifierFinishWorkspaceOrientation.orientMachine orient_noRuleAtAccept

theorem rules_pairwise_query_distinct :
    machine.rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  exact WorkMachineChain.rules_pairwise_query_distinct classifierMachine
    dispatchMachine BuilderPhysicalClassifierFinishWorkspaceOrientation.composedRules_pairwise_query_distinct
    dispatchRules_pairwise_query_distinct classifier_noRuleAtAccept

theorem machine_acceptState_ne_rejectState :
    machine.acceptState ≠ machine.rejectState := by
  exact WorkMachineChain.machine_acceptState_ne_rejectState classifierMachine
    dispatchMachine dispatchMachine_acceptState_ne_rejectState

theorem run_compile_exact {language : Language}
    (problem : VerifierTableauProblem language) :
    run (compileWorkMachine machine) (6 * workSteps problem)
        (encodeWorkConfiguration (entryConfiguration problem)) =
      encodeWorkConfiguration (finalConfiguration problem) := by
  exact run_compileWorkMachine_mul_of_workRunExact machine
    (workSteps problem) (entryConfiguration problem)
    (finalConfiguration problem) (workRunExact problem)

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

theorem workSteps_positive {language : Language}
    (problem : VerifierTableauProblem language) :
    0 < workSteps problem := by
  unfold workSteps
  omega

theorem one_step_short_not_halted {language : Language}
    (problem : VerifierTableauProblem language) :
    machine.isHalted
      (workRun machine (workSteps problem - 1) (entryConfiguration problem)) =
        false := by
  let short := workSteps problem - 1
  have hSucc : short + 1 = workSteps problem := by
    have hPositive := workSteps_positive problem
    dsimp [short]
    omega
  have hExact := workRunExact problem
  rw [← hSucc] at hExact
  rcases workRunExact_succ_split_last machine short
      (entryConfiguration problem) (finalConfiguration problem) hExact with
    ⟨before, hPrefix, hLast⟩
  have hRun : workRun machine short (entryConfiguration problem) = before :=
    workRun_eq_of_workRunExact machine short (entryConfiguration problem)
      before hPrefix
  rw [hRun]
  exact isHalted_false_of_workStep_some machine before
    (finalConfiguration problem) hLast

/-! ## Uniform polynomial bound -/

def rawTimeBound {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderPhysicalClassifierFinishWorkspaceOrientation.rawTimeBound verifier)
    (.add (.constant 6) (BuilderPhysicalOptionalTokenDispatch.rawTimeBound verifier))

theorem rawTimeBound_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (rawTimeBound problem.verifier).eval problem.input.length =
      (BuilderPhysicalClassifierFinishWorkspaceOrientation.rawTimeBound problem.verifier).eval problem.input.length +
        (6 + (BuilderPhysicalOptionalTokenDispatch.rawTimeBound problem.verifier).eval
          problem.input.length) := by
  rfl

theorem compiledSteps_le_rawTimeBound {language : Language}
    (problem : VerifierTableauProblem language) :
    6 * workSteps problem ≤
      (rawTimeBound problem.verifier).eval problem.input.length := by
  have hClassifier := BuilderPhysicalClassifierFinishWorkspaceOrientation.composedCompiledSteps_le_rawTimeBound problem
  have hDispatch := BuilderPhysicalOptionalTokenDispatch.canonicalCompiledSteps_le_rawTimeBound problem
    (BuilderPhysicalClassifierFinishWorkspaceOrientation.finishIndex problem)
  rw [rawTimeBound_eval]
  unfold workSteps dispatchWorkSteps
  omega

def FinishMirroredDispatchHolds {language : Language}
    (problem : VerifierTableauProblem language) : Prop :=
  BuilderPhysicalClassifierFinishWorkspaceOrientation.FinishWorkspaceOrientationHolds problem /\
    workRunExact? dispatchMachine (dispatchWorkSteps problem)
      (dispatchEntryConfiguration problem) =
        some (dispatchFinalConfiguration problem) /\
    workRunExact? machine (workSteps problem) (entryConfiguration problem) =
      some (finalConfiguration problem) /\
    run (compileWorkMachine machine) (6 * workSteps problem)
      (encodeWorkConfiguration (entryConfiguration problem)) =
        encodeWorkConfiguration (finalConfiguration problem) /\
    machine.isHalted
      (workRun machine (workSteps problem - 1) (entryConfiguration problem)) =
        false /\
    6 * workSteps problem ≤
      (rawTimeBound problem.verifier).eval problem.input.length

theorem finishMirroredDispatchHolds {language : Language}
    (problem : VerifierTableauProblem language) :
    FinishMirroredDispatchHolds problem := by
  exact ⟨BuilderPhysicalClassifierFinishWorkspaceOrientation.finishWorkspaceOrientationHolds problem,
    dispatch_workRunExact problem, workRunExact problem,
    run_compile_exact problem, one_step_short_not_halted problem,
    compiledSteps_le_rawTimeBound problem⟩

/-- M223 executes the full M220--M222 classifier's unique Finish path through
the spatial reflection of M217's fixed dispatcher.  One collision-free
813-rule machine has an exact work trace, exact compiled trace, one-step-short
nonhalting witness, and uniform polynomial bound, and its reflected appender
endpoint contains the complete canonical CNF token encoding.  It does not
derive body-token or padding requests, connect all classifier outcomes,
iterate the physical schedule, prove builder `RawRefinement`, or package the
Cook--Levin reduction. -/
theorem cook_levin_builder_physical_classifier_finish_mirrored_dispatch_checked_complete
    {language : Language} (problem : VerifierTableauProblem language) :
    (forall tape, mirrorTape (mirrorTape tape) = tape) /\
    dispatchMachine.rules.length = 64 /\
    machine.rules.length = 813 /\
    machine.rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) /\
    machine.acceptState ≠ machine.rejectState /\
    FinishMirroredDispatchHolds problem := by
  exact ⟨mirrorTape_mirrorTape, dispatchRules_length, rules_length,
    rules_pairwise_query_distinct, machine_acceptState_ne_rejectState,
    finishMirroredDispatchHolds problem⟩

end BuilderPhysicalClassifierFinishMirroredDispatch

end PNP.Concrete.CookLevin
