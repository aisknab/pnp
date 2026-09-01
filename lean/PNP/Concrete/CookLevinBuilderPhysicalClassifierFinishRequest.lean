/-
Copyright (c) 2026 PNP Labs.

A fixed literal Finish-request writer after the complete M220 physical
classifier pipeline.

At the unique canonical Finish coordinate, the M220 classifier's rejecting
terminal is reinterpreted as the accepting entry to a one-rule writer.  The
writer changes only the focused end marker into M217's tape-resident Finish
request and preserves every protected workspace cell.  Body-token and padding
request generation, dispatcher-ready workspace orientation, a repeated
physical loop, builder RawRefinement, and the packaged Cook--Levin reduction
remain open.
-/

import PNP.Concrete.CookLevinBuilderPhysicalClassifierPipeline

namespace PNP.Concrete

namespace CookLevin

namespace BuilderPhysicalClassifierFinishRequest

open PipelineStateNamespace
open BuilderPostDividerSelectedTokenLaunch

abbrev classifierMachine : WorkMachine :=
  BuilderPhysicalClassifierPipeline.machine

abbrev writerMachine : WorkMachine :=
  BuilderPhysicalFinishRequest.writerMachine

abbrev endSymbol : WorkSymbol :=
  BuilderPhysicalFinishRequest.endSymbol

def finishIndex {language : Language}
    (problem : VerifierTableauProblem language) :
    Fin (BuilderFullScheduleCursorController.bodySlotCount problem) :=
  BuilderPhysicalFinishRequest.finishIndex problem

theorem finishIndex_scheduleEntry {language : Language}
    (problem : VerifierTableauProblem language) :
    scheduleEntry problem (finishIndex problem) = some .finish := by
  exact BuilderPhysicalFinishRequest.finishIndex_scheduleEntry problem

/-! ## Finish-selecting classifier and one-cell writer -/

/-- M220 uses its rejecting terminal for the unique Finish route.  Swapping
the two verdict names leaves the rule table and operational semantics
unchanged while making that route composable with the writer. -/
def finishClassifierMachine : WorkMachine :=
  { classifierMachine with
    acceptState := classifierMachine.rejectState
    rejectState := classifierMachine.acceptState }

theorem finishClassifierMachine_isHalted
    (configuration : WorkConfiguration) :
    finishClassifierMachine.isHalted configuration =
      classifierMachine.isHalted configuration := by
  simp [finishClassifierMachine, WorkMachine.isHalted, Bool.or_comm]

theorem finishClassifierMachine_workStep
    (configuration : WorkConfiguration) :
    workStep? finishClassifierMachine configuration =
      workStep? classifierMachine configuration := by
  unfold workStep?
  rw [finishClassifierMachine_isHalted]
  rfl

theorem finishClassifierMachine_workRunExact (steps : Nat)
    (configuration : WorkConfiguration) :
    workRunExact? finishClassifierMachine steps configuration =
      workRunExact? classifierMachine steps configuration := by
  induction steps generalizing configuration with
  | zero => rfl
  | succ steps ih =>
      simp only [workRunExact?]
      rw [finishClassifierMachine_workStep]
      cases hStep : workStep? classifierMachine configuration with
      | none => rfl
      | some next => exact ih next

def classifierEntryConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  BuilderPhysicalClassifierPipeline.entryConfiguration problem
    (finishIndex problem) workspace

def classifierFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  BuilderPhysicalClassifierPipeline.finalConfiguration problem
    (finishIndex problem) workspace

theorem classifierFinal_state {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) :
    (classifierFinalConfiguration problem workspace).state =
      finishClassifierMachine.acceptState := by
  have hRoute := BuilderPhysicalClassifierPipeline.routeAgreement problem
    (finishIndex problem) workspace
  unfold BuilderPhysicalClassifierPipeline.RouteAgreement at hRoute
  unfold finishIndex at hRoute
  rw [BuilderPhysicalFinishRequest.finishIndex_postHeaderRoute problem] at hRoute
  simpa [classifierFinalConfiguration, finishClassifierMachine, finishIndex] using hRoute

theorem classifierFinal_head {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) :
    (classifierFinalConfiguration problem workspace).tape.head = endSymbol := by
  have hWidth := BuilderPostHeaderRawLaunch.formulaTokensPerClause_pos problem
  have hFinish := BuilderPhysicalFinishRequest.finishIndex_postHeaderRoute problem
  have hIndex :=
    (BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute_eq_finish_iff
      problem (finishIndex problem).val).1 hFinish
  have hQuotient :
      (finishIndex problem).val /
          BuilderPhysicalClassifierPipeline.width problem =
        BuilderPhysicalClassifierPipeline.clauseCount problem := by
    rw [hIndex]
    simpa [BuilderPhysicalClassifierPipeline.width,
      BuilderPhysicalClassifierPipeline.clauseCount, Nat.mul_comm] using
        (Nat.mul_div_right problem.formulaClauseSlotCount hWidth)
  cases hValue : (finishIndex problem).val with
  | zero =>
      have hCount :
          BuilderPhysicalClassifierPipeline.clauseCount problem = 0 := by
        simpa [hValue] using hQuotient.symm
      simp [classifierFinalConfiguration,
        BuilderPhysicalClassifierPipeline.finalConfiguration, hValue,
        BuilderPhysicalClassifierPipeline.equalFinalConfiguration,
        BuilderPhysicalClassifierPipeline.equalComparatorFinalConfiguration,
        BuilderPostDividerRawRouteClassifier.shieldedComparatorFinalConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorTape,
        BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration,
        BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration,
        BuilderPostDividerRawRouteClassifier.compareResult_self, hCount,
        endSymbol, BuilderPhysicalFinishRequest.endSymbol,
        BuilderPostDividerRawRouteClassifier.endSymbol,
        BuilderArbitrarySlotHeaderRouter.RawRouter.endSymbol,
        renameConfiguration]
  | succ remaining =>
      have hGreaterQuotient :
          BuilderPhysicalClassifierPipeline.greaterQuotient problem remaining =
            BuilderPhysicalClassifierPipeline.clauseCount problem := by
        unfold BuilderPhysicalClassifierPipeline.greaterQuotient
        rw [← hValue]
        exact hQuotient
      simp [classifierFinalConfiguration,
        BuilderPhysicalClassifierPipeline.finalConfiguration, hValue,
        BuilderPhysicalClassifierPipeline.greaterFinalConfiguration,
        BuilderPhysicalClassifierPipeline.greaterComparatorFinalConfiguration,
        BuilderPostDividerRawRouteClassifier.shieldedComparatorFinalConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorTape,
        BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration,
        BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration,
        BuilderPostDividerRawRouteClassifier.compareResult_self,
        hGreaterQuotient, endSymbol,
        BuilderPhysicalFinishRequest.endSymbol,
        BuilderPostDividerRawRouteClassifier.endSymbol,
        BuilderArbitrarySlotHeaderRouter.RawRouter.endSymbol,
        renameConfiguration]

theorem classifier_workRunExact {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) :
    workRunExact? finishClassifierMachine
        (BuilderPhysicalClassifierPipeline.workSteps problem
          (finishIndex problem))
        (classifierEntryConfiguration problem workspace) =
      some (classifierFinalConfiguration problem workspace) := by
  rw [finishClassifierMachine_workRunExact]
  exact BuilderPhysicalClassifierPipeline.workRunExact problem
    (finishIndex problem) workspace

def writerFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  BuilderPhysicalFinishRequest.writerFinalConfiguration
    (classifierFinalConfiguration problem workspace).tape

theorem writer_workRunExact {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) :
    workRunExact? writerMachine 1
        (BuilderPhysicalFinishRequest.writerInputConfiguration
          (classifierFinalConfiguration problem workspace).tape) =
      some (writerFinalConfiguration problem workspace) := by
  exact BuilderPhysicalFinishRequest.writer_workRunExact
    (classifierFinalConfiguration problem workspace).tape
    (classifierFinal_head problem workspace)

theorem writerFinal_tape_exact {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) :
    (writerFinalConfiguration problem workspace).tape =
      (classifierFinalConfiguration problem workspace).tape.write
        (BuilderPhysicalOptionalTokenDispatch.requestSymbol (some .finish)) := by
  rfl

theorem writerFinal_request {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) :
    (writerFinalConfiguration problem workspace).tape.head =
      BuilderPhysicalOptionalTokenDispatch.requestSymbol (some .finish) := by
  rfl

/-! ## One fixed composed machine -/

def machine : WorkMachine :=
  WorkMachineChain.machine finishClassifierMachine writerMachine

set_option maxRecDepth 1000000 in
theorem rules_length : machine.rules.length = 721 := by
  rfl

set_option maxRecDepth 1000000 in
private theorem finishClassifier_noRuleAtAccept :
    WorkMachineChain.NoRuleAtAccept finishClassifierMachine := by
  intro rule hRule
  change rule.sourceState ≠ classifierMachine.rejectState
  change rule ∈ classifierMachine.rules at hRule
  decide +revert

private theorem writer_rules_pairwise_query_distinct :
    writerMachine.rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  decide

theorem rules_pairwise_query_distinct :
    machine.rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  have hClassifier :
      finishClassifierMachine.rules.Pairwise WorkMachineChain.QueryDistinct := by
    change classifierMachine.rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol))
    exact BuilderPhysicalClassifierPipeline.rules_pairwise_query_distinct
  exact WorkMachineChain.rules_pairwise_query_distinct
    finishClassifierMachine writerMachine
    hClassifier
    writer_rules_pairwise_query_distinct
    finishClassifier_noRuleAtAccept

theorem machine_acceptState_ne_rejectState :
    machine.acceptState ≠ machine.rejectState := by
  decide

def entryConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.firstState
    (classifierEntryConfiguration problem workspace)

def finalConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.secondState
    (writerFinalConfiguration problem workspace)

def workSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderPhysicalClassifierPipeline.workSteps problem (finishIndex problem) + 2

theorem workRunExact {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) :
    workRunExact? machine (workSteps problem)
        (entryConfiguration problem workspace) =
      some (finalConfiguration problem workspace) := by
  let classifierInitial := classifierEntryConfiguration problem workspace
  let classifierFinal := classifierFinalConfiguration problem workspace
  let writerFinal := writerFinalConfiguration problem workspace
  have hClassifier : workRunExact? finishClassifierMachine
      (BuilderPhysicalClassifierPipeline.workSteps problem
        (finishIndex problem)) classifierInitial = some classifierFinal := by
    simpa [classifierInitial, classifierFinal] using
      classifier_workRunExact problem workspace
  have hClassifierAccept :
      classifierFinal.state = finishClassifierMachine.acceptState := by
    simpa [classifierFinal] using classifierFinal_state problem workspace
  have hWriter : workRunExact? writerMachine 1
      { state := writerMachine.startState, tape := classifierFinal.tape } =
        some writerFinal := by
    simpa [classifierFinal, writerFinal,
      BuilderPhysicalFinishRequest.writerInputConfiguration] using
        writer_workRunExact problem workspace
  have hAll := WorkMachineChain.workRunExact finishClassifierMachine
    writerMachine
    (BuilderPhysicalClassifierPipeline.workSteps problem (finishIndex problem))
    1 classifierInitial classifierFinal writerFinal hClassifier
    hClassifierAccept hWriter
  simpa [machine, workSteps, entryConfiguration, finalConfiguration,
    classifierInitial, classifierFinal, writerFinal, Nat.add_assoc] using hAll

theorem run_compile_exact {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps problem)
        (encodeWorkConfiguration (entryConfiguration problem workspace)) =
      encodeWorkConfiguration (finalConfiguration problem workspace) := by
  exact run_compileWorkMachine_mul_of_workRunExact machine
    (workSteps problem) (entryConfiguration problem workspace)
    (finalConfiguration problem workspace) (workRunExact problem workspace)

theorem final_request_exact {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) :
    (finalConfiguration problem workspace).tape =
      (classifierFinalConfiguration problem workspace).tape.write
        (BuilderPhysicalOptionalTokenDispatch.requestSymbol (some .finish)) := by
  exact writerFinal_tape_exact problem workspace

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
               | some result => workRunExact? selectedMachine (steps + 1) result) =
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
    (problem : VerifierTableauProblem language) : 0 < workSteps problem := by
  unfold workSteps
  omega

theorem one_step_short_not_halted {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) :
    machine.isHalted
      (workRun machine (workSteps problem - 1)
        (entryConfiguration problem workspace)) = false := by
  have hPositive := workSteps_positive problem
  let short := workSteps problem - 1
  have hSucc : short + 1 = workSteps problem := by
    dsimp [short]
    omega
  have hExact := workRunExact problem workspace
  rw [← hSucc] at hExact
  rcases workRunExact_succ_split_last machine short
      (entryConfiguration problem workspace)
      (finalConfiguration problem workspace) hExact with
    ⟨before, hPrefix, hLast⟩
  have hRun : workRun machine short
      (entryConfiguration problem workspace) = before :=
    workRun_eq_of_workRunExact machine short
      (entryConfiguration problem workspace) before hPrefix
  rw [hRun]
  exact isHalted_false_of_workStep_some machine before
    (finalConfiguration problem workspace) hLast

def rawTimeBound {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderPhysicalClassifierPipeline.rawTimeBound verifier)
    (.constant 12)

theorem rawTimeBound_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (rawTimeBound problem.verifier).eval problem.input.length =
      (BuilderPhysicalClassifierPipeline.rawTimeBound
        problem.verifier).eval problem.input.length + 12 := by
  rfl

theorem compiledSteps_le_rawTimeBound {language : Language}
    (problem : VerifierTableauProblem language) :
    6 * workSteps problem <=
      (rawTimeBound problem.verifier).eval problem.input.length := by
  have hClassifier :=
    BuilderPhysicalClassifierPipeline.compiledSteps_le_rawTimeBound problem
      (finishIndex problem)
  rw [rawTimeBound_eval]
  unfold workSteps
  omega

def ClassifierFinishRequestHolds {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) : Prop :=
  BuilderPhysicalClassifierPipeline.PhysicalClassifierPipelineHolds problem
      (finishIndex problem) workspace /\
    workRunExact? machine (workSteps problem)
        (entryConfiguration problem workspace) =
      some (finalConfiguration problem workspace) /\
    run (compileWorkMachine machine) (6 * workSteps problem)
        (encodeWorkConfiguration (entryConfiguration problem workspace)) =
      encodeWorkConfiguration (finalConfiguration problem workspace) /\
    machine.isHalted
      (workRun machine (workSteps problem - 1)
        (entryConfiguration problem workspace)) = false /\
    (finalConfiguration problem workspace).tape =
      (classifierFinalConfiguration problem workspace).tape.write
        (BuilderPhysicalOptionalTokenDispatch.requestSymbol (some .finish))

theorem classifierFinishRequestHolds {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) :
    ClassifierFinishRequestHolds problem workspace := by
  exact ⟨BuilderPhysicalClassifierPipeline.physicalClassifierPipelineHolds
      problem (finishIndex problem) workspace,
    workRunExact problem workspace,
    run_compile_exact problem workspace,
    one_step_short_not_halted problem workspace,
    final_request_exact problem workspace⟩

/-- M221 connects the complete M220 physical classifier's unique Finish
terminal to one literal M217-compatible Finish request cell in a fixed
collision-free machine.  It does not derive body-token or padding requests,
reorient the preserved workspace for M217's dispatcher, iterate the physical
schedule, establish builder RawRefinement, or package the reduction. -/
theorem cook_levin_builder_physical_classifier_finish_request_checked_complete
    {language : Language} (problem : VerifierTableauProblem language) :
    scheduleEntry problem (finishIndex problem) = some .finish /\
    machine.rules.length = 721 /\
    machine.rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) /\
    (forall workspace, ClassifierFinishRequestHolds problem workspace) /\
    6 * workSteps problem <=
      (rawTimeBound problem.verifier).eval problem.input.length := by
  exact ⟨finishIndex_scheduleEntry problem, rules_length,
    rules_pairwise_query_distinct, classifierFinishRequestHolds problem,
    compiledSteps_le_rawTimeBound problem⟩

end BuilderPhysicalClassifierFinishRequest

end CookLevin

end PNP.Concrete
