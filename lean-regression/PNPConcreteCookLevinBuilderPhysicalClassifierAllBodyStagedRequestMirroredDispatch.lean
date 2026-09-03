import PNP

namespace PNP.Concrete.CookLevinBuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatchRegression

open CookLevin
open CookLevin.BuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch
open CookLevin.BuilderPostDividerSelectedTokenLaunch
open PipelineStateNamespace

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) :
    (bodyIndex problem index).val = index.val :=
  bodyIndex_val problem index

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) :
    exists clauseCoordinate tokenCoordinate,
      BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute problem index.val =
        .body clauseCoordinate tokenCoordinate :=
  bodyIndex_route problem index

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) :
    request problem index ∈ BuilderPhysicalOptionalTokenDispatch.requestOrder :=
  request_mem_requestOrder problem index

example : relayMachine.rules.length = 14 := relayRules_length

example : classifierRelayMachine.rules.length = 734 :=
  classifierRelayRules_length

example : dispatchMachine.rules.length = 64 := dispatchRules_length

example : machine.rules.length = 807 := rules_length

example : machine.rules.Pairwise (fun left right =>
    (left.sourceState, left.readSymbol) ≠
      (right.sourceState, right.readSymbol)) :=
  rules_pairwise_query_distinct

example : machine.acceptState ≠ machine.rejectState :=
  machine_acceptState_ne_rejectState

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) :
    workRunExact? relayMachine (relayWorkSteps problem index)
        (relayEntryConfiguration problem index) =
      some (relayFinalConfiguration problem index) :=
  relay_workRunExact problem index

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) :
    workRunExact? machine (workSteps problem index)
        (entryConfiguration problem index) =
      some (finalConfiguration problem index) :=
  workRunExact problem index

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) :
    run (compileWorkMachine machine) (6 * workSteps problem index)
        (encodeWorkConfiguration (entryConfiguration problem index)) =
      encodeWorkConfiguration (finalConfiguration problem index) :=
  run_compile_exact problem index

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) :
    machine.isHalted
      (workRun machine (workSteps problem index - 1)
        (entryConfiguration problem index)) = false :=
  one_step_short_not_halted problem index

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) :
    (finalConfiguration problem index).tape =
      (BuilderPhysicalClassifierFinishMirroredDispatch.mirrorConfiguration
        (renameConfiguration BuilderPhysicalOptionalTokenDispatch.appenderState
          (BuilderTokenAppender.finalConfiguration problem.input
            (dispatchOutsideLeft problem index)
            (emittedPrefix problem (index.val + 1))))).tape := by
  rfl

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) :
    6 * workSteps problem index ≤
      (BuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch.rawTimeBound
        problem.verifier).eval problem.input.length :=
  compiledSteps_le_rawTimeBound problem index

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) :
    AllBodyStagedRequestMirroredDispatchHolds problem index :=
  allBodyStagedRequestMirroredDispatchHolds problem index

example {language : Language} (problem : VerifierTableauProblem language) :=
  cook_levin_builder_physical_classifier_all_body_staged_request_mirrored_dispatch_checked_complete
    problem

end PNP.Concrete.CookLevinBuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatchRegression
