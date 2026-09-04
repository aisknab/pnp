import PNP

namespace PNP.Concrete.CookLevinBuilderPhysicalClassifierAllRouteStagedRequestMirroredDispatchRegression

open CookLevin
open CookLevin.BuilderPhysicalClassifierAllRouteStagedRequestMirroredDispatch

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

example :
    PNP.Concrete.CookLevin.BuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch.relayRules.length =
      14 :=
  PNP.Concrete.CookLevin.BuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch.relayRules_length

example : dispatchMachine.rules.length = 64 :=
  PNP.Concrete.CookLevin.BuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch.dispatchRules_length

example : classifierRelayMachine.rules.length = 743 :=
  classifierRelayRules_length

example : machine.rules.length = 816 := rules_length

example : machine.rules.Pairwise (fun left right =>
    (left.sourceState, left.readSymbol) ≠
      (right.sourceState, right.readSymbol)) :=
  rules_pairwise_query_distinct

example : machine.acceptState ≠ machine.rejectState :=
  machine_acceptState_ne_rejectState

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute problem index.val ≠
      .outOfRange :=
  route_ne_outOfRange problem index

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    request problem index ∈ BuilderPhysicalOptionalTokenDispatch.requestOrder :=
  request_mem_requestOrder problem index

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    workRunExact? relayMachine (relayWorkSteps problem index)
        (relayEntryConfiguration problem index) =
      some (relayFinalConfiguration problem index) :=
  relay_workRunExact problem index

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    (relayFinalConfiguration problem index).tape =
      (dispatchEntryConfiguration problem index).tape :=
  relayFinal_tape_eq_dispatchEntry problem index

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    workRunExact? dispatchMachine (dispatchWorkSteps problem index)
        (dispatchEntryConfiguration problem index) =
      some (dispatchFinalConfiguration problem index) :=
  dispatch_workRunExact problem index

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    workRunExact? machine (workSteps problem index)
        (entryConfiguration problem index) =
      some (finalConfiguration problem index) :=
  workRunExact problem index

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    run (compileWorkMachine machine) (6 * workSteps problem index)
        (encodeWorkConfiguration (entryConfiguration problem index)) =
      encodeWorkConfiguration (finalConfiguration problem index) :=
  run_compile_exact problem index

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    machine.isHalted
      (workRun machine (workSteps problem index - 1)
        (entryConfiguration problem index)) = false :=
  one_step_short_not_halted problem index

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    6 * workSteps problem index ≤
      (rawTimeBound problem.verifier).eval problem.input.length :=
  compiledSteps_le_rawTimeBound problem index

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    AllRouteStagedRequestMirroredDispatchHolds problem index :=
  allRouteStagedRequestMirroredDispatchHolds problem index

example {language : Language} (problem : VerifierTableauProblem language) :=
  cook_levin_builder_physical_classifier_all_route_staged_request_mirrored_dispatch_checked_complete
    problem

end PNP.Concrete.CookLevinBuilderPhysicalClassifierAllRouteStagedRequestMirroredDispatchRegression
