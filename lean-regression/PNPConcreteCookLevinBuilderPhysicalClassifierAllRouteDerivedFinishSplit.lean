import PNP

namespace PNP.Concrete.CookLevin.BuilderPhysicalClassifierAllRouteDerivedFinishSplitRegression

open CookLevin
open CookLevin.BuilderPhysicalClassifierAllRouteDerivedFinishSplit

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

example : relayMachine.rules.length = 20 := relayRules_length

example : classifierRelayMachine.rules.length = 749 :=
  classifierRelayRules_length

example : dispatchMachine.rules.length = 65 := dispatchRules_length

example : machine.rules.length = 823 := rules_length

example : machine.rules.Pairwise (fun left right =>
    (left.sourceState, left.readSymbol) ≠
      (right.sourceState, right.readSymbol)) :=
  rules_pairwise_query_distinct

example : machine.acceptState ≠ machine.rejectState :=
  machine_acceptState_ne_rejectState

example (request : Option CNFToken) :
    bodyPendingSymbol ≠
      BuilderPhysicalOptionalTokenDispatch.requestSymbol request :=
  bodyPendingSymbol_ne_requestSymbol request

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    classifierWorkspace problem index =
      WorkSymbol.blank :: builderWord problem index := by
  rfl

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute problem index.val ≠
      .outOfRange :=
  route_ne_outOfRange problem index

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (clauseCoordinate : Fin problem.formulaClauseSlotCount)
    (tokenCoordinate : Fin problem.formulaTokensPerClause)
    (hRoute : BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute
      problem index.val = .body clauseCoordinate tokenCoordinate) :
    (classifierFinalConfiguration problem index
      (classifierWorkspace problem index)).tape.head = unitSymbol :=
  classifierFinal_head_eq_unit_of_body problem index
    (classifierWorkspace problem index) clauseCoordinate tokenCoordinate hRoute

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (hRoute : BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute
      problem index.val = .finish) :
    (classifierFinalConfiguration problem index
      (classifierWorkspace problem index)).tape.head = endSymbol :=
  classifierFinal_head_eq_end_of_finish problem index
    (classifierWorkspace problem index) hRoute

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (hRoute : BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute
      problem index.val = .finish) :
    BuilderPhysicalOptionalTokenDispatch.canonicalRequest problem index =
      some .finish :=
  canonicalRequest_eq_finish_of_route problem index hRoute

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    workRunExact? relayMachine (relayWorkSteps problem index)
        (relayEntryConfiguration problem index) =
      some (relayFinalConfiguration problem index) :=
  relay_workRunExact problem index

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
    RouteTerminalHolds problem index :=
  routeTerminalHolds problem index

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    6 * workSteps problem index ≤
      (rawTimeBound problem.verifier).eval problem.input.length :=
  compiledSteps_le_rawTimeBound problem index

example {language : Language} (problem : VerifierTableauProblem language) :
    AllRouteDerivedFinishSplitHolds problem :=
  allRouteDerivedFinishSplitHolds problem

example {language : Language} (problem : VerifierTableauProblem language) :=
  cook_levin_builder_physical_classifier_all_route_derived_finish_split_checked_complete
    problem

end PNP.Concrete.CookLevin.BuilderPhysicalClassifierAllRouteDerivedFinishSplitRegression
