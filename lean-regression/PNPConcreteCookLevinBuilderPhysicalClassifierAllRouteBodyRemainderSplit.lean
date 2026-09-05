import PNP

namespace PNP.Concrete.CookLevin.BuilderPhysicalClassifierAllRouteBodyRemainderSplitRegression

open CookLevin
open CookLevin.BuilderPhysicalClassifierAllRouteBodyRemainderSplit

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

example : Splitter.rules.length = 36 := Splitter.rules_length
example : machine.rules.length = 895 := rules_length
example : machine.rules.Pairwise (fun left right =>
    (left.sourceState, left.readSymbol) ≠
      (right.sourceState, right.readSymbol)) := rules_pairwise_query_distinct
example : machine.acceptState ≠ machine.rejectState :=
  machine_acceptState_ne_rejectState

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    BuilderPhysicalClassifierAllRouteDerivedFinishSplit.classifierTrail
        problem index = physicalTrail problem index :=
  classifierTrail_eq_physicalTrail problem index

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (clauseCoordinate : Fin problem.formulaClauseSlotCount)
    (tokenCoordinate : Fin problem.formulaTokensPerClause)
    (hRoute : BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute
      problem index.val = .body clauseCoordinate tokenCoordinate) :
    workRunExact? Splitter.machine (splitterWorkSteps problem index)
        (splitterEntryConfiguration problem index) =
      some (splitterFinalConfiguration problem index) :=
  splitter_workRunExact problem index clauseCoordinate tokenCoordinate hRoute

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    workRunExact? machine (workSteps problem index)
        (entryConfiguration problem index) =
      some (finalConfiguration problem index) := workRunExact problem index

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    run compiledMachine (6 * workSteps problem index)
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
    RouteTerminalHolds problem index := routeTerminalHolds problem index

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    6 * workSteps problem index ≤
      (rawTimeBound problem.verifier).eval problem.input.length :=
  compiledSteps_le_rawTimeBound problem index

example {language : Language} (problem : VerifierTableauProblem language) :
    AllRouteBodyRemainderSplitHolds problem := allRouteBodyRemainderSplitHolds problem

example {language : Language} (problem : VerifierTableauProblem language) :=
  cook_levin_builder_physical_classifier_all_route_body_remainder_split_checked_complete
    problem

-- Independent literal executions guard the zero, positive, consumed-prefix,
-- and one-step-short boundaries; these fixtures earn no milestone credit.
example : workRunExact? Splitter.machine 4
    { state := Splitter.machine.startState
      tape :=
        { left := []
          head := Splitter.bodyPendingSymbol
          right := [Splitter.leftBoundary, Splitter.leftBoundary,
          Splitter.separatorSymbol] } } =
    some (Splitter.finalConfiguration [] [] [] [] 0 0) := by decide

example : workRunExact? Splitter.machine 6
    { state := Splitter.machine.startState
      tape :=
        { left := []
          head := Splitter.bodyPendingSymbol
          right := [Splitter.leftBoundary, Splitter.leftBoundary,
          Splitter.consumedDividend, Splitter.consumedDividend,
          Splitter.unitSymbol, Splitter.unitSymbol, Splitter.separatorSymbol] } } =
    some (Splitter.finalConfiguration [] [] [] [] 2 2) := by decide

example : Splitter.machine.isHalted
    (workRun Splitter.machine 5
      { state := Splitter.machine.startState
        tape :=
          { left := []
            head := Splitter.bodyPendingSymbol
            right := [Splitter.leftBoundary, Splitter.leftBoundary,
            Splitter.consumedDividend, Splitter.consumedDividend,
            Splitter.unitSymbol, Splitter.unitSymbol,
            Splitter.separatorSymbol] } }) = false := by decide

end PNP.Concrete.CookLevin.BuilderPhysicalClassifierAllRouteBodyRemainderSplitRegression
