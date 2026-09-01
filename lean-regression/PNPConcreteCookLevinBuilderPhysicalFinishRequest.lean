import PNP

namespace PNP.Concrete.CookLevinBuilderPhysicalFinishRequestRegression

open CookLevin
open CookLevin.BuilderPhysicalFinishRequest

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

example (coordinate boundary : Nat) (leftExterior rightExterior : List WorkSymbol) :
    workRunExact? comparatorMachine
        (BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps coordinate boundary)
        (appendRightExteriorConfiguration
          (BuilderPostDividerRawRouteClassifier.shieldedComparatorStartConfiguration
            coordinate boundary leftExterior) rightExterior) =
      some
        (appendRightExteriorConfiguration
          (BuilderPostDividerRawRouteClassifier.shieldedComparatorFinalConfiguration
            coordinate boundary leftExterior) rightExterior) :=
  shielded_comparator_workRunExact_with_right_exterior coordinate boundary
    leftExterior rightExterior

example {language : Language} (problem : VerifierTableauProblem language) :
    BuilderPostDividerSelectedTokenLaunch.scheduleEntry problem
        (finishIndex problem) = some .finish :=
  finishIndex_scheduleEntry problem

example {language : Language} (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) :
    BuilderPostDividerRawRouteClassifier.InRangeRouteClassifierHolds problem
      (BuilderPostDividerSelectedTokenLaunch.scheduleCoordinate problem
        (finishIndex problem)) workspace :=
  finishIndex_classifier_holds problem workspace

example : machine.rules.length = 137 := rules_length

example : machine.rules.Pairwise (fun left right =>
    (left.sourceState, left.readSymbol) ≠
      (right.sourceState, right.readSymbol)) :=
  rules_pairwise_query_distinct

example {language : Language} (problem : VerifierTableauProblem language)
    (classifierExterior : List WorkSymbol) :
    workRunExact? machine (workSteps problem)
        (entryConfiguration problem classifierExterior) =
      some (finalConfiguration problem classifierExterior) :=
  workRunExact problem classifierExterior

example {language : Language} (problem : VerifierTableauProblem language)
    (classifierExterior : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps problem)
        (encodeWorkConfiguration (entryConfiguration problem
          classifierExterior)) =
      encodeWorkConfiguration (finalConfiguration problem
        classifierExterior) :=
  run_compile_exact problem classifierExterior

example {language : Language} (problem : VerifierTableauProblem language)
    (classifierExterior : List WorkSymbol) :
    machine.isHalted
      (workRun machine (workSteps problem - 1)
        (entryConfiguration problem classifierExterior)) = false :=
  one_step_short_not_halted problem classifierExterior

example {language : Language} (problem : VerifierTableauProblem language) :
    6 * workSteps problem ≤
      (rawTimeBound problem.verifier).eval problem.input.length :=
  compiledSteps_le_rawTimeBound problem

example {language : Language} (problem : VerifierTableauProblem language)
    (classifierExterior : List WorkSymbol) :
    FinishRequestHolds problem classifierExterior :=
  finishRequestHolds problem classifierExterior

example {language : Language} (problem : VerifierTableauProblem language) :=
  cook_levin_builder_physical_finish_request_checked_complete problem

end PNP.Concrete.CookLevinBuilderPhysicalFinishRequestRegression
