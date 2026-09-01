import PNP

namespace PNP.Concrete.CookLevinBuilderPhysicalClassifierPipelineRegression

open CookLevin
open CookLevin.BuilderPhysicalClassifierPipeline

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

example : machine.rules.length = 711 := rules_length

example : machine.rules.Pairwise (fun left right =>
    (left.sourceState, left.readSymbol) ≠
      (right.sourceState, right.readSymbol)) :=
  rules_pairwise_query_distinct

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol) :
    StageHandoffsHold problem index workspace :=
  stageHandoffsHold problem index workspace

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol) :
    workRunExact? machine (workSteps problem index)
        (entryConfiguration problem index workspace) =
      some (finalConfiguration problem index workspace) :=
  workRunExact problem index workspace

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps problem index)
        (encodeWorkConfiguration (entryConfiguration problem index workspace)) =
      encodeWorkConfiguration (finalConfiguration problem index workspace) :=
  run_compile_exact problem index workspace

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol) :
    machine.isHalted
      (workRun machine (workSteps problem index - 1)
        (entryConfiguration problem index workspace)) = false :=
  one_step_short_not_halted problem index workspace

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol) :
    RouteAgreement problem index workspace :=
  routeAgreement problem index workspace

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    6 * workSteps problem index ≤
      (rawTimeBound problem.verifier).eval problem.input.length :=
  compiledSteps_le_rawTimeBound problem index

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol) :
    PhysicalClassifierPipelineHolds problem index workspace :=
  physicalClassifierPipelineHolds problem index workspace

example {language : Language} (problem : VerifierTableauProblem language) :=
  cook_levin_builder_physical_classifier_pipeline_checked_complete problem

end PNP.Concrete.CookLevinBuilderPhysicalClassifierPipelineRegression
