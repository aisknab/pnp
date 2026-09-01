import PNP

namespace PNP.Concrete.CookLevinBuilderPhysicalClassifierFinishRequestRegression

open CookLevin
open CookLevin.BuilderPhysicalClassifierFinishRequest

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

example : machine.rules.length = 721 := rules_length

example : machine.rules.Pairwise (fun left right =>
    (left.sourceState, left.readSymbol) ≠
      (right.sourceState, right.readSymbol)) :=
  rules_pairwise_query_distinct

example {language : Language} (problem : VerifierTableauProblem language) :
    BuilderPostDividerSelectedTokenLaunch.scheduleEntry problem
      (finishIndex problem) = some .finish :=
  finishIndex_scheduleEntry problem

example {language : Language} (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) :
    (classifierFinalConfiguration problem workspace).state =
      finishClassifierMachine.acceptState :=
  classifierFinal_state problem workspace

example {language : Language} (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) :
    (classifierFinalConfiguration problem workspace).tape.head = endSymbol :=
  classifierFinal_head problem workspace

example {language : Language} (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) :
    workRunExact? finishClassifierMachine
        (BuilderPhysicalClassifierPipeline.workSteps problem
          (finishIndex problem))
        (classifierEntryConfiguration problem workspace) =
      some (classifierFinalConfiguration problem workspace) :=
  classifier_workRunExact problem workspace

example {language : Language} (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) :
    (writerFinalConfiguration problem workspace).tape =
      (classifierFinalConfiguration problem workspace).tape.write
        (BuilderPhysicalOptionalTokenDispatch.requestSymbol (some .finish)) :=
  writerFinal_tape_exact problem workspace

example {language : Language} (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) :
    workRunExact? machine (workSteps problem)
        (entryConfiguration problem workspace) =
      some (finalConfiguration problem workspace) :=
  workRunExact problem workspace

example {language : Language} (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps problem)
        (encodeWorkConfiguration (entryConfiguration problem workspace)) =
      encodeWorkConfiguration (finalConfiguration problem workspace) :=
  run_compile_exact problem workspace

example {language : Language} (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) :
    machine.isHalted
      (workRun machine (workSteps problem - 1)
        (entryConfiguration problem workspace)) = false :=
  one_step_short_not_halted problem workspace

example {language : Language} (problem : VerifierTableauProblem language) :
    6 * workSteps problem ≤
      (rawTimeBound problem.verifier).eval problem.input.length :=
  compiledSteps_le_rawTimeBound problem

example {language : Language} (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) :
    ClassifierFinishRequestHolds problem workspace :=
  classifierFinishRequestHolds problem workspace

example {language : Language} (problem : VerifierTableauProblem language) :=
  cook_levin_builder_physical_classifier_finish_request_checked_complete problem

end PNP.Concrete.CookLevinBuilderPhysicalClassifierFinishRequestRegression
