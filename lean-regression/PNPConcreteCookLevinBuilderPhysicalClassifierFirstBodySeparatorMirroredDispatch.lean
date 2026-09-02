import PNP

namespace PNP.Concrete.CookLevinBuilderPhysicalClassifierFirstBodySeparatorMirroredDispatchRegression

open CookLevin
open CookLevin.BuilderPhysicalClassifierFirstBodySeparatorMirroredDispatch
open CookLevin.BuilderPostDividerSelectedTokenLaunch
open PipelineStateNamespace

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

example {language : Language} (problem : VerifierTableauProblem language) :
    (firstBodyIndex problem).val = 0 := by
  rfl

example {language : Language} (problem : VerifierTableauProblem language) :
    0 < BuilderPhysicalClassifierPipeline.clauseCount problem :=
  clauseCount_positive problem

example {language : Language} (problem : VerifierTableauProblem language) :
    scheduleEntry problem (firstBodyIndex problem) = some .sep :=
  firstBodyIndex_scheduleEntry problem

example : writerMachine.rules.length = 2 := writerRules_length

example : orientMachine.rules.length = 10 := orientRules_length

example : dispatchMachine.rules.length = 64 := dispatchRules_length

example : machine.rules.length = 814 := rules_length

example : machine.rules.Pairwise (fun left right =>
    (left.sourceState, left.readSymbol) ≠
      (right.sourceState, right.readSymbol)) :=
  rules_pairwise_query_distinct

example : machine.acceptState ≠ machine.rejectState :=
  machine_acceptState_ne_rejectState

example {language : Language} (problem : VerifierTableauProblem language) :
    workRunExact? writerMachine
        (writerWorkSteps
          (BuilderPhysicalClassifierPipeline.clauseCount problem))
        { state := writerMachine.startState
          tape :=
            (classifierFinalConfiguration problem
              (classifierWorkspace problem)).tape } =
      some (bodyWriterFinalConfiguration problem
        (classifierWorkspace problem)) :=
  bodyWriter_workRunExact problem (classifierWorkspace problem)

example {language : Language} (problem : VerifierTableauProblem language) :
    workRunExact? machine (workSteps problem) (entryConfiguration problem) =
      some (finalConfiguration problem) :=
  workRunExact problem

example {language : Language} (problem : VerifierTableauProblem language) :
    run (compileWorkMachine machine) (6 * workSteps problem)
        (encodeWorkConfiguration (entryConfiguration problem)) =
      encodeWorkConfiguration (finalConfiguration problem) :=
  run_compile_exact problem

example {language : Language} (problem : VerifierTableauProblem language) :
    machine.isHalted
      (workRun machine (workSteps problem - 1) (entryConfiguration problem)) =
        false :=
  one_step_short_not_halted problem

example {language : Language} (problem : VerifierTableauProblem language) :
    (finalConfiguration problem).tape =
      (BuilderPhysicalClassifierFinishMirroredDispatch.mirrorConfiguration
        (renameConfiguration BuilderPhysicalOptionalTokenDispatch.appenderState
          (BuilderTokenAppender.finalConfiguration problem.input
            (dispatchOutsideLeft problem)
            (output problem ++ [.sep])))).tape :=
  final_output_exact problem

example {language : Language} (problem : VerifierTableauProblem language) :
    6 * workSteps problem ≤
      (BuilderPhysicalClassifierFirstBodySeparatorMirroredDispatch.rawTimeBound
        problem.verifier).eval problem.input.length :=
  compiledSteps_le_rawTimeBound problem

example {language : Language} (problem : VerifierTableauProblem language) :
    FirstBodySeparatorMirroredDispatchHolds problem :=
  firstBodySeparatorMirroredDispatchHolds problem

example {language : Language} (problem : VerifierTableauProblem language) :=
  cook_levin_builder_physical_classifier_first_body_separator_mirrored_dispatch_checked_complete
    problem

end PNP.Concrete.CookLevinBuilderPhysicalClassifierFirstBodySeparatorMirroredDispatchRegression
