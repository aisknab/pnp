import PNP

namespace PNP.Concrete.CookLevinBuilderPhysicalClassifierFinishWorkspaceOrientationRegression

open CookLevin
open CookLevin.BuilderPhysicalClassifierFinishWorkspaceOrientation

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

example : orientRules.length = 10 := orientRules_length

example : composedMachine.rules.length = 740 := composedRules_length

example : composedMachine.rules.Pairwise (fun left right =>
    (left.sourceState, left.readSymbol) ≠
      (right.sourceState, right.readSymbol)) :=
  composedRules_pairwise_query_distinct

example : composedMachine.acceptState ≠ composedMachine.rejectState :=
  composedMachine_acceptState_ne_rejectState

example {language : Language} (problem : VerifierTableauProblem language) :
    WorkSymbol.blank ∉ classifierPrefix problem :=
  blank_not_mem_classifierPrefix problem

example {language : Language} (problem : VerifierTableauProblem language) :
    (classifierPrefix problem).length ≤
      12 * (BuilderPhysicalClassifierPipeline.firstBodySlot problem +
        BuilderFullScheduleCursorController.bodySlotCount problem +
        BuilderPhysicalClassifierPipeline.width problem + 1) :=
  classifierPrefix_length_le problem

example (scanWord builderWord : List WorkSymbol)
    (hScanWord : ∀ symbol ∈ scanWord,
      symbol ≠ WorkSymbol.blank) :
    workRunExact? orientMachine (orientWorkSteps scanWord)
        (orientEntryConfiguration scanWord builderWord) =
      some (orientFinalConfiguration scanWord builderWord) :=
  orient_workRunExact scanWord builderWord hScanWord

example {language : Language} (problem : VerifierTableauProblem language) :
    (classifierWriterFinalConfiguration problem).tape =
      (orientEntryConfiguration (classifierPrefix problem)
        (builderWord problem)).tape :=
  classifierWriterFinal_tape_eq_orientEntry problem

example {language : Language} (problem : VerifierTableauProblem language) :
    workRunExact? composedMachine (composedWorkSteps problem)
        (composedEntryConfiguration problem) =
      some (composedFinalConfiguration problem) :=
  composed_workRunExact problem

example {language : Language} (problem : VerifierTableauProblem language) :
    run (compileWorkMachine composedMachine) (6 * composedWorkSteps problem)
        (encodeWorkConfiguration (composedEntryConfiguration problem)) =
      encodeWorkConfiguration (composedFinalConfiguration problem) :=
  composed_run_compile_exact problem

example {language : Language} (problem : VerifierTableauProblem language) :
    composedMachine.isHalted
      (workRun composedMachine (composedWorkSteps problem - 1)
        (composedEntryConfiguration problem)) = false :=
  composed_one_step_short_not_halted problem

example {language : Language} (problem : VerifierTableauProblem language) :
    (composedFinalConfiguration problem).tape =
      mirrorTape
        (BuilderPhysicalOptionalTokenDispatch.entryConfiguration
          problem.input (dispatchOutsideLeft problem) (output problem)
          (some .finish)).tape :=
  composedFinal_tape_eq_mirrored_dispatch_entry problem

example {language : Language} (problem : VerifierTableauProblem language) :
    6 * orientWorkSteps (classifierPrefix problem) ≤
      (orientationRawTimeBound problem.verifier).eval problem.input.length :=
  orientCompiledSteps_le_orientationRawTimeBound problem

example {language : Language} (problem : VerifierTableauProblem language) :
    6 * composedWorkSteps problem ≤
      (rawTimeBound problem.verifier).eval problem.input.length :=
  composedCompiledSteps_le_rawTimeBound problem

example {language : Language} (problem : VerifierTableauProblem language) :
    FinishWorkspaceOrientationHolds problem :=
  finishWorkspaceOrientationHolds problem

example {language : Language} (problem : VerifierTableauProblem language) :=
  cook_levin_builder_physical_classifier_finish_workspace_orientation_checked_complete
    problem

end PNP.Concrete.CookLevinBuilderPhysicalClassifierFinishWorkspaceOrientationRegression
