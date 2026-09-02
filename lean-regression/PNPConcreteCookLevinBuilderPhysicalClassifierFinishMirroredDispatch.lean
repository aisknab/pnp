import PNP

namespace PNP.Concrete.CookLevinBuilderPhysicalClassifierFinishMirroredDispatchRegression

open CookLevin
open CookLevin.BuilderPhysicalClassifierFinishMirroredDispatch

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

example (move : HeadMove) : mirrorMove (mirrorMove move) = move :=
  mirrorMove_mirrorMove move

example (tape : WorkTape) : mirrorTape (mirrorTape tape) = tape :=
  mirrorTape_mirrorTape tape

example (source : WorkMachine) (steps : Nat)
    (initial final : WorkConfiguration)
    (hRun : workRunExact? source steps initial = some final) :
    workRunExact? (mirrorMachine source) steps
        (mirrorConfiguration initial) =
      some (mirrorConfiguration final) :=
  workRunExact?_mirror_of_some source steps initial final hRun

example : dispatchMachine.rules.length = 64 := dispatchRules_length

example : dispatchMachine.rules.Pairwise (fun left right =>
    (left.sourceState, left.readSymbol) ≠
      (right.sourceState, right.readSymbol)) :=
  dispatchRules_pairwise_query_distinct

example {language : Language} (problem : VerifierTableauProblem language) :
    (BuilderPhysicalClassifierFinishWorkspaceOrientation.finishIndex
        problem).val + 1 =
      BuilderFullScheduleCursorController.bodySlotCount problem :=
  finishIndex_succ_eq_bodySlotCount problem

example {language : Language} (problem : VerifierTableauProblem language) :
    workRunExact? dispatchMachine (dispatchWorkSteps problem)
        (dispatchEntryConfiguration problem) =
      some (dispatchFinalConfiguration problem) :=
  dispatch_workRunExact problem

example {language : Language} (problem : VerifierTableauProblem language) :
    run (compileWorkMachine dispatchMachine) (6 * dispatchWorkSteps problem)
        (encodeWorkConfiguration (dispatchEntryConfiguration problem)) =
      encodeWorkConfiguration (dispatchFinalConfiguration problem) :=
  dispatch_run_compile_exact problem

example {language : Language} (problem : VerifierTableauProblem language) :
    (BuilderPhysicalClassifierFinishWorkspaceOrientation.composedFinalConfiguration
        problem).tape = (dispatchEntryConfiguration problem).tape :=
  classifierFinal_tape_eq_dispatchEntry problem

example : machine.rules.length = 813 := rules_length

example : machine.rules.Pairwise (fun left right =>
    (left.sourceState, left.readSymbol) ≠
      (right.sourceState, right.readSymbol)) :=
  rules_pairwise_query_distinct

example : machine.acceptState ≠ machine.rejectState :=
  machine_acceptState_ne_rejectState

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
    6 * workSteps problem ≤
      (rawTimeBound problem.verifier).eval problem.input.length :=
  compiledSteps_le_rawTimeBound problem

example {language : Language} (problem : VerifierTableauProblem language) :
    FinishMirroredDispatchHolds problem :=
  finishMirroredDispatchHolds problem

example {language : Language} (problem : VerifierTableauProblem language) :=
  cook_levin_builder_physical_classifier_finish_mirrored_dispatch_checked_complete
    problem

end PNP.Concrete.CookLevinBuilderPhysicalClassifierFinishMirroredDispatchRegression
