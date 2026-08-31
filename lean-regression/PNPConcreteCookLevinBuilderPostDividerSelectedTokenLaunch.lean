import PNP

namespace PNP.Concrete.CookLevinBuilderPostDividerSelectedTokenLaunchRegression

open CookLevin
open CookLevin.BuilderPostDividerSelectedTokenLaunch

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    BuilderArbitrarySlotHeaderRouter.outerRoute problem
        (scheduleCoordinate problem index).val = .postHeader index.val :=
  scheduleCoordinate_outerRoute problem index

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    selectedEntry? problem index.val = some (scheduleEntry problem index) :=
  selectedEntry?_eq_some_getElem problem index

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    emittedPrefix problem (index.val + 1) =
      match scheduleEntry problem index with
      | none => emittedPrefix problem index.val
      | some token => emittedPrefix problem index.val ++ [token] :=
  emittedPrefix_succ problem index

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (outsideLeft : List WorkSymbol) :
    launch? problem index outsideLeft =
      some (BuilderTokenAppender.finalConfiguration problem.input outsideLeft
        (emittedPrefix problem (index.val + 1))) :=
  launch?_eq_nextPrefix problem index outsideLeft

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (outsideLeft : List WorkSymbol) (request : CNFToken) :
    workRunExact? appenderMachine
        (BuilderTokenAppender.workSteps problem.input
          (emittedPrefix problem index.val))
        (BuilderTokenAppender.entryConfiguration request
          (BuilderTokenAppender.workspaceTape problem.input outsideLeft
            (emittedPrefix problem index.val))) =
      some (BuilderTokenAppender.finalConfiguration problem.input outsideLeft
        (emittedPrefix problem index.val ++ [request])) :=
  appender_workRunExact problem index outsideLeft request

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (outsideLeft : List WorkSymbol) (request : CNFToken) :
    run (compileWorkMachine appenderMachine)
        (6 * BuilderTokenAppender.workSteps problem.input
          (emittedPrefix problem index.val))
        (encodeWorkConfiguration
          (BuilderTokenAppender.entryConfiguration request
            (BuilderTokenAppender.workspaceTape problem.input outsideLeft
              (emittedPrefix problem index.val)))) =
      encodeWorkConfiguration
        (BuilderTokenAppender.finalConfiguration problem.input outsideLeft
          (emittedPrefix problem index.val ++ [request])) :=
  appender_run_compile_exact problem index outsideLeft request

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (outsideLeft : List WorkSymbol) (request : CNFToken) :
    appenderMachine.isHalted
        (workRun appenderMachine
          (BuilderTokenAppender.workSteps problem.input
            (emittedPrefix problem index.val) - 1)
          (BuilderTokenAppender.entryConfiguration request
            (BuilderTokenAppender.workspaceTape problem.input outsideLeft
              (emittedPrefix problem index.val)))) = false :=
  appender_one_step_short_not_halted problem index outsideLeft request

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    stagedCompiledSteps problem index <=
      (rawTimeBound problem.verifier).eval problem.input.length :=
  stagedCompiledSteps_le_rawTimeBound problem index

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (classifierWorkspace outsideLeft : List WorkSymbol) :
    PostDividerEmissionHolds problem index classifierWorkspace outsideLeft :=
  postDividerEmissionHolds problem index classifierWorkspace outsideLeft

example {language : Language} (problem : VerifierTableauProblem language) :=
  cook_levin_builder_post_divider_selected_token_launch_checked_complete problem

end PNP.Concrete.CookLevinBuilderPostDividerSelectedTokenLaunchRegression
