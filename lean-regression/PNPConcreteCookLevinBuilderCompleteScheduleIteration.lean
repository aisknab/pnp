import PNP

namespace PNP.Concrete.CookLevinBuilderCompleteScheduleIterationRegression

open CookLevin
open CookLevin.BuilderCompleteScheduleIteration

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) :
    CookLevin.BuilderCompleteScheduleIteration.run problem (index + 1) =
      match
        CookLevin.BuilderPostDividerSelectedTokenLaunch.selectedEntry?
          problem index with
      | none => CookLevin.BuilderCompleteScheduleIteration.run problem index
      | some none => CookLevin.BuilderCompleteScheduleIteration.run problem index
      | some (some token) =>
          CookLevin.BuilderCompleteScheduleIteration.run problem index ++
            [token] :=
  CookLevin.BuilderCompleteScheduleIteration.run_succ problem index

example {language : Language} (problem : VerifierTableauProblem language)
    (count : Nat)
    (hCount : count <=
      CookLevin.BuilderFullScheduleCursorController.bodySlotCount problem) :
    CookLevin.BuilderCompleteScheduleIteration.run problem count =
      CookLevin.BuilderPostDividerSelectedTokenLaunch.emittedPrefix
        problem count :=
  CookLevin.BuilderCompleteScheduleIteration.run_eq_emittedPrefix problem
    count hCount

example {language : Language} (problem : VerifierTableauProblem language) :
    CookLevin.BuilderPostDividerSelectedTokenLaunch.emittedPrefix problem
        (CookLevin.BuilderFullScheduleCursorController.bodySlotCount problem) =
      encodeCNFTokens problem.formula :=
  CookLevin.BuilderCompleteScheduleIteration.emittedPrefix_bodySlotCount_eq_encodeCNFTokens
    problem

example {language : Language} (problem : VerifierTableauProblem language) :
    CookLevin.BuilderCompleteScheduleIteration.run problem
        (CookLevin.BuilderFullScheduleCursorController.bodySlotCount problem) =
      encodeCNFTokens problem.formula :=
  CookLevin.BuilderCompleteScheduleIteration.run_bodySlotCount_eq_encodeCNFTokens
    problem

example {language : Language} (problem : VerifierTableauProblem language) :
    (CookLevin.BuilderCompleteScheduleIteration.rawTimeBound
      problem.verifier).eval problem.input.length =
      CookLevin.BuilderFullScheduleCursorController.bodySlotCount problem *
        (CookLevin.BuilderPostDividerSelectedTokenLaunch.rawTimeBound
          problem.verifier).eval problem.input.length :=
  CookLevin.BuilderCompleteScheduleIteration.rawTimeBound_eval problem

example {language : Language} (problem : VerifierTableauProblem language)
    (count : Nat)
    (hCount : count <=
      CookLevin.BuilderFullScheduleCursorController.bodySlotCount problem) :
    CookLevin.BuilderCompleteScheduleIteration.accumulatedStagedCompiledSteps
        problem count <=
      count *
        (CookLevin.BuilderPostDividerSelectedTokenLaunch.rawTimeBound
          problem.verifier).eval problem.input.length :=
  CookLevin.BuilderCompleteScheduleIteration.accumulatedStagedCompiledSteps_le
    problem count hCount

example {language : Language} (problem : VerifierTableauProblem language) :
    CookLevin.BuilderCompleteScheduleIteration.totalStagedCompiledSteps
        problem <=
      (CookLevin.BuilderCompleteScheduleIteration.rawTimeBound
        problem.verifier).eval problem.input.length :=
  CookLevin.BuilderCompleteScheduleIteration.totalStagedCompiledSteps_le_rawTimeBound
    problem

example {language : Language} (problem : VerifierTableauProblem language) :=
  CookLevin.BuilderCompleteScheduleIteration.cook_levin_builder_complete_schedule_iteration_checked_complete
    problem

end PNP.Concrete.CookLevinBuilderCompleteScheduleIterationRegression
