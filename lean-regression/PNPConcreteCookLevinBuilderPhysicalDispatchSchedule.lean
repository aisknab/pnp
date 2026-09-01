import PNP

namespace PNP.Concrete.CookLevinBuilderPhysicalDispatchScheduleRegression

open CookLevin
open CookLevin.BuilderPhysicalDispatchSchedule

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat)
    (hIndex : index <
      CookLevin.BuilderFullScheduleCursorController.bodySlotCount problem) :
    physicalOutput problem (index + 1) =
      CookLevin.BuilderPhysicalOptionalTokenDispatch.nextOutput
        (physicalOutput problem index)
        (CookLevin.BuilderPhysicalOptionalTokenDispatch.canonicalRequest
          problem ⟨index, hIndex⟩) :=
  physicalOutput_succ_of_lt problem index hIndex

example {language : Language} (problem : VerifierTableauProblem language)
    (count : Nat)
    (hCount : count <=
      CookLevin.BuilderFullScheduleCursorController.bodySlotCount problem) :
    physicalOutput problem count =
      CookLevin.BuilderPostDividerSelectedTokenLaunch.emittedPrefix
        problem count :=
  physicalOutput_eq_emittedPrefix problem count hCount

example {language : Language} (problem : VerifierTableauProblem language) :
    physicalOutput problem
        (CookLevin.BuilderFullScheduleCursorController.bodySlotCount problem) =
      encodeCNFTokens problem.formula :=
  physicalOutput_bodySlotCount_eq_encodeCNFTokens problem

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin
      (CookLevin.BuilderFullScheduleCursorController.bodySlotCount problem)) :
    stepWorkSteps problem index =
      CookLevin.BuilderPhysicalOptionalTokenDispatch.canonicalWorkSteps
        problem index :=
  stepWorkSteps_eq_canonicalWorkSteps problem index

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin
      (CookLevin.BuilderFullScheduleCursorController.bodySlotCount problem))
    (outsideLeft : List WorkSymbol) :
    PhysicalStepHolds problem index outsideLeft :=
  physicalStepHolds problem index outsideLeft

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin
      (CookLevin.BuilderFullScheduleCursorController.bodySlotCount problem)) :
    6 * stepWorkSteps problem index <=
      (CookLevin.BuilderPhysicalOptionalTokenDispatch.rawTimeBound
        problem.verifier).eval problem.input.length :=
  stepCompiledSteps_le_rawTimeBound problem index

example {language : Language} (problem : VerifierTableauProblem language) :
    (rawTimeBound problem.verifier).eval problem.input.length =
      CookLevin.BuilderFullScheduleCursorController.bodySlotCount problem *
        (CookLevin.BuilderPhysicalOptionalTokenDispatch.rawTimeBound
          problem.verifier).eval problem.input.length :=
  rawTimeBound_eval problem

example {language : Language} (problem : VerifierTableauProblem language)
    (count : Nat)
    (hCount : count <=
      CookLevin.BuilderFullScheduleCursorController.bodySlotCount problem) :
    accumulatedCompiledSteps problem count <=
      count *
        (CookLevin.BuilderPhysicalOptionalTokenDispatch.rawTimeBound
          problem.verifier).eval problem.input.length :=
  accumulatedCompiledSteps_le problem count hCount

example {language : Language} (problem : VerifierTableauProblem language) :
    totalCompiledSteps problem <=
      (rawTimeBound problem.verifier).eval problem.input.length :=
  totalCompiledSteps_le_rawTimeBound problem

example {language : Language} (problem : VerifierTableauProblem language) :=
  cook_levin_builder_physical_dispatch_schedule_checked_complete problem

end PNP.Concrete.CookLevinBuilderPhysicalDispatchScheduleRegression
