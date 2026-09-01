/-
Copyright (c) 2026 PNP Labs.

All-coordinate composition of the physical optional-token dispatcher.

For every concrete verifier problem, this module recursively applies M217's
fixed request-coded dispatcher at every canonical post-header schedule
coordinate.  The recursive output agrees with the canonical emitted prefix,
the final output is the complete encoded CNF token stream, every constituent
work-machine and compiled trace is exact, and the aggregate dispatch cost is
bounded by one verifier-derived source-size polynomial.

The canonical request for each coordinate is still constructed in Lean.  The
successive exact traces are not yet connected by one literal looping machine.
This module therefore does not construct the request cell from M214's raw
classifier, prove builder `RawRefinement`, package the Cook--Levin reduction,
prove `CNFSAT` in `P`, or prove `P = NP`.
-/

import PNP.Concrete.CookLevinBuilderPhysicalOptionalTokenDispatch

namespace PNP.Concrete

namespace CookLevin

namespace BuilderPhysicalDispatchSchedule

open BuilderFullScheduleCursorController
  BuilderPostDividerSelectedTokenLaunch
  BuilderPhysicalOptionalTokenDispatch
open PipelineTape PipelineStateNamespace

/-- Recursively apply the exact optional-token output action at every bounded
post-header schedule opportunity.  Coordinates outside the canonical body
range are inert, which keeps the definition total on `Nat`. -/
def physicalOutput {language : Language}
    (problem : VerifierTableauProblem language) : Nat -> List CNFToken
  | 0 => emittedPrefix problem 0
  | index + 1 =>
      if hIndex : index < bodySlotCount problem then
        nextOutput (physicalOutput problem index)
          (canonicalRequest problem ⟨index, hIndex⟩)
      else
        physicalOutput problem index

theorem physicalOutput_succ_of_lt {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat)
    (hIndex : index < bodySlotCount problem) :
    physicalOutput problem (index + 1) =
      nextOutput (physicalOutput problem index)
        (canonicalRequest problem ⟨index, hIndex⟩) := by
  rw [physicalOutput, dif_pos hIndex]

/-- Every bounded recursive output is exactly the canonical emitted prefix. -/
theorem physicalOutput_eq_emittedPrefix {language : Language}
    (problem : VerifierTableauProblem language) (count : Nat)
    (hCount : count <= bodySlotCount problem) :
    physicalOutput problem count = emittedPrefix problem count := by
  induction count with
  | zero => rfl
  | succ index inductionHypothesis =>
      have hIndex : index < bodySlotCount problem := by omega
      rw [physicalOutput_succ_of_lt problem index hIndex,
        inductionHypothesis (by omega)]
      exact canonical_nextOutput problem ⟨index, hIndex⟩

/-- The all-coordinate physical-dispatch output is the complete canonical
formula encoding. -/
theorem physicalOutput_bodySlotCount_eq_encodeCNFTokens
    {language : Language} (problem : VerifierTableauProblem language) :
    physicalOutput problem (bodySlotCount problem) =
      encodeCNFTokens problem.formula := by
  rw [physicalOutput_eq_emittedPrefix problem (bodySlotCount problem)
      (Nat.le_refl _),
    BuilderCompleteScheduleIteration.emittedPrefix_bodySlotCount_eq_encodeCNFTokens]

/-- Exact work steps for the dispatcher when its output prefix is supplied by
the recursive physical schedule invariant. -/
def stepWorkSteps {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodySlotCount problem)) : Nat :=
  workSteps problem.input (physicalOutput problem index.val)
    (canonicalRequest problem index)

theorem stepWorkSteps_eq_canonicalWorkSteps {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodySlotCount problem)) :
    stepWorkSteps problem index = canonicalWorkSteps problem index := by
  unfold stepWorkSteps canonicalWorkSteps
  rw [physicalOutput_eq_emittedPrefix problem index.val (by omega)]

/-- One schedule row has an exact work-machine trace, compiled trace, and
one-step-short nonhalting result whose source and target outputs are the
recursive physical prefixes. -/
def PhysicalStepHolds {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodySlotCount problem))
    (outsideLeft : List WorkSymbol) : Prop :=
  workRunExact? machine (stepWorkSteps problem index)
      (entryConfiguration problem.input outsideLeft
        (physicalOutput problem index.val) (canonicalRequest problem index)) =
    some
      (renameConfiguration appenderState
        (BuilderTokenAppender.finalConfiguration problem.input outsideLeft
          (physicalOutput problem (index.val + 1)))) /\
  run (compileWorkMachine machine) (6 * stepWorkSteps problem index)
      (encodeWorkConfiguration
        (entryConfiguration problem.input outsideLeft
          (physicalOutput problem index.val) (canonicalRequest problem index))) =
    encodeWorkConfiguration
      (renameConfiguration appenderState
        (BuilderTokenAppender.finalConfiguration problem.input outsideLeft
          (physicalOutput problem (index.val + 1)))) /\
  machine.isHalted
      (workRun machine (stepWorkSteps problem index - 1)
        (entryConfiguration problem.input outsideLeft
          (physicalOutput problem index.val) (canonicalRequest problem index))) =
    false

theorem physicalStepHolds {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodySlotCount problem))
    (outsideLeft : List WorkSymbol) :
    PhysicalStepHolds problem index outsideLeft := by
  have hCurrent := physicalOutput_eq_emittedPrefix problem index.val (by omega)
  have hNext := physicalOutput_eq_emittedPrefix problem (index.val + 1)
    (by omega)
  simpa [PhysicalStepHolds, CanonicalDispatchHolds, stepWorkSteps,
    canonicalWorkSteps, hCurrent, hNext] using
      canonicalDispatchHolds problem index outsideLeft

theorem stepCompiledSteps_le_rawTimeBound {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodySlotCount problem)) :
    6 * stepWorkSteps problem index <=
      (BuilderPhysicalOptionalTokenDispatch.rawTimeBound
        problem.verifier).eval problem.input.length := by
  rw [stepWorkSteps_eq_canonicalWorkSteps]
  exact canonicalCompiledSteps_le_rawTimeBound problem index

/-- Sum exact physical-dispatch work over a bounded prefix of schedule
coordinates. -/
def accumulatedCompiledSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat -> Nat
  | 0 => 0
  | index + 1 =>
      if hIndex : index < bodySlotCount problem then
        accumulatedCompiledSteps problem index +
          6 * stepWorkSteps problem ⟨index, hIndex⟩
      else
        accumulatedCompiledSteps problem index

def totalCompiledSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  accumulatedCompiledSteps problem (bodySlotCount problem)

/-- The number of physical dispatch opportunities multiplied by M217's
uniform per-coordinate bound. -/
def rawTimeBound {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .mul (bodySlotCountPolynomial verifier)
    (BuilderPhysicalOptionalTokenDispatch.rawTimeBound verifier)

theorem rawTimeBound_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (rawTimeBound problem.verifier).eval problem.input.length =
      bodySlotCount problem *
        (BuilderPhysicalOptionalTokenDispatch.rawTimeBound
          problem.verifier).eval problem.input.length := by
  rfl

theorem accumulatedCompiledSteps_le {language : Language}
    (problem : VerifierTableauProblem language) (count : Nat)
    (hCount : count <= bodySlotCount problem) :
    accumulatedCompiledSteps problem count <=
      count *
        (BuilderPhysicalOptionalTokenDispatch.rawTimeBound
          problem.verifier).eval problem.input.length := by
  induction count with
  | zero => simp [accumulatedCompiledSteps]
  | succ index inductionHypothesis =>
      have hIndex : index < bodySlotCount problem := by omega
      rw [accumulatedCompiledSteps, dif_pos hIndex]
      calc
        accumulatedCompiledSteps problem index +
              6 * stepWorkSteps problem ⟨index, hIndex⟩ <=
            index *
                (BuilderPhysicalOptionalTokenDispatch.rawTimeBound
                  problem.verifier).eval problem.input.length +
              (BuilderPhysicalOptionalTokenDispatch.rawTimeBound
                problem.verifier).eval problem.input.length :=
          Nat.add_le_add
            (inductionHypothesis (by omega))
            (stepCompiledSteps_le_rawTimeBound problem ⟨index, hIndex⟩)
        _ = (index + 1) *
              (BuilderPhysicalOptionalTokenDispatch.rawTimeBound
                problem.verifier).eval problem.input.length := by
          rw [Nat.succ_mul]

theorem totalCompiledSteps_le_rawTimeBound {language : Language}
    (problem : VerifierTableauProblem language) :
    totalCompiledSteps problem <=
      (rawTimeBound problem.verifier).eval problem.input.length := by
  rw [rawTimeBound_eval]
  exact accumulatedCompiledSteps_le problem (bodySlotCount problem)
    (Nat.le_refl _)

/-- M218 composes M217's one fixed physical dispatcher over every canonical
post-header opportunity.  It reaches the complete encoded formula, retains
M214's all-coordinate physical classifier evidence, proves every exact work
and compiled dispatch trace against the recursive prefix, and bounds their
aggregate cost by one source-size polynomial.  Canonical requests are still
constructed in Lean and the traces are not one literal raw-machine loop. -/
theorem cook_levin_builder_physical_dispatch_schedule_checked_complete
    {language : Language} (problem : VerifierTableauProblem language) :
    physicalOutput problem (bodySlotCount problem) =
        encodeCNFTokens problem.formula /\
    (forall index outsideLeft,
      PhysicalStepHolds problem index outsideLeft) /\
    (forall index classifierWorkspace,
      BuilderPostDividerRawRouteClassifier.InRangeRouteClassifierHolds problem
        (scheduleCoordinate problem index) classifierWorkspace) /\
    totalCompiledSteps problem <=
      (rawTimeBound problem.verifier).eval problem.input.length := by
  refine ⟨physicalOutput_bodySlotCount_eq_encodeCNFTokens problem,
    physicalStepHolds problem, ?_, totalCompiledSteps_le_rawTimeBound problem⟩
  intro index classifierWorkspace
  exact BuilderPostDividerRawRouteClassifier.inRangeRouteClassifierHolds
    problem (scheduleCoordinate problem index) classifierWorkspace

end BuilderPhysicalDispatchSchedule

end CookLevin

end PNP.Concrete
