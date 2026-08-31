/-
Copyright (c) 2026 PNP Labs.

Complete semantic iteration of M215's proof-carrying post-header stages.

For every verifier and raw input, this module recursively consumes every
post-header opportunity in the canonical Cook--Levin token schedule.  Padding
is preserved, populated entries append exactly their selected token, the final
output is the complete encoded CNF token stream, and the aggregate staged work
is bounded by one source-size polynomial.

The recursion composes M215's independently checked physical classifier and
appender stages through Lean orchestration.  It is not one literal raw-machine
loop, does not bridge one stage's final tape directly into the next stage's
initial tape, and does not prove builder `RawRefinement`, package a
`PolynomialReduction`, prove `CNFSAT` in `P`, or prove `P = NP`.
-/

import PNP.Concrete.CookLevinBuilderPostDividerSelectedTokenLaunch

namespace PNP.Concrete

namespace CookLevin

namespace BuilderCompleteScheduleIteration

open BuilderFullScheduleCursorController
  BuilderPostDividerSelectedTokenLaunch

/-- Iterate the canonical post-header selection and append operation.  The
base prefix is the already constructed unary header. -/
def run {language : Language}
    (problem : VerifierTableauProblem language) : Nat -> List CNFToken
  | 0 => emittedPrefix problem 0
  | index + 1 =>
      match selectedEntry? problem index with
      | none => run problem index
      | some none => run problem index
      | some (some token) => run problem index ++ [token]

theorem run_succ {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    run problem (index + 1) =
      match selectedEntry? problem index with
      | none => run problem index
      | some none => run problem index
      | some (some token) => run problem index ++ [token] := by
  rfl

/-- Every bounded recursive prefix agrees exactly with the canonical emitted
schedule prefix. -/
theorem run_eq_emittedPrefix {language : Language}
    (problem : VerifierTableauProblem language) (count : Nat)
    (hCount : count <= bodySlotCount problem) :
    run problem count = emittedPrefix problem count := by
  induction count with
  | zero => rfl
  | succ index inductionHypothesis =>
      have hIndex : index < bodySlotCount problem := by omega
      let coordinate : Fin (bodySlotCount problem) := ⟨index, hIndex⟩
      rw [run_succ, inductionHypothesis (by omega)]
      have hSelected := selectedEntry?_eq_some_getElem problem coordinate
      have hPrefix := emittedPrefix_succ problem coordinate
      have hSelectedAtIndex :
          selectedEntry? problem index =
            some (scheduleEntry problem coordinate) := by
        simpa [coordinate] using hSelected
      rw [hSelectedAtIndex]
      cases hEntry : scheduleEntry problem coordinate with
      | none =>
          rw [hEntry] at hPrefix
          simpa [coordinate, hEntry] using hPrefix.symm
      | some token =>
          rw [hEntry] at hPrefix
          simpa [coordinate, hEntry] using hPrefix.symm

/-- The complete post-header prefix is the exact canonical formula encoding. -/
theorem emittedPrefix_bodySlotCount_eq_encodeCNFTokens
    {language : Language} (problem : VerifierTableauProblem language) :
    emittedPrefix problem (bodySlotCount problem) =
      encodeCNFTokens problem.formula := by
  unfold emittedPrefix
  rw [firstBodySlot_add_bodySlotCount, terminalSlot_eq,
    problem.formulaTokenSlotCountDirect_eq, List.take_length]
  exact problem.formulaTokenSchedule_emit_eq_encodeCNFTokens

/-- The recursive all-coordinate pass returns the complete encoded formula
token stream. -/
theorem run_bodySlotCount_eq_encodeCNFTokens
    {language : Language} (problem : VerifierTableauProblem language) :
    run problem (bodySlotCount problem) =
      encodeCNFTokens problem.formula := by
  rw [run_eq_emittedPrefix problem (bodySlotCount problem) (Nat.le_refl _),
    emittedPrefix_bodySlotCount_eq_encodeCNFTokens]

/-- Accumulate the exact compiled classifier/appender work over a bounded
prefix of post-header schedule coordinates. -/
def accumulatedStagedCompiledSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat -> Nat
  | 0 => 0
  | index + 1 =>
      if hIndex : index < bodySlotCount problem then
        accumulatedStagedCompiledSteps problem index +
          BuilderPostDividerSelectedTokenLaunch.stagedCompiledSteps problem
            ⟨index, hIndex⟩
      else
        accumulatedStagedCompiledSteps problem index

/-- Total accounted work over the complete post-header schedule. -/
def totalStagedCompiledSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  accumulatedStagedCompiledSteps problem (bodySlotCount problem)

/-- The number of post-header opportunities multiplied by M215's uniform
per-coordinate polynomial. -/
def rawTimeBound {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .mul (bodySlotCountPolynomial verifier)
    (BuilderPostDividerSelectedTokenLaunch.rawTimeBound verifier)

theorem rawTimeBound_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (rawTimeBound problem.verifier).eval problem.input.length =
      bodySlotCount problem *
        (BuilderPostDividerSelectedTokenLaunch.rawTimeBound
          problem.verifier).eval problem.input.length := by
  rfl

theorem accumulatedStagedCompiledSteps_le
    {language : Language} (problem : VerifierTableauProblem language)
    (count : Nat) (hCount : count <= bodySlotCount problem) :
    accumulatedStagedCompiledSteps problem count <=
      count *
        (BuilderPostDividerSelectedTokenLaunch.rawTimeBound
          problem.verifier).eval problem.input.length := by
  induction count with
  | zero => simp [accumulatedStagedCompiledSteps]
  | succ index inductionHypothesis =>
      have hIndex : index < bodySlotCount problem := by omega
      rw [accumulatedStagedCompiledSteps, dif_pos hIndex, Nat.succ_mul]
      exact Nat.add_le_add
        (inductionHypothesis (by omega))
        (stagedCompiledSteps_le_rawTimeBound problem ⟨index, hIndex⟩)

/-- Summing every canonical stage remains bounded by one polynomial in the
encoded source input size. -/
theorem totalStagedCompiledSteps_le_rawTimeBound
    {language : Language} (problem : VerifierTableauProblem language) :
    totalStagedCompiledSteps problem <=
      (rawTimeBound problem.verifier).eval problem.input.length := by
  rw [rawTimeBound_eval]
  exact accumulatedStagedCompiledSteps_le problem
    (bodySlotCount problem) (Nat.le_refl _)

/-- M216 closes the complete semantic schedule-iteration boundary.  The
canonical input derives every coordinate and token, the recursion reaches
the exact full encoding, every constituent stage retains M215's physical
classifier/appender evidence for arbitrary workspace, and their aggregate
compiled work has one source-size polynomial bound.  This remains executable
Lean orchestration, not a literal single raw loop or a builder refinement. -/
theorem cook_levin_builder_complete_schedule_iteration_checked_complete
    {language : Language} (problem : VerifierTableauProblem language) :
    run problem (bodySlotCount problem) =
        encodeCNFTokens problem.formula /\
    (forall index classifierWorkspace outsideLeft,
      BuilderPostDividerSelectedTokenLaunch.PostDividerEmissionHolds
        problem index classifierWorkspace outsideLeft) /\
    totalStagedCompiledSteps problem <=
      (rawTimeBound problem.verifier).eval problem.input.length := by
  exact ⟨run_bodySlotCount_eq_encodeCNFTokens problem,
    BuilderPostDividerSelectedTokenLaunch.postDividerEmissionHolds problem,
    totalStagedCompiledSteps_le_rawTimeBound problem⟩

end BuilderCompleteScheduleIteration

end CookLevin

end PNP.Concrete
