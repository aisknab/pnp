/-
Copyright (c) 2026 PNP Labs.

Finite proof-bearing composition of the five reconstructed terminal
`SaturatePositive` sub-obligations.  The input is an existing candidate-derived
BCEL anchor problem and an explicit proof that its normalized seed has positive
full slack.  The classifier either preserves full positivity and exposes the
whole-support projection outcome, or returns the exact first local interface,
origin/kernel/obligation, or remaining nontransparent route coordinate.

This is not the manuscript-wide `RW-SaturatePositive` theorem.  Local routes
are not mapped to the complete global outcome set, Package E, verified gains,
exact routes, strict descent, or RankWF.  No polynomial runtime, SAT-in-P, or
P = NP conclusion is claimed.
-/

import PNP.ResidualTerminalOriginKernelObligationRouting

namespace PNP
namespace DirectWire

/-! ## Proof-bearing finite problem -/

/-- Existing candidate-derived anchor data together with the positive starting
    premise required by the manuscript's saturation theorem. -/
structure TerminalFiniteSaturatePositiveProblem
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate) where
  anchorProblem : TerminalCandidateBCELAnchorProblem candidate model
  initialPositive :
    0 < (terminalSaturationCostSnapshot candidate model
      (terminalSaturateTrace
        (terminalCandidateSaturationSystem candidate model)
        anchorProblem.support.seed).normalizedSeed.reverse).fullSlack

/-- The exact production trace selected by the proof-bearing problem. -/
def TerminalFiniteSaturatePositiveProblem.trace
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (problem : TerminalFiniteSaturatePositiveProblem candidate model) :
    TerminalSaturationTrace inputs gates outputs profileWidth :=
  terminalSaturateTrace
    (terminalCandidateSaturationSystem candidate model)
    problem.anchorProblem.support.seed

/-! ## Total finite composition -/

/-- The finite composed result.  The two preserved branches distinguish an
    explicit checked-lift projection loss from a positive projection defect
    that enters the existing BCEL classifier. -/
inductive TerminalFiniteSaturatePositiveOutcome
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (problem : TerminalFiniteSaturatePositiveProblem candidate model) where
  | fullPositiveProjectionLost
      (allSafe : ∀ event, event ∈ problem.trace.events →
        TerminalSaturationClosureSafeStep candidate model event)
      (finalPositive :
        0 < (terminalSaturationCostSnapshot candidate model
          problem.trace.replayRecords).fullSlack)
      (loss : TerminalProjectionPositivityLoss
        problem.anchorProblem.toProblem)
  | projectionPositive
      (allSafe : ∀ event, event ∈ problem.trace.events →
        TerminalSaturationClosureSafeStep candidate model event)
      (finalPositive :
        0 < (terminalSaturationCostSnapshot candidate model
          problem.trace.replayRecords).fullSlack)
      (wholePositive : 0 < problem.anchorProblem.toProblem.familyDefect
        problem.anchorProblem.toProblem.anchorRecords)
      (bcel : TerminalBCELAnchorNucleusOutcome
        problem.anchorProblem.toProblem)
  | interfaceExposure
      (first : TerminalFirstSaturationClosureEvent candidate model
        problem.trace.events)
      (route : TerminalInterfaceExposureERoute
        candidate model first.event)
  | originKernelObligation
      (first : TerminalFirstSaturationClosureEvent candidate model
        problem.trace.events)
      (route : TerminalOriginKernelObligationClosureRoute
        candidate model first.event)
  | otherNontransparent
      (first : TerminalFirstSaturationClosureEvent candidate model
        problem.trace.events)
      (failure : TerminalOtherNontransparentSaturationFailure
        candidate model first.event)

/-- Compose exact-first closure routing, full-slack preservation, and the
    existing whole-support projection firewall. -/
def classifyTerminalFiniteSaturatePositive
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (problem : TerminalFiniteSaturatePositiveProblem candidate model) :
    TerminalFiniteSaturatePositiveOutcome candidate model problem :=
  match _routed : classifyTerminalSaturationClosureRouting
      candidate model problem.anchorProblem.support.seed with
  | .interfaceExposure first route => .interfaceExposure first route
  | .originKernelObligation first route =>
      .originKernelObligation first route
  | .otherNontransparent first failure =>
      .otherNontransparent first failure
  | .balanced allSafe =>
      let allTransparent : ∀ event, event ∈ problem.trace.events →
          TerminalTransparentSaturationStep candidate model event :=
        fun event member => (allSafe event member).transparent
      let finalPositive :
          0 < (terminalSaturationCostSnapshot candidate model
            problem.trace.replayRecords).fullSlack :=
        TerminalSaturationBalanceOutcome.balanced_fullPositive_preserved
          (allTransparent := allTransparent) problem.initialPositive
      match classifyTerminalCandidateSaturationPositivity
          problem.anchorProblem with
      | .projectionPositivityLost loss =>
          .fullPositiveProjectionLost allSafe finalPositive loss
      | .bcel wholePositive bcel =>
          .projectionPositive allSafe finalPositive wholePositive bcel

/-! ## Exact soundness surface -/

/-- Kernel proposition exposed by each finite composition branch. -/
def TerminalFiniteSaturatePositiveOutcome.Sound
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {problem : TerminalFiniteSaturatePositiveProblem candidate model}
    (outcome : TerminalFiniteSaturatePositiveOutcome
      candidate model problem) : Prop :=
  match outcome with
  | .fullPositiveProjectionLost _allSafe _finalPositive loss =>
      (∀ event, event ∈ problem.trace.events →
        TerminalSaturationClosureSafeStep candidate model event) ∧
      0 < (terminalSaturationCostSnapshot candidate model
        problem.trace.replayRecords).fullSlack ∧
      problem.anchorProblem.toProblem.familyDefect
        problem.anchorProblem.toProblem.anchorRecords = 0 ∧
      Nonempty (TerminalCheckedFullLift loss.comparison)
  | .projectionPositive _allSafe _finalPositive _wholePositive _bcel =>
      (∀ event, event ∈ problem.trace.events →
        TerminalSaturationClosureSafeStep candidate model event) ∧
      0 < (terminalSaturationCostSnapshot candidate model
        problem.trace.replayRecords).fullSlack ∧
      0 < problem.anchorProblem.toProblem.familyDefect
        problem.anchorProblem.toProblem.anchorRecords ∧
      Nonempty (TerminalBCELAnchorNucleusOutcome
        problem.anchorProblem.toProblem)
  | .interfaceExposure first route =>
      problem.trace.events =
          first.prior ++ first.event :: first.remaining ∧
        (∀ event, event ∈ first.prior →
          TerminalSaturationClosureSafeStep candidate model event) ∧
        route.Sound
  | .originKernelObligation first route =>
      problem.trace.events =
          first.prior ++ first.event :: first.remaining ∧
        (∀ event, event ∈ first.prior →
          TerminalSaturationClosureSafeStep candidate model event) ∧
        route.Sound
  | .otherNontransparent first _failure =>
      problem.trace.events =
          first.prior ++ first.event :: first.remaining ∧
        (∀ event, event ∈ first.prior →
          TerminalSaturationClosureSafeStep candidate model event) ∧
        ¬TerminalTransparentSaturationStep candidate model first.event ∧
        terminalCandidateInterfaceExposureCoordinate?
          candidate model first.event = none ∧
        terminalCandidateOriginKernelObligationCoordinate?
          candidate model first.event = none

/-- Every returned finite composition branch carries its exact checked facts. -/
theorem TerminalFiniteSaturatePositiveOutcome.sound
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {problem : TerminalFiniteSaturatePositiveProblem candidate model}
    (outcome : TerminalFiniteSaturatePositiveOutcome
      candidate model problem) : outcome.Sound := by
  cases outcome with
  | fullPositiveProjectionLost allSafe finalPositive loss =>
      exact ⟨allSafe, finalPositive, loss.defectZero,
        ⟨loss.checkedFullLift⟩⟩
  | projectionPositive allSafe finalPositive wholePositive bcel =>
      exact ⟨allSafe, finalPositive, wholePositive, ⟨bcel⟩⟩
  | interfaceExposure first route =>
      exact ⟨first.split, first.priorSafe, route.sound⟩
  | originKernelObligation first route =>
      exact ⟨first.split, first.priorSafe, route.sound⟩
  | otherNontransparent first failure =>
      exact ⟨first.split, first.priorSafe, failure.failure,
        failure.notInterface, failure.notClosure⟩

/-- Every proof-bearing finite problem has one total composed result. -/
theorem classifyTerminalFiniteSaturatePositive_exhaustive
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (problem : TerminalFiniteSaturatePositiveProblem candidate model) :
    Nonempty (TerminalFiniteSaturatePositiveOutcome
      candidate model problem) :=
  ⟨classifyTerminalFiniteSaturatePositive candidate model problem⟩

end DirectWire
end PNP
