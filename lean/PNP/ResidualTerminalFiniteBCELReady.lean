/-
Copyright (c) 2026 PNP Labs.

Checked composition from the finite terminal `SaturatePositive` classifier to
the computed BCEL-ready anchor nucleus.  The checker reruns the production
classifier and accepts only its positive-projection / ready-nucleus branch.
The resulting certificate retains the exact classifier equality, safe
saturation trace, positive final slack, positive whole-support projection
defect, and computed BCEL nucleus.

The proof-bearing terminal candidate, saturation model, anchor problem, and
initial positive full-slack premise remain explicit inputs.  Rejecting every
other finite classifier branch is not a proof that those local branches map to
the complete manuscript route system.  This module does not construct BN3--BN6
data, derive constant activation, prove ZeroSlack, PCCMin, polynomial runtime,
SAT in P, or P = NP.
-/

import PNP.ResidualTerminalFiniteSaturatePositive

namespace PNP
namespace DirectWire

/-! ## Exact checked ready branch -/

/-- Proof-bearing successful branch selected by the production finite
    `SaturatePositive` classifier and its nested BCEL classifier.  The
    `selected` equality prevents a detached caller-supplied ready nucleus. -/
structure TerminalFiniteBCELReadyCertificate
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (problem : TerminalFiniteSaturatePositiveProblem candidate model) where
  allSafe : ∀ event, event ∈ problem.trace.events →
    TerminalSaturationClosureSafeStep candidate model event
  finalPositive :
    0 < (terminalSaturationCostSnapshot candidate model
      problem.trace.replayRecords).fullSlack
  wholePositive : 0 < problem.anchorProblem.toProblem.familyDefect
    problem.anchorProblem.toProblem.anchorRecords
  result : TerminalComputedBCELAnchorNucleus problem.anchorProblem.toProblem
  selected : classifyTerminalFiniteSaturatePositive candidate model problem =
    .projectionPositive allSafe finalPositive wholePositive (.ready result)

/-- Recompute both nested classifiers and accept exactly the finite
    positive-projection branch whose computed anchor nucleus is ready. -/
def checkTerminalFiniteBCELReady
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (problem : TerminalFiniteSaturatePositiveProblem candidate model) : Bool :=
  match classifyTerminalFiniteSaturatePositive candidate model problem with
  | .projectionPositive _allSafe _finalPositive _wholePositive (.ready _result) =>
      true
  | _ => false

/-- Acceptance reconstructs the exact proof-bearing ready branch selected by
    the production classifier.  No caller Boolean or detached nucleus is
    trusted. -/
theorem terminal_finite_saturate_positive_bcel_ready_checked_complete
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (problem : TerminalFiniteSaturatePositiveProblem candidate model)
    (accepted : checkTerminalFiniteBCELReady candidate model problem = true) :
    Nonempty (TerminalFiniteBCELReadyCertificate problem) := by
  generalize selected :
      classifyTerminalFiniteSaturatePositive candidate model problem = outcome
  cases outcome with
  | fullPositiveProjectionLost allSafe finalPositive loss =>
      simp [checkTerminalFiniteBCELReady, selected] at accepted
  | interfaceExposure first route =>
      simp [checkTerminalFiniteBCELReady, selected] at accepted
  | originKernelObligation first route =>
      simp [checkTerminalFiniteBCELReady, selected] at accepted
  | otherNontransparent first failure =>
      simp [checkTerminalFiniteBCELReady, selected] at accepted
  | projectionPositive allSafe finalPositive wholePositive bcel =>
      cases bcel with
      | insufficient failure =>
          simp [checkTerminalFiniteBCELReady, selected] at accepted
      | algebraFailure nucleus first failure =>
          simp [checkTerminalFiniteBCELReady, selected] at accepted
      | cutDefectFailure nucleus first failure =>
          simp [checkTerminalFiniteBCELReady, selected] at accepted
      | cutRouteFailure nucleus first failure =>
          simp [checkTerminalFiniteBCELReady, selected] at accepted
      | ready result =>
          exact ⟨
            { allSafe := allSafe
              finalPositive := finalPositive
              wholePositive := wholePositive
              result := result
              selected := selected }⟩

/-- A checked finite ready branch exposes the minimum-cardinality positive
    nucleus size required for nontrivial BCEL cuts. -/
theorem TerminalFiniteBCELReadyCertificate.anchorSizeAtLeastTwo
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {problem : TerminalFiniteSaturatePositiveProblem candidate model}
    (certificate : TerminalFiniteBCELReadyCertificate problem) :
    2 <= certificate.result.nucleus.anchors.length :=
  certificate.result.anchorSizeAtLeastTwo

/-- A checked finite ready branch exposes the exact constant-cut equation for
    every oriented nonempty proper cut of its computed nucleus. -/
theorem TerminalFiniteBCELReadyCertificate.properCutConstantEquation
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {problem : TerminalFiniteSaturatePositiveProblem candidate model}
    (certificate : TerminalFiniteBCELReadyCertificate problem)
    (cut : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (proper : TerminalBCELProperCutSeed
      certificate.result.nucleus.anchors cut) :
    ((problem.anchorProblem.toProblem.cutCarrier
      certificate.result.nucleus.anchors cut).optimizationCorners
        problem.anchorProblem.toProblem.observe).projectionExcess =
      Int.ofNat (problem.anchorProblem.toProblem.familyDefect
        certificate.result.nucleus.anchors) :=
  certificate.result.properCutConstantEquation cut proper

/-- A checked finite ready branch exposes the complete local full/quotient BN2
    conclusion for every oriented nonempty proper cut. -/
theorem TerminalFiniteBCELReadyCertificate.properCutLocalConclusion
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {problem : TerminalFiniteSaturatePositiveProblem candidate model}
    (certificate : TerminalFiniteBCELReadyCertificate problem)
    (cut : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (proper : TerminalBCELProperCutSeed
      certificate.result.nucleus.anchors cut) :
    TerminalComputedBN2LocalConclusion
      (problem.anchorProblem.toProblem.cutCarrier
        certificate.result.nucleus.anchors cut)
      problem.anchorProblem.toProblem.observe :=
  certificate.result.properCutLocalConclusion cut proper

end DirectWire
end PNP
