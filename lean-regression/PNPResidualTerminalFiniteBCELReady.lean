import PNP.ResidualTerminalFiniteBCELReady

namespace PNP
namespace DirectWire

/-! The public theorem is polymorphic over every finite proof-bearing terminal
    problem.  Its sole acceptance premise is the recomputed production checker;
    no caller-supplied success flag or detached nucleus enters the result. -/

example
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (problem : TerminalFiniteSaturatePositiveProblem candidate model)
    (accepted : checkTerminalFiniteBCELReady candidate model problem = true) :
    Nonempty (TerminalFiniteBCELReadyCertificate problem) :=
  terminal_finite_saturate_positive_bcel_ready_checked_complete
    candidate model problem accepted

example
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {problem : TerminalFiniteSaturatePositiveProblem candidate model}
    (certificate : TerminalFiniteBCELReadyCertificate problem) :
    (∀ event, event ∈ problem.trace.events →
      TerminalSaturationClosureSafeStep candidate model event) ∧
    0 < (terminalSaturationCostSnapshot candidate model
      problem.trace.replayRecords).fullSlack ∧
    0 < problem.anchorProblem.toProblem.familyDefect
      problem.anchorProblem.toProblem.anchorRecords ∧
    2 <= certificate.result.nucleus.anchors.length := by
  exact ⟨certificate.allSafe, certificate.finalPositive,
    certificate.wholePositive, certificate.anchorSizeAtLeastTwo⟩

example
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
  certificate.properCutConstantEquation cut proper

end DirectWire
end PNP
