/-
Copyright (c) 2026 PNP Labs.

Computed fail-closed classification of the whole-support terminal projection
defect.  A zero defect returns an attained quotient minimum together with the
checked full lift that makes loss of positive projection defect explicit.  A
positive defect is passed, with its internally computed proof, to the existing
terminal BCEL anchor-nucleus classifier.

This closes only the pinned manuscript's
`projectionPositivityNotLostSilently` sub-obligation.  The input remains an
explicit finite terminal dependency system with an already computed governed,
proper-positive support, one forgetful projection, and one executable ambient
observer.  No full `SaturatePositive`, `BCELReady`, global route-completeness,
runtime, SAT-in-P, or P = NP claim is made.
-/

import PNP.ResidualTerminalBCELAnchorNucleus

namespace PNP
namespace DirectWire

/-! ## Canonical whole-support comparison -/

/-- The four-corner optimization family whose left corner is the complete
    canonical anchor family of the computed saturated support. -/
def TerminalBCELAnchorProblem.wholeCorners
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system) :
    TerminalProjectionFourCorners (inputs + gates) gates profileWidth :=
  (problem.carrier problem.anchorRecords []).optimizationCorners
    problem.observe

/-- The whole-corner projection defect is definitionally the BCEL problem's
    complete-anchor-family defect. -/
@[simp] theorem TerminalBCELAnchorProblem.wholeCorners_projectionDefect
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system) :
    terminalProjectionDefect problem.wholeCorners.system
        problem.wholeCorners.projection problem.wholeCorners.left =
      problem.familyDefect problem.anchorRecords := rfl

/-! ## Proof-bearing zero-defect boundary -/

/-- Loss of positive whole-support projection defect is explicit rather than
    silent: the defect is zero and an attained quotient minimum carries the
    checked full lift reconstructing every forgotten coordinate. -/
structure TerminalProjectionPositivityLoss
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system) where
  defectZero : problem.familyDefect problem.anchorRecords = 0
  comparison : TerminalQuotientComparison problem.wholeCorners.system
    problem.wholeCorners.projection problem.wholeCorners.left
  atMinimum : comparison.realization.implementation.gateCount =
    terminalQuotientProfileMinimum problem.wholeCorners.system
      problem.wholeCorners.projection problem.wholeCorners.left
  checkedFullLift : TerminalCheckedFullLift comparison

/-- Construct the exact checked-lift witness forced by zero whole-support
    projection defect. -/
def terminalProjectionPositivityLossOfZero
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (defectZero : problem.familyDefect problem.anchorRecords = 0) :
    TerminalProjectionPositivityLoss problem := by
  have wholeZero :
      terminalProjectionDefect problem.wholeCorners.system
          problem.wholeCorners.projection problem.wholeCorners.left = 0 := by
    simpa using defectZero
  have minimaEqual :=
    (terminalProjectionDefect_eq_zero_iff_minima_eq
      problem.wholeCorners.system problem.wholeCorners.projection
      problem.wholeCorners.left).mp wholeZero
  let full := terminalFullProfileMinimumRealization
    problem.wholeCorners.system problem.wholeCorners.left
  let comparison := full.project
    (projection := problem.wholeCorners.projection)
  exact
    { defectZero := defectZero
      comparison := comparison
      atMinimum := by
        rw [TerminalFullCarrierRealization.project_gateCount]
        rw [terminalFullProfileMinimumRealization_gateCount]
        exact minimaEqual.symm
      checkedFullLift := full.checkedFullLift }

/-- A reported positivity loss gives exact equality of the quotient and full
    exhaustive minima at the whole-support corner. -/
theorem TerminalProjectionPositivityLoss.minima_eq
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {problem : TerminalBCELAnchorProblem candidate system}
    (loss : TerminalProjectionPositivityLoss problem) :
    terminalQuotientProfileMinimum problem.wholeCorners.system
        problem.wholeCorners.projection problem.wholeCorners.left =
      terminalFullProfileMinimum problem.wholeCorners.system
        problem.wholeCorners.left := by
  apply (terminalProjectionDefect_eq_zero_iff_minima_eq
    problem.wholeCorners.system problem.wholeCorners.projection
    problem.wholeCorners.left).mp
  simpa using loss.defectZero

/-! ## Total saturation-positivity firewall -/

/-- Total computed split at the terminal saturation-to-BCEL boundary. -/
inductive TerminalSaturationPositivityOutcome
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system) where
  | projectionPositivityLost
      (loss : TerminalProjectionPositivityLoss problem)
  | bcel
      (wholePositive : 0 < problem.familyDefect problem.anchorRecords)
      (outcome : TerminalBCELAnchorNucleusOutcome problem)

/-- Compute the whole-support defect.  Zero returns its checked lift; positive
    defect invokes the existing fail-closed BCEL classifier with no caller
    proof and without changing the BCEL failure scan. -/
def classifyTerminalSaturationPositivity
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system) :
    TerminalSaturationPositivityOutcome problem :=
  if defectZero : problem.familyDefect problem.anchorRecords = 0 then
    .projectionPositivityLost
      (terminalProjectionPositivityLossOfZero problem defectZero)
  else
    let wholePositive := Nat.pos_of_ne_zero defectZero
    .bcel wholePositive
      (classifyTerminalBCELAnchorNucleus problem wholePositive)

/-- Zero whole-support defect always selects the explicit checked-lift branch. -/
theorem classifyTerminalSaturationPositivity_loss_of_zero
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (defectZero : problem.familyDefect problem.anchorRecords = 0) :
    ∃ loss : TerminalProjectionPositivityLoss problem,
      classifyTerminalSaturationPositivity problem =
        .projectionPositivityLost loss := by
  refine ⟨terminalProjectionPositivityLossOfZero problem defectZero, ?_⟩
  unfold classifyTerminalSaturationPositivity
  rw [dif_pos defectZero]

/-- Positive whole-support defect delegates exactly to the existing BCEL
    classifier and retains its proof-bearing outcome. -/
theorem classifyTerminalSaturationPositivity_bcel_of_positive
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (wholePositive : 0 < problem.familyDefect problem.anchorRecords) :
    ∃ positive : 0 < problem.familyDefect problem.anchorRecords,
      classifyTerminalSaturationPositivity problem =
        .bcel positive
          (classifyTerminalBCELAnchorNucleus problem positive) := by
  have defectNotZero :
      problem.familyDefect problem.anchorRecords ≠ 0 :=
    Nat.ne_of_gt wholePositive
  unfold classifyTerminalSaturationPositivity
  rw [dif_neg defectNotZero]
  exact ⟨Nat.pos_of_ne_zero defectNotZero, rfl⟩

/-- In the positive branch no attained quotient minimum can silently carry a
    checked full lift. -/
theorem terminalSaturationPositivity_no_checkedFullLiftAtMinimum
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (wholePositive : 0 < problem.familyDefect problem.anchorRecords)
    (comparison : TerminalQuotientComparison problem.wholeCorners.system
      problem.wholeCorners.projection problem.wholeCorners.left)
    (atMinimum : comparison.realization.implementation.gateCount =
      terminalQuotientProfileMinimum problem.wholeCorners.system
        problem.wholeCorners.projection problem.wholeCorners.left) :
    ¬TerminalCheckedFullLift comparison := by
  apply terminalProjectionDefect_pos_no_checkedFullLiftAtMinimum
    problem.wholeCorners.system problem.wholeCorners.projection
    problem.wholeCorners.left
  · simpa using wholePositive
  · exact atMinimum

/-- Every finite terminal problem is classified; there is no silent third
    whole-support projection-defect case. -/
theorem classifyTerminalSaturationPositivity_exhaustive
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system) :
    Nonempty (TerminalSaturationPositivityOutcome problem) :=
  ⟨classifyTerminalSaturationPositivity problem⟩

end DirectWire
end PNP
