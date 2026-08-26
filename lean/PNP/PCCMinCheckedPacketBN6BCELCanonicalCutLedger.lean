/-
Copyright (c) 2026 PNP Labs.

Raw cut-ledger form of the checked canonical BN6/HB PCCMin boundary.

M197 constructs the grouped BN6 family from supplied raw positive cells but
reports the remaining BCEL obstruction through the derived grouped activation
sum.  The generic cut-ledger conservation theorem proves that this sum is
exactly the direct crossing-mass sum of the raw cells.  The public endpoint can
therefore expose the remaining mismatch without a supplied grouping equation.

The terminal problem, raw cells, checked table, claims, ranks, route-clear
equation, dependency data, and HB closure remain supplied.  The raw cells are
not derived from terminal data, an activation mismatch is not converted to a
gain, and no polynomial PCCMin, unconditional ZeroSlack, CNFSAT-in-P, root
theorem, or P = NP result is claimed.
-/

import PNP.PCCMinCheckedPacketBN6BCELCanonicalGrouping
import PNP.ResidualTerminalBN6CanonicalCutLedger

namespace PNP
namespace DirectWire

/-- The M197 grouped family computes exactly the direct raw positive-cell cut
    ledger on every cut. -/
theorem PCCMinCheckedPacketBN6BCELPositiveCells.groupedFamily_activationWeight_eq_raw
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {problem : TerminalFiniteSaturatePositiveProblem candidate model}
    {terminalReady : TerminalFiniteBCELReadyCertificate problem}
    (positiveCells : PCCMinCheckedPacketBN6BCELPositiveCells
      problem terminalReady rankCount)
    (cut : List (TerminalPrimitiveRecord
      inputs gates outputs profileWidth)) :
    positiveCells.groupedCells.family.activationWeight cut =
      terminalBN6PositiveCellsActivationWeight
        terminalReady.result.nucleus.anchors positiveCells.cells cut := by
  change
    ((terminalBN6CanonicalPositiveGroups
      terminalReady.result.nucleus.anchors positiveCells.carrier_nodup
      positiveCells.cells).map fun group =>
        if group.consumerSystem.cutActivationBool cut then group.mass else 0).sum =
      terminalBN6PositiveCellsActivationWeight
        terminalReady.result.nucleus.anchors positiveCells.cells cut
  exact terminalBN6CanonicalPositiveGroups_activationWeight_eq_raw
    terminalReady.result.nucleus.anchors positiveCells.carrier_nodup
    positiveCells.cells cut

/-- Public M198 endpoint: checked selector silence yields either zero residual
    slack or a proper cut where the direct raw positive-cell crossing ledger
    differs from the checked BCEL defect. -/
theorem pccmin_checked_packet_bn6_bcel_canonical_cut_ledger_route_or_zeroslack_checked_complete
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (data : PCCMinCheckedPacketBN6BCELCanonicalGroupingHBData
      candidate model rankCount)
    (silence : ∀ rank selector,
      selector ∈
        data.rawTable.withComputedPacketSelectorFaithfulness.selectorsAtRank
          rank →
      ∃ reason : TerminalPacketTypedRealizerBot
          data.positiveCells.groupedCells.family.PacketSelectorHandle rankCount,
        data.rawTable.withComputedPacketSelectorFaithfulness.checkedOutcome
            data.claimsAccepted selector = .blocked reason) :
    residualSlack candidate.toImplementation = 0 ∨
      ∃ cut,
        cut.Sublist data.terminalReady.result.nucleus.anchors ∧
        cut ≠ [] ∧
        cut ≠ data.terminalReady.result.nucleus.anchors ∧
        terminalBN6PositiveCellsActivationWeight
            data.terminalReady.result.nucleus.anchors
            data.positiveCells.cells cut ≠
          data.problem.anchorProblem.toProblem.familyDefect
            data.terminalReady.result.nucleus.anchors := by
  obtain zeroSlack | ⟨cut, included, nonempty, proper, mismatch⟩ :=
    pccmin_checked_packet_bn6_bcel_canonical_grouping_route_or_zeroslack_checked_complete
      data silence
  · exact Or.inl zeroSlack
  · right
    rw [data.positiveCells.groupedFamily_activationWeight_eq_raw cut] at mismatch
    exact ⟨cut, included, nonempty, proper, mismatch⟩

end DirectWire
end PNP
