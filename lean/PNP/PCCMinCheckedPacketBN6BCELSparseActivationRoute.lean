/-
Copyright (c) 2026 PNP Labs.

Sparse proper-cut activation routing at the checked BN6/BCEL/HB PCCMin
boundary.

M198 retains an exact raw positive-cell cut ledger but finds a mismatch by
scanning every proper subset. M199 removes that scan on its accepted shape
basis branch but returns only a structural basis obstruction otherwise. The
quadratic singleton/pair classifier now supplies either the complete V53
constant-cut equation or one exact small proper-cut mismatch. This adapter
reflects that mismatch into the raw ledger and reuses M199 only on the
coherent branch.

The raw cells, payloads, checked table, ranks, dependency data, route-clear
result, and HB closure remain supplied. A mismatch is not a verified gain or
globally decreasing route, and no complete polynomial PCCMin or unconditional
ZeroSlack result is claimed.
-/

import PNP.PCCMinCheckedPacketBN6BCELCanonicalConstantCutBasis
import PNP.ResidualTerminalV53SparseProperCutBasis

namespace PNP
namespace DirectWire

/-- Exact small-cut obstruction reflected through M198's direct raw positive-
    cell activation ledger. -/
structure PCCMinCheckedPacketBN6BCELSparseActivationMismatch
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (data : PCCMinCheckedPacketBN6BCELCanonicalGroupingHBData
      candidate model rankCount) where
  cut : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)
  included : cut.Sublist data.terminalReady.result.nucleus.anchors
  nonempty : cut ≠ []
  proper : cut ≠ data.terminalReady.result.nucleus.anchors
  length_le_two : cut.length ≤ 2
  rawMismatch :
    terminalBN6PositiveCellsActivationWeight
        data.terminalReady.result.nucleus.anchors
        data.positiveCells.cells cut ≠
      data.problem.anchorProblem.toProblem.familyDefect
        data.terminalReady.result.nucleus.anchors

/-- Total checked result of the sparse activation-route boundary. -/
inductive PCCMinCheckedPacketBN6BCELSparseActivationRouteOrZeroSlack
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (data : PCCMinCheckedPacketBN6BCELCanonicalGroupingHBData
      candidate model rankCount) where
  | zeroSlack (result : ZeroSlackResult candidate.toImplementation)
  | activationRoute
      (route : PCCMinCheckedPacketBN6BCELSparseActivationMismatch data)

/-- Run the quadratic singleton/pair classifier. Only its complete coherent
    branch may enter the existing checked Packet/HB contradiction. -/
def PCCMinCheckedPacketBN6BCELCanonicalGroupingHBData.sparseActivationRouteOrZeroSlackOfSilence
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
    PCCMinCheckedPacketBN6BCELSparseActivationRouteOrZeroSlack data := by
  let system := data.positiveCells.groupedCells.family.hypergraph
  have carrierAtLeastTwo : 2 ≤ system.carrier.length := by
    change 2 ≤ data.positiveCells.groupedCells.family.carrier.length
    rw [data.positiveCells.groupedFamily_carrier]
    exact data.terminalReady.anchorSizeAtLeastTwo
  match classified : classifyTerminalV53SmallProperCuts system with
  | .insufficient carrierSmall => exact False.elim (by omega)
  | .coherent constant =>
      have basis : system.CanonicalConstantCutBasis :=
        (terminalV53_canonicalConstantCutBasis_iff_constantProperCuts
          system carrierAtLeastTwo).2 constant
      exact .zeroSlack
        ((data.toBN6HBZeroSlackDataOfCanonicalCutBasis basis
          ).zeroSlackOfSilence silence)
  | .routed route =>
      have rawMismatch :
          terminalBN6PositiveCellsActivationWeight
              data.terminalReady.result.nucleus.anchors
              data.positiveCells.cells route.cut ≠
            data.problem.anchorProblem.toProblem.familyDefect
              data.terminalReady.result.nucleus.anchors := by
        intro rawEqual
        apply route.mismatch
        calc
          system.cutWeight route.cut =
              terminalBN6PositiveCellsActivationWeight
                data.terminalReady.result.nucleus.anchors
                data.positiveCells.cells route.cut :=
            data.positiveCells.groupedHypergraph_cutWeight_eq_raw route.cut
          _ = data.problem.anchorProblem.toProblem.familyDefect
                data.terminalReady.result.nucleus.anchors := rawEqual
          _ = system.cutValue :=
            data.positiveCells.groupedFamily_cutValue.symm
      exact .activationRoute
        { cut := route.cut
          included := by
            rw [← data.positiveCells.groupedFamily_carrier]
            exact route.proper.1
          nonempty := route.proper.2.1
          proper := by
            intro cutCarrier
            apply route.proper.2.2
            change route.cut =
              data.positiveCells.groupedCells.family.carrier
            rw [data.positiveCells.groupedFamily_carrier]
            exact cutCarrier
          length_le_two := route.length_le_two
          rawMismatch := rawMismatch }

/-- Public M200 endpoint: complete exact-rank selector silence yields genuine
    zero residual slack or one explicit singleton/pair proper cut where the
    direct raw activation ledger differs from the checked BCEL defect. -/
theorem pccmin_checked_packet_bn6_bcel_sparse_activation_route_or_zeroslack_checked_complete
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
        cut.length ≤ 2 ∧
        terminalBN6PositiveCellsActivationWeight
            data.terminalReady.result.nucleus.anchors
            data.positiveCells.cells cut ≠
          data.problem.anchorProblem.toProblem.familyDefect
            data.terminalReady.result.nucleus.anchors := by
  exact match data.sparseActivationRouteOrZeroSlackOfSilence silence with
    | .zeroSlack result => Or.inl result.sound
    | .activationRoute route =>
        Or.inr ⟨route.cut, route.included, route.nonempty, route.proper,
          route.length_le_two, route.rawMismatch⟩

end DirectWire
end PNP
