/-
Copyright (c) 2026 PNP Labs.

Canonical positive-cell grouping at the checked BN6/HB PCCMin boundary.

M196 derives the BN6 carrier and cut value from a checked BCEL-ready nucleus,
but still accepts already-grouped cells and every structural grouping proof.
This module accepts only a finite ledger of raw support lists and positive
payload atoms. The generic canonical grouping constructor normalizes supports
inside the checked carrier, builds singleton-consumer V54 systems, coalesces
equal footprints, and proves the complete M196 grouping interface.

The terminal problem, raw supports and payloads, checked table, claims, ranks,
route-clear equation, dependency data, and HB closure remain supplied. The
remaining activation mismatch is not converted to a gain or decreasing global
route. No complete PkgC construction, polynomial PCCMin, unconditional
ZeroSlack, CNFSAT-in-P, root theorem, or P = NP result is claimed.
-/

import PNP.PCCMinCheckedPacketBN6BCELDerivedFamily
import PNP.ResidualTerminalBN6CanonicalPositiveCellGrouping

namespace PNP
namespace DirectWire

/-! ## Positive cells over the exact checked BCEL carrier -/

/-- The M197 input ledger. Each entry contains one raw support and one positive
    payload atom; all BN6 consumer systems and grouping proofs are derived. -/
structure PCCMinCheckedPacketBN6BCELPositiveCells
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (problem : TerminalFiniteSaturatePositiveProblem candidate model)
    (terminalReady : TerminalFiniteBCELReadyCertificate problem)
    (rankCount : Nat) where
  cells : List (TerminalBN6PositiveCell
    (TerminalPrimitiveRecord inputs gates outputs profileWidth)
    (TerminalPacketSelectorFaithfulnessPayload rankCount)
    terminalReady.result.nucleus.anchors)

theorem PCCMinCheckedPacketBN6BCELPositiveCells.carrier_nodup
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {problem : TerminalFiniteSaturatePositiveProblem candidate model}
    {terminalReady : TerminalFiniteBCELReadyCertificate problem}
    (_positiveCells : PCCMinCheckedPacketBN6BCELPositiveCells
      problem terminalReady rankCount) :
    terminalReady.result.nucleus.anchors.Nodup := by
  simpa only [TerminalComputedBCELAnchorNucleus.requestAtoms] using
    terminalReady.result.requestAtoms_nodup

/-- Construct every M196 grouped-cell field from the raw positive ledger. -/
def PCCMinCheckedPacketBN6BCELPositiveCells.groupedCells
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {problem : TerminalFiniteSaturatePositiveProblem candidate model}
    {terminalReady : TerminalFiniteBCELReadyCertificate problem}
    (positiveCells : PCCMinCheckedPacketBN6BCELPositiveCells
      problem terminalReady rankCount) :
    PCCMinCheckedPacketBN6BCELGroupedCells
      problem terminalReady rankCount where
  groups := terminalBN6CanonicalPositiveGroups
    terminalReady.result.nucleus.anchors positiveCells.carrier_nodup
    positiveCells.cells
  groupCarrier := by
    intro group groupMember
    exact terminalBN6CanonicalPositiveGroups_carrier
      terminalReady.result.nucleus.anchors positiveCells.carrier_nodup
      positiveCells.cells group groupMember
  groupFootprintLarge := by
    intro group groupMember
    exact terminalBN6CanonicalPositiveGroups_footprintLarge
      terminalReady.result.nucleus.anchors positiveCells.carrier_nodup
      positiveCells.cells group groupMember
  groupFootprintsNodup :=
    terminalBN6CanonicalPositiveGroups_footprintsNodup
      terminalReady.result.nucleus.anchors positiveCells.carrier_nodup
      positiveCells.cells

/-- The constructed M196 family still uses the exact checked BCEL carrier. -/
theorem PCCMinCheckedPacketBN6BCELPositiveCells.groupedFamily_carrier
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {problem : TerminalFiniteSaturatePositiveProblem candidate model}
    {terminalReady : TerminalFiniteBCELReadyCertificate problem}
    (positiveCells : PCCMinCheckedPacketBN6BCELPositiveCells
      problem terminalReady rankCount) :
    positiveCells.groupedCells.family.carrier =
      terminalReady.result.nucleus.anchors := rfl

/-- The constructed M196 family still uses the exact positive BCEL defect. -/
theorem PCCMinCheckedPacketBN6BCELPositiveCells.groupedFamily_cutValue
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {problem : TerminalFiniteSaturatePositiveProblem candidate model}
    {terminalReady : TerminalFiniteBCELReadyCertificate problem}
    (positiveCells : PCCMinCheckedPacketBN6BCELPositiveCells
      problem terminalReady rankCount) :
    positiveCells.groupedCells.family.cutValue =
      problem.anchorProblem.toProblem.familyDefect
        terminalReady.result.nucleus.anchors := rfl

/-- Every raw positive payload survives in the constructed M196 group at its
    exact normalized footprint. -/
theorem PCCMinCheckedPacketBN6BCELPositiveCells.payload_preserved
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {problem : TerminalFiniteSaturatePositiveProblem candidate model}
    {terminalReady : TerminalFiniteBCELReadyCertificate problem}
    (positiveCells : PCCMinCheckedPacketBN6BCELPositiveCells
      problem terminalReady rankCount)
    (cell : TerminalBN6PositiveCell
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)
      (TerminalPacketSelectorFaithfulnessPayload rankCount)
      terminalReady.result.nucleus.anchors)
    (cellMember : cell ∈ positiveCells.cells) :
    ∃ group,
      group ∈ positiveCells.groupedCells.groups ∧
      group.footprint = cell.footprint ∧
      cell.payloadAtom ∈ group.atoms := by
  exact cell.exists_canonical_group positiveCells.carrier_nodup cellMember

/-! ## Checked Packet/HB data over the canonical grouping -/

/-- M197 data. Unlike M196, callers cannot supply grouped BN6 cells or any of
    the consumer-system and grouping certificates. -/
structure PCCMinCheckedPacketBN6BCELCanonicalGroupingHBData
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (rankCount : Nat) where
  problem : TerminalFiniteSaturatePositiveProblem candidate model
  terminalReady : TerminalFiniteBCELReadyCertificate problem
  positiveCells : PCCMinCheckedPacketBN6BCELPositiveCells
    problem terminalReady rankCount
  rawTable : TerminalPacketTypedRealizerTable candidate.toImplementation
    positiveCells.groupedCells.family rankCount
  claimsAccepted :
    rawTable.withComputedPacketSelectorFaithfulness.checkEveryClaim = true
  dependencyTable : TerminalPacketHBDependencyTable rankCount
  hbClosureAccepted : dependencyTable.checkNoOutcomeActiveClosure
    rawTable.withComputedPacketSelectorFaithfulness.environment = true
  routesClear : positiveCells.groupedCells.family.checkPacketSelectorRoutesClear
    rawTable.environment.rankOf = true

/-- Install the canonical grouping in M196's derived-family boundary. -/
def PCCMinCheckedPacketBN6BCELCanonicalGroupingHBData.toDerivedFamilyData
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (data : PCCMinCheckedPacketBN6BCELCanonicalGroupingHBData
      candidate model rankCount) :
    PCCMinCheckedPacketBN6BCELDerivedFamilyHBData
      candidate model rankCount where
  problem := data.problem
  terminalReady := data.terminalReady
  groupedCells := data.positiveCells.groupedCells
  rawTable := data.rawTable
  claimsAccepted := data.claimsAccepted
  dependencyTable := data.dependencyTable
  hbClosureAccepted := data.hbClosureAccepted
  routesClear := data.routesClear

/-- Public M197 endpoint: canonical finite grouping removes every supplied
    M196 grouping certificate while preserving its exact activation route or
    conditional ZeroSlack result. -/
theorem pccmin_checked_packet_bn6_bcel_canonical_grouping_route_or_zeroslack_checked_complete
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
        data.positiveCells.groupedCells.family.activationWeight cut ≠
          data.problem.anchorProblem.toProblem.familyDefect
            data.terminalReady.result.nucleus.anchors := by
  exact
    pccmin_checked_packet_bn6_bcel_derived_family_route_or_zeroslack_checked_complete
      data.toDerivedFamilyData silence

end DirectWire
end PNP
