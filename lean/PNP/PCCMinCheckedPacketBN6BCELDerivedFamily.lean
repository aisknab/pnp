/-
Copyright (c) 2026 PNP Labs.

BCEL-derived grouped-family boundary for the checked BN6/HB PCCMin route.

M195 accepts a complete grouped BN6 family and then compares its carrier and
cut value with the checked finite BCEL-ready nucleus. This module removes those
two independent inputs. A grouped-cell ledger supplies only the surviving
positive cells and their structural grouping facts; its BN6 family takes the
carrier and positive cut value definitionally from the checked BCEL result.
Consequently the only remaining linkage failure is a genuine proper-cut
activation mismatch.

The terminal problem, checked ready certificate, grouped cells and payloads,
table, claims, ranks, route-clear equation, dependency data, and HB closure
remain supplied. The activation mismatch is not compiled to a gain or a
decreasing global route, the inherited finite cut scan may be exponential, and
no unconditional ZeroSlack, polynomial PCCMin, CNFSAT-in-P, root theorem, or
P = NP result is claimed.
-/

import PNP.PCCMinCheckedPacketBN6BCELActivationRoute

namespace PNP
namespace DirectWire

/-! ## Grouped cells over the exact checked BCEL carrier -/

/-- The remaining BN6 grouping input after the carrier and cut value have been
fixed by one checked finite BCEL-ready nucleus. -/
structure PCCMinCheckedPacketBN6BCELGroupedCells
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (problem : TerminalFiniteSaturatePositiveProblem candidate model)
    (terminalReady : TerminalFiniteBCELReadyCertificate problem)
    (rankCount : Nat) where
  groups : List (TerminalBN6GroupedCell
    (TerminalPrimitiveRecord inputs gates outputs profileWidth)
    (TerminalPacketSelectorFaithfulnessPayload rankCount))
  groupCarrier : ∀ cell, cell ∈ groups →
    cell.consumerSystem.carrier = terminalReady.result.nucleus.anchors
  groupFootprintLarge : ∀ cell, cell ∈ groups →
    2 ≤ cell.footprint.length
  groupFootprintsNodup : (groups.map
    TerminalBN6GroupedCell.footprint).Nodup

/-- Construct the BN6 family skeleton from checked BCEL data. The carrier,
carrier uniqueness, cut value, and cut-value positivity are not caller fields. -/
def PCCMinCheckedPacketBN6BCELGroupedCells.family
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {problem : TerminalFiniteSaturatePositiveProblem candidate model}
    {terminalReady : TerminalFiniteBCELReadyCertificate problem}
    (grouped : PCCMinCheckedPacketBN6BCELGroupedCells
      problem terminalReady rankCount) :
    TerminalBN6GroupedFamily
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)
      (TerminalPacketSelectorFaithfulnessPayload rankCount) where
  carrier := terminalReady.result.nucleus.anchors
  carrierNodup := by
    simpa only [TerminalComputedBCELAnchorNucleus.requestAtoms] using
      terminalReady.result.requestAtoms_nodup
  groups := grouped.groups
  groupCarrier := grouped.groupCarrier
  groupFootprintLarge := grouped.groupFootprintLarge
  groupFootprintsNodup := grouped.groupFootprintsNodup
  cutValue := problem.anchorProblem.toProblem.familyDefect
    terminalReady.result.nucleus.anchors
  cutValuePositive := terminalReady.result.nucleus.positive

/-- The constructed Packet family uses the exact computed BCEL carrier. -/
theorem PCCMinCheckedPacketBN6BCELGroupedCells.family_carrier
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {problem : TerminalFiniteSaturatePositiveProblem candidate model}
    {terminalReady : TerminalFiniteBCELReadyCertificate problem}
    (grouped : PCCMinCheckedPacketBN6BCELGroupedCells
      problem terminalReady rankCount) :
    grouped.family.carrier = terminalReady.result.nucleus.anchors := rfl

/-- The constructed Packet family uses the exact positive BCEL defect. -/
theorem PCCMinCheckedPacketBN6BCELGroupedCells.family_cutValue
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {problem : TerminalFiniteSaturatePositiveProblem candidate model}
    {terminalReady : TerminalFiniteBCELReadyCertificate problem}
    (grouped : PCCMinCheckedPacketBN6BCELGroupedCells
      problem terminalReady rankCount) :
    grouped.family.cutValue =
      problem.anchorProblem.toProblem.familyDefect
        terminalReady.result.nucleus.anchors := rfl

/-! ## Checked Packet/HB data over the derived family -/

/-- M196 data. Unlike M195, it has no independently supplied grouped family:
only a grouped-cell ledger is accepted before the checked table and HB data. -/
structure PCCMinCheckedPacketBN6BCELDerivedFamilyHBData
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (rankCount : Nat) where
  problem : TerminalFiniteSaturatePositiveProblem candidate model
  terminalReady : TerminalFiniteBCELReadyCertificate problem
  groupedCells : PCCMinCheckedPacketBN6BCELGroupedCells
    problem terminalReady rankCount
  rawTable : TerminalPacketTypedRealizerTable candidate.toImplementation
    groupedCells.family rankCount
  claimsAccepted :
    rawTable.withComputedPacketSelectorFaithfulness.checkEveryClaim = true
  dependencyTable : TerminalPacketHBDependencyTable rankCount
  hbClosureAccepted : dependencyTable.checkNoOutcomeActiveClosure
    rawTable.withComputedPacketSelectorFaithfulness.environment = true
  routesClear : groupedCells.family.checkPacketSelectorRoutesClear
    rawTable.environment.rankOf = true

/-- The exact BCEL carrier inherited by the derived Packet family. -/
def PCCMinCheckedPacketBN6BCELDerivedFamilyHBData.bcelCarrier
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (data : PCCMinCheckedPacketBN6BCELDerivedFamilyHBData
      candidate model rankCount) :
    List (TerminalPrimitiveRecord inputs gates outputs profileWidth) :=
  data.terminalReady.result.nucleus.anchors

/-- The exact positive BCEL defect inherited by the derived Packet family. -/
def PCCMinCheckedPacketBN6BCELDerivedFamilyHBData.bcelDefect
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (data : PCCMinCheckedPacketBN6BCELDerivedFamilyHBData
      candidate model rankCount) : Nat :=
  data.problem.anchorProblem.toProblem.familyDefect data.bcelCarrier

/-- Install the BCEL-derived family in M195's checked activation boundary. -/
def PCCMinCheckedPacketBN6BCELDerivedFamilyHBData.toBCELActivationData
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (data : PCCMinCheckedPacketBN6BCELDerivedFamilyHBData
      candidate model rankCount) :
    PCCMinCheckedPacketBN6BCELHBData candidate model rankCount where
  problem := data.problem
  terminalReady := data.terminalReady
  family := data.groupedCells.family
  rawTable := data.rawTable
  claimsAccepted := data.claimsAccepted
  dependencyTable := data.dependencyTable
  hbClosureAccepted := data.hbClosureAccepted
  routesClear := data.routesClear

/-- M195's carrier comparison is definitionally true for the derived family. -/
theorem PCCMinCheckedPacketBN6BCELDerivedFamilyHBData.family_carrier_eq_bcelCarrier
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (data : PCCMinCheckedPacketBN6BCELDerivedFamilyHBData
      candidate model rankCount) :
    data.toBCELActivationData.family.carrier =
      data.toBCELActivationData.bcelCarrier := rfl

/-- M195's cut-value comparison is definitionally true for the derived family. -/
theorem PCCMinCheckedPacketBN6BCELDerivedFamilyHBData.family_cutValue_eq_bcelDefect
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (data : PCCMinCheckedPacketBN6BCELDerivedFamilyHBData
      candidate model rankCount) :
    data.toBCELActivationData.family.cutValue =
      data.toBCELActivationData.bcelDefect := rfl

/-! ## The one remaining route -/

/-- The only M195 linkage obstruction that can survive construction of the
family carrier and cut value from the checked BCEL nucleus. -/
inductive PCCMinCheckedPacketBN6BCELDerivedFamilyRoute
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (data : PCCMinCheckedPacketBN6BCELDerivedFamilyHBData
      candidate model rankCount) where
  | activationMismatch
      (cut : List
        (TerminalPrimitiveRecord inputs gates outputs profileWidth))
      (included : cut.Sublist data.bcelCarrier)
      (nonempty : cut ≠ [])
      (proper : cut ≠ data.bcelCarrier)
      (mismatch : data.groupedCells.family.activationWeight cut ≠
        data.bcelDefect)

/-- Total terminal result after eliminating M195's two artificial duplicate-
data mismatch branches. -/
inductive PCCMinCheckedPacketBN6BCELDerivedFamilyRouteOrZeroSlack
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (data : PCCMinCheckedPacketBN6BCELDerivedFamilyHBData
      candidate model rankCount) where
  | zeroSlack (result : ZeroSlackResult candidate.toImplementation)
  | activationRoute
      (route : PCCMinCheckedPacketBN6BCELDerivedFamilyRoute data)

/-- Reuse the complete M195 classifier. Carrier and cut-value mismatch cases
are impossible by construction; coherent and activation-mismatch cases retain
their exact checked meanings. -/
def PCCMinCheckedPacketBN6BCELDerivedFamilyHBData.routeOrZeroSlackOfSilence
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (data : PCCMinCheckedPacketBN6BCELDerivedFamilyHBData
      candidate model rankCount)
    (silence : ∀ rank selector,
      selector ∈
        data.rawTable.withComputedPacketSelectorFaithfulness.selectorsAtRank
          rank →
      ∃ reason : TerminalPacketTypedRealizerBot
          data.groupedCells.family.PacketSelectorHandle rankCount,
        data.rawTable.withComputedPacketSelectorFaithfulness.checkedOutcome
            data.claimsAccepted selector = .blocked reason) :
    PCCMinCheckedPacketBN6BCELDerivedFamilyRouteOrZeroSlack data :=
  match data.toBCELActivationData.routeOrZeroSlackOfSilence silence with
  | .zeroSlack result => .zeroSlack result
  | .activationRoute route =>
      match route with
      | .carrierMismatch mismatch =>
          False.elim (mismatch data.family_carrier_eq_bcelCarrier)
      | .cutValueMismatch _carrierBinding mismatch =>
          False.elim (mismatch data.family_cutValue_eq_bcelDefect)
      | .activationMismatch _carrierBinding _cutValueBinding cut included
          nonempty proper mismatch =>
          .activationRoute (.activationMismatch cut included nonempty proper
            mismatch)

/-- Public M196 endpoint: exact-rank selector silence yields either genuine
zero residual slack or a proper-cut activation mismatch. The independently
supplied carrier and cut-value mismatch alternatives no longer exist. -/
theorem pccmin_checked_packet_bn6_bcel_derived_family_route_or_zeroslack_checked_complete
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (data : PCCMinCheckedPacketBN6BCELDerivedFamilyHBData
      candidate model rankCount)
    (silence : ∀ rank selector,
      selector ∈
        data.rawTable.withComputedPacketSelectorFaithfulness.selectorsAtRank
          rank →
      ∃ reason : TerminalPacketTypedRealizerBot
          data.groupedCells.family.PacketSelectorHandle rankCount,
        data.rawTable.withComputedPacketSelectorFaithfulness.checkedOutcome
            data.claimsAccepted selector = .blocked reason) :
    residualSlack candidate.toImplementation = 0 ∨
      ∃ cut,
        cut.Sublist data.bcelCarrier ∧ cut ≠ [] ∧
        cut ≠ data.bcelCarrier ∧
        data.groupedCells.family.activationWeight cut ≠ data.bcelDefect := by
  exact match data.routeOrZeroSlackOfSilence silence with
    | .zeroSlack result => Or.inl result.sound
    | .activationRoute route => by
        right
        cases route with
        | activationMismatch cut included nonempty proper mismatch =>
            exact ⟨cut, included, nonempty, proper, mismatch⟩

end DirectWire
end PNP
