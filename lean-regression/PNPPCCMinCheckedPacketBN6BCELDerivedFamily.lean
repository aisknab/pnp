import PNP.PCCMinCheckedPacketBN6BCELDerivedFamily

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire
namespace PCCMinCheckedPacketBN6BCELDerivedFamilyRegression

variable {inputs gates outputs profileWidth rankCount : Nat}
variable {candidate : Candidate inputs gates outputs}
variable {model : TerminalCandidateSaturationModel
  (profileWidth := profileWidth) candidate}
variable {problem : TerminalFiniteSaturatePositiveProblem candidate model}
variable {terminalReady : TerminalFiniteBCELReadyCertificate problem}

/-! ## BCEL-derived family skeleton -/

variable (grouped : PCCMinCheckedPacketBN6BCELGroupedCells
  problem terminalReady rankCount)

example : grouped.family.carrier = terminalReady.result.nucleus.anchors :=
  grouped.family_carrier

example : grouped.family.cutValue =
    problem.anchorProblem.toProblem.familyDefect
      terminalReady.result.nucleus.anchors :=
  grouped.family_cutValue

example : 0 < grouped.family.cutValue :=
  grouped.family.cutValuePositive

/-! ## Elimination of duplicate-data mismatch branches -/

variable (data : PCCMinCheckedPacketBN6BCELDerivedFamilyHBData
  candidate model rankCount)

example : data.toBCELActivationData.family.carrier =
    data.toBCELActivationData.bcelCarrier :=
  data.family_carrier_eq_bcelCarrier

example : data.toBCELActivationData.family.cutValue =
    data.toBCELActivationData.bcelDefect :=
  data.family_cutValue_eq_bcelDefect

example
    (cut : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (included : cut.Sublist data.bcelCarrier)
    (nonempty : cut ≠ [])
    (proper : cut ≠ data.bcelCarrier)
    (mismatch : data.groupedCells.family.activationWeight cut ≠
      data.bcelDefect) :
    PCCMinCheckedPacketBN6BCELDerivedFamilyRoute data :=
  .activationMismatch cut included nonempty proper mismatch

/-! ## Exact activation-route-or-ZeroSlack terminal boundary -/

variable (silence : ∀ rank selector,
  selector ∈
    data.rawTable.withComputedPacketSelectorFaithfulness.selectorsAtRank rank →
  ∃ reason : TerminalPacketTypedRealizerBot
      data.groupedCells.family.PacketSelectorHandle rankCount,
    data.rawTable.withComputedPacketSelectorFaithfulness.checkedOutcome
        data.claimsAccepted selector = .blocked reason)

example : PCCMinCheckedPacketBN6BCELDerivedFamilyRouteOrZeroSlack data :=
  data.routeOrZeroSlackOfSilence silence

example :
    residualSlack candidate.toImplementation = 0 ∨
      ∃ cut,
        cut.Sublist data.bcelCarrier ∧ cut ≠ [] ∧
        cut ≠ data.bcelCarrier ∧
        data.groupedCells.family.activationWeight cut ≠ data.bcelDefect :=
  pccmin_checked_packet_bn6_bcel_derived_family_route_or_zeroslack_checked_complete
    data silence

end PCCMinCheckedPacketBN6BCELDerivedFamilyRegression
end DirectWire
end PNP
