import PNP.PCCMinCheckedPacketBN6BCELCanonicalGrouping

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire
namespace PCCMinCheckedPacketBN6BCELCanonicalGroupingRegression

/-! ## General carrier-normalized grouping -/

variable {Atom Payload : Type} [DecidableEq Atom]
variable {carrier : List Atom} (carrierNodup : carrier.Nodup)

example (support : List Atom) :
    (terminalBN6NormalizeSupport carrier support).Sublist carrier :=
  terminalBN6NormalizeSupport_sublist carrier support

example (support : List Atom) :
    (terminalBN6NormalizeSupport carrier support).Nodup :=
  terminalBN6NormalizeSupport_nodup carrierNodup support

variable (cell : TerminalBN6PositiveCell Atom Payload carrier)

example : cell.footprint.Sublist carrier := cell.footprint_sublist

example : cell.footprint.Nodup := cell.footprint_nodup carrierNodup

example : 2 ≤ cell.footprint.length := cell.footprintLarge

variable (footprint : List Atom)
variable (footprintSublist : footprint.Sublist carrier)
variable (footprintNodup : footprint.Nodup)

example :
    (terminalBN6SingletonConsumerSystem carrier carrierNodup footprint
      footprintSublist footprintNodup).singletonFootprint = footprint :=
  terminalBN6SingletonConsumerSystem_singletonFootprint
    carrier carrierNodup footprint footprintSublist footprintNodup

example :
    (terminalBN6SingletonConsumerSystem carrier carrierNodup footprint
      footprintSublist footprintNodup).DisjointPairsSingletonized :=
  terminalBN6SingletonConsumerSystem_singletonized
    carrier carrierNodup footprint footprintSublist footprintNodup

variable (cells : List (TerminalBN6PositiveCell Atom Payload carrier))

example : (terminalBN6CanonicalPositiveFootprints carrier cells).Nodup :=
  terminalBN6CanonicalPositiveFootprints_nodup carrier cells

example (candidateFootprint : List Atom) :
    candidateFootprint ∈ terminalBN6CanonicalPositiveFootprints carrier cells ↔
      ∃ sourceCell, sourceCell ∈ cells ∧
        sourceCell.footprint = candidateFootprint :=
  mem_terminalBN6CanonicalPositiveFootprints_iff
    carrier cells candidateFootprint

example :
    ((terminalBN6CanonicalPositiveGroups carrier carrierNodup cells).map
      TerminalBN6GroupedCell.footprint).Nodup :=
  terminalBN6CanonicalPositiveGroups_footprintsNodup
    carrier carrierNodup cells

example (group : TerminalBN6GroupedCell Atom Payload)
    (groupMember : group ∈
      terminalBN6CanonicalPositiveGroups carrier carrierNodup cells) :
    group.consumerSystem.carrier = carrier :=
  terminalBN6CanonicalPositiveGroups_carrier
    carrier carrierNodup cells group groupMember

example (group : TerminalBN6GroupedCell Atom Payload)
    (groupMember : group ∈
      terminalBN6CanonicalPositiveGroups carrier carrierNodup cells) :
    2 ≤ group.footprint.length :=
  terminalBN6CanonicalPositiveGroups_footprintLarge
    carrier carrierNodup cells group groupMember

example (sourceCell : TerminalBN6PositiveCell Atom Payload carrier)
    (sourceMember : sourceCell ∈ cells) :
    ∃ group,
      group ∈ terminalBN6CanonicalPositiveGroups carrier carrierNodup cells ∧
      group.footprint = sourceCell.footprint ∧
      sourceCell.payloadAtom ∈ group.atoms :=
  sourceCell.exists_canonical_group carrierNodup sourceMember

/-! ## Concrete normalization and duplicate coalescing fixture -/

private def firstPositiveCell :
    TerminalBN6PositiveCell Nat Nat [0, 1, 2] where
  support := [2, 0, 2]
  payloadAtom := { mass := 1, massPositive := by omega, payload := 7 }
  footprintLarge := by decide

private def secondPositiveCell :
    TerminalBN6PositiveCell Nat Nat [0, 1, 2] where
  support := [0, 2]
  payloadAtom := { mass := 2, massPositive := by omega, payload := 9 }
  footprintLarge := by decide

example : firstPositiveCell.footprint = [0, 2] := by decide

example : secondPositiveCell.footprint = [0, 2] := by decide

example :
    terminalBN6CanonicalPositiveFootprints [0, 1, 2]
      [firstPositiveCell, secondPositiveCell] = [[0, 2]] := by decide

example :
    (terminalBN6CanonicalPositiveGroups [0, 1, 2] (by decide)
      [firstPositiveCell, secondPositiveCell]).length = 1 := by decide

/-! ## PCCMin adapter and exact terminal boundary -/

variable {inputs gates outputs profileWidth rankCount : Nat}
variable {candidate : Candidate inputs gates outputs}
variable {model : TerminalCandidateSaturationModel
  (profileWidth := profileWidth) candidate}
variable {problem : TerminalFiniteSaturatePositiveProblem candidate model}
variable {terminalReady : TerminalFiniteBCELReadyCertificate problem}

variable (positiveCells : PCCMinCheckedPacketBN6BCELPositiveCells
  problem terminalReady rankCount)

example : positiveCells.groupedCells.family.carrier =
    terminalReady.result.nucleus.anchors :=
  positiveCells.groupedFamily_carrier

example : positiveCells.groupedCells.family.cutValue =
    problem.anchorProblem.toProblem.familyDefect
      terminalReady.result.nucleus.anchors :=
  positiveCells.groupedFamily_cutValue

example (sourceCell : TerminalBN6PositiveCell
    (TerminalPrimitiveRecord inputs gates outputs profileWidth)
    (TerminalPacketSelectorFaithfulnessPayload rankCount)
    terminalReady.result.nucleus.anchors)
    (sourceMember : sourceCell ∈ positiveCells.cells) :
    ∃ group,
      group ∈ positiveCells.groupedCells.groups ∧
      group.footprint = sourceCell.footprint ∧
      sourceCell.payloadAtom ∈ group.atoms :=
  positiveCells.payload_preserved sourceCell sourceMember

variable (data : PCCMinCheckedPacketBN6BCELCanonicalGroupingHBData
  candidate model rankCount)

example : PCCMinCheckedPacketBN6BCELDerivedFamilyHBData
    candidate model rankCount := data.toDerivedFamilyData

variable (silence : ∀ rank selector,
  selector ∈
    data.rawTable.withComputedPacketSelectorFaithfulness.selectorsAtRank rank →
  ∃ reason : TerminalPacketTypedRealizerBot
      data.positiveCells.groupedCells.family.PacketSelectorHandle rankCount,
    data.rawTable.withComputedPacketSelectorFaithfulness.checkedOutcome
        data.claimsAccepted selector = .blocked reason)

example :
    residualSlack candidate.toImplementation = 0 ∨
      ∃ cut,
        cut.Sublist data.terminalReady.result.nucleus.anchors ∧
        cut ≠ [] ∧
        cut ≠ data.terminalReady.result.nucleus.anchors ∧
        data.positiveCells.groupedCells.family.activationWeight cut ≠
          data.problem.anchorProblem.toProblem.familyDefect
            data.terminalReady.result.nucleus.anchors :=
  pccmin_checked_packet_bn6_bcel_canonical_grouping_route_or_zeroslack_checked_complete
    data silence

end PCCMinCheckedPacketBN6BCELCanonicalGroupingRegression
end DirectWire
end PNP
