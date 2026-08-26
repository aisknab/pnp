import PNP.PCCMinCheckedPacketBN6BCELCanonicalCutLedger

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire
namespace PCCMinCheckedPacketBN6BCELCanonicalCutLedgerRegression

/-! ## General raw-ledger conservation -/

variable {Atom Payload : Type} [DecidableEq Atom]
variable {carrier : List Atom} (carrierNodup : carrier.Nodup)
variable (cells : List (TerminalBN6PositiveCell Atom Payload carrier))
variable (cut : List Atom)

example (cell : TerminalBN6PositiveCell Atom Payload carrier) :
    cell.toHyperedge.footprint = cell.footprint := rfl

example (cell : TerminalBN6PositiveCell Atom Payload carrier) :
    cell.toHyperedge.mass = cell.payloadAtom.mass := rfl

example (footprint : List Atom) :
    ((terminalBN6PositiveAtomsAt carrier cells footprint).map
      TerminalBN6PayloadAtom.mass).sum =
      (cells.map fun cell =>
        if cell.footprint = footprint then cell.payloadAtom.mass else 0).sum :=
  terminalBN6PositiveAtomsAt_mass_sum carrier cells footprint

example :
    ((terminalBN6CanonicalPositiveGroups carrier carrierNodup cells).map
      fun group =>
        if group.consumerSystem.cutActivationBool cut then group.mass else 0).sum =
      terminalBN6PositiveCellsActivationWeight carrier cells cut :=
  terminalBN6CanonicalPositiveGroups_activationWeight_eq_raw
    carrier carrierNodup cells cut

/-! ## Duplicate-footprint active and inactive cut fixtures -/

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

private def duplicateCells :
    List (TerminalBN6PositiveCell Nat Nat [0, 1, 2]) :=
  [firstPositiveCell, secondPositiveCell]

example :
    terminalBN6PositiveCellsActivationWeight [0, 1, 2]
      duplicateCells [0] = 3 := by decide

example :
    terminalBN6PositiveCellsActivationWeight [0, 1, 2]
      duplicateCells [1] = 0 := by decide

example :
    ((terminalBN6CanonicalPositiveGroups [0, 1, 2] (by decide)
      duplicateCells).map fun group =>
        if group.consumerSystem.cutActivationBool [0] then group.mass else 0).sum =
      3 := by
  rw [terminalBN6CanonicalPositiveGroups_activationWeight_eq_raw]
  decide

/-! ## Checked PCCMin adapter and exact terminal boundary -/

variable {inputs gates outputs profileWidth rankCount : Nat}
variable {candidate : Candidate inputs gates outputs}
variable {model : TerminalCandidateSaturationModel
  (profileWidth := profileWidth) candidate}
variable {problem : TerminalFiniteSaturatePositiveProblem candidate model}
variable {terminalReady : TerminalFiniteBCELReadyCertificate problem}

variable (positiveCells : PCCMinCheckedPacketBN6BCELPositiveCells
  problem terminalReady rankCount)

example (candidateCut : List (TerminalPrimitiveRecord
    inputs gates outputs profileWidth)) :
    positiveCells.groupedCells.family.activationWeight candidateCut =
      terminalBN6PositiveCellsActivationWeight
        terminalReady.result.nucleus.anchors positiveCells.cells candidateCut :=
  positiveCells.groupedFamily_activationWeight_eq_raw candidateCut

variable (data : PCCMinCheckedPacketBN6BCELCanonicalGroupingHBData
  candidate model rankCount)

variable (silence : ∀ rank selector,
  selector ∈
    data.rawTable.withComputedPacketSelectorFaithfulness.selectorsAtRank rank →
  ∃ reason : TerminalPacketTypedRealizerBot
      data.positiveCells.groupedCells.family.PacketSelectorHandle rankCount,
    data.rawTable.withComputedPacketSelectorFaithfulness.checkedOutcome
        data.claimsAccepted selector = .blocked reason)

example :
    residualSlack candidate.toImplementation = 0 ∨
      ∃ candidateCut,
        candidateCut.Sublist data.terminalReady.result.nucleus.anchors ∧
        candidateCut ≠ [] ∧
        candidateCut ≠ data.terminalReady.result.nucleus.anchors ∧
        terminalBN6PositiveCellsActivationWeight
            data.terminalReady.result.nucleus.anchors
            data.positiveCells.cells candidateCut ≠
          data.problem.anchorProblem.toProblem.familyDefect
            data.terminalReady.result.nucleus.anchors :=
  pccmin_checked_packet_bn6_bcel_canonical_cut_ledger_route_or_zeroslack_checked_complete
    data silence

end PCCMinCheckedPacketBN6BCELCanonicalCutLedgerRegression
end DirectWire
end PNP
