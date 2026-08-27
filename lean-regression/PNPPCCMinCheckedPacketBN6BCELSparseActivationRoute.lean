import PNP.PCCMinCheckedPacketBN6BCELSparseActivationRoute

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire
namespace PCCMinCheckedPacketBN6BCELSparseActivationRouteRegression

/-! ## Arbitrary-finite theorem interface -/

variable {Atom : Type} [DecidableEq Atom]
variable (system : TerminalV53Hypergraph Atom)

example (carrierAtLeastTwo : 2 ≤ system.carrier.length) :
    system.SmallProperCutEquation ↔ system.ConstantProperCuts :=
  terminalV53_smallProperCutEquation_iff_constantProperCuts system
    carrierAtLeastTwo

example : system.smallProperCuts.Nodup := system.smallProperCuts_nodup

example :
    system.smallProperCuts.length ≤
      system.carrier.length + system.carrier.length * system.carrier.length :=
  system.smallProperCuts_length_le

example : Nonempty (TerminalV53SmallProperCutClassification system) :=
  classifyTerminalV53SmallProperCuts_exhaustive system

/-! ## Executable two-, three-, and four-anchor fixtures -/

abbrev M200Atom := Fin 4

private def twoAnchorCoherent : TerminalV53Hypergraph M200Atom where
  carrier := [0, 1]
  carrierNodup := by decide
  cells := [{ footprint := [0, 1], mass := 5 }]
  footprintsNodup := by decide
  footprintSublist := by
    intro cell cellMember
    simp only [List.mem_singleton] at cellMember
    subst cell
    decide
  footprintLarge := by
    intro cell cellMember
    simp only [List.mem_singleton] at cellMember
    subst cell
    simp
  massPositive := by
    intro cell cellMember
    simp only [List.mem_singleton] at cellMember
    subst cell
    simp
  cutValue := 5
  cutValuePositive := by simp

private def threeAnchorCoherent : TerminalV53Hypergraph M200Atom where
  carrier := [0, 1, 2]
  carrierNodup := by decide
  cells := [{ footprint := [0, 1, 2], mass := 5 }]
  footprintsNodup := by decide
  footprintSublist := by
    intro cell cellMember
    simp only [List.mem_singleton] at cellMember
    subst cell
    decide
  footprintLarge := by
    intro cell cellMember
    simp only [List.mem_singleton] at cellMember
    subst cell
    simp
  massPositive := by
    intro cell cellMember
    simp only [List.mem_singleton] at cellMember
    subst cell
    simp
  cutValue := 5
  cutValuePositive := by simp

private def fourAnchorCoherent : TerminalV53Hypergraph M200Atom where
  carrier := [0, 1, 2, 3]
  carrierNodup := by decide
  cells := [{ footprint := [0, 1, 2, 3], mass := 5 }]
  footprintsNodup := by decide
  footprintSublist := by
    intro cell cellMember
    simp only [List.mem_singleton] at cellMember
    subst cell
    decide
  footprintLarge := by
    intro cell cellMember
    simp only [List.mem_singleton] at cellMember
    subst cell
    simp
  massPositive := by
    intro cell cellMember
    simp only [List.mem_singleton] at cellMember
    subst cell
    simp
  cutValue := 5
  cutValuePositive := by simp

private def twoAnchorWeightMismatch : TerminalV53Hypergraph M200Atom where
  carrier := [0, 1]
  carrierNodup := by decide
  cells := [{ footprint := [0, 1], mass := 5 }]
  footprintsNodup := by decide
  footprintSublist := by
    intro cell cellMember
    simp only [List.mem_singleton] at cellMember
    subst cell
    decide
  footprintLarge := by
    intro cell cellMember
    simp only [List.mem_singleton] at cellMember
    subst cell
    simp
  massPositive := by
    intro cell cellMember
    simp only [List.mem_singleton] at cellMember
    subst cell
    simp
  cutValue := 4
  cutValuePositive := by simp

private def threeAnchorWeightMismatch : TerminalV53Hypergraph M200Atom where
  carrier := [0, 1, 2]
  carrierNodup := by decide
  cells := [{ footprint := [0, 1, 2], mass := 5 }]
  footprintsNodup := by decide
  footprintSublist := by
    intro cell cellMember
    simp only [List.mem_singleton] at cellMember
    subst cell
    decide
  footprintLarge := by
    intro cell cellMember
    simp only [List.mem_singleton] at cellMember
    subst cell
    simp
  massPositive := by
    intro cell cellMember
    simp only [List.mem_singleton] at cellMember
    subst cell
    simp
  cutValue := 4
  cutValuePositive := by simp

private def fourAnchorNonFullCell : TerminalV53Hypergraph M200Atom where
  carrier := [0, 1, 2, 3]
  carrierNodup := by decide
  cells := [{ footprint := [0, 1], mass := 5 }]
  footprintsNodup := by decide
  footprintSublist := by
    intro cell cellMember
    simp only [List.mem_singleton] at cellMember
    subst cell
    decide
  footprintLarge := by
    intro cell cellMember
    simp only [List.mem_singleton] at cellMember
    subst cell
    simp
  massPositive := by
    intro cell cellMember
    simp only [List.mem_singleton] at cellMember
    subst cell
    simp
  cutValue := 5
  cutValuePositive := by simp

private def fourAnchorWeightMismatch : TerminalV53Hypergraph M200Atom where
  carrier := [0, 1, 2, 3]
  carrierNodup := by decide
  cells := [{ footprint := [0, 1, 2, 3], mass := 5 }]
  footprintsNodup := by decide
  footprintSublist := by
    intro cell cellMember
    simp only [List.mem_singleton] at cellMember
    subst cell
    decide
  footprintLarge := by
    intro cell cellMember
    simp only [List.mem_singleton] at cellMember
    subst cell
    simp
  massPositive := by
    intro cell cellMember
    simp only [List.mem_singleton] at cellMember
    subst cell
    simp
  cutValue := 4
  cutValuePositive := by simp

private def classificationCoherent
    (candidate : TerminalV53Hypergraph M200Atom) : Bool :=
  match classifyTerminalV53SmallProperCuts candidate with
  | .coherent _ => true
  | .insufficient _ | .routed _ => false

private def classifiedMismatchCut?
    (candidate : TerminalV53Hypergraph M200Atom) : Option (List M200Atom) :=
  match classifyTerminalV53SmallProperCuts candidate with
  | .routed route => some route.cut
  | .insufficient _ | .coherent _ => none

example : twoAnchorCoherent.smallProperCuts = [[0], [1]] := by native_decide

example : fourAnchorCoherent.smallProperCuts =
    [[0], [0, 1], [0, 2], [0, 3], [1], [1, 2], [1, 3], [2],
      [2, 3], [3]] := by
  native_decide

example : classificationCoherent twoAnchorCoherent = true := by native_decide
example : classificationCoherent threeAnchorCoherent = true := by native_decide
example : classificationCoherent fourAnchorCoherent = true := by native_decide

example : classifiedMismatchCut? twoAnchorWeightMismatch = some [0] := by
  native_decide
example : classifiedMismatchCut? threeAnchorWeightMismatch = some [0] := by
  native_decide
example : classifiedMismatchCut? fourAnchorNonFullCell = some [0, 1] := by
  native_decide
example : classifiedMismatchCut? fourAnchorWeightMismatch = some [0] := by
  native_decide

example : Nonempty
    (TerminalV53SmallProperCutMismatch fourAnchorNonFullCell) := by
  match classified : classifyTerminalV53SmallProperCuts
      fourAnchorNonFullCell with
  | .routed route => exact ⟨route⟩
  | .insufficient small => simp [fourAnchorNonFullCell] at small
  | .coherent constant =>
      have impossible := fourAnchorNonFullCell.cellsFull_of_four constant
        (by decide)
      have full := impossible { footprint := [0, 1], mass := 5 }
        (by simp [fourAnchorNonFullCell])
      simp [fourAnchorNonFullCell] at full

/-! ## Checked PCC adapter retains the exact raw small-cut ledger -/

variable {inputs gates outputs profileWidth rankCount : Nat}
variable {candidate : Candidate inputs gates outputs}
variable {model : TerminalCandidateSaturationModel
  (profileWidth := profileWidth) candidate}

variable (data : PCCMinCheckedPacketBN6BCELCanonicalGroupingHBData
  candidate model rankCount)

variable (silence : ∀ rank selector,
  selector ∈
    data.rawTable.withComputedPacketSelectorFaithfulness.selectorsAtRank rank →
  ∃ reason : TerminalPacketTypedRealizerBot
      data.positiveCells.groupedCells.family.PacketSelectorHandle rankCount,
    data.rawTable.withComputedPacketSelectorFaithfulness.checkedOutcome
        data.claimsAccepted selector = .blocked reason)

example : PCCMinCheckedPacketBN6BCELSparseActivationRouteOrZeroSlack data :=
  data.sparseActivationRouteOrZeroSlackOfSilence silence

example :
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
            data.terminalReady.result.nucleus.anchors :=
  pccmin_checked_packet_bn6_bcel_sparse_activation_route_or_zeroslack_checked_complete
    data silence

end PCCMinCheckedPacketBN6BCELSparseActivationRouteRegression
end DirectWire
end PNP
