import PNP.PCCMinCheckedPacketBN6BCELCanonicalConstantCutBasis

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire
namespace PCCMinCheckedPacketBN6BCELCanonicalConstantCutBasisRegression

/-! ## Arbitrary-carrier theorem interface -/

variable {Atom : Type} [DecidableEq Atom]
variable (system : TerminalV53Hypergraph Atom)

example (carrierAtLeastTwo : 2 ≤ system.carrier.length) :
    system.CanonicalConstantCutBasis ↔ system.ConstantProperCuts :=
  terminalV53_canonicalConstantCutBasis_iff_constantProperCuts system
    carrierAtLeastTwo

example :
    Nonempty (TerminalV53CanonicalConstantCutBasisClassification system) :=
  classifyTerminalV53CanonicalConstantCutBasis_exhaustive system

/-! ## Executable two-, three-, and four-anchor fixtures -/

abbrev M199Atom := Fin 4

private def twoAnchorCoherent : TerminalV53Hypergraph M199Atom where
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

private def threeAnchorCoherent : TerminalV53Hypergraph M199Atom where
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

private def fourAnchorCoherent : TerminalV53Hypergraph M199Atom where
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

private def classificationAccepted
    (candidate : TerminalV53Hypergraph M199Atom) : Bool :=
  match classifyTerminalV53CanonicalConstantCutBasis candidate with
  | .coherent _ => true
  | .routed _ => false

example : twoAnchorCoherent.CanonicalConstantCutBasis := by
  change twoAnchorCoherent.footprintWeight twoAnchorCoherent.carrier =
    twoAnchorCoherent.cutValue
  native_decide

example : threeAnchorCoherent.CanonicalConstantCutBasis := by
  change
    threeAnchorCoherent.cutWeight [0] = threeAnchorCoherent.cutValue ∧
    threeAnchorCoherent.cutWeight [1] = threeAnchorCoherent.cutValue ∧
    threeAnchorCoherent.cutWeight [2] = threeAnchorCoherent.cutValue
  native_decide

example : fourAnchorCoherent.CanonicalConstantCutBasis := by
  change
    (∀ cell, cell ∈ fourAnchorCoherent.cells ->
      cell.footprint = fourAnchorCoherent.carrier) ∧
    fourAnchorCoherent.footprintWeight fourAnchorCoherent.carrier =
      fourAnchorCoherent.cutValue
  constructor
  · intro cell cellMember
    simp only [fourAnchorCoherent, List.mem_singleton] at cellMember
    subst cell
    rfl
  · native_decide

example : classificationAccepted twoAnchorCoherent = true := by native_decide
example : classificationAccepted threeAnchorCoherent = true := by native_decide
example : classificationAccepted fourAnchorCoherent = true := by native_decide

/-! ## Each structural failure remains a typed route -/

private def twoAnchorWeightMismatch : TerminalV53Hypergraph M199Atom where
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

private def threeAnchorSingletonMismatch : TerminalV53Hypergraph M199Atom where
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

private def fourAnchorNonFullCell : TerminalV53Hypergraph M199Atom where
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

private def fourAnchorWeightMismatch : TerminalV53Hypergraph M199Atom where
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

example : Nonempty
    (TerminalV53CanonicalConstantCutBasisRoute twoAnchorWeightMismatch) :=
  ⟨.twoFullWeightMismatch (by decide) (by decide)⟩

example : Nonempty
    (TerminalV53CanonicalConstantCutBasisRoute
      threeAnchorSingletonMismatch) :=
  ⟨.threeSingletonMismatch (by decide) 0 (by decide) (by decide)⟩

example : Nonempty
    (TerminalV53CanonicalConstantCutBasisRoute fourAnchorNonFullCell) :=
  ⟨.largeNonFullCell (by decide) { footprint := [0, 1], mass := 5 }
    (by simp [fourAnchorNonFullCell]) (by decide)⟩

example : Nonempty
    (TerminalV53CanonicalConstantCutBasisRoute fourAnchorWeightMismatch) :=
  ⟨.largeFullWeightMismatch (by decide) (by
      intro cell cellMember
      simp only [fourAnchorWeightMismatch, List.mem_singleton] at cellMember
      subst cell
      rfl) (by decide)⟩

example : classificationAccepted twoAnchorWeightMismatch = false := by
  native_decide
example : classificationAccepted threeAnchorSingletonMismatch = false := by
  native_decide
example : classificationAccepted fourAnchorNonFullCell = false := by
  native_decide
example : classificationAccepted fourAnchorWeightMismatch = false := by
  native_decide

/-! ## Checked PCC adapter retains the exact raw cut ledger -/

variable {inputs gates outputs profileWidth rankCount : Nat}
variable {candidate : Candidate inputs gates outputs}
variable {model : TerminalCandidateSaturationModel
  (profileWidth := profileWidth) candidate}
variable {problem : TerminalFiniteSaturatePositiveProblem candidate model}
variable {terminalReady : TerminalFiniteBCELReadyCertificate problem}

variable (positiveCells : PCCMinCheckedPacketBN6BCELPositiveCells
  problem terminalReady rankCount)

example (cut : List (TerminalPrimitiveRecord
    inputs gates outputs profileWidth)) :
    positiveCells.groupedCells.family.hypergraph.cutWeight cut =
      terminalBN6PositiveCellsActivationWeight
        terminalReady.result.nucleus.anchors positiveCells.cells cut :=
  positiveCells.groupedHypergraph_cutWeight_eq_raw cut

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
      Nonempty (TerminalV53CanonicalConstantCutBasisRoute
        data.positiveCells.groupedCells.family.hypergraph) :=
  pccmin_checked_packet_bn6_bcel_canonical_cut_basis_route_or_zeroslack_checked_complete
    data silence

end PCCMinCheckedPacketBN6BCELCanonicalConstantCutBasisRegression
end DirectWire
end PNP
