/-
Copyright (c) 2026 PNP Labs.

Proof-bearing PkgC-to-BN6 positive cellization for an arbitrary finite family
of active quotient consumer systems.  Every source cell carries one genuine
two-sided active cut and one positive payload atom over a common carrier.  The
total classifier either retains an exact PkgC same-key cancellation or proves
that every source system is singletonized.  In the latter branch, the active
cut forces a singleton footprint of size at least two, so the raw BN6 support
and its size proof are constructed rather than supplied.

The constructed BN6 ledger preserves source order, payloads, and the exact
two-sided activation weight on every cut.  The source systems, payloads, and
typed full-restoration operation remain explicit inputs.  This module does
not derive them from terminal data, turn a cancellation into a global gain or
descent, establish the BCEL constant-cut equation, prove complete PkgC/BN6
route integration, ZeroSlack, PCCMin, polynomial runtime, SAT in P, or P = NP.
-/

import PNP.ResidualTerminalPkgCSameKeyCancellation
import PNP.ResidualTerminalBN6CanonicalCutLedger

namespace PNP
namespace DirectWire

/-! ## Active source cells -/

/-- One positive quotient source cell before PkgC singletonization.  The
    active cut is proof-bearing source data; its existence will force the
    derived singleton footprint to contain at least two anchors. -/
structure TerminalPkgCBN6SourceCell
    (Atom Payload : Type) [DecidableEq Atom]
    (carrier : List Atom) where
  consumerSystem : TerminalV54ConsumerSystem Atom
  carrierBinding : consumerSystem.carrier = carrier
  activeCut : List Atom
  active : consumerSystem.CutActive activeCut
  payloadAtom : TerminalBN6PayloadAtom Payload

/-- The singleton footprint is an ordered sublist of the common carrier. -/
theorem TerminalPkgCBN6SourceCell.singletonFootprint_sublist
    {Atom Payload : Type} [DecidableEq Atom]
    {carrier : List Atom}
    (cell : TerminalPkgCBN6SourceCell Atom Payload carrier) :
    cell.consumerSystem.singletonFootprint.Sublist carrier := by
  have included : cell.consumerSystem.singletonFootprint.Sublist
      cell.consumerSystem.carrier :=
    List.filter_sublist
  simpa only [cell.carrierBinding] using included

/-- The common carrier is duplicate-free because it is exactly the source
    consumer system's carrier. -/
theorem TerminalPkgCBN6SourceCell.carrier_nodup
    {Atom Payload : Type} [DecidableEq Atom]
    {carrier : List Atom}
    (cell : TerminalPkgCBN6SourceCell Atom Payload carrier) :
    carrier.Nodup := by
  simpa only [cell.carrierBinding] using
    cell.consumerSystem.carrierNodup

/-- The singleton footprint is duplicate-free. -/
theorem TerminalPkgCBN6SourceCell.singletonFootprint_nodup
    {Atom Payload : Type} [DecidableEq Atom]
    {carrier : List Atom}
    (cell : TerminalPkgCBN6SourceCell Atom Payload carrier) :
    cell.consumerSystem.singletonFootprint.Nodup :=
  cell.singletonFootprint_sublist.nodup cell.carrier_nodup

/-- After PkgC singletonization, a genuinely active cut supplies two distinct
    singleton consumers on opposite sides and hence a footprint of size at
    least two. -/
theorem TerminalPkgCBN6SourceCell.singletonFootprint_length_at_least_two
    {Atom Payload : Type} [DecidableEq Atom]
    {carrier : List Atom}
    (cell : TerminalPkgCBN6SourceCell Atom Payload carrier)
    (singletonized :
      cell.consumerSystem.DisjointPairsSingletonized) :
    2 ≤ cell.consumerSystem.singletonFootprint.length := by
  have crosses : cell.consumerSystem.FootprintCrossesCut cell.activeCut :=
    (terminalV54_consumerAntichain_normal_form_iff
      cell.consumerSystem singletonized cell.activeCut).1 cell.active
  obtain ⟨left, leftFootprint, leftCut, right, rightFootprint,
    rightComplement⟩ := crosses
  have rightNotCut : right ∉ cell.activeCut :=
    (mem_terminalV54Complement_iff cell.consumerSystem.carrier
      cell.activeCut right).1 rightComplement |>.2
  have different : left ≠ right := by
    intro equal
    subst right
    exact rightNotCut leftCut
  have pairLength :
      (terminalV53CanonicalPair
        cell.consumerSystem.singletonFootprint left right).length = 2 :=
    terminalV53CanonicalPair_length
      cell.consumerSystem.singletonFootprint left right
      cell.singletonFootprint_nodup leftFootprint rightFootprint different
  have pairSublist :
      (terminalV53CanonicalPair
        cell.consumerSystem.singletonFootprint left right).Sublist
          cell.consumerSystem.singletonFootprint :=
    terminalV53CanonicalPair_sublist
      cell.consumerSystem.singletonFootprint left right
  have pairLengthBound := pairSublist.length_le
  omega

/-- The source footprint is already in common-carrier order, so BN6
    normalization leaves it unchanged. -/
theorem TerminalPkgCBN6SourceCell.normalized_singletonFootprint
    {Atom Payload : Type} [DecidableEq Atom]
    {carrier : List Atom}
    (cell : TerminalPkgCBN6SourceCell Atom Payload carrier) :
    terminalBN6NormalizeSupport carrier
        cell.consumerSystem.singletonFootprint =
      cell.consumerSystem.singletonFootprint :=
  terminalBN6NormalizeSupport_eq_self_of_sublist
    cell.singletonFootprint_sublist cell.carrier_nodup

/-- Construct the raw BN6 positive cell from the source system.  Neither its
    support nor its size certificate is accepted independently. -/
def TerminalPkgCBN6SourceCell.toBN6PositiveCell
    {Atom Payload : Type} [DecidableEq Atom]
    {carrier : List Atom}
    (cell : TerminalPkgCBN6SourceCell Atom Payload carrier)
    (singletonized :
      cell.consumerSystem.DisjointPairsSingletonized) :
    TerminalBN6PositiveCell Atom Payload carrier where
  support := cell.consumerSystem.singletonFootprint
  payloadAtom := cell.payloadAtom
  footprintLarge := by
    rw [cell.normalized_singletonFootprint]
    exact cell.singletonFootprint_length_at_least_two singletonized

/-- The constructed BN6 footprint is exactly the source singleton footprint. -/
theorem TerminalPkgCBN6SourceCell.toBN6PositiveCell_footprint
    {Atom Payload : Type} [DecidableEq Atom]
    {carrier : List Atom}
    (cell : TerminalPkgCBN6SourceCell Atom Payload carrier)
    (singletonized :
      cell.consumerSystem.DisjointPairsSingletonized) :
    (cell.toBN6PositiveCell singletonized).footprint =
      cell.consumerSystem.singletonFootprint :=
  cell.normalized_singletonFootprint

/-- One source cell's exact two-sided activation contribution. -/
def TerminalPkgCBN6SourceCell.cutContribution
    {Atom Payload : Type} [DecidableEq Atom]
    {carrier : List Atom}
    (cell : TerminalPkgCBN6SourceCell Atom Payload carrier)
    (cut : List Atom) : Nat :=
  if cell.consumerSystem.cutActivationBool cut then
    cell.payloadAtom.mass
  else 0

/-- A one-atom grouped cell used only to reuse V54's exact Boolean activation
    reflection. -/
private def TerminalPkgCBN6SourceCell.toSingletonizedGroupedCell
    {Atom Payload : Type} [DecidableEq Atom]
    {carrier : List Atom}
    (cell : TerminalPkgCBN6SourceCell Atom Payload carrier)
    (singletonized :
      cell.consumerSystem.DisjointPairsSingletonized) :
    TerminalBN6GroupedCell Atom Payload where
  consumerSystem := cell.consumerSystem
  singletonized := singletonized
  atoms := [cell.payloadAtom]
  atomsNonempty := by simp

private theorem TerminalPkgCBN6SourceCell.toBN6PositiveCell_hyperedge_eq
    {Atom Payload : Type} [DecidableEq Atom]
    {carrier : List Atom}
    (cell : TerminalPkgCBN6SourceCell Atom Payload carrier)
    (singletonized :
      cell.consumerSystem.DisjointPairsSingletonized) :
    (cell.toBN6PositiveCell singletonized).toHyperedge =
      (cell.toSingletonizedGroupedCell singletonized).toHyperedge := by
  unfold TerminalBN6PositiveCell.toHyperedge
    TerminalBN6GroupedCell.toHyperedge
  rw [cell.toBN6PositiveCell_footprint singletonized]
  simp [TerminalBN6GroupedCell.footprint,
    TerminalPkgCBN6SourceCell.toBN6PositiveCell,
    TerminalPkgCBN6SourceCell.toSingletonizedGroupedCell,
    TerminalBN6GroupedCell.mass]

/-- PkgC singletonization makes the constructed BN6 crossing contribution
    exactly equal to the original two-sided request activation contribution
    on every cut. -/
theorem TerminalPkgCBN6SourceCell.toBN6PositiveCell_cutContribution
    {Atom Payload : Type} [DecidableEq Atom]
    {carrier : List Atom}
    (cell : TerminalPkgCBN6SourceCell Atom Payload carrier)
    (singletonized :
      cell.consumerSystem.DisjointPairsSingletonized)
    (cut : List Atom) :
    (cell.toBN6PositiveCell singletonized).cutContribution cut =
      cell.cutContribution cut := by
  unfold TerminalBN6PositiveCell.cutContribution
    TerminalPkgCBN6SourceCell.cutContribution
    TerminalV53Hyperedge.cutContribution
  rw [cell.toBN6PositiveCell_hyperedge_eq singletonized]
  rw [(cell.toSingletonizedGroupedCell singletonized
    ).crossesBool_eq_cutActivationBool cut]
  simp [TerminalPkgCBN6SourceCell.toSingletonizedGroupedCell,
    TerminalBN6GroupedCell.toHyperedge, TerminalBN6GroupedCell.mass]

/-! ## Arbitrary-finite source-ledger conversion -/

/-- Exact activation weight of the source PkgC systems before BN6
    cellization. -/
def terminalPkgCBN6SourceActivationWeight
    {Atom Payload : Type} [DecidableEq Atom]
    {carrier : List Atom}
    (cells : List (TerminalPkgCBN6SourceCell Atom Payload carrier))
    (cut : List Atom) : Nat :=
  (cells.map fun cell => cell.cutContribution cut).sum

/-- Convert a completely singletonized source list without accepting raw BN6
    supports or footprint-size certificates. -/
def terminalPkgCBN6PositiveCells
    {Atom Payload : Type} [DecidableEq Atom]
    {carrier : List Atom}
    (cells : List (TerminalPkgCBN6SourceCell Atom Payload carrier))
    (singletonized : ∀ cell, cell ∈ cells →
      cell.consumerSystem.DisjointPairsSingletonized) :
    List (TerminalBN6PositiveCell Atom Payload carrier) :=
  cells.attach.map fun cell =>
    cell.1.toBN6PositiveCell (singletonized cell.1 cell.2)

theorem terminalPkgCBN6PositiveCells_length
    {Atom Payload : Type} [DecidableEq Atom]
    {carrier : List Atom}
    (cells : List (TerminalPkgCBN6SourceCell Atom Payload carrier))
    (singletonized : ∀ cell, cell ∈ cells →
      cell.consumerSystem.DisjointPairsSingletonized) :
    (terminalPkgCBN6PositiveCells cells singletonized).length = cells.length := by
  simp [terminalPkgCBN6PositiveCells]

/-- Cellization preserves every payload atom in exact source-list order. -/
theorem terminalPkgCBN6PositiveCells_payloadAtoms
    {Atom Payload : Type} [DecidableEq Atom]
    {carrier : List Atom}
    (cells : List (TerminalPkgCBN6SourceCell Atom Payload carrier))
    (singletonized : ∀ cell, cell ∈ cells →
      cell.consumerSystem.DisjointPairsSingletonized) :
    (terminalPkgCBN6PositiveCells cells singletonized).map
        TerminalBN6PositiveCell.payloadAtom =
      cells.map TerminalPkgCBN6SourceCell.payloadAtom := by
  simp [terminalPkgCBN6PositiveCells,
    TerminalPkgCBN6SourceCell.toBN6PositiveCell, List.map_map]

/-- The whole constructed BN6 ledger has exactly the source PkgC activation
    weight on every cut. -/
theorem terminalPkgCBN6PositiveCells_activationWeight
    {Atom Payload : Type} [DecidableEq Atom]
    {carrier : List Atom}
    (cells : List (TerminalPkgCBN6SourceCell Atom Payload carrier))
    (singletonized : ∀ cell, cell ∈ cells →
      cell.consumerSystem.DisjointPairsSingletonized)
    (cut : List Atom) :
    terminalBN6PositiveCellsActivationWeight carrier
        (terminalPkgCBN6PositiveCells cells singletonized) cut =
      terminalPkgCBN6SourceActivationWeight cells cut := by
  unfold terminalBN6PositiveCellsActivationWeight
    terminalPkgCBN6PositiveCells terminalPkgCBN6SourceActivationWeight
  rw [List.map_map]
  change
    (cells.attach.map fun cell =>
      (cell.1.toBN6PositiveCell
        (singletonized cell.1 cell.2)).cutContribution cut).sum =
      (cells.map fun cell => cell.cutContribution cut).sum
  have pointwise :
      (cells.attach.map fun cell =>
        (cell.1.toBN6PositiveCell
          (singletonized cell.1 cell.2)).cutContribution cut) =
        cells.attach.map fun cell => cell.1.cutContribution cut := by
    apply List.map_congr_left
    intro cell _cellMember
    exact cell.1.toBN6PositiveCell_cutContribution
      (singletonized cell.1 cell.2) cut
  rw [pointwise]
  have attached :
      (cells.attach.map fun cell => cell.1.cutContribution cut) =
        cells.map fun cell => cell.cutContribution cut := by
    rw [show (cells.attach.map fun cell => cell.1.cutContribution cut) =
        (cells.attach.map Subtype.val).map
          (fun cell => cell.cutContribution cut) by
      simp]
    rw [List.attach_map_subtype_val]
  rw [attached]

/-! ## Total PkgC classifier -/

/-- The exact finite outcome: every source system is PkgC-singletonized, or
    one listed source cell retains a proof-bearing same-key cancellation. -/
inductive TerminalPkgCBN6CellizationOutcome
    {Atom Payload FullCandidate ActivationAtom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq Atom] [DecidableEq ActivationAtom]
    [DecidableEq SemanticSignature] [DecidableEq TransportType]
    [DecidableEq Frontier] [DecidableEq ChargeOwner]
    [DecidableEq Obligation] [DecidableEq OriginKernel]
    [DecidableEq ModeProjection]
    (carrier : List Atom)
    (cells : List (TerminalPkgCBN6SourceCell Atom Payload carrier))
    (restorer : TerminalPkgCTypedRestorer Atom FullCandidate
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection)) where
  | cellized
      (singletonized : ∀ cell, cell ∈ cells →
        cell.consumerSystem.DisjointPairsSingletonized)
  | pkgCCancellation
      (cell : TerminalPkgCBN6SourceCell Atom Payload carrier)
      (member : cell ∈ cells)
      (pair : TerminalPkgCSeparatingPair cell.consumerSystem)
      (realization :
        TerminalPkgCSameKeyCancellationRealization pair restorer)

/-- Scan source cells in list order and retain the first PkgC same-key
    cancellation. If no such route exists, construct the complete
    singletonization proof needed for BN6 cellization. -/
def classifyTerminalPkgCBN6Cellization
    {Atom Payload FullCandidate ActivationAtom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq Atom] [DecidableEq ActivationAtom]
    [DecidableEq SemanticSignature] [DecidableEq TransportType]
    [DecidableEq Frontier] [DecidableEq ChargeOwner]
    [DecidableEq Obligation] [DecidableEq OriginKernel]
    [DecidableEq ModeProjection]
    (carrier : List Atom)
    (restorer : TerminalPkgCTypedRestorer Atom FullCandidate
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection)) :
    (cells : List (TerminalPkgCBN6SourceCell Atom Payload carrier)) →
      TerminalPkgCBN6CellizationOutcome carrier cells restorer
  | [] => .cellized (by simp)
  | head :: tail =>
      match classifyTerminalPkgCSameKeyCancellation
          head.consumerSystem restorer with
      | .cancelled pair realization =>
          .pkgCCancellation head (by simp) pair realization
      | .singletonized headSingletonized =>
          match classifyTerminalPkgCBN6Cellization carrier restorer tail with
          | .pkgCCancellation cell member pair realization =>
              .pkgCCancellation cell (by simp [member]) pair realization
          | .cellized tailSingletonized =>
              .cellized (by
                intro cell member
                rcases List.mem_cons.mp member with cellHead | cellTail
                · subst cell
                  exact headSingletonized
                · exact tailSingletonized cell cellTail)

/-- Public M201 endpoint. Every arbitrary finite active source ledger either
    produces the exact constructed BN6 ledger with conserved all-cut
    activation weight, or exposes a proof-bearing PkgC same-key cancellation
    for one of its source systems. -/
theorem terminalPkgC_bn6_positive_cellization_checked_complete
    {Atom Payload FullCandidate ActivationAtom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq Atom] [DecidableEq ActivationAtom]
    [DecidableEq SemanticSignature] [DecidableEq TransportType]
    [DecidableEq Frontier] [DecidableEq ChargeOwner]
    [DecidableEq Obligation] [DecidableEq OriginKernel]
    [DecidableEq ModeProjection]
    (carrier : List Atom)
    (cells : List (TerminalPkgCBN6SourceCell Atom Payload carrier))
    (restorer : TerminalPkgCTypedRestorer Atom FullCandidate
      (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
        TransportType Frontier ChargeOwner Obligation OriginKernel
        ModeProjection)) :
    (∃ singletonized : ∀ cell, cell ∈ cells →
        cell.consumerSystem.DisjointPairsSingletonized,
      (terminalPkgCBN6PositiveCells cells singletonized).length = cells.length ∧
      (terminalPkgCBN6PositiveCells cells singletonized).map
          TerminalBN6PositiveCell.payloadAtom =
        cells.map TerminalPkgCBN6SourceCell.payloadAtom ∧
      ∀ cut,
        terminalBN6PositiveCellsActivationWeight carrier
            (terminalPkgCBN6PositiveCells cells singletonized) cut =
          terminalPkgCBN6SourceActivationWeight cells cut) ∨
      ∃ cell, cell ∈ cells ∧
        ∃ pair : TerminalPkgCSeparatingPair cell.consumerSystem,
          Nonempty (TerminalPkgCSameKeyCancellationRealization pair
            restorer) := by
  match classifyTerminalPkgCBN6Cellization carrier restorer cells with
  | .cellized singletonized =>
      exact Or.inl ⟨singletonized,
        terminalPkgCBN6PositiveCells_length cells singletonized,
        terminalPkgCBN6PositiveCells_payloadAtoms cells singletonized,
        terminalPkgCBN6PositiveCells_activationWeight cells singletonized⟩
  | .pkgCCancellation cell member pair realization =>
      exact Or.inr ⟨cell, member, pair, ⟨realization⟩⟩

end DirectWire
end PNP
