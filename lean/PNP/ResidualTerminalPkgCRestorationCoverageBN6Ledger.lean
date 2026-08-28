/-
Copyright (c) 2026 PNP Labs.

Family-level PkgC restoration coverage at the BN6 boundary.

M201 constructs an arbitrary finite BN6 source ledger only after an
always-total typed restorer proves every source system singletonized. M204
instead preserves one source system's exact Hall branch and computes the
coverage-derived ambient BN4 consequence without accepting such a restorer.
This module lifts M204 over the complete source ledger in canonical list order.
The first Hall, ambient-reduction, or ambient-mismatch result is retained
literally. Only the all-singletonized branch constructs M201's BN6 positive
cells and inherits exact payload order and all-cut activation conservation.

The source cells, active cuts, payloads, restoration universes, coordinate
maps, full-restoration coordinate lists, and ambient BN4 ledgers remain explicit
inputs. A Hall deficit or ambient mismatch is not yet a globally decreasing
route, and a computed remainder is not proved empty. This module does not
complete PkgC/BN3-BN6, prove unconditional ZeroSlack, polynomial PCCMin,
SAT in P, or P = NP.
-/

import PNP.ResidualTerminalPkgCRestorationCoverageAmbientRoute

namespace PNP
namespace DirectWire

/-! ## Enriched arbitrary-finite source ledger -/

/-- One active PkgC source cell together with the exact finite restoration and
    ambient BN4 data consumed by M204. No typed restorer is present. -/
structure TerminalPkgCRestorationCoverageBN6SourceCell
    (Atom Payload ActivationAtom SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type)
    [DecidableEq Atom] [DecidableEq ActivationAtom]
    [DecidableEq SemanticSignature] [DecidableEq TransportType]
    [DecidableEq Frontier] [DecidableEq ChargeOwner]
    [DecidableEq Obligation] [DecidableEq OriginKernel]
    [DecidableEq ModeProjection]
    (carrier : List Atom) where
  source : TerminalPkgCBN6SourceCell Atom Payload carrier
  restoration : TerminalPkgCRestorationUniverse Atom
    (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
      TransportType Frontier ChargeOwner Obligation OriginKernel
      ModeProjection)
  ambient : List (TerminalBN4ActivationCell ActivationAtom SemanticSignature
    TransportType)

/-- Forget only the per-source restoration and ambient routing data. -/
def terminalPkgCRestorationCoverageBN6SourceCells
    {Atom Payload ActivationAtom SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq Atom] [DecidableEq ActivationAtom]
    [DecidableEq SemanticSignature] [DecidableEq TransportType]
    [DecidableEq Frontier] [DecidableEq ChargeOwner]
    [DecidableEq Obligation] [DecidableEq OriginKernel]
    [DecidableEq ModeProjection]
    {carrier : List Atom}
    (cells : List (TerminalPkgCRestorationCoverageBN6SourceCell Atom Payload
      ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection carrier)) :
    List (TerminalPkgCBN6SourceCell Atom Payload carrier) :=
  cells.map TerminalPkgCRestorationCoverageBN6SourceCell.source

/-- Singletonization of every enriched source cell proves singletonization of
    every cell in the projected M201 ledger. -/
theorem terminalPkgCRestorationCoverageBN6SourceCells_singletonized
    {Atom Payload ActivationAtom SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq Atom] [DecidableEq ActivationAtom]
    [DecidableEq SemanticSignature] [DecidableEq TransportType]
    [DecidableEq Frontier] [DecidableEq ChargeOwner]
    [DecidableEq Obligation] [DecidableEq OriginKernel]
    [DecidableEq ModeProjection]
    {carrier : List Atom}
    (cells : List (TerminalPkgCRestorationCoverageBN6SourceCell Atom Payload
      ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection carrier))
    (singletonized : forall cell, cell ∈ cells ->
      cell.source.consumerSystem.DisjointPairsSingletonized) :
    forall source,
      source ∈ terminalPkgCRestorationCoverageBN6SourceCells cells ->
        source.consumerSystem.DisjointPairsSingletonized := by
  intro source sourceMember
  obtain ⟨cell, cellMember, sourceEqual⟩ := List.mem_map.mp sourceMember
  subst source
  exact singletonized cell cellMember

/-- Construct the BN6 ledger only from the projected source cells and the
    proved all-source singletonization result. -/
def terminalPkgCRestorationCoverageBN6PositiveCells
    {Atom Payload ActivationAtom SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq Atom] [DecidableEq ActivationAtom]
    [DecidableEq SemanticSignature] [DecidableEq TransportType]
    [DecidableEq Frontier] [DecidableEq ChargeOwner]
    [DecidableEq Obligation] [DecidableEq OriginKernel]
    [DecidableEq ModeProjection]
    {carrier : List Atom}
    (cells : List (TerminalPkgCRestorationCoverageBN6SourceCell Atom Payload
      ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection carrier))
    (singletonized : forall cell, cell ∈ cells ->
      cell.source.consumerSystem.DisjointPairsSingletonized) :
    List (TerminalBN6PositiveCell Atom Payload carrier) :=
  terminalPkgCBN6PositiveCells
    (terminalPkgCRestorationCoverageBN6SourceCells cells)
    (terminalPkgCRestorationCoverageBN6SourceCells_singletonized cells
      singletonized)

theorem terminalPkgCRestorationCoverageBN6PositiveCells_length
    {Atom Payload ActivationAtom SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq Atom] [DecidableEq ActivationAtom]
    [DecidableEq SemanticSignature] [DecidableEq TransportType]
    [DecidableEq Frontier] [DecidableEq ChargeOwner]
    [DecidableEq Obligation] [DecidableEq OriginKernel]
    [DecidableEq ModeProjection]
    {carrier : List Atom}
    (cells : List (TerminalPkgCRestorationCoverageBN6SourceCell Atom Payload
      ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection carrier))
    (singletonized : forall cell, cell ∈ cells ->
      cell.source.consumerSystem.DisjointPairsSingletonized) :
    (terminalPkgCRestorationCoverageBN6PositiveCells cells
      singletonized).length = cells.length := by
  unfold terminalPkgCRestorationCoverageBN6PositiveCells
  rw [terminalPkgCBN6PositiveCells_length]
  simp [terminalPkgCRestorationCoverageBN6SourceCells]

theorem terminalPkgCRestorationCoverageBN6PositiveCells_payloadAtoms
    {Atom Payload ActivationAtom SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq Atom] [DecidableEq ActivationAtom]
    [DecidableEq SemanticSignature] [DecidableEq TransportType]
    [DecidableEq Frontier] [DecidableEq ChargeOwner]
    [DecidableEq Obligation] [DecidableEq OriginKernel]
    [DecidableEq ModeProjection]
    {carrier : List Atom}
    (cells : List (TerminalPkgCRestorationCoverageBN6SourceCell Atom Payload
      ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection carrier))
    (singletonized : forall cell, cell ∈ cells ->
      cell.source.consumerSystem.DisjointPairsSingletonized) :
    (terminalPkgCRestorationCoverageBN6PositiveCells cells singletonized).map
        TerminalBN6PositiveCell.payloadAtom =
      cells.map fun cell => cell.source.payloadAtom := by
  unfold terminalPkgCRestorationCoverageBN6PositiveCells
  rw [terminalPkgCBN6PositiveCells_payloadAtoms]
  simp [terminalPkgCRestorationCoverageBN6SourceCells, List.map_map]

/-- Source activation weight after forgetting only the routing side data. -/
def terminalPkgCRestorationCoverageBN6SourceActivationWeight
    {Atom Payload ActivationAtom SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq Atom] [DecidableEq ActivationAtom]
    [DecidableEq SemanticSignature] [DecidableEq TransportType]
    [DecidableEq Frontier] [DecidableEq ChargeOwner]
    [DecidableEq Obligation] [DecidableEq OriginKernel]
    [DecidableEq ModeProjection]
    {carrier : List Atom}
    (cells : List (TerminalPkgCRestorationCoverageBN6SourceCell Atom Payload
      ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection carrier))
    (cut : List Atom) : Nat :=
  terminalPkgCBN6SourceActivationWeight
    (terminalPkgCRestorationCoverageBN6SourceCells cells) cut

theorem terminalPkgCRestorationCoverageBN6PositiveCells_activationWeight
    {Atom Payload ActivationAtom SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq Atom] [DecidableEq ActivationAtom]
    [DecidableEq SemanticSignature] [DecidableEq TransportType]
    [DecidableEq Frontier] [DecidableEq ChargeOwner]
    [DecidableEq Obligation] [DecidableEq OriginKernel]
    [DecidableEq ModeProjection]
    {carrier : List Atom}
    (cells : List (TerminalPkgCRestorationCoverageBN6SourceCell Atom Payload
      ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection carrier))
    (singletonized : forall cell, cell ∈ cells ->
      cell.source.consumerSystem.DisjointPairsSingletonized)
    (cut : List Atom) :
    terminalBN6PositiveCellsActivationWeight carrier
        (terminalPkgCRestorationCoverageBN6PositiveCells cells singletonized)
        cut =
      terminalPkgCRestorationCoverageBN6SourceActivationWeight cells cut := by
  exact terminalPkgCBN6PositiveCells_activationWeight
    (terminalPkgCRestorationCoverageBN6SourceCells cells)
    (terminalPkgCRestorationCoverageBN6SourceCells_singletonized cells
      singletonized) cut

/-! ## Total first-obstruction classifier -/

inductive TerminalPkgCRestorationCoverageBN6LedgerOutcome
    {Atom Payload ActivationAtom SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq Atom] [DecidableEq ActivationAtom]
    [DecidableEq SemanticSignature] [DecidableEq TransportType]
    [DecidableEq Frontier] [DecidableEq ChargeOwner]
    [DecidableEq Obligation] [DecidableEq OriginKernel]
    [DecidableEq ModeProjection]
    (carrier : List Atom)
    (cells : List (TerminalPkgCRestorationCoverageBN6SourceCell Atom Payload
      ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection carrier)) where
  | cellized
      (singletonized : forall cell, cell ∈ cells ->
        cell.source.consumerSystem.DisjointPairsSingletonized)
  | hallRoute
      (cell : TerminalPkgCRestorationCoverageBN6SourceCell Atom Payload
        ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
        Obligation OriginKernel ModeProjection carrier)
      (member : cell ∈ cells)
      (pair : TerminalPkgCSeparatingPair cell.source.consumerSystem)
      (deficit : TerminalBN5HallDeficit
        (pair.quotientUnits cell.restoration)
        (cell.restoration.fullRestorations pair))
  | reduced
      (cell : TerminalPkgCRestorationCoverageBN6SourceCell Atom Payload
        ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
        Obligation OriginKernel ModeProjection carrier)
      (member : cell ∈ cells)
      (pair : TerminalPkgCSeparatingPair cell.source.consumerSystem)
      (realization : TerminalPkgCRestorationCoverageCancellationRealization
        pair cell.restoration)
      (remainder : List (TerminalBN4ActivationCell ActivationAtom
        SemanticSignature TransportType))
      (embedding : TerminalPkgCRestorationCoverageAmbientBN4Embedding pair
        cell.restoration cell.ambient remainder)
      (reduction :
        TerminalPkgCRestorationCoverageAmbientBN4ResidualReduction embedding)
  | ambientMismatch
      (cell : TerminalPkgCRestorationCoverageBN6SourceCell Atom Payload
        ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
        Obligation OriginKernel ModeProjection carrier)
      (member : cell ∈ cells)
      (pair : TerminalPkgCSeparatingPair cell.source.consumerSystem)
      (realization : TerminalPkgCRestorationCoverageCancellationRealization
        pair cell.restoration)
      (missingCell : TerminalBN4ActivationCell ActivationAtom
        SemanticSignature TransportType)
      (generatedMember : missingCell ∈
        pair.restorationCoverageCancellationCells cell.restoration)
      (noExactEmbedding : forall remainder,
        ¬ TerminalPkgCRestorationCoverageAmbientBN4Embedding pair
          cell.restoration cell.ambient remainder)

def classifyTerminalPkgCRestorationCoverageBN6Ledger
    {Atom Payload ActivationAtom SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq Atom] [DecidableEq ActivationAtom]
    [DecidableEq SemanticSignature] [DecidableEq TransportType]
    [DecidableEq Frontier] [DecidableEq ChargeOwner]
    [DecidableEq Obligation] [DecidableEq OriginKernel]
    [DecidableEq ModeProjection]
    (carrier : List Atom) :
    (cells : List (TerminalPkgCRestorationCoverageBN6SourceCell Atom Payload
      ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection carrier)) ->
      TerminalPkgCRestorationCoverageBN6LedgerOutcome carrier cells
  | [] => .cellized (by simp)
  | head :: tail =>
      match classifyTerminalPkgCRestorationCoverageAmbientBN4Route
          head.source.consumerSystem head.restoration head.ambient with
      | .singletonized headSingletonized =>
          match classifyTerminalPkgCRestorationCoverageBN6Ledger carrier
              tail with
          | .cellized tailSingletonized =>
              .cellized (by
                intro cell member
                rcases List.mem_cons.mp member with headEqual | tailMember
                · subst cell
                  exact headSingletonized
                · exact tailSingletonized cell tailMember)
          | .hallRoute cell member pair deficit =>
              .hallRoute cell (List.Mem.tail head member) pair deficit
          | .reduced cell member pair realization remainder embedding
              reduction =>
              .reduced cell (List.Mem.tail head member) pair realization
                remainder embedding reduction
          | .ambientMismatch cell member pair realization missingCell
              generatedMember noExactEmbedding =>
              .ambientMismatch cell (List.Mem.tail head member) pair
                realization missingCell generatedMember noExactEmbedding
      | .hallRoute pair deficit =>
          .hallRoute head (List.Mem.head tail) pair deficit
      | .reduced pair realization remainder embedding reduction =>
          .reduced head (List.Mem.head tail) pair realization remainder
            embedding reduction
      | .ambientMismatch pair realization missingCell generatedMember
          noExactEmbedding =>
          .ambientMismatch head (List.Mem.head tail) pair realization
            missingCell generatedMember noExactEmbedding

/-- Public M205 endpoint. The complete arbitrary-finite source ledger either
    constructs M201's exact BN6 ledger without a typed restorer, or preserves
    the first exact M204 Hall, reduction, or incompatibility result. -/
theorem terminalPkgC_restorationCoverage_bn6_cellization_checked_complete
    {Atom Payload ActivationAtom SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq Atom] [DecidableEq ActivationAtom]
    [DecidableEq SemanticSignature] [DecidableEq TransportType]
    [DecidableEq Frontier] [DecidableEq ChargeOwner]
    [DecidableEq Obligation] [DecidableEq OriginKernel]
    [DecidableEq ModeProjection]
    (carrier : List Atom)
    (cells : List (TerminalPkgCRestorationCoverageBN6SourceCell Atom Payload
      ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection carrier)) :
    (∃ singletonized : forall cell, cell ∈ cells ->
        cell.source.consumerSystem.DisjointPairsSingletonized,
      (terminalPkgCRestorationCoverageBN6PositiveCells cells
          singletonized).length = cells.length ∧
      (terminalPkgCRestorationCoverageBN6PositiveCells cells
          singletonized).map TerminalBN6PositiveCell.payloadAtom =
        cells.map (fun cell => cell.source.payloadAtom) ∧
      forall cut,
        terminalBN6PositiveCellsActivationWeight carrier
            (terminalPkgCRestorationCoverageBN6PositiveCells cells
              singletonized) cut =
          terminalPkgCRestorationCoverageBN6SourceActivationWeight cells
            cut) ∨
      ∃ cell, cell ∈ cells ∧
        ∃ pair : TerminalPkgCSeparatingPair cell.source.consumerSystem,
          (∃ deficit : TerminalBN5HallDeficit
              (pair.quotientUnits cell.restoration)
              (cell.restoration.fullRestorations pair),
            deficit.pkgCNamedLocalRoute = .qRestorationHall ∧
              deficit.neighborShadows.length < deficit.fullSubset.length) ∨
          Nonempty
              (TerminalPkgCRestorationCoverageCancellationRealization pair
                cell.restoration) ∧
            ((∃ remainder,
                ∃ embedding :
                    TerminalPkgCRestorationCoverageAmbientBN4Embedding pair
                      cell.restoration cell.ambient remainder,
                  Nonempty
                    (TerminalPkgCRestorationCoverageAmbientBN4ResidualReduction
                      embedding)) ∨
              ∃ missingCell,
                missingCell ∈
                  pair.restorationCoverageCancellationCells
                    cell.restoration ∧
                forall remainder,
                  ¬ TerminalPkgCRestorationCoverageAmbientBN4Embedding pair
                    cell.restoration cell.ambient remainder) := by
  exact match classifyTerminalPkgCRestorationCoverageBN6Ledger carrier cells
      with
    | .cellized singletonized =>
        Or.inl ⟨singletonized,
          terminalPkgCRestorationCoverageBN6PositiveCells_length cells
            singletonized,
          terminalPkgCRestorationCoverageBN6PositiveCells_payloadAtoms cells
            singletonized,
          terminalPkgCRestorationCoverageBN6PositiveCells_activationWeight
            cells singletonized⟩
    | .hallRoute cell member pair deficit =>
        Or.inr ⟨cell, member, pair, Or.inl ⟨deficit, rfl,
          deficit.neighbor_card_lt_full_card⟩⟩
    | .reduced cell member pair realization remainder embedding reduction =>
        Or.inr ⟨cell, member, pair, Or.inr ⟨⟨realization⟩,
          Or.inl ⟨remainder, embedding, ⟨reduction⟩⟩⟩⟩
    | .ambientMismatch cell member pair realization missingCell
        generatedMember noExactEmbedding =>
        Or.inr ⟨cell, member, pair, Or.inr ⟨⟨realization⟩,
          Or.inr ⟨missingCell, generatedMember, noExactEmbedding⟩⟩⟩

end DirectWire
end PNP
