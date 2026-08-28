/-
Copyright (c) 2026 PNP Labs.

Candidate-bound PkgC restoration coverage at the checked BN6/BCEL route.

M205 scans an arbitrary finite enriched PkgC source ledger without an
always-total typed restorer.  It preserves the first exact restoration Hall
deficit, ambient BN4 residual reduction, or ambient incompatibility, and only
constructs the BN6 positive-cell ledger after every source system has been
proved singletonized.  M202 separately feeds the older typed-restorer
cellization into the checked BN6/BCEL sparse activation boundary.

This module composes those two boundaries.  Every ambient ledger is tied to
the same computed BCEL nucleus, every M205 obstruction is retained literally,
and only the all-singletonized branch enters the downstream checked Packet/HB
classifier.  A downstream raw-cell mismatch is reflected back to the original
enriched source ledger by M205's all-cut activation conservation theorem.

The terminal problem, enriched source cells, restoration universes, ambient
ledgers, ranks, claims, dependency table, checked HB closure, route-clear
result, and selector silence remain supplied.  Hall, ambient, and activation
outcomes are not yet verified gains or globally decreasing routes.  This
module does not complete PkgC/BN3--BN6, prove unconditional ZeroSlack,
polynomial PCCMin, SAT in P, or P = NP.
-/

import PNP.ResidualTerminalPkgCRestorationCoverageBN6Ledger

namespace PNP
namespace DirectWire

/-! ## Candidate-bound restoration-coverage source data -/

/-- An arbitrary finite M205 source ledger tied to one checked BCEL nucleus.
    The downstream checked data may depend on the proof that every source
    consumer system is singletonized, but neither a typed restorer nor an
    independent BN6 positive-cell ledger is admitted. -/
structure PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELSourceData
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (rankCount : Nat)
    (SemanticSignature TransportType Frontier ChargeOwner Obligation
      OriginKernel ModeProjection : Type)
    [DecidableEq SemanticSignature] [DecidableEq TransportType]
    [DecidableEq Frontier] [DecidableEq ChargeOwner]
    [DecidableEq Obligation] [DecidableEq OriginKernel]
    [DecidableEq ModeProjection] where
  problem : TerminalFiniteSaturatePositiveProblem candidate model
  terminalReady : TerminalFiniteBCELReadyCertificate problem
  sourceCells : List (TerminalPkgCRestorationCoverageBN6SourceCell
    (TerminalPrimitiveRecord inputs gates outputs profileWidth)
    (TerminalPacketSelectorFaithfulnessPayload rankCount)
    (TerminalPrimitiveRecord inputs gates outputs profileWidth)
    SemanticSignature TransportType Frontier ChargeOwner Obligation
    OriginKernel ModeProjection terminalReady.result.nucleus.anchors)
  ambientCanonicalAtoms : forall cell, cell ∈ sourceCells ->
    TerminalBN4CellsUseCanonicalAtoms terminalReady.result cell.ambient
  cellizedData :
    (singletonized : forall cell, cell ∈ sourceCells ->
      cell.source.consumerSystem.DisjointPairsSingletonized) ->
    PCCMinCheckedPacketPkgCBN6BCELCellizedData problem terminalReady
      rankCount
      (terminalPkgCRestorationCoverageBN6SourceCells sourceCells)
      (terminalPkgCRestorationCoverageBN6SourceCells_singletonized sourceCells
        singletonized)

/-! ## Total restoration/BN6/BCEL classifier -/

/-- The complete proof-bearing M206 outcome.  The first three route branches
    are M205's exact obstructions; the final route is M200's sparse proper-cut
    mismatch reflected to the original enriched source ledger. -/
inductive PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELRouteOrZeroSlack
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {SemanticSignature TransportType Frontier ChargeOwner Obligation
      OriginKernel ModeProjection : Type}
    [DecidableEq SemanticSignature] [DecidableEq TransportType]
    [DecidableEq Frontier] [DecidableEq ChargeOwner]
    [DecidableEq Obligation] [DecidableEq OriginKernel]
    [DecidableEq ModeProjection]
    (data :
      PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELSourceData candidate
        model rankCount SemanticSignature TransportType Frontier ChargeOwner
        Obligation OriginKernel ModeProjection) where
  | zeroSlack (result : ZeroSlackResult candidate.toImplementation)
  | hallRoute
      (cell : TerminalPkgCRestorationCoverageBN6SourceCell
        (TerminalPrimitiveRecord inputs gates outputs profileWidth)
        (TerminalPacketSelectorFaithfulnessPayload rankCount)
        (TerminalPrimitiveRecord inputs gates outputs profileWidth)
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection data.terminalReady.result.nucleus.anchors)
      (member : cell ∈ data.sourceCells)
      (pair : TerminalPkgCSeparatingPair cell.source.consumerSystem)
      (deficit : TerminalBN5HallDeficit
        (pair.quotientUnits cell.restoration)
        (cell.restoration.fullRestorations pair))
  | ambientReduction
      (cell : TerminalPkgCRestorationCoverageBN6SourceCell
        (TerminalPrimitiveRecord inputs gates outputs profileWidth)
        (TerminalPacketSelectorFaithfulnessPayload rankCount)
        (TerminalPrimitiveRecord inputs gates outputs profileWidth)
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection data.terminalReady.result.nucleus.anchors)
      (member : cell ∈ data.sourceCells)
      (pair : TerminalPkgCSeparatingPair cell.source.consumerSystem)
      (canonicalAtoms :
        TerminalBN4CellsUseCanonicalAtoms data.terminalReady.result
          cell.ambient)
      (realization : TerminalPkgCRestorationCoverageCancellationRealization
        pair cell.restoration)
      (remainder : List (TerminalBN4ActivationCell
        (TerminalPrimitiveRecord inputs gates outputs profileWidth)
        SemanticSignature TransportType))
      (embedding : TerminalPkgCRestorationCoverageAmbientBN4Embedding pair
        cell.restoration cell.ambient remainder)
      (reduction :
        TerminalPkgCRestorationCoverageAmbientBN4ResidualReduction embedding)
  | ambientMismatch
      (cell : TerminalPkgCRestorationCoverageBN6SourceCell
        (TerminalPrimitiveRecord inputs gates outputs profileWidth)
        (TerminalPacketSelectorFaithfulnessPayload rankCount)
        (TerminalPrimitiveRecord inputs gates outputs profileWidth)
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection data.terminalReady.result.nucleus.anchors)
      (member : cell ∈ data.sourceCells)
      (pair : TerminalPkgCSeparatingPair cell.source.consumerSystem)
      (canonicalAtoms :
        TerminalBN4CellsUseCanonicalAtoms data.terminalReady.result
          cell.ambient)
      (realization : TerminalPkgCRestorationCoverageCancellationRealization
        pair cell.restoration)
      (missingCell : TerminalBN4ActivationCell
        (TerminalPrimitiveRecord inputs gates outputs profileWidth)
        SemanticSignature TransportType)
      (generatedMember : missingCell ∈
        pair.restorationCoverageCancellationCells cell.restoration)
      (noExactEmbedding : forall remainder,
        ¬ TerminalPkgCRestorationCoverageAmbientBN4Embedding pair
          cell.restoration cell.ambient remainder)
  | activationRoute
      (cut : List
        (TerminalPrimitiveRecord inputs gates outputs profileWidth))
      (included : cut.Sublist data.terminalReady.result.nucleus.anchors)
      (nonempty : cut ≠ [])
      (proper : cut ≠ data.terminalReady.result.nucleus.anchors)
      (length_le_two : cut.length <= 2)
      (sourceMismatch :
        terminalPkgCRestorationCoverageBN6SourceActivationWeight
            data.sourceCells cut ≠
          data.problem.anchorProblem.toProblem.familyDefect
            data.terminalReady.result.nucleus.anchors)

/-- Run M205 first.  Only its all-singletonized result constructs the exact
    source-derived BN6 ledger and enters M200's checked sparse-activation
    classifier. -/
def PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELSourceData.routeOrZeroSlack
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {SemanticSignature TransportType Frontier ChargeOwner Obligation
      OriginKernel ModeProjection : Type}
    [DecidableEq SemanticSignature] [DecidableEq TransportType]
    [DecidableEq Frontier] [DecidableEq ChargeOwner]
    [DecidableEq Obligation] [DecidableEq OriginKernel]
    [DecidableEq ModeProjection]
    (data :
      PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELSourceData candidate
        model rankCount SemanticSignature TransportType Frontier ChargeOwner
        Obligation OriginKernel ModeProjection) :
    PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELRouteOrZeroSlack data := by
  match classifyTerminalPkgCRestorationCoverageBN6Ledger
      data.terminalReady.result.nucleus.anchors data.sourceCells with
  | .cellized singletonized =>
      let downstream := data.cellizedData singletonized
      let canonical := downstream.toCanonicalGroupingData
      match canonical.sparseActivationRouteOrZeroSlackOfSilence
          downstream.silence with
      | .zeroSlack result => exact .zeroSlack result
      | .activationRoute route =>
          have sourceMismatch :
              terminalPkgCRestorationCoverageBN6SourceActivationWeight
                  data.sourceCells route.cut ≠
                data.problem.anchorProblem.toProblem.familyDefect
                  data.terminalReady.result.nucleus.anchors := by
            intro sourceEqual
            apply route.rawMismatch
            change terminalBN6PositiveCellsActivationWeight
                data.terminalReady.result.nucleus.anchors
                (terminalPkgCRestorationCoverageBN6PositiveCells
                  data.sourceCells singletonized) route.cut =
              data.problem.anchorProblem.toProblem.familyDefect
                data.terminalReady.result.nucleus.anchors
            exact
              (terminalPkgCRestorationCoverageBN6PositiveCells_activationWeight
                data.sourceCells singletonized route.cut).trans sourceEqual
          exact .activationRoute route.cut route.included route.nonempty
            route.proper route.length_le_two sourceMismatch
  | .hallRoute cell member pair deficit =>
      exact .hallRoute cell member pair deficit
  | .reduced cell member pair realization remainder embedding reduction =>
      exact .ambientReduction cell member pair
        (data.ambientCanonicalAtoms cell member) realization remainder
        embedding reduction
  | .ambientMismatch cell member pair realization missingCell
      generatedMember noExactEmbedding =>
      exact .ambientMismatch cell member pair
        (data.ambientCanonicalAtoms cell member) realization missingCell
        generatedMember noExactEmbedding

/-- Public M206 endpoint.  The arbitrary finite candidate-bound source ledger
    yields conditional ZeroSlack, the first exact restoration/Hall/ambient
    obstruction, or one source-ledger singleton/pair activation mismatch. -/
theorem pccmin_checked_packet_pkgc_restoration_coverage_bn6_bcel_route_or_zeroslack_checked_complete
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {SemanticSignature TransportType Frontier ChargeOwner Obligation
      OriginKernel ModeProjection : Type}
    [DecidableEq SemanticSignature] [DecidableEq TransportType]
    [DecidableEq Frontier] [DecidableEq ChargeOwner]
    [DecidableEq Obligation] [DecidableEq OriginKernel]
    [DecidableEq ModeProjection]
    (data :
      PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELSourceData candidate
        model rankCount SemanticSignature TransportType Frontier ChargeOwner
        Obligation OriginKernel ModeProjection) :
    residualSlack candidate.toImplementation = 0 ∨
      (exists cell, cell ∈ data.sourceCells ∧
        exists pair : TerminalPkgCSeparatingPair
            cell.source.consumerSystem,
          (exists deficit : TerminalBN5HallDeficit
              (pair.quotientUnits cell.restoration)
              (cell.restoration.fullRestorations pair),
            deficit.pkgCNamedLocalRoute = .qRestorationHall ∧
              deficit.neighborShadows.length < deficit.fullSubset.length) ∨
          TerminalBN4CellsUseCanonicalAtoms data.terminalReady.result
              cell.ambient ∧
            Nonempty
              (TerminalPkgCRestorationCoverageCancellationRealization pair
                cell.restoration) ∧
            ((exists remainder,
                exists embedding :
                    TerminalPkgCRestorationCoverageAmbientBN4Embedding pair
                      cell.restoration cell.ambient remainder,
                  Nonempty
                    (TerminalPkgCRestorationCoverageAmbientBN4ResidualReduction
                      embedding)) ∨
              exists missingCell,
                missingCell ∈
                  pair.restorationCoverageCancellationCells
                    cell.restoration ∧
                forall remainder,
                  ¬ TerminalPkgCRestorationCoverageAmbientBN4Embedding pair
                    cell.restoration cell.ambient remainder)) ∨
      exists cut,
        cut.Sublist data.terminalReady.result.nucleus.anchors ∧
        cut ≠ [] ∧
        cut ≠ data.terminalReady.result.nucleus.anchors ∧
        cut.length <= 2 ∧
        terminalPkgCRestorationCoverageBN6SourceActivationWeight
            data.sourceCells cut ≠
          data.problem.anchorProblem.toProblem.familyDefect
            data.terminalReady.result.nucleus.anchors := by
  exact match data.routeOrZeroSlack with
    | .zeroSlack result => Or.inl result.sound
    | .hallRoute cell member pair deficit =>
        Or.inr (Or.inl ⟨cell, member, pair, Or.inl ⟨deficit, rfl,
          deficit.neighbor_card_lt_full_card⟩⟩)
    | .ambientReduction cell member pair canonicalAtoms realization remainder
        embedding reduction =>
        Or.inr (Or.inl ⟨cell, member, pair, Or.inr ⟨canonicalAtoms,
          ⟨realization⟩, Or.inl ⟨remainder, embedding, ⟨reduction⟩⟩⟩⟩)
    | .ambientMismatch cell member pair canonicalAtoms realization missingCell
        generatedMember noExactEmbedding =>
        Or.inr (Or.inl ⟨cell, member, pair, Or.inr ⟨canonicalAtoms,
          ⟨realization⟩, Or.inr ⟨missingCell, generatedMember,
            noExactEmbedding⟩⟩⟩)
    | .activationRoute cut included nonempty proper length_le_two
        sourceMismatch =>
        Or.inr (Or.inr ⟨cut, included, nonempty, proper, length_le_two,
          sourceMismatch⟩)

end DirectWire
end PNP
