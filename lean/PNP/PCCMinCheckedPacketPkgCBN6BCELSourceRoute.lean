/-
Copyright (c) 2026 PNP Labs.

Source-derived PkgC/BN6 activation routing at the checked BCEL boundary.

M201 turns an arbitrary finite ledger of active PkgC source systems into an
exact same-key cancellation or a raw BN6 positive-cell ledger whose activation
weight agrees with the source ledger on every cut. M200 independently sends a
raw BN6 ledger through canonical grouping and the checked Packet/HB boundary.
This module composes those results without accepting an independent BN6 cell
list: it retains a PkgC cancellation, genuine conditional ZeroSlack, or one
singleton/pair proper-cut mismatch reflected back to the original source
ledger.

The terminal problem, checked BCEL-ready certificate, source systems,
payloads, typed restorer, realizer table, claims, dependency table, checked HB
closure, route-clear result, and selector silence remain supplied. A returned
cancellation or activation mismatch is not yet a verified gain or globally
decreasing route. This module does not establish complete PkgC/BN3--BN6 route
integration, unconditional ZeroSlack, polynomial PCCMin, SAT in P, or P = NP.
-/

import PNP.PCCMinCheckedPacketBN6BCELSparseActivationRoute
import PNP.ResidualTerminalPkgCBN6PositiveCellization

namespace PNP
namespace DirectWire

/-! ## Source-derived positive cells and downstream data -/

/-- Install the exact M201 cellization in M197's raw positive-cell boundary.
    The caller cannot provide an independent raw BN6 ledger. -/
def terminalPkgCBN6BCELPositiveCells
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (problem : TerminalFiniteSaturatePositiveProblem candidate model)
    (terminalReady : TerminalFiniteBCELReadyCertificate problem)
    (rankCount : Nat)
    (sourceCells : List (TerminalPkgCBN6SourceCell
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)
      (TerminalPacketSelectorFaithfulnessPayload rankCount)
      terminalReady.result.nucleus.anchors))
    (singletonized : forall cell, cell ∈ sourceCells ->
      cell.consumerSystem.DisjointPairsSingletonized) :
    PCCMinCheckedPacketBN6BCELPositiveCells
      problem terminalReady rankCount where
  cells := terminalPkgCBN6PositiveCells sourceCells singletonized

/-- The still-supplied checked Packet/HB data after M201 has constructed the
    only raw positive-cell ledger admitted by this boundary. -/
structure PCCMinCheckedPacketPkgCBN6BCELCellizedData
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (problem : TerminalFiniteSaturatePositiveProblem candidate model)
    (terminalReady : TerminalFiniteBCELReadyCertificate problem)
    (rankCount : Nat)
    (sourceCells : List (TerminalPkgCBN6SourceCell
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)
      (TerminalPacketSelectorFaithfulnessPayload rankCount)
      terminalReady.result.nucleus.anchors))
    (singletonized : forall cell, cell ∈ sourceCells ->
      cell.consumerSystem.DisjointPairsSingletonized) where
  rawTable : TerminalPacketTypedRealizerTable candidate.toImplementation
    (terminalPkgCBN6BCELPositiveCells problem terminalReady rankCount
      sourceCells singletonized).groupedCells.family rankCount
  claimsAccepted :
    rawTable.withComputedPacketSelectorFaithfulness.checkEveryClaim = true
  dependencyTable : TerminalPacketHBDependencyTable rankCount
  hbClosureAccepted : dependencyTable.checkNoOutcomeActiveClosure
    rawTable.withComputedPacketSelectorFaithfulness.environment = true
  routesClear :
    (terminalPkgCBN6BCELPositiveCells problem terminalReady rankCount
      sourceCells singletonized).groupedCells.family.checkPacketSelectorRoutesClear
        rawTable.environment.rankOf = true
  silence : forall rank selector,
    selector ∈
      rawTable.withComputedPacketSelectorFaithfulness.selectorsAtRank rank ->
    exists reason : TerminalPacketTypedRealizerBot
        (terminalPkgCBN6BCELPositiveCells problem terminalReady rankCount
          sourceCells singletonized).groupedCells.family.PacketSelectorHandle
          rankCount,
      rawTable.withComputedPacketSelectorFaithfulness.checkedOutcome
          claimsAccepted selector = .blocked reason

/-- Repackage the source-derived ledger and supplied downstream checks in the
    exact canonical-grouping boundary consumed by M200. -/
def PCCMinCheckedPacketPkgCBN6BCELCellizedData.toCanonicalGroupingData
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {problem : TerminalFiniteSaturatePositiveProblem candidate model}
    {terminalReady : TerminalFiniteBCELReadyCertificate problem}
    {sourceCells : List (TerminalPkgCBN6SourceCell
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)
      (TerminalPacketSelectorFaithfulnessPayload rankCount)
      terminalReady.result.nucleus.anchors)}
    {singletonized : forall cell, cell ∈ sourceCells ->
      cell.consumerSystem.DisjointPairsSingletonized}
    (data : PCCMinCheckedPacketPkgCBN6BCELCellizedData
      problem terminalReady rankCount sourceCells singletonized) :
    PCCMinCheckedPacketBN6BCELCanonicalGroupingHBData
      candidate model rankCount where
  problem := problem
  terminalReady := terminalReady
  positiveCells := terminalPkgCBN6BCELPositiveCells problem terminalReady
    rankCount sourceCells singletonized
  rawTable := data.rawTable
  claimsAccepted := data.claimsAccepted
  dependencyTable := data.dependencyTable
  hbClosureAccepted := data.hbClosureAccepted
  routesClear := data.routesClear

/-! ## Total source classifier -/

/-- Source-level data. Downstream checked data may depend on the proof that
    the entire supplied source ledger is PkgC-singletonized, but its positive
    cells are definitionally fixed by that ledger. -/
structure PCCMinCheckedPacketPkgCBN6BCELSourceHBData
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (rankCount : Nat)
    (FullCandidate ActivationAtom SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type)
    [DecidableEq ActivationAtom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType] [DecidableEq Frontier]
    [DecidableEq ChargeOwner] [DecidableEq Obligation]
    [DecidableEq OriginKernel] [DecidableEq ModeProjection] where
  problem : TerminalFiniteSaturatePositiveProblem candidate model
  terminalReady : TerminalFiniteBCELReadyCertificate problem
  sourceCells : List (TerminalPkgCBN6SourceCell
    (TerminalPrimitiveRecord inputs gates outputs profileWidth)
    (TerminalPacketSelectorFaithfulnessPayload rankCount)
    terminalReady.result.nucleus.anchors)
  restorer : TerminalPkgCTypedRestorer
    (TerminalPrimitiveRecord inputs gates outputs profileWidth)
    FullCandidate
    (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature
      TransportType Frontier ChargeOwner Obligation OriginKernel
      ModeProjection)
  cellizedData : (singletonized : forall cell, cell ∈ sourceCells ->
    cell.consumerSystem.DisjointPairsSingletonized) ->
    PCCMinCheckedPacketPkgCBN6BCELCellizedData problem terminalReady
      rankCount sourceCells singletonized

/-- Total proof-bearing outcome at the source-derived PkgC/BN6/BCEL boundary. -/
inductive PCCMinCheckedPacketPkgCBN6BCELSourceRouteOrZeroSlack
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {FullCandidate ActivationAtom SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ActivationAtom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType] [DecidableEq Frontier]
    [DecidableEq ChargeOwner] [DecidableEq Obligation]
    [DecidableEq OriginKernel] [DecidableEq ModeProjection]
    (data : PCCMinCheckedPacketPkgCBN6BCELSourceHBData candidate model
      rankCount FullCandidate ActivationAtom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection) where
  | zeroSlack (result : ZeroSlackResult candidate.toImplementation)
  | pkgCCancellation
      (cell : TerminalPkgCBN6SourceCell
        (TerminalPrimitiveRecord inputs gates outputs profileWidth)
        (TerminalPacketSelectorFaithfulnessPayload rankCount)
        data.terminalReady.result.nucleus.anchors)
      (member : cell ∈ data.sourceCells)
      (pair : TerminalPkgCSeparatingPair cell.consumerSystem)
      (realization : TerminalPkgCSameKeyCancellationRealization pair
        data.restorer)
  | activationRoute
      (cut : List
        (TerminalPrimitiveRecord inputs gates outputs profileWidth))
      (included : cut.Sublist data.terminalReady.result.nucleus.anchors)
      (nonempty : cut ≠ [])
      (proper : cut ≠ data.terminalReady.result.nucleus.anchors)
      (length_le_two : cut.length <= 2)
      (sourceMismatch :
        terminalPkgCBN6SourceActivationWeight data.sourceCells cut ≠
          data.problem.anchorProblem.toProblem.familyDefect
            data.terminalReady.result.nucleus.anchors)

/-- First classify the exact source PkgC ledger. Only a fully singletonized
    result enters M200; its raw mismatch is then transported back through
    M201's all-cut activation conservation theorem. -/
def PCCMinCheckedPacketPkgCBN6BCELSourceHBData.sourceRouteOrZeroSlack
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {FullCandidate ActivationAtom SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ActivationAtom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType] [DecidableEq Frontier]
    [DecidableEq ChargeOwner] [DecidableEq Obligation]
    [DecidableEq OriginKernel] [DecidableEq ModeProjection]
    (data : PCCMinCheckedPacketPkgCBN6BCELSourceHBData candidate model
      rankCount FullCandidate ActivationAtom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection) :
    PCCMinCheckedPacketPkgCBN6BCELSourceRouteOrZeroSlack data := by
  match classifyTerminalPkgCBN6Cellization
      data.terminalReady.result.nucleus.anchors data.restorer
      data.sourceCells with
  | .pkgCCancellation cell member pair realization =>
      exact .pkgCCancellation cell member pair realization
  | .cellized singletonized =>
      let downstream := data.cellizedData singletonized
      let canonical := downstream.toCanonicalGroupingData
      match canonical.sparseActivationRouteOrZeroSlackOfSilence
          downstream.silence with
      | .zeroSlack result => exact .zeroSlack result
      | .activationRoute route =>
          have sourceMismatch :
              terminalPkgCBN6SourceActivationWeight data.sourceCells
                  route.cut ≠
                data.problem.anchorProblem.toProblem.familyDefect
                  data.terminalReady.result.nucleus.anchors := by
            intro sourceEqual
            apply route.rawMismatch
            change terminalBN6PositiveCellsActivationWeight
                data.terminalReady.result.nucleus.anchors
                (terminalPkgCBN6PositiveCells data.sourceCells singletonized)
                route.cut =
              data.problem.anchorProblem.toProblem.familyDefect
                data.terminalReady.result.nucleus.anchors
            exact (terminalPkgCBN6PositiveCells_activationWeight
              data.sourceCells singletonized route.cut).trans sourceEqual
          exact .activationRoute route.cut route.included route.nonempty
            route.proper route.length_le_two sourceMismatch

/-- Public M202 endpoint: the arbitrary finite source ledger yields genuine
    conditional ZeroSlack, an exact source-member PkgC same-key cancellation,
    or a singleton/pair proper cut whose original source activation differs
    from the checked BCEL defect. -/
theorem pccmin_checked_packet_pkgc_bn6_bcel_source_route_or_zeroslack_checked_complete
    {inputs gates outputs profileWidth rankCount : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {FullCandidate ActivationAtom SemanticSignature TransportType Frontier
      ChargeOwner Obligation OriginKernel ModeProjection : Type}
    [DecidableEq ActivationAtom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType] [DecidableEq Frontier]
    [DecidableEq ChargeOwner] [DecidableEq Obligation]
    [DecidableEq OriginKernel] [DecidableEq ModeProjection]
    (data : PCCMinCheckedPacketPkgCBN6BCELSourceHBData candidate model
      rankCount FullCandidate ActivationAtom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection) :
    residualSlack candidate.toImplementation = 0 ∨
      (exists cell, cell ∈ data.sourceCells ∧
        exists pair : TerminalPkgCSeparatingPair cell.consumerSystem,
          Nonempty (TerminalPkgCSameKeyCancellationRealization pair
            data.restorer)) ∨
      exists cut,
        cut.Sublist data.terminalReady.result.nucleus.anchors ∧
        cut ≠ [] ∧
        cut ≠ data.terminalReady.result.nucleus.anchors ∧
        cut.length <= 2 ∧
        terminalPkgCBN6SourceActivationWeight data.sourceCells cut ≠
          data.problem.anchorProblem.toProblem.familyDefect
            data.terminalReady.result.nucleus.anchors := by
  exact match data.sourceRouteOrZeroSlack with
    | .zeroSlack result => Or.inl result.sound
    | .pkgCCancellation cell member pair realization =>
        Or.inr (Or.inl ⟨cell, member, pair, ⟨realization⟩⟩)
    | .activationRoute cut included nonempty proper length_le_two
        sourceMismatch =>
        Or.inr (Or.inr ⟨cut, included, nonempty, proper, length_le_two,
          sourceMismatch⟩)

end DirectWire
end PNP
