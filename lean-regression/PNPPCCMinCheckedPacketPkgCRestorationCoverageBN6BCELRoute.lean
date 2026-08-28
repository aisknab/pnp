import PNP.PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELRoute

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire
namespace PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELRouteRegression

variable {inputs gates outputs profileWidth rankCount : Nat}
variable {candidate : Candidate inputs gates outputs}
variable {model : TerminalCandidateSaturationModel
  (profileWidth := profileWidth) candidate}
variable {SemanticSignature TransportType Frontier ChargeOwner Obligation
  OriginKernel ModeProjection : Type}
variable [DecidableEq SemanticSignature] [DecidableEq TransportType]
variable [DecidableEq Frontier] [DecidableEq ChargeOwner]
variable [DecidableEq Obligation] [DecidableEq OriginKernel]
variable [DecidableEq ModeProjection]

variable (data :
  PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELSourceData candidate model
    rankCount SemanticSignature TransportType Frontier ChargeOwner Obligation
    OriginKernel ModeProjection)

/-! ## Every total-classifier branch remains distinct -/

private def outcomeTag :
    PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELRouteOrZeroSlack data →
      Nat
  | .zeroSlack _ => 0
  | .hallRoute _ _ _ _ => 1
  | .ambientReduction _ _ _ _ _ _ _ _ => 2
  | .ambientMismatch _ _ _ _ _ _ _ _ => 3
  | .activationRoute _ _ _ _ _ _ => 4

example
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
    (classified : classifyTerminalPkgCRestorationCoverageBN6Ledger
      data.terminalReady.result.nucleus.anchors data.sourceCells =
        .hallRoute cell member pair deficit) :
    outcomeTag data data.routeOrZeroSlack = 1 := by
  simp [PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELSourceData.routeOrZeroSlack,
    classified, outcomeTag]

example
    (cell : TerminalPkgCRestorationCoverageBN6SourceCell
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)
      (TerminalPacketSelectorFaithfulnessPayload rankCount)
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)
      SemanticSignature TransportType Frontier ChargeOwner Obligation
      OriginKernel ModeProjection data.terminalReady.result.nucleus.anchors)
    (member : cell ∈ data.sourceCells)
    (pair : TerminalPkgCSeparatingPair cell.source.consumerSystem)
    (realization : TerminalPkgCRestorationCoverageCancellationRealization
      pair cell.restoration)
    (remainder : List (TerminalBN4ActivationCell
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)
      SemanticSignature TransportType))
    (embedding : TerminalPkgCRestorationCoverageAmbientBN4Embedding pair
      cell.restoration cell.ambient remainder)
    (reduction :
      TerminalPkgCRestorationCoverageAmbientBN4ResidualReduction embedding)
    (classified : classifyTerminalPkgCRestorationCoverageBN6Ledger
      data.terminalReady.result.nucleus.anchors data.sourceCells =
        .reduced cell member pair realization remainder embedding reduction) :
    outcomeTag data data.routeOrZeroSlack = 2 := by
  simp [PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELSourceData.routeOrZeroSlack,
    classified, outcomeTag]

example
    (cell : TerminalPkgCRestorationCoverageBN6SourceCell
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)
      (TerminalPacketSelectorFaithfulnessPayload rankCount)
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)
      SemanticSignature TransportType Frontier ChargeOwner Obligation
      OriginKernel ModeProjection data.terminalReady.result.nucleus.anchors)
    (member : cell ∈ data.sourceCells)
    (pair : TerminalPkgCSeparatingPair cell.source.consumerSystem)
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
    (classified : classifyTerminalPkgCRestorationCoverageBN6Ledger
      data.terminalReady.result.nucleus.anchors data.sourceCells =
        .ambientMismatch cell member pair realization missingCell
          generatedMember noExactEmbedding) :
    outcomeTag data data.routeOrZeroSlack = 3 := by
  simp [PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELSourceData.routeOrZeroSlack,
    classified, outcomeTag]

example
    (singletonized : forall cell, cell ∈ data.sourceCells ->
      cell.source.consumerSystem.DisjointPairsSingletonized)
    (result : ZeroSlackResult candidate.toImplementation)
    (classified : classifyTerminalPkgCRestorationCoverageBN6Ledger
      data.terminalReady.result.nucleus.anchors data.sourceCells =
        .cellized singletonized)
    (closed :
      let downstream := data.cellizedData singletonized
      let canonical := downstream.toCanonicalGroupingData
      canonical.sparseActivationRouteOrZeroSlackOfSilence
        downstream.silence = .zeroSlack result) :
    outcomeTag data data.routeOrZeroSlack = 0 := by
  simp [PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELSourceData.routeOrZeroSlack,
    classified, closed, outcomeTag]

example
    (singletonized : forall cell, cell ∈ data.sourceCells ->
      cell.source.consumerSystem.DisjointPairsSingletonized)
    (route :
      let downstream := data.cellizedData singletonized
      let canonical := downstream.toCanonicalGroupingData
      PCCMinCheckedPacketBN6BCELSparseActivationMismatch canonical)
    (classified : classifyTerminalPkgCRestorationCoverageBN6Ledger
      data.terminalReady.result.nucleus.anchors data.sourceCells =
        .cellized singletonized)
    (routed :
      let downstream := data.cellizedData singletonized
      let canonical := downstream.toCanonicalGroupingData
      canonical.sparseActivationRouteOrZeroSlackOfSilence
        downstream.silence = .activationRoute route) :
    outcomeTag data data.routeOrZeroSlack = 4 := by
  simp [PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELSourceData.routeOrZeroSlack,
    classified, routed, outcomeTag]

/-! ## The successful branch uses the projected M205 ledger definitionally -/

variable
  (singletonized : forall cell, cell ∈ data.sourceCells ->
    cell.source.consumerSystem.DisjointPairsSingletonized)

example :
    (terminalPkgCBN6BCELPositiveCells data.problem data.terminalReady
      rankCount
      (terminalPkgCRestorationCoverageBN6SourceCells data.sourceCells)
      (terminalPkgCRestorationCoverageBN6SourceCells_singletonized
        data.sourceCells singletonized)).cells =
      terminalPkgCRestorationCoverageBN6PositiveCells data.sourceCells
        singletonized := rfl

example (cut : List
    (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    terminalBN6PositiveCellsActivationWeight
        data.terminalReady.result.nucleus.anchors
        (terminalPkgCRestorationCoverageBN6PositiveCells data.sourceCells
          singletonized) cut =
      terminalPkgCRestorationCoverageBN6SourceActivationWeight
        data.sourceCells cut :=
  terminalPkgCRestorationCoverageBN6PositiveCells_activationWeight
    data.sourceCells singletonized cut

example :=
  pccmin_checked_packet_pkgc_restoration_coverage_bn6_bcel_route_or_zeroslack_checked_complete
    data

#print axioms PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELSourceData
#print axioms PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELSourceData.routeOrZeroSlack
#print axioms pccmin_checked_packet_pkgc_restoration_coverage_bn6_bcel_route_or_zeroslack_checked_complete

end PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELRouteRegression
end DirectWire
end PNP
