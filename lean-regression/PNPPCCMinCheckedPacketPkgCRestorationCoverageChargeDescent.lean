import PNP.PCCMinCheckedPacketPkgCRestorationCoverageChargeDescent

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire
namespace PCCMinCheckedPacketPkgCRestorationCoverageChargeDescentRegression

/-! ## The charge measure is mass-sensitive and permutation invariant -/

private def heavyCell : TerminalBN4ActivationCell Nat Nat Nat :=
  { key := { atom := 1, semanticSignature := 2, transportType := 3 }
    sign := .positive
    mass := 7 }

example : terminalBN4UnsignedChargeSize [heavyCell] = 7 := rfl

example : terminalBN4UnsignedChargeSize [heavyCell, heavyCell] = 14 := rfl

example : terminalBN4UnsignedChargeSize [heavyCell, heavyCell] =
    terminalBN4UnsignedChargeSize ([heavyCell] ++ [heavyCell]) := by
  rfl

/-! ## Arbitrary exact embeddings yield scalar and rank descent -/

variable {ConsumerAtom ActivationAtom SemanticSignature TransportType Frontier
  ChargeOwner Obligation OriginKernel ModeProjection : Type}
variable [DecidableEq ActivationAtom] [DecidableEq SemanticSignature]
variable [DecidableEq TransportType]
variable {system : TerminalV54ConsumerSystem ConsumerAtom}
variable {pair : TerminalPkgCSeparatingPair system}
variable {restoration : TerminalPkgCRestorationUniverse ConsumerAtom
  (TerminalBN5ShadowCoordinate ActivationAtom SemanticSignature TransportType
    Frontier ChargeOwner Obligation OriginKernel ModeProjection)}
variable {ambient remainder : List (TerminalBN4ActivationCell ActivationAtom
  SemanticSignature TransportType)}
variable (embedding : TerminalPkgCRestorationCoverageAmbientBN4Embedding pair
  restoration ambient remainder)

example : terminalBN4UnsignedChargeSize ambient =
    terminalBN4UnsignedChargeSize
        (pair.restorationCoverageCancellationCells restoration) +
      terminalBN4UnsignedChargeSize remainder :=
  embedding.unsignedChargeSize_decomposition

example : terminalBN4UnsignedChargeSize remainder <
    terminalBN4UnsignedChargeSize ambient :=
  embedding.remainder_unsignedChargeSize_lt

example (context : TerminalPkgCBN4ChargeRankContext) :
    (context.rank (terminalBN4UnsignedChargeSize remainder)).LexLT
      (context.rank (terminalBN4UnsignedChargeSize ambient)) :=
  embedding.chargeRank_lt context

example : Nonempty
    (TerminalPkgCRestorationCoverageAmbientBN4ChargeDescent embedding) :=
  ⟨embedding.chargeDescent⟩

/-! ## Every M206 branch remains distinct after composition -/

variable {inputs gates outputs profileWidth rankCount : Nat}
variable {candidate : Candidate inputs gates outputs}
variable {model : TerminalCandidateSaturationModel
  (profileWidth := profileWidth) candidate}
variable {RouteSemanticSignature RouteTransportType RouteFrontier
  RouteChargeOwner RouteObligation RouteOriginKernel RouteModeProjection : Type}
variable [DecidableEq RouteSemanticSignature]
variable [DecidableEq RouteTransportType]
variable [DecidableEq RouteFrontier] [DecidableEq RouteChargeOwner]
variable [DecidableEq RouteObligation] [DecidableEq RouteOriginKernel]
variable [DecidableEq RouteModeProjection]

variable (data :
  PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELSourceData candidate model
    rankCount RouteSemanticSignature RouteTransportType RouteFrontier
    RouteChargeOwner RouteObligation RouteOriginKernel RouteModeProjection)

private def outcomeTag :
    PCCMinCheckedPacketPkgCRestorationCoverageChargeRouteOrZeroSlack data → Nat
  | .zeroSlack _ => 0
  | .hallRoute _ _ _ _ => 1
  | .ambientChargeDescent _ _ _ _ _ _ _ _ => 2
  | .ambientMismatch _ _ _ _ _ _ _ _ => 3
  | .activationRoute _ _ _ _ _ _ => 4

example
    (cell : TerminalPkgCRestorationCoverageBN6SourceCell
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)
      (TerminalPacketSelectorFaithfulnessPayload rankCount)
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)
      RouteSemanticSignature RouteTransportType RouteFrontier RouteChargeOwner
      RouteObligation RouteOriginKernel RouteModeProjection
      data.terminalReady.result.nucleus.anchors)
    (member : cell ∈ data.sourceCells)
    (routePair : TerminalPkgCSeparatingPair cell.source.consumerSystem)
    (deficit : TerminalBN5HallDeficit
      (routePair.quotientUnits cell.restoration)
      (cell.restoration.fullRestorations routePair))
    (classified : data.routeOrZeroSlack =
      .hallRoute cell member routePair deficit) :
    outcomeTag data data.chargeRouteOrZeroSlack = 1 := by
  simp [PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELSourceData.chargeRouteOrZeroSlack,
    classified, outcomeTag]

example
    (cell : TerminalPkgCRestorationCoverageBN6SourceCell
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)
      (TerminalPacketSelectorFaithfulnessPayload rankCount)
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)
      RouteSemanticSignature RouteTransportType RouteFrontier RouteChargeOwner
      RouteObligation RouteOriginKernel RouteModeProjection
      data.terminalReady.result.nucleus.anchors)
    (member : cell ∈ data.sourceCells)
    (routePair : TerminalPkgCSeparatingPair cell.source.consumerSystem)
    (canonicalAtoms :
      TerminalBN4CellsUseCanonicalAtoms data.terminalReady.result cell.ambient)
    (realization : TerminalPkgCRestorationCoverageCancellationRealization
      routePair cell.restoration)
    (routeRemainder : List (TerminalBN4ActivationCell
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)
      RouteSemanticSignature RouteTransportType))
    (routeEmbedding : TerminalPkgCRestorationCoverageAmbientBN4Embedding
      routePair cell.restoration cell.ambient routeRemainder)
    (reduction :
      TerminalPkgCRestorationCoverageAmbientBN4ResidualReduction
        routeEmbedding)
    (classified : data.routeOrZeroSlack =
      .ambientReduction cell member routePair canonicalAtoms realization
        routeRemainder routeEmbedding reduction) :
    outcomeTag data data.chargeRouteOrZeroSlack = 2 := by
  simp [PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELSourceData.chargeRouteOrZeroSlack,
    classified, outcomeTag]

example
    (cell : TerminalPkgCRestorationCoverageBN6SourceCell
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)
      (TerminalPacketSelectorFaithfulnessPayload rankCount)
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)
      RouteSemanticSignature RouteTransportType RouteFrontier RouteChargeOwner
      RouteObligation RouteOriginKernel RouteModeProjection
      data.terminalReady.result.nucleus.anchors)
    (member : cell ∈ data.sourceCells)
    (routePair : TerminalPkgCSeparatingPair cell.source.consumerSystem)
    (canonicalAtoms :
      TerminalBN4CellsUseCanonicalAtoms data.terminalReady.result cell.ambient)
    (realization : TerminalPkgCRestorationCoverageCancellationRealization
      routePair cell.restoration)
    (missingCell : TerminalBN4ActivationCell
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)
      RouteSemanticSignature RouteTransportType)
    (generatedMember : missingCell ∈
      routePair.restorationCoverageCancellationCells cell.restoration)
    (noExactEmbedding : forall routeRemainder,
      ¬ TerminalPkgCRestorationCoverageAmbientBN4Embedding routePair
        cell.restoration cell.ambient routeRemainder)
    (classified : data.routeOrZeroSlack =
      .ambientMismatch cell member routePair canonicalAtoms realization
        missingCell generatedMember noExactEmbedding) :
    outcomeTag data data.chargeRouteOrZeroSlack = 3 := by
  simp [PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELSourceData.chargeRouteOrZeroSlack,
    classified, outcomeTag]

example
    (result : ZeroSlackResult candidate.toImplementation)
    (classified : data.routeOrZeroSlack = .zeroSlack result) :
    outcomeTag data data.chargeRouteOrZeroSlack = 0 := by
  simp [PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELSourceData.chargeRouteOrZeroSlack,
    classified, outcomeTag]

example
    (cut : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (included : cut.Sublist data.terminalReady.result.nucleus.anchors)
    (nonempty : cut ≠ [])
    (proper : cut ≠ data.terminalReady.result.nucleus.anchors)
    (length_le_two : cut.length <= 2)
    (sourceMismatch :
      terminalPkgCRestorationCoverageBN6SourceActivationWeight
          data.sourceCells cut ≠
        data.problem.anchorProblem.toProblem.familyDefect
          data.terminalReady.result.nucleus.anchors)
    (classified : data.routeOrZeroSlack =
      .activationRoute cut included nonempty proper length_le_two
        sourceMismatch) :
    outcomeTag data data.chargeRouteOrZeroSlack = 4 := by
  simp [PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELSourceData.chargeRouteOrZeroSlack,
    classified, outcomeTag]

example :=
  pccmin_checked_packet_pkgc_restoration_coverage_charge_route_or_zeroslack_checked_complete
    data

#print axioms terminalBN4UnsignedChargeSize
#print axioms TerminalPkgCRestorationCoverageAmbientBN4Embedding.chargeDescent
#print axioms PCCMinCheckedPacketPkgCRestorationCoverageBN6BCELSourceData.chargeRouteOrZeroSlack
#print axioms pccmin_checked_packet_pkgc_restoration_coverage_charge_route_or_zeroslack_checked_complete

end PCCMinCheckedPacketPkgCRestorationCoverageChargeDescentRegression
end DirectWire
end PNP
