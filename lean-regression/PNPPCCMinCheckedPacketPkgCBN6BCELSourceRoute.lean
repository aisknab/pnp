import PNP.PCCMinCheckedPacketPkgCBN6BCELSourceRoute

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire
namespace PCCMinCheckedPacketPkgCBN6BCELSourceRouteRegression

/-! ## The raw BN6 ledger is definitionally source-derived -/

variable {inputs gates outputs profileWidth rankCount : Nat}
variable {candidate : Candidate inputs gates outputs}
variable {model : TerminalCandidateSaturationModel
  (profileWidth := profileWidth) candidate}
variable (problem : TerminalFiniteSaturatePositiveProblem candidate model)
variable (terminalReady : TerminalFiniteBCELReadyCertificate problem)
variable (sourceCells : List (TerminalPkgCBN6SourceCell
  (TerminalPrimitiveRecord inputs gates outputs profileWidth)
  (TerminalPacketSelectorFaithfulnessPayload rankCount)
  terminalReady.result.nucleus.anchors))
variable (singletonized : ∀ cell, cell ∈ sourceCells →
  cell.consumerSystem.DisjointPairsSingletonized)

example :
    (terminalPkgCBN6BCELPositiveCells problem terminalReady rankCount
      sourceCells singletonized).cells =
      terminalPkgCBN6PositiveCells sourceCells singletonized := rfl

example :
    (terminalPkgCBN6BCELPositiveCells problem terminalReady rankCount
      sourceCells singletonized).cells.length = sourceCells.length :=
  terminalPkgCBN6PositiveCells_length sourceCells singletonized

example :
    (terminalPkgCBN6BCELPositiveCells problem terminalReady rankCount
      sourceCells singletonized).cells.map
        TerminalBN6PositiveCell.payloadAtom =
      sourceCells.map TerminalPkgCBN6SourceCell.payloadAtom :=
  terminalPkgCBN6PositiveCells_payloadAtoms sourceCells singletonized

example (cut : List
    (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    terminalBN6PositiveCellsActivationWeight
        terminalReady.result.nucleus.anchors
        (terminalPkgCBN6BCELPositiveCells problem terminalReady rankCount
          sourceCells singletonized).cells cut =
      terminalPkgCBN6SourceActivationWeight sourceCells cut :=
  terminalPkgCBN6PositiveCells_activationWeight sourceCells singletonized cut

/-! ## All three total-classifier branches remain proof-bearing -/

variable {FullCandidate ActivationAtom SemanticSignature TransportType Frontier
  ChargeOwner Obligation OriginKernel ModeProjection : Type}
variable [DecidableEq ActivationAtom] [DecidableEq SemanticSignature]
variable [DecidableEq TransportType] [DecidableEq Frontier]
variable [DecidableEq ChargeOwner] [DecidableEq Obligation]
variable [DecidableEq OriginKernel] [DecidableEq ModeProjection]

variable (data : PCCMinCheckedPacketPkgCBN6BCELSourceHBData candidate model
  rankCount FullCandidate ActivationAtom SemanticSignature TransportType
  Frontier ChargeOwner Obligation OriginKernel ModeProjection)

private def outcomeTag :
    PCCMinCheckedPacketPkgCBN6BCELSourceRouteOrZeroSlack data → Nat
  | .zeroSlack _ => 0
  | .pkgCCancellation _ _ _ _ => 1
  | .activationRoute _ _ _ _ _ _ => 2

example
    (cell : TerminalPkgCBN6SourceCell
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)
      (TerminalPacketSelectorFaithfulnessPayload rankCount)
      data.terminalReady.result.nucleus.anchors)
    (member : cell ∈ data.sourceCells)
    (pair : TerminalPkgCSeparatingPair cell.consumerSystem)
    (realization : TerminalPkgCSameKeyCancellationRealization pair
      data.restorer)
    (classified : classifyTerminalPkgCBN6Cellization
      data.terminalReady.result.nucleus.anchors data.restorer
      data.sourceCells =
        .pkgCCancellation cell member pair realization) :
    outcomeTag data data.sourceRouteOrZeroSlack = 1 := by
  simp [PCCMinCheckedPacketPkgCBN6BCELSourceHBData.sourceRouteOrZeroSlack,
    classified, outcomeTag]

example
    (singletonized : ∀ cell, cell ∈ data.sourceCells →
      cell.consumerSystem.DisjointPairsSingletonized)
    (result : ZeroSlackResult candidate.toImplementation)
    (classified : classifyTerminalPkgCBN6Cellization
      data.terminalReady.result.nucleus.anchors data.restorer
      data.sourceCells = .cellized singletonized)
    (closed :
      let downstream := data.cellizedData singletonized
      let canonical := downstream.toCanonicalGroupingData
      canonical.sparseActivationRouteOrZeroSlackOfSilence
        downstream.silence = .zeroSlack result) :
    outcomeTag data data.sourceRouteOrZeroSlack = 0 := by
  simp [PCCMinCheckedPacketPkgCBN6BCELSourceHBData.sourceRouteOrZeroSlack,
    classified, closed, outcomeTag]

example
    (singletonized : ∀ cell, cell ∈ data.sourceCells →
      cell.consumerSystem.DisjointPairsSingletonized)
    (route :
      let downstream := data.cellizedData singletonized
      let canonical := downstream.toCanonicalGroupingData
      PCCMinCheckedPacketBN6BCELSparseActivationMismatch canonical)
    (classified : classifyTerminalPkgCBN6Cellization
      data.terminalReady.result.nucleus.anchors data.restorer
      data.sourceCells = .cellized singletonized)
    (routed :
      let downstream := data.cellizedData singletonized
      let canonical := downstream.toCanonicalGroupingData
      canonical.sparseActivationRouteOrZeroSlackOfSilence
        downstream.silence = .activationRoute route) :
    outcomeTag data data.sourceRouteOrZeroSlack = 2 := by
  simp [PCCMinCheckedPacketPkgCBN6BCELSourceHBData.sourceRouteOrZeroSlack,
    classified, routed, outcomeTag]

example :
    residualSlack candidate.toImplementation = 0 ∨
      (∃ cell, cell ∈ data.sourceCells ∧
        ∃ pair : TerminalPkgCSeparatingPair cell.consumerSystem,
          Nonempty (TerminalPkgCSameKeyCancellationRealization pair
            data.restorer)) ∨
      ∃ cut,
        cut.Sublist data.terminalReady.result.nucleus.anchors ∧
        cut ≠ [] ∧
        cut ≠ data.terminalReady.result.nucleus.anchors ∧
        cut.length ≤ 2 ∧
        terminalPkgCBN6SourceActivationWeight data.sourceCells cut ≠
          data.problem.anchorProblem.toProblem.familyDefect
            data.terminalReady.result.nucleus.anchors :=
  pccmin_checked_packet_pkgc_bn6_bcel_source_route_or_zeroslack_checked_complete
    data

end PCCMinCheckedPacketPkgCBN6BCELSourceRouteRegression
end DirectWire
end PNP
