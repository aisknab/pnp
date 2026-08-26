import PNP.PCCMinCheckedPacketBN6BCELActivationRoute

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire
namespace PCCMinCheckedPacketBN6BCELActivationRouteRegression

variable {inputs gates outputs profileWidth rankCount : Nat}
variable {candidate : Candidate inputs gates outputs}
variable {model : TerminalCandidateSaturationModel
  (profileWidth := profileWidth) candidate}
variable (data : PCCMinCheckedPacketBN6BCELHBData
  candidate model rankCount)

/-! ## Total arbitrary-finite classification -/

example : Nonempty
    (PCCMinCheckedPacketBN6BCELActivationClassification data) :=
  classifyPCCMinCheckedPacketBN6BCELActivation_exhaustive data

example (mismatch : data.family.carrier ≠ data.bcelCarrier) :
    PCCMinCheckedPacketBN6BCELActivationRoute data :=
  .carrierMismatch mismatch

example
    (carrierBinding : data.family.carrier = data.bcelCarrier)
    (mismatch : data.family.cutValue ≠ data.bcelDefect) :
    PCCMinCheckedPacketBN6BCELActivationRoute data :=
  .cutValueMismatch carrierBinding mismatch

example
    (carrierBinding : data.family.carrier = data.bcelCarrier)
    (cutValueBinding : data.family.cutValue = data.bcelDefect)
    (cut : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (included : cut.Sublist data.family.carrier)
    (nonempty : cut ≠ [])
    (proper : cut ≠ data.family.carrier)
    (mismatch : data.family.activationWeight cut ≠ data.bcelDefect) :
    PCCMinCheckedPacketBN6BCELActivationRoute data :=
  .activationMismatch carrierBinding cutValueBinding cut included nonempty
    proper mismatch

/-! ## Coherent BCEL branch -/

example
    (coherent : PCCMinCheckedPacketBN6BCELActivationCoherent data) :
    2 ≤ data.family.carrier.length :=
  coherent.carrierAtLeastTwo

example
    (coherent : PCCMinCheckedPacketBN6BCELActivationCoherent data) :
    data.family.ConstantActivation :=
  coherent.constantActivation

example
    (coherent : PCCMinCheckedPacketBN6BCELActivationCoherent data)
    (cut : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (proper : TerminalBCELProperCutSeed data.bcelCarrier cut) :
    Int.ofNat (data.family.activationWeight cut) =
      ((data.problem.anchorProblem.toProblem.cutCarrier
        data.terminalReady.result.nucleus.anchors cut).optimizationCorners
          data.problem.anchorProblem.toProblem.observe).projectionExcess :=
  coherent.activation_eq_projectionExcess cut proper

example
    (coherent : PCCMinCheckedPacketBN6BCELActivationCoherent data) :
    PCCMinCheckedPacketBN6HBZeroSlackData candidate.toImplementation
      (TerminalPrimitiveRecord inputs gates outputs profileWidth) rankCount :=
  coherent.toBN6HBZeroSlackData

/-! ## Exact route-or-ZeroSlack terminal boundary -/

variable (silence : ∀ rank selector,
  selector ∈
    data.rawTable.withComputedPacketSelectorFaithfulness.selectorsAtRank rank →
  ∃ reason : TerminalPacketTypedRealizerBot
      data.family.PacketSelectorHandle rankCount,
    data.rawTable.withComputedPacketSelectorFaithfulness.checkedOutcome
        data.claimsAccepted selector = .blocked reason)

example : PCCMinCheckedPacketBN6BCELRouteOrZeroSlack data :=
  data.routeOrZeroSlackOfSilence silence

example :
    residualSlack candidate.toImplementation = 0 ∨
      data.family.carrier ≠ data.bcelCarrier ∨
      (data.family.carrier = data.bcelCarrier ∧
        data.family.cutValue ≠ data.bcelDefect) ∨
      ∃ cut,
        data.family.carrier = data.bcelCarrier ∧
        data.family.cutValue = data.bcelDefect ∧
        cut.Sublist data.family.carrier ∧ cut ≠ [] ∧
        cut ≠ data.family.carrier ∧
        data.family.activationWeight cut ≠ data.bcelDefect :=
  pccmin_checked_packet_bn6_bcel_activation_route_or_zeroslack_checked_complete
    data silence

end PCCMinCheckedPacketBN6BCELActivationRouteRegression
end DirectWire
end PNP
