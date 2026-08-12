import PNP.ResidualTerminalPacketSelectorSeeds

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire

variable {Atom Payload : Type} [DecidableEq Atom]
variable {family : TerminalBN6GroupedFamily Atom Payload}

/-! ## Generic branch regressions -/

example
    (carrierLength : family.carrier.length = 2)
    (fullWeight : family.hypergraph.footprintWeight family.carrier =
      family.cutValue)
    (fullPositive : 0 <
      family.hypergraph.footprintWeight family.carrier)
    (payload : family.HasPayloadAt family.carrier) :
    TerminalPacketSelectorSeedConclusion family :=
  (TerminalBN6PacketConclusion.pair carrierLength fullWeight fullPositive
    payload).selectorSeeds

example
    (carrierLength : family.carrier.length = 3)
    (pairMass : Nat)
    (pairPositive : 0 < pairMass)
    (everyPair : ∀ footprint, footprint.Sublist family.carrier ->
      footprint.length = 2 ->
        family.hypergraph.footprintWeight footprint = pairMass)
    (massEquation : family.hypergraph.footprintWeight family.carrier +
      2 * pairMass = family.cutValue)
    (balancedPayloads : 0 < pairMass ->
      ∀ footprint, footprint.Sublist family.carrier ->
        footprint.length = 2 -> family.HasPayloadAt footprint)
    (fullSpanPayload :
      0 < family.hypergraph.footprintWeight family.carrier ->
        family.HasPayloadAt family.carrier) :
    TerminalPacketSelectorSeedConclusion family :=
  (TerminalBN6PacketConclusion.balancedTripleOrFullSpan carrierLength
    pairMass everyPair massEquation (Or.inl pairPositive)
    balancedPayloads fullSpanPayload).selectorSeeds

example
    (carrierLength : family.carrier.length = 3)
    (pairMass : Nat)
    (everyPair : ∀ footprint, footprint.Sublist family.carrier ->
      footprint.length = 2 ->
        family.hypergraph.footprintWeight footprint = pairMass)
    (massEquation : family.hypergraph.footprintWeight family.carrier +
      2 * pairMass = family.cutValue)
    (fullPositive : 0 <
      family.hypergraph.footprintWeight family.carrier)
    (balancedPayloads : 0 < pairMass ->
      ∀ footprint, footprint.Sublist family.carrier ->
        footprint.length = 2 -> family.HasPayloadAt footprint)
    (fullSpanPayload :
      0 < family.hypergraph.footprintWeight family.carrier ->
        family.HasPayloadAt family.carrier) :
    TerminalPacketSelectorSeedConclusion family :=
  (TerminalBN6PacketConclusion.balancedTripleOrFullSpan carrierLength
    pairMass everyPair massEquation (Or.inr fullPositive)
    balancedPayloads fullSpanPayload).selectorSeeds

example
    (carrierLarge : 4 ≤ family.carrier.length)
    (properFootprintsZero :
      ∀ footprint, footprint.Sublist family.carrier ->
        2 ≤ footprint.length -> footprint ≠ family.carrier ->
          family.hypergraph.footprintWeight footprint = 0)
    (fullWeight : family.hypergraph.footprintWeight family.carrier =
      family.cutValue)
    (fullPositive : 0 <
      family.hypergraph.footprintWeight family.carrier)
    (payload : family.HasPayloadAt family.carrier) :
    TerminalPacketSelectorSeedConclusion family :=
  (TerminalBN6PacketConclusion.fullSpan carrierLarge properFootprintsZero
    fullWeight fullPositive payload).selectorSeeds

/-! ## Seed premises remain visible -/

example {footprint : List Atom}
    (seed : family.HasPacketSelectorSeedAt footprint) :
    footprint.Sublist family.carrier ∧
      2 ≤ footprint.length ∧ family.HasPayloadAt footprint :=
  seed

#print axioms TerminalBN6PacketConclusion.selectorSeeds
#print axioms terminalBN6_packet_selector_seeds

end DirectWire
end PNP
