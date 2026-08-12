import PNP.ResidualTerminalPacketSelectorUniverse

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire

variable {Atom Payload : Type} [DecidableEq Atom]
variable {family : TerminalBN6GroupedFamily Atom Payload}

/-! ## Exact universe membership from arbitrary seed data -/

example {footprint : List Atom}
    (seed : family.HasPacketSelectorSeedAt footprint) :
    family.HasPacketPayloadSelectorAt footprint :=
  family.hasPacketPayloadSelectorAt_of_seed footprint seed

example {footprint : List Atom}
    (selector : family.HasPacketPayloadSelectorAt footprint) :
    footprint ∈ family.packetPayloadSelectorUniverse ∧
      footprint.Sublist family.carrier ∧
      2 ≤ footprint.length ∧ family.HasPayloadAt footprint :=
  ⟨selector.1, selector.2⟩

example : family.packetPayloadSelectorUniverse.Nodup :=
  family.packetPayloadSelectorUniverse_nodup

/-! ## Every logical Packet branch upgrades without a fixed carrier -/

example
    (carrierLength : family.carrier.length = 2)
    (fullPositive : 0 <
      family.hypergraph.footprintWeight family.carrier)
    (seed : family.HasPacketSelectorSeedAt family.carrier) :
    TerminalPacketPayloadSelectorConclusion family :=
  (TerminalPacketSelectorSeedConclusion.pair carrierLength fullPositive seed)
    |>.payloadSelectors

example
    (carrierLength : family.carrier.length = 3)
    (pairMass : Nat)
    (pairPositive : 0 < pairMass)
    (everyPair : ∀ footprint, footprint.Sublist family.carrier ->
      footprint.length = 2 ->
        family.hypergraph.footprintWeight footprint = pairMass)
    (seeds : ∀ footprint, footprint.Sublist family.carrier ->
      footprint.length = 2 ->
        family.HasPacketSelectorSeedAt footprint) :
    TerminalPacketPayloadSelectorConclusion family :=
  (TerminalPacketSelectorSeedConclusion.balancedTriple carrierLength
    pairMass pairPositive everyPair seeds).payloadSelectors

example
    (carrierLength : 3 ≤ family.carrier.length)
    (fullPositive : 0 <
      family.hypergraph.footprintWeight family.carrier)
    (seed : family.HasPacketSelectorSeedAt family.carrier) :
    TerminalPacketPayloadSelectorConclusion family :=
  (TerminalPacketSelectorSeedConclusion.fullSpan carrierLength fullPositive
    seed).payloadSelectors

example
    (conclusion : TerminalBN6PacketConclusion family) :
    TerminalPacketPayloadSelectorConclusion family :=
  conclusion.payloadSelectors

#print axioms TerminalBN6GroupedFamily.hasPacketPayloadSelectorAt_of_seed
#print axioms TerminalPacketSelectorSeedConclusion.payloadSelectors
#print axioms TerminalBN6PacketConclusion.payloadSelectors
#print axioms terminalBN6_packet_payload_selectors

end DirectWire
end PNP
