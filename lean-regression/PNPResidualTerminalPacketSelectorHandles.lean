import PNP.ResidualTerminalPacketSelectorHandles

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire

variable {Atom Payload : Type} [DecidableEq Atom]
variable {family : TerminalBN6GroupedFamily Atom Payload}

/-! ## Generic decoding and retained evidence -/

example (handle : family.PacketSelectorHandle) :
    family.packetSelectorFootprint handle ∈
      family.packetPayloadSelectorUniverse :=
  family.packetSelectorFootprint_mem_universe handle

example {left right : family.PacketSelectorHandle}
    (equal : family.packetSelectorFootprint left =
      family.packetSelectorFootprint right) :
    left = right :=
  family.packetSelectorFootprint_injective equal

example (handle : family.PacketSelectorHandle) :
    (family.packetSelectorFootprint handle).Sublist family.carrier ∧
      2 ≤ (family.packetSelectorFootprint handle).length ∧
      family.HasPayloadAt (family.packetSelectorFootprint handle) :=
  ⟨family.packetSelectorFootprint_sublist_carrier handle,
    family.packetSelectorFootprint_large handle,
    family.packetSelectorFootprint_hasPayloadAt handle⟩

example {footprint : List Atom} :
    (∃ handle : family.PacketSelectorHandle,
      family.packetSelectorFootprint handle = footprint ∧
        ∀ other : family.PacketSelectorHandle,
          family.packetSelectorFootprint other = footprint ->
            other = handle) ↔
      family.HasPacketPayloadSelectorAt footprint :=
  family.existsUnique_packetSelectorHandle_iff_payloadSelector footprint

/-! ## Every logical Packet branch upgrades without a fixed bound -/

example
    (carrierLength : family.carrier.length = 2)
    (fullPositive : 0 <
      family.hypergraph.footprintWeight family.carrier)
    (selector : family.HasPacketPayloadSelectorAt family.carrier) :
    TerminalPacketSelectorHandleConclusion family :=
  (TerminalPacketPayloadSelectorConclusion.pair carrierLength fullPositive
    selector).selectorHandles

example
    (carrierLength : family.carrier.length = 3)
    (pairMass : Nat)
    (pairPositive : 0 < pairMass)
    (everyPair : ∀ footprint, footprint.Sublist family.carrier ->
      footprint.length = 2 ->
        family.hypergraph.footprintWeight footprint = pairMass)
    (selectors : ∀ footprint, footprint.Sublist family.carrier ->
      footprint.length = 2 ->
        family.HasPacketPayloadSelectorAt footprint) :
    TerminalPacketSelectorHandleConclusion family :=
  (TerminalPacketPayloadSelectorConclusion.balancedTriple carrierLength
    pairMass pairPositive everyPair selectors).selectorHandles

example
    (carrierLength : 3 ≤ family.carrier.length)
    (fullPositive : 0 <
      family.hypergraph.footprintWeight family.carrier)
    (selector : family.HasPacketPayloadSelectorAt family.carrier) :
    TerminalPacketSelectorHandleConclusion family :=
  (TerminalPacketPayloadSelectorConclusion.fullSpan carrierLength
    fullPositive selector).selectorHandles

example (conclusion : TerminalBN6PacketConclusion family) :
    TerminalPacketSelectorHandleConclusion family :=
  conclusion.selectorHandles

#print axioms TerminalBN6GroupedFamily.packetSelectorFootprint_injective
#print axioms TerminalBN6GroupedFamily.packetSelectorFootprint_sublist_carrier
#print axioms TerminalBN6GroupedFamily.packetSelectorFootprint_hasPayloadAt
#print axioms TerminalBN6GroupedFamily.existsUnique_packetSelectorHandle_iff_payloadSelector
#print axioms TerminalPacketPayloadSelectorConclusion.selectorHandles
#print axioms TerminalBN6PacketConclusion.selectorHandles
#print axioms terminalBN6_packet_selector_handles

end DirectWire
end PNP
