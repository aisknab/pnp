import PNP.ResidualTerminalPacketSelectorCodec

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire

variable {Atom Payload : Type} [DecidableEq Atom]
variable {family : TerminalBN6GroupedFamily Atom Payload}

/-! ## Generic round trip, canonicality, bounds, and evidence -/

example (handle : family.PacketSelectorHandle) :
    family.decodePacketSelectorHandle
      (family.encodePacketSelectorHandle handle) = some handle :=
  family.decodePacketSelectorHandle_encode handle

example {left right : family.PacketSelectorHandle}
    (equal : family.encodePacketSelectorHandle left =
      family.encodePacketSelectorHandle right) :
    left = right :=
  family.encodePacketSelectorHandle_injective equal

example (handle : family.PacketSelectorHandle) :
    (family.encodePacketSelectorHandle handle).length = handle.val + 1 ∧
      (family.encodePacketSelectorHandle handle).length ≤
        family.packetPayloadSelectorUniverse.length :=
  ⟨family.encodePacketSelectorHandle_length handle,
    family.encodePacketSelectorHandle_length_le_universe handle⟩

example (bits : Concrete.BitString) (handle : family.PacketSelectorHandle)
    (decoded : family.decodePacketSelectorHandle bits = some handle) :
    family.encodePacketSelectorHandle handle = bits ∧
      family.HasPacketPayloadSelectorAt
        (family.packetSelectorFootprint handle) ∧
      (family.packetSelectorFootprint handle).Sublist family.carrier ∧
      2 ≤ (family.packetSelectorFootprint handle).length ∧
      family.HasPayloadAt (family.packetSelectorFootprint handle) :=
  ⟨family.decodePacketSelectorHandle_canonical bits handle decoded,
    family.decodePacketSelectorHandle_payloadEvidence bits handle decoded⟩

example {footprint : List Atom} :
    (∃ bits : Concrete.BitString,
      family.IsEncodedPacketSelectorAt bits footprint ∧
        ∀ other : Concrete.BitString,
          family.IsEncodedPacketSelectorAt other footprint -> other = bits) ↔
      family.HasPacketPayloadSelectorAt footprint :=
  family.existsUnique_encodedPacketSelector_iff_payloadSelector footprint

/-! ## Every logical Packet branch upgrades without a fixed bound -/

example
    (carrierLength : family.carrier.length = 2)
    (fullPositive : 0 <
      family.hypergraph.footprintWeight family.carrier)
    (selector : family.HasPacketPayloadSelectorAt family.carrier) :
    TerminalPacketEncodedSelectorConclusion family :=
  (TerminalPacketPayloadSelectorConclusion.pair carrierLength fullPositive
    selector).selectorCodes

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
    TerminalPacketEncodedSelectorConclusion family :=
  (TerminalPacketPayloadSelectorConclusion.balancedTriple carrierLength
    pairMass pairPositive everyPair selectors).selectorCodes

example
    (carrierLength : 3 ≤ family.carrier.length)
    (fullPositive : 0 <
      family.hypergraph.footprintWeight family.carrier)
    (selector : family.HasPacketPayloadSelectorAt family.carrier) :
    TerminalPacketEncodedSelectorConclusion family :=
  (TerminalPacketPayloadSelectorConclusion.fullSpan carrierLength
    fullPositive selector).selectorCodes

example (conclusion : TerminalBN6PacketConclusion family) :
    TerminalPacketEncodedSelectorConclusion family :=
  conclusion.selectorCodes

#print axioms TerminalBN6GroupedFamily.decodePacketSelectorHandle_encode
#print axioms TerminalBN6GroupedFamily.encodePacketSelectorHandle_injective
#print axioms TerminalBN6GroupedFamily.encodePacketSelectorHandle_length_le_universe
#print axioms TerminalBN6GroupedFamily.decodePacketSelectorHandle_canonical
#print axioms TerminalBN6GroupedFamily.decodePacketSelectorHandle_payloadEvidence
#print axioms TerminalBN6GroupedFamily.existsUnique_encodedPacketSelector_iff_payloadSelector
#print axioms TerminalPacketPayloadSelectorConclusion.selectorCodes
#print axioms TerminalBN6PacketConclusion.selectorCodes
#print axioms terminalBN6_packet_selector_codes

end DirectWire
end PNP
