import PNP.ResidualTerminalPacketSelectorPayloadRealization

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire

variable {Atom Payload : Type} [DecidableEq Atom]
variable {family : TerminalBN6GroupedFamily Atom Payload}

/-! ## Generic source-payload materialization -/

example (handle : family.PacketSelectorHandle) :
    family.packetSelectorCell handle ∈ family.groups ∧
      (family.packetSelectorCell handle).footprint =
        family.packetSelectorFootprint handle ∧
      family.packetSelectorPayloadAtom handle ∈
        (family.packetSelectorCell handle).atoms ∧
      0 < (family.packetSelectorPayloadAtom handle).mass :=
  ⟨family.packetSelectorCell_mem_groups handle,
    family.packetSelectorCell_footprint handle,
    family.packetSelectorPayloadAtom_mem handle,
    (family.packetSelectorPayloadAtom handle).massPositive⟩

example (bits : Concrete.BitString) :
    family.realizePacketSelectorPayload bits = none ↔
      family.decodePacketSelectorHandle bits = none :=
  family.realizePacketSelectorPayload_eq_none_iff bits

example (bits : Concrete.BitString)
    (realized : TerminalPacketSelectorPayloadRealization family)
    (result : family.realizePacketSelectorPayload bits = some realized) :
    family.decodePacketSelectorHandle bits = some realized.handle ∧
      family.encodePacketSelectorHandle realized.handle = bits ∧
      realized.cell ∈ family.groups ∧
      realized.cell.footprint =
        family.packetSelectorFootprint realized.handle ∧
      realized.atom ∈ realized.cell.atoms ∧
      0 < realized.atom.mass :=
  ⟨family.decodePacketSelectorHandle_eq_some_of_realize bits realized result,
    family.realizePacketSelectorPayload_sound bits realized result⟩

example (handle : family.PacketSelectorHandle) :
    ∃ realized,
      family.realizePacketSelectorPayload
        (family.encodePacketSelectorHandle handle) = some realized ∧
      realized.handle = handle :=
  family.exists_realizePacketSelectorPayload_encode handle

example (bits : Concrete.BitString) (footprint : List Atom) :
    family.IsRealizedPacketSelectorAt bits footprint ↔
      family.IsEncodedPacketSelectorAt bits footprint :=
  family.isRealizedPacketSelectorAt_iff_encoded bits footprint

example (footprint : List Atom) :
    family.HasRealizedPacketSelectorAt footprint ↔
      family.HasPacketPayloadSelectorAt footprint :=
  family.hasRealizedPacketSelectorAt_iff_payloadSelector footprint

/-! ## Every logical Packet branch upgrades without a fixed bound -/

example
    (carrierLength : family.carrier.length = 2)
    (fullPositive : 0 <
      family.hypergraph.footprintWeight family.carrier)
    (selector : family.HasEncodedPacketSelectorAt family.carrier) :
    TerminalPacketRealizedSelectorConclusion family :=
  (TerminalPacketEncodedSelectorConclusion.pair carrierLength fullPositive
    selector).selectorPayloadRealizations

example
    (carrierLength : family.carrier.length = 3)
    (pairMass : Nat)
    (pairPositive : 0 < pairMass)
    (everyPair : ∀ footprint, footprint.Sublist family.carrier ->
      footprint.length = 2 ->
        family.hypergraph.footprintWeight footprint = pairMass)
    (selectors : ∀ footprint, footprint.Sublist family.carrier ->
      footprint.length = 2 ->
        family.HasEncodedPacketSelectorAt footprint) :
    TerminalPacketRealizedSelectorConclusion family :=
  (TerminalPacketEncodedSelectorConclusion.balancedTriple carrierLength
    pairMass pairPositive everyPair selectors).selectorPayloadRealizations

example
    (carrierLength : 3 ≤ family.carrier.length)
    (fullPositive : 0 <
      family.hypergraph.footprintWeight family.carrier)
    (selector : family.HasEncodedPacketSelectorAt family.carrier) :
    TerminalPacketRealizedSelectorConclusion family :=
  (TerminalPacketEncodedSelectorConclusion.fullSpan carrierLength fullPositive
    selector).selectorPayloadRealizations

example (conclusion : TerminalBN6PacketConclusion family) :
    TerminalPacketRealizedSelectorConclusion family :=
  conclusion.selectorPayloadRealizations

#print axioms TerminalBN6GroupedFamily.packetSelectorCell_footprint
#print axioms TerminalBN6GroupedFamily.packetSelectorPayloadAtom_mem
#print axioms TerminalBN6GroupedFamily.realizePacketSelectorPayload_eq_none_iff
#print axioms TerminalBN6GroupedFamily.decodePacketSelectorHandle_eq_some_of_realize
#print axioms TerminalBN6GroupedFamily.exists_realizePacketSelectorPayload_encode
#print axioms TerminalBN6GroupedFamily.realizePacketSelectorPayload_sound
#print axioms TerminalBN6GroupedFamily.isRealizedPacketSelectorAt_iff_encoded
#print axioms TerminalBN6GroupedFamily.hasRealizedPacketSelectorAt_iff_payloadSelector
#print axioms TerminalPacketEncodedSelectorConclusion.selectorPayloadRealizations
#print axioms TerminalBN6PacketConclusion.selectorPayloadRealizations
#print axioms terminalBN6_packet_selector_payload_realizations

end DirectWire
end PNP
