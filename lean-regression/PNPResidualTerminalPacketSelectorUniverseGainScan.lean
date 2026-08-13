import PNP.ResidualTerminalPacketSelectorUniverseGainScan

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire

variable {Atom : Type} [DecidableEq Atom]
variable {inputs outputs : Nat}
variable {family : TerminalBN6GroupedFamily Atom
  (Implementation inputs outputs)}
variable {current : Implementation inputs outputs}

/-! ## Exact exhaustive handle enumeration and scan -/

example (handle : family.PacketSelectorHandle) :
    handle ∈ family.packetSelectorHandles :=
  family.mem_packetSelectorHandles handle

example :
    family.packetSelectorHandles.length =
      family.packetPayloadSelectorUniverse.length :=
  family.packetSelectorHandles_length

example (handles : List family.PacketSelectorHandle) :
    (∃ handle, handle ∈ handles ∧
      ∃ atom : TerminalBN6PayloadAtom (Implementation inputs outputs),
        atom ∈ (family.packetSelectorCell handle).atoms ∧
          StrictEquivalentGain current atom.payload) ∨
      (∀ handle, handle ∈ handles ->
        ∀ atom, atom ∈ (family.packetSelectorCell handle).atoms ->
          ¬StrictEquivalentGain current atom.payload) :=
  (scanTerminalPacketSelectorHandleGains family current handles).sound

example :
    (∃ handle : family.PacketSelectorHandle,
      ∃ atom : TerminalBN6PayloadAtom (Implementation inputs outputs),
        atom ∈ (family.packetSelectorCell handle).atoms ∧
          StrictEquivalentGain current atom.payload) ∨
      (∀ handle : family.PacketSelectorHandle,
        ∀ atom, atom ∈ (family.packetSelectorCell handle).atoms ->
          ¬StrictEquivalentGain current atom.payload) :=
  family.scanPacketSelectorUniverseGains_sound current

/-! ## Exact source, canonical code, and strict descent -/

example (handle : family.PacketSelectorHandle)
    (atom : TerminalBN6PayloadAtom (Implementation inputs outputs))
    (atomMember : atom ∈ (family.packetSelectorCell handle).atoms)
    (verified : StrictEquivalentGain current atom.payload) :
    family.decodePacketSelectorHandle
        (family.encodePacketSelectorHandle handle) = some handle ∧
      family.packetSelectorCell handle ∈ family.groups ∧
      (family.packetSelectorCell handle).footprint =
        family.packetSelectorFootprint handle ∧
      atom ∈ (family.packetSelectorCell handle).atoms ∧
      StrictEquivalentGain current atom.payload :=
  family.universeGain_source_and_code current handle atom atomMember verified

example (handle : family.PacketSelectorHandle)
    (atom : TerminalBN6PayloadAtom (Implementation inputs outputs))
    (atomMember : atom ∈ (family.packetSelectorCell handle).atoms)
    (verified : StrictEquivalentGain current atom.payload) :
    residualSlack atom.payload < residualSlack current :=
  TerminalPacketSelectorUniverseGainOutcome.gain_strictResidualDescent
    handle atom atomMember verified

example
    (noGain : ∀ handle : family.PacketSelectorHandle,
      ∀ atom, atom ∈ (family.packetSelectorCell handle).atoms ->
        ¬StrictEquivalentGain current atom.payload)
    (bits : Concrete.BitString)
    (scan : TerminalPacketSelectorGainScan family current)
    (scanned : family.scanPacketSelectorGains current bits = some scan)
    (atom : TerminalBN6PayloadAtom (Implementation inputs outputs))
    (atomMember : atom ∈
      (family.packetSelectorCell scan.handle).atoms) :
    ¬StrictEquivalentGain current atom.payload :=
  family.universeNoGain_of_gainScan current noGain bits scan scanned atom
    atomMember

/-! ## Every Packet alternative is retained literally -/

example
    (carrierLength : family.carrier.length = 2)
    (fullPositive : 0 <
      family.hypergraph.footprintWeight family.carrier)
    (selector : family.HasEncodedPacketSelectorAt family.carrier) :
    TerminalPacketSelectorUniverseGainScanConclusion family current :=
  (TerminalPacketEncodedSelectorConclusion.pair carrierLength fullPositive
    selector).universeGainScan current

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
    TerminalPacketSelectorUniverseGainScanConclusion family current :=
  (TerminalPacketEncodedSelectorConclusion.balancedTriple carrierLength
    pairMass pairPositive everyPair selectors).universeGainScan current

example
    (carrierLength : 3 ≤ family.carrier.length)
    (fullPositive : 0 <
      family.hypergraph.footprintWeight family.carrier)
    (selector : family.HasEncodedPacketSelectorAt family.carrier) :
    TerminalPacketSelectorUniverseGainScanConclusion family current :=
  (TerminalPacketEncodedSelectorConclusion.fullSpan carrierLength fullPositive
    selector).universeGainScan current

example (conclusion : TerminalPacketEncodedSelectorConclusion family) :
    (conclusion.universeGainScan current).packet = conclusion :=
  conclusion.universeGainScan_packet current

example (conclusion : TerminalBN6PacketConclusion family) :
    TerminalPacketSelectorUniverseGainScanConclusion family current :=
  conclusion.universeGainScan current

end DirectWire
end PNP
