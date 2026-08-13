import PNP.ResidualTerminalPacketSelectorGainScan

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire

variable {Atom : Type} [DecidableEq Atom]
variable {inputs outputs : Nat}
variable {family : TerminalBN6GroupedFamily Atom
  (Implementation inputs outputs)}
variable {current : Implementation inputs outputs}

/-! ## Generic exact source-cell scan -/

example (handle : family.PacketSelectorHandle)
    (candidate : Implementation inputs outputs) :
    candidate ∈ family.packetSelectorCandidateImplementations handle ↔
      ∃ atom : TerminalBN6PayloadAtom (Implementation inputs outputs),
        atom ∈ (family.packetSelectorCell handle).atoms ∧
          atom.payload = candidate :=
  family.mem_packetSelectorCandidateImplementations_iff handle candidate

example (atoms : List (TerminalBN6PayloadAtom
    (Implementation inputs outputs))) :
    (∃ atom, atom ∈ atoms ∧ StrictEquivalentGain current atom.payload) ∨
      (∀ atom, atom ∈ atoms →
        ¬StrictEquivalentGain current atom.payload) :=
  (scanTerminalPacketCandidateGains current atoms).sound

example (handle : family.PacketSelectorHandle) :
    (∃ atom,
      atom ∈ (family.packetSelectorCell handle).atoms ∧
        StrictEquivalentGain current atom.payload) ∨
      (∀ atom, atom ∈ (family.packetSelectorCell handle).atoms →
        ¬StrictEquivalentGain current atom.payload) :=
  (family.packetSelectorGainOutcome current handle).sound

example (atom : TerminalBN6PayloadAtom
    (Implementation inputs outputs))
    (verified : StrictEquivalentGain current atom.payload) :
    residualSlack atom.payload < residualSlack current :=
  TerminalPacketCandidateGainOutcome.gain_strictResidualDescent atom verified

/-! ## Fail-closed decoding and exact source recovery -/

example (bits : Concrete.BitString) :
    family.scanPacketSelectorGains current bits = none ↔
      family.decodePacketSelectorHandle bits = none :=
  family.scanPacketSelectorGains_eq_none_iff current bits

example (bits : Concrete.BitString) :
    (∃ scan, family.scanPacketSelectorGains current bits = some scan) ↔
      ∃ handle, family.decodePacketSelectorHandle bits = some handle :=
  family.exists_scanPacketSelectorGains_iff current bits

example (bits : Concrete.BitString)
    (scan : TerminalPacketSelectorGainScan family current)
    (scanned : family.scanPacketSelectorGains current bits = some scan) :
    family.decodePacketSelectorHandle bits = some scan.handle ∧
      family.encodePacketSelectorHandle scan.handle = bits ∧
      family.packetSelectorCell scan.handle ∈ family.groups ∧
      (family.packetSelectorCell scan.handle).footprint =
        family.packetSelectorFootprint scan.handle ∧
      ((∃ atom,
        atom ∈ (family.packetSelectorCell scan.handle).atoms ∧
          StrictEquivalentGain current atom.payload) ∨
        (∀ atom, atom ∈ (family.packetSelectorCell scan.handle).atoms →
          ¬StrictEquivalentGain current atom.payload)) :=
  ⟨family.decodePacketSelectorHandle_eq_some_of_gainScan current bits scan
      scanned,
    family.scanPacketSelectorGains_sound current bits scan scanned⟩

example (handle : family.PacketSelectorHandle) :
    ∃ scan,
      family.scanPacketSelectorGains current
        (family.encodePacketSelectorHandle handle) = some scan ∧
      scan.handle = handle :=
  family.exists_scanPacketSelectorGains_encode current handle

example (footprint : List Atom) :
    family.HasPacketSelectorGainScanAt current footprint ↔
      family.HasEncodedPacketSelectorAt footprint :=
  family.hasPacketSelectorGainScanAt_iff_encoded current footprint

/-! ## Every logical Packet branch upgrades without a fixed bound -/

example
    (carrierLength : family.carrier.length = 2)
    (fullPositive : 0 <
      family.hypergraph.footprintWeight family.carrier)
    (selector : family.HasEncodedPacketSelectorAt family.carrier) :
    TerminalPacketGainScanConclusion family current :=
  (TerminalPacketEncodedSelectorConclusion.pair carrierLength fullPositive
    selector).gainScans current

example
    (carrierLength : family.carrier.length = 3)
    (pairMass : Nat)
    (pairPositive : 0 < pairMass)
    (everyPair : ∀ footprint, footprint.Sublist family.carrier →
      footprint.length = 2 →
        family.hypergraph.footprintWeight footprint = pairMass)
    (selectors : ∀ footprint, footprint.Sublist family.carrier →
      footprint.length = 2 →
        family.HasEncodedPacketSelectorAt footprint) :
    TerminalPacketGainScanConclusion family current :=
  (TerminalPacketEncodedSelectorConclusion.balancedTriple carrierLength
    pairMass pairPositive everyPair selectors).gainScans current

example
    (carrierLength : 3 ≤ family.carrier.length)
    (fullPositive : 0 <
      family.hypergraph.footprintWeight family.carrier)
    (selector : family.HasEncodedPacketSelectorAt family.carrier) :
    TerminalPacketGainScanConclusion family current :=
  (TerminalPacketEncodedSelectorConclusion.fullSpan carrierLength fullPositive
    selector).gainScans current

example (conclusion : TerminalBN6PacketConclusion family) :
    TerminalPacketGainScanConclusion family current :=
  conclusion.gainScans current

#print axioms TerminalBN6GroupedFamily.mem_packetSelectorCandidateImplementations_iff
#print axioms scanTerminalPacketCandidateGains
#print axioms TerminalPacketCandidateGainOutcome.sound
#print axioms TerminalPacketCandidateGainOutcome.gain_strictResidualDescent
#print axioms TerminalBN6GroupedFamily.scanPacketSelectorGains_eq_none_iff
#print axioms TerminalBN6GroupedFamily.exists_scanPacketSelectorGains_iff
#print axioms TerminalBN6GroupedFamily.decodePacketSelectorHandle_eq_some_of_gainScan
#print axioms TerminalBN6GroupedFamily.scanPacketSelectorGains_sound
#print axioms TerminalBN6GroupedFamily.exists_scanPacketSelectorGains_encode
#print axioms TerminalBN6GroupedFamily.hasPacketSelectorGainScanAt_iff_encoded
#print axioms TerminalPacketEncodedSelectorConclusion.gainScans
#print axioms TerminalBN6PacketConclusion.gainScans
#print axioms terminalBN6_packet_selector_gain_scans

end DirectWire
end PNP
