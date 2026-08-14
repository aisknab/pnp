import PNP.ResidualTerminalPacketSelectorGainCoverage

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire

variable {Atom : Type} [DecidableEq Atom]
variable {inputs outputs : Nat}
variable {family : TerminalBN6GroupedFamily Atom
  (Implementation inputs outputs)}
variable {current : Implementation inputs outputs}

example (coverage : TerminalPacketSelectorGainCoverage family current)
    (noGain : ∀ handle : family.PacketSelectorHandle,
      ∀ atom, atom ∈ (family.packetSelectorCell handle).atoms ->
        ¬StrictEquivalentGain current atom.payload) :
    ∀ next : Implementation inputs outputs,
      ¬StrictEquivalentGain current next :=
  coverage.noStrictEquivalentGain noGain

example (coverage : TerminalPacketSelectorGainCoverage family current)
    (noGain : ∀ handle : family.PacketSelectorHandle,
      ∀ atom, atom ∈ (family.packetSelectorCell handle).atoms ->
        ¬StrictEquivalentGain current atom.payload) :
    ZeroSlackResult current :=
  coverage.zeroSlackResult noGain

example (coverage : TerminalPacketSelectorGainCoverage family current)
    (noGain : ∀ handle : family.PacketSelectorHandle,
      ∀ atom, atom ∈ (family.packetSelectorCell handle).atoms ->
        ¬StrictEquivalentGain current atom.payload) :
    residualSlack current = 0 :=
  coverage.residualSlack_eq_zero_of_noGain noGain

example (coverage : TerminalPacketSelectorGainCoverage family current) :
    (∃ handle : family.PacketSelectorHandle,
      ∃ atom : TerminalBN6PayloadAtom (Implementation inputs outputs),
        atom ∈ (family.packetSelectorCell handle).atoms ∧
          StrictEquivalentGain current atom.payload) ∨
      ZeroSlackResult current :=
  family.scanCoveredPacketSelectorGains_sound current coverage

example (coverage : TerminalPacketSelectorGainCoverage family current) :
    (∃ handle : family.PacketSelectorHandle,
      ∃ atom : TerminalBN6PayloadAtom (Implementation inputs outputs),
        atom ∈ (family.packetSelectorCell handle).atoms ∧
          residualSlack atom.payload < residualSlack current) ∨
      residualSlack current = 0 :=
  (family.scanCoveredPacketSelectorGains current coverage).residualSlack_spec

/-! Every Packet branch remains literally present. -/

example (coverage : TerminalPacketSelectorGainCoverage family current)
    (carrierLength : family.carrier.length = 2)
    (fullPositive : 0 <
      family.hypergraph.footprintWeight family.carrier)
    (selector : family.HasEncodedPacketSelectorAt family.carrier) :
    TerminalPacketSelectorGainCoverageConclusion family current :=
  (TerminalPacketEncodedSelectorConclusion.pair carrierLength fullPositive
    selector).coveredGainScan current coverage

example (coverage : TerminalPacketSelectorGainCoverage family current)
    (carrierLength : family.carrier.length = 3)
    (pairMass : Nat)
    (pairPositive : 0 < pairMass)
    (everyPair : ∀ footprint, footprint.Sublist family.carrier ->
      footprint.length = 2 ->
        family.hypergraph.footprintWeight footprint = pairMass)
    (selectors : ∀ footprint, footprint.Sublist family.carrier ->
      footprint.length = 2 ->
        family.HasEncodedPacketSelectorAt footprint) :
    TerminalPacketSelectorGainCoverageConclusion family current :=
  (TerminalPacketEncodedSelectorConclusion.balancedTriple carrierLength
    pairMass pairPositive everyPair selectors).coveredGainScan current coverage

example (coverage : TerminalPacketSelectorGainCoverage family current)
    (carrierLength : 3 ≤ family.carrier.length)
    (fullPositive : 0 <
      family.hypergraph.footprintWeight family.carrier)
    (selector : family.HasEncodedPacketSelectorAt family.carrier) :
    TerminalPacketSelectorGainCoverageConclusion family current :=
  (TerminalPacketEncodedSelectorConclusion.fullSpan carrierLength fullPositive
    selector).coveredGainScan current coverage

example (coverage : TerminalPacketSelectorGainCoverage family current)
    (conclusion : TerminalPacketEncodedSelectorConclusion family) :
    (conclusion.coveredGainScan current coverage).packet = conclusion :=
  conclusion.coveredGainScan_packet current coverage

/-! Empty finite-family silence cannot manufacture global gain coverage. -/

def coverageEmptyFamily :
    TerminalBN6GroupedFamily Unit (Implementation 1 1) where
  carrier := []
  carrierNodup := by simp
  groups := []
  groupCarrier := by simp
  groupFootprintLarge := by simp
  groupFootprintsNodup := by simp
  cutValue := 1
  cutValuePositive := by simp

theorem coverageEmptyFamily_scan_unresolved :
    ∃ noGain, coverageEmptyFamily.scanPacketSelectorUniverseGains
      redundantIdentityImplementation =
        TerminalPacketSelectorUniverseGainOutcome.unresolved noGain := by
  cases scanned : coverageEmptyFamily.scanPacketSelectorUniverseGains
      redundantIdentityImplementation with
  | gain handle _atom _atomMember _verified => exact Fin.elim0 handle
  | unresolved noGain => exact ⟨noGain, scanned⟩

theorem coverageEmptyFamily_not_gainCoverage :
    ¬TerminalPacketSelectorGainCoverage coverageEmptyFamily
      redundantIdentityImplementation := by
  intro coverage
  have positive : 0 < residualSlack redundantIdentityImplementation := by
    rw [redundantIdentity_positiveSlack]
    decide
  have verified :=
    referenceMinimumImplementation_strictEquivalentGain_of_residualSlack_pos
      positive
  obtain ⟨handle, _atom, _atomMember, _payloadEquation⟩ :=
    coverage.covers
      (referenceMinimumImplementation redundantIdentityImplementation)
      verified
  exact Fin.elim0 handle

end DirectWire
end PNP
