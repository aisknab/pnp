/-
Copyright (c) 2026 PNP Labs.

Same-candidate carrier coherence between the checked finite terminal
BCEL-ready nucleus and the grouped BN6 Packet family consumed by the
report-facing ZeroSlack boundary.  The terminal problem is indexed by the
exact candidate and saturation model already stored in the Packet/budget
no-lower certificate.  An explicit anchor bijection and a reflected list
equality then identify the supplied Packet carrier with the image of the
computed terminal nucleus.

The terminal problem, initial positivity proof, Packet family, anchor
bijection, payloads, budget, realizer table, dependency table, and rank maps
remain supplied finite inputs.  This module does not identify Packet-family
activation weights with terminal projection excess, derive constant activation
from positive residual slack, construct BN3--BN6 data, prove unconditional
ZeroSlack or PCCMin, establish polynomial runtime, put SAT in P, remove a
project assumption, or prove P = NP.
-/

import PNP.ResidualTerminalFiniteBCELReady
import PNP.ResidualTerminalZeroSlackPacketSelectorHBCoherence

namespace PNP

/-- Proof-bearing same-candidate binding from the exact M183 ready nucleus to
    the M180 grouped Packet carrier.  The carrier equality is reflected from
    decidable data rather than accepted as a plain caller proposition. -/
structure TerminalFiniteBCELPacketCarrierCoherenceCertificate
    (packetBudgetNoLower : PacketBudgetNoLowerZeroSlackSidecarCertificate) where
  problem : DirectWire.TerminalFiniteSaturatePositiveProblem
    packetBudgetNoLower.candidate packetBudgetNoLower.model
  terminalReady : DirectWire.TerminalFiniteBCELReadyCertificate problem
  anchorMap :
    DirectWire.TerminalPrimitiveRecord packetBudgetNoLower.inputs
        packetBudgetNoLower.gates packetBudgetNoLower.outputs
        packetBudgetNoLower.profileWidth →
      packetBudgetNoLower.Anchor
  anchorMapInjective : ∀ {left right},
    anchorMap left = anchorMap right → left = right
  anchorMapSurjective : ∀ anchor, ∃ primitive, anchorMap primitive = anchor
  carrierBindingChecked : decide
    (packetBudgetNoLower.family.carrier =
      terminalReady.result.nucleus.anchors.map anchorMap) = true

/-- The reflected check exposes the exact mapped-carrier identity. -/
theorem TerminalFiniteBCELPacketCarrierCoherenceCertificate.family_carrier_eq
    {packetBudgetNoLower : PacketBudgetNoLowerZeroSlackSidecarCertificate}
    (certificate :
      TerminalFiniteBCELPacketCarrierCoherenceCertificate
        packetBudgetNoLower) :
    packetBudgetNoLower.family.carrier =
      certificate.terminalReady.result.nucleus.anchors.map
        certificate.anchorMap :=
  of_decide_eq_true certificate.carrierBindingChecked

/-- The Packet carrier inherits the M183 nucleus's nontrivial size; no second
    carrier-size Boolean is needed at this coherent boundary. -/
theorem TerminalFiniteBCELPacketCarrierCoherenceCertificate.carrier_at_least_two
    {packetBudgetNoLower : PacketBudgetNoLowerZeroSlackSidecarCertificate}
    (certificate :
      TerminalFiniteBCELPacketCarrierCoherenceCertificate
        packetBudgetNoLower) :
    2 ≤ packetBudgetNoLower.family.carrier.length := by
  rw [certificate.family_carrier_eq, List.length_map]
  exact certificate.terminalReady.anchorSizeAtLeastTwo

/-- The exact accepted M180 branch excludes a positive Packet on the coherently
    bound family. -/
theorem TerminalFiniteBCELPacketCarrierCoherenceCertificate.no_positive_packet
    {packetBudgetNoLower : PacketBudgetNoLowerZeroSlackSidecarCertificate}
    (_certificate :
      TerminalFiniteBCELPacketCarrierCoherenceCertificate
        packetBudgetNoLower) :
    ¬DirectWire.TerminalBN6PacketConclusion packetBudgetNoLower.family :=
  packetBudgetNoLower.no_positive_packet

/-- Constant activation on the coherently bound family would construct the
    positive Packet excluded by the exact M180 checker. -/
theorem TerminalFiniteBCELPacketCarrierCoherenceCertificate.not_constant_activation
    {packetBudgetNoLower : PacketBudgetNoLowerZeroSlackSidecarCertificate}
    (certificate :
      TerminalFiniteBCELPacketCarrierCoherenceCertificate
        packetBudgetNoLower) :
    ¬packetBudgetNoLower.family.ConstantActivation := by
  intro constantActivation
  exact certificate.no_positive_packet
    (DirectWire.terminalBN6_hypergraph_packet packetBudgetNoLower.family
      certificate.carrier_at_least_two constantActivation)

/-- Named M184 endpoint: the M183 ready branch and the M180 Packet exclusion
    share one candidate, model, and exactly equivalent carrier. -/
theorem terminal_finite_bcel_packet_carrier_coherent_checked_complete
    {packetBudgetNoLower : PacketBudgetNoLowerZeroSlackSidecarCertificate}
    (certificate :
      TerminalFiniteBCELPacketCarrierCoherenceCertificate
        packetBudgetNoLower) :
    (∀ event, event ∈ certificate.problem.trace.events →
      DirectWire.TerminalSaturationClosureSafeStep
        packetBudgetNoLower.candidate packetBudgetNoLower.model event) ∧
    0 < (DirectWire.terminalSaturationCostSnapshot
      packetBudgetNoLower.candidate packetBudgetNoLower.model
      certificate.problem.trace.replayRecords).fullSlack ∧
    0 < certificate.problem.anchorProblem.toProblem.familyDefect
      certificate.problem.anchorProblem.toProblem.anchorRecords ∧
    (∀ {left right}, certificate.anchorMap left =
      certificate.anchorMap right → left = right) ∧
    (∀ anchor, ∃ primitive, certificate.anchorMap primitive = anchor) ∧
    packetBudgetNoLower.family.carrier =
      certificate.terminalReady.result.nucleus.anchors.map
        certificate.anchorMap ∧
    2 ≤ packetBudgetNoLower.family.carrier.length ∧
    (¬DirectWire.TerminalBN6PacketConclusion
      packetBudgetNoLower.family) ∧
    ¬packetBudgetNoLower.family.ConstantActivation := by
  exact ⟨certificate.terminalReady.allSafe,
    certificate.terminalReady.finalPositive,
    certificate.terminalReady.wholePositive,
    certificate.anchorMapInjective,
    certificate.anchorMapSurjective,
    certificate.family_carrier_eq,
    certificate.carrier_at_least_two,
    certificate.no_positive_packet,
    certificate.not_constant_activation⟩

end PNP
