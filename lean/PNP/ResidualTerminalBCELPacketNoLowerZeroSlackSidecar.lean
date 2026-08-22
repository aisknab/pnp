/-
Copyright (c) 2026 PNP Labs.

Proof-bearing BCEL/Packet no-lower contradiction sidecar for the report-facing
ZeroSlack certificate.  The sidecar reuses the exact accepted M180
Packet/budget no-lower certificate over one supplied grouped BN6 family and
checks, from the family data, that its carrier contains at least two anchors.

The existing BN6 theorem turns constant activation on every nonempty proper
cut into a positive Packet conclusion.  The accepted no-lower certificate
excludes that conclusion for the same family.  Their composition therefore
proves that the supplied family cannot satisfy the BCEL constant-activation
premise.

The grouped family and every terminal, budget, Packet, realizer, dependency,
and rank input retained by M180 remain supplied.  This bounded contradiction
does not derive the family or constant activation from positive residual slack,
construct BCELReady from a terminal candidate, complete the manuscript's
no-lower ledger, prove unconditional ZeroSlack or PCCMin, establish polynomial
runtime, remove a project assumption, put SAT in P, or prove P = NP.
-/

import PNP.ResidualTerminalPacketBudgetNoLowerZeroSlackSidecar

namespace PNP

/-- Checked evidence that the accepted same-family Packet/budget no-lower
    branch excludes the BCEL constant-activation premise.  The carrier lower
    bound is stored only as the exact result of the decidable data check. -/
structure BCELContradictionCertificate
    (packetBudgetNoLower : PacketBudgetNoLowerZeroSlackSidecarCertificate) where
  carrierAtLeastTwoChecked :
    decide (2 ≤ packetBudgetNoLower.family.carrier.length) = true

/-- The stored Boolean equation reflects the exact carrier lower bound needed
    by the arbitrary-finite BN6 packet theorem. -/
theorem BCELContradictionCertificate.carrier_at_least_two
    {packetBudgetNoLower : PacketBudgetNoLowerZeroSlackSidecarCertificate}
    (certificate : BCELContradictionCertificate packetBudgetNoLower) :
    2 ≤ packetBudgetNoLower.family.carrier.length :=
  of_decide_eq_true certificate.carrierAtLeastTwoChecked

/-- The linked M180 checker excludes a positive Packet for this exact family. -/
theorem BCELContradictionCertificate.no_positive_packet
    {packetBudgetNoLower : PacketBudgetNoLowerZeroSlackSidecarCertificate}
    (_certificate : BCELContradictionCertificate packetBudgetNoLower) :
    ¬DirectWire.TerminalBN6PacketConclusion packetBudgetNoLower.family :=
  packetBudgetNoLower.no_positive_packet

/-- BCEL constant activation would construct the positive Packet excluded by
    the accepted same-family no-lower certificate. -/
theorem BCELContradictionCertificate.not_constant_activation
    {packetBudgetNoLower : PacketBudgetNoLowerZeroSlackSidecarCertificate}
    (certificate : BCELContradictionCertificate packetBudgetNoLower) :
    ¬packetBudgetNoLower.family.ConstantActivation := by
  intro constantActivation
  exact certificate.no_positive_packet
    (DirectWire.terminalBN6_hypergraph_packet packetBudgetNoLower.family
      certificate.carrier_at_least_two constantActivation)

/-- Named M181 endpoint: the proof-bearing boundary checks the carrier domain,
    retains the exact positive-Packet exclusion, and rules out the same
    family's BCEL constant-activation premise. -/
theorem bcel_packet_no_lower_zeroslack_sidecar_checked_complete
    {packetBudgetNoLower : PacketBudgetNoLowerZeroSlackSidecarCertificate}
    (certificate : BCELContradictionCertificate packetBudgetNoLower) :
    (2 ≤ packetBudgetNoLower.family.carrier.length) ∧
      (¬DirectWire.TerminalBN6PacketConclusion
        packetBudgetNoLower.family) ∧
      ¬packetBudgetNoLower.family.ConstantActivation := by
  exact ⟨certificate.carrier_at_least_two,
    certificate.no_positive_packet, certificate.not_constant_activation⟩

end PNP
