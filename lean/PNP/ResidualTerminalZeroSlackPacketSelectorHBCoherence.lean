/-
Copyright (c) 2026 PNP Labs.

Same-family coherence for the report-facing Selector/HB, Packet no-lower, and
BCEL ZeroSlack boundaries.  The accepted Packet/budget checker already
recomputes selector silence and HB no-outcome closure after rebuilding the
table's faithfulness function from the exact Packet payload.  This module
derives the public Selector/HB sidecar from that exact computed table instead
of accepting a detached second certificate.

The grouped family, terminal and budget inputs, typed payloads, realizer
claims, activity environment, dependency rows, and residual ranks remain
supplied through the Packet/budget certificate.  This coherence theorem does
not construct those inputs from terminal data, derive BCELReady or constant
activation from positive residual slack, complete the manuscript no-lower
ledger, prove unconditional ZeroSlack or PCCMin, establish polynomial runtime,
put SAT in P, remove a project assumption, or prove P = NP.
-/

import PNP.ResidualTerminalSelectorHBZeroSlackSidecar
import PNP.ResidualTerminalBCELPacketNoLowerZeroSlackSidecar

namespace PNP

/-- The exact table on which M180 recomputes selector silence and HB closure.
    Its family, claims, activity environment, and dependency inputs are not
    copied into a second report-facing certificate. -/
def PacketBudgetNoLowerZeroSlackSidecarCertificate.computedSelectorHBTable
    (certificate : PacketBudgetNoLowerZeroSlackSidecarCertificate) :=
  certificate.table.withComputedPacketSelectorBN5FrontierObligationActivationDirectionBudgetFaithfulness
    certificate.beforeRank certificate.afterRank

/-- M180 acceptance contains selector silence for the exact computed table. -/
theorem PacketBudgetNoLowerZeroSlackSidecarCertificate.selector_silence_accepted
    (certificate : PacketBudgetNoLowerZeroSlackSidecarCertificate) :
    certificate.computedSelectorHBTable.checkSelectorSilent = true := by
  exact certificate.accepted.2.2.2.1

/-- M180 acceptance contains HB no-outcome closure for the same computed
    environment and exact dependency table. -/
theorem PacketBudgetNoLowerZeroSlackSidecarCertificate.hb_closure_accepted
    (certificate : PacketBudgetNoLowerZeroSlackSidecarCertificate) :
    certificate.dependencyTable.checkNoOutcomeActiveClosure
      certificate.computedSelectorHBTable.environment = true := by
  exact certificate.accepted.2.2.2.2.1

/-- Derive the report-facing Selector/HB sidecar from M180's exact family,
    computed table, and dependency table.  No coherence proof, digest, caller
    Boolean, or duplicate data field is accepted. -/
def PacketBudgetNoLowerZeroSlackSidecarCertificate.selectorHB
    (certificate : PacketBudgetNoLowerZeroSlackSidecarCertificate) :
    SelectorHBZeroSlackSidecarCertificate where
  Atom := certificate.Anchor
  Payload := DirectWire.TerminalPacketSelectorBN5BudgetPayload
    certificate.rankCount certificate.ActivationAtom
      certificate.SemanticSignature certificate.TransportType
      certificate.Frontier certificate.ChargeOwner certificate.Obligation
      certificate.OriginKernel certificate.ModeProjection
      certificate.Direction certificate.PacketBudget
  atomDecidableEq := certificate.anchorDecidableEq
  inputs := certificate.inputs
  outputs := certificate.outputs
  rankCount := certificate.rankCount
  current := certificate.candidate.toImplementation
  family := certificate.family
  realizerTable := certificate.computedSelectorHBTable
  dependencyTable := certificate.dependencyTable
  selectorSilenceAccepted := certificate.selector_silence_accepted
  hbClosureAccepted := certificate.hb_closure_accepted

/-- The derived sidecar is definitionally tied to the M180 family. -/
theorem PacketBudgetNoLowerZeroSlackSidecarCertificate.selectorHB_family
    (certificate : PacketBudgetNoLowerZeroSlackSidecarCertificate) :
    certificate.selectorHB.family = certificate.family :=
  rfl

/-- The derived sidecar uses exactly M180's computed table. -/
theorem PacketBudgetNoLowerZeroSlackSidecarCertificate.selectorHB_realizerTable
    (certificate : PacketBudgetNoLowerZeroSlackSidecarCertificate) :
    certificate.selectorHB.realizerTable =
      certificate.computedSelectorHBTable :=
  rfl

/-- The derived sidecar uses exactly M180's dependency table. -/
theorem PacketBudgetNoLowerZeroSlackSidecarCertificate.selectorHB_dependencyTable
    (certificate : PacketBudgetNoLowerZeroSlackSidecarCertificate) :
    certificate.selectorHB.dependencyTable = certificate.dependencyTable :=
  rfl

/-- Named M182 dependency endpoint: one accepted M180 certificate supplies
    the exact same-family Selector/HB consequences and Packet exclusion, while
    its dependent M181 certificate excludes constant activation on that family. -/
theorem packet_selector_hb_bcel_coherent_checked_complete
    (packetBudgetNoLower : PacketBudgetNoLowerZeroSlackSidecarCertificate)
    (bcel : BCELContradictionCertificate packetBudgetNoLower) :
    (∀ handle : packetBudgetNoLower.family.PacketSelectorHandle,
      packetBudgetNoLower.selectorHB.realizerTable.environment.faithful
        handle = false) ∧
    packetBudgetNoLower.selectorHB.dependencyTable.NoOutcomeActiveClosureValid
      packetBudgetNoLower.selectorHB.realizerTable.environment ∧
    (∀ node,
      packetBudgetNoLower.selectorHB.realizerTable.environment.hbActive
        node = false) ∧
    (¬DirectWire.TerminalBN6PacketConclusion
      packetBudgetNoLower.family) ∧
    ¬packetBudgetNoLower.family.ConstantActivation := by
  exact ⟨packetBudgetNoLower.selectorHB.no_faithful,
    packetBudgetNoLower.selectorHB.hb_closure_valid,
    packetBudgetNoLower.selectorHB.no_hb_active,
    packetBudgetNoLower.no_positive_packet,
    bcel.not_constant_activation⟩

end PNP
