/-
Copyright (c) 2026 PNP Labs.

ZeroSlack and oracle certificate layer for the Lean bridge.

This file replaces the opaque PCCMin string handles with structured certificate
objects for the report's rank-ordered oracle and ZeroSlack contradiction. The
HResolve, Budget, joint selector/HB, finite Packet/budget no-lower, and
same-candidate finite BCEL-ready/Packet carrier-coherence boundaries are now
checked proof-bearing certificates; the remaining fields are still digest or
proof handles in this pass.
-/

import PNP.ResidualBand
import PNP.ResidualTerminalHResolveZeroSlackSidecar
import PNP.ResidualTerminalBudgetZeroSlackSidecar
import PNP.ResidualTerminalPacketBudgetNoLowerZeroSlackSidecar
import PNP.ResidualTerminalFiniteBCELPacketActivationObstruction

namespace PNP

/-- Structured ZeroSlack certificate boundary from report Section 16.

The normalization and polynomial fields remain handles in this pass. Later
passes must still construct terminal MuBridge, SaturatePositive and BCELReady
from positive residual slack, complete all no-lower routes, and prove the
polynomial final contradiction. -/
structure ZeroSlackCertificate where
  normalizedInputRecord : String
  hResolve : HResolveSidecarCertificate
  budget : BudgetSidecarCertificate
  packetBudgetNoLower : PacketBudgetNoLowerZeroSlackSidecarCertificate
  bcelCarrierCoherence :
    TerminalFiniteBCELPacketCarrierCoherenceCertificate packetBudgetNoLower
  certificateEncodingPolynomial : String
  certificatePolynomialSize : String

/-- Rank-ordered PCCOracle certificate boundary. -/
structure PCCOracleCertificate where
  normalizedInputRecord : String
  hResolve : HResolveSidecarCertificate
  budget : BudgetSidecarCertificate
  zeroSlack : ZeroSlackCertificate

/-- The Selector/HB boundary is derived from the exact Packet/budget family,
    computed table, and dependency table rather than stored independently. -/
def ZeroSlackCertificate.selectorHBClosure
    (z : ZeroSlackCertificate) : SelectorHBZeroSlackSidecarCertificate :=
  z.packetBudgetNoLower.selectorHB

/-- The oracle exposes the same derived Selector/HB boundary as its dependent
    ZeroSlack certificate. -/
def PCCOracleCertificate.selectorHBClosure
    (certificate : PCCOracleCertificate) :
    SelectorHBZeroSlackSidecarCertificate :=
  certificate.zeroSlack.selectorHBClosure

/-- Exact finite soundness proposition currently exposed at the report-facing
    ZeroSlack boundary. It is not unconditional ZeroSlack. -/
def zeroSlackSoundnessBoundary (z : ZeroSlackCertificate) : Prop :=
  ¬z.packetBudgetNoLower.family.ConstantActivation

/-- The coherent finite BCEL-ready/Packet carrier certificate proves the
    current report-facing soundness boundary. -/
theorem zeroSlackSoundnessBoundary_proved (z : ZeroSlackCertificate) :
    zeroSlackSoundnessBoundary z :=
  z.bcelCarrierCoherence.not_constant_activation

/-- Report-facing endpoint introduced in M182 and strengthened in M184:
    Selector/HB silence and closure, positive-Packet exclusion, and the BCEL
    contradiction use the exact M180 family, computed dependency data, and
    coherently mapped M183 ready nucleus. -/
theorem zeroslack_packet_selector_hb_bcel_coherent_checked_complete
    (z : ZeroSlackCertificate) :
    (∀ handle : z.packetBudgetNoLower.family.PacketSelectorHandle,
      z.selectorHBClosure.realizerTable.environment.faithful handle = false) ∧
    z.selectorHBClosure.dependencyTable.NoOutcomeActiveClosureValid
      z.selectorHBClosure.realizerTable.environment ∧
    (∀ node,
      z.selectorHBClosure.realizerTable.environment.hbActive node = false) ∧
    (¬DirectWire.TerminalBN6PacketConclusion
      z.packetBudgetNoLower.family) ∧
    ¬z.packetBudgetNoLower.family.ConstantActivation := by
  exact ⟨z.packetBudgetNoLower.selectorHB.no_faithful,
    z.packetBudgetNoLower.selectorHB.hb_closure_valid,
    z.packetBudgetNoLower.selectorHB.no_hb_active,
    z.bcelCarrierCoherence.no_positive_packet,
    z.bcelCarrierCoherence.not_constant_activation⟩

/-- The report-facing certificate exposes the deterministic M185 obstruction
    without storing another family, defect, cut sample, or caller flag. -/
def ZeroSlackCertificate.bcelPacketActivationObstruction
    (z : ZeroSlackCertificate) :
    TerminalFiniteBCELPacketActivationObstruction
      z.bcelCarrierCoherence :=
  classifyTerminalFiniteBCELPacketActivationObstruction
    z.bcelCarrierCoherence

/-- Report-facing M185 endpoint: the exact finite BCEL/Packet activation-
    coherence check rejects with a declared-value or proper-cut mismatch. This
    is a diagnostic finite obstruction, not unconditional ZeroSlack. -/
theorem zeroslack_bcel_packet_activation_obstruction_checked_complete
    (z : ZeroSlackCertificate) :
    checkTerminalFiniteBCELPacketActivationCoherence
        z.bcelCarrierCoherence = false ∧
    (z.packetBudgetNoLower.family.cutValue ≠
        z.bcelCarrierCoherence.terminalDefect ∨
      ∃ cut, cut.Sublist z.packetBudgetNoLower.family.carrier ∧ cut ≠ [] ∧
        cut ≠ z.packetBudgetNoLower.family.carrier ∧
        z.packetBudgetNoLower.family.activationWeight cut ≠
          z.bcelCarrierCoherence.terminalDefect) :=
  terminal_finite_bcel_packet_activation_obstruction_checked_complete
    z.bcelCarrierCoherence

/-- Extract the polynomial-size certificate handle. -/
def zeroSlackPolynomialSizeHandle (z : ZeroSlackCertificate) : String :=
  z.certificatePolynomialSize

/-- The report-facing list of ZeroSlack obligations tracked by the structured
certificate layer. -/
def zeroSlackObligationNames : List String := [
  "zeroSlackEarlierRoutesExcluded",
  "zeroSlackNoLowerRouteLedgerComplete",
  "zeroSlackFaithfulSelectorExcludedAllRanks",
  "zeroSlackHNBUDBlockersExcludedAllRanks",
  "zeroSlackPositiveSlackContradictionComplete",
  "zeroSlackContradictionFromPositiveSlack",
  "zeroSlackCertificateEncodingPolynomial",
  "zeroSlackCertificatePolynomialSize"
]

end PNP
