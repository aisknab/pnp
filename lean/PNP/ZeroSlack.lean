/-
Copyright (c) 2026 PNP Labs.

ZeroSlack and oracle certificate layer for the Lean bridge.

This file replaces the opaque PCCMin string handles with structured certificate
objects for the report's rank-ordered oracle and ZeroSlack contradiction. The
HResolve, Budget, joint selector/HB, finite Packet/budget no-lower, and bounded
BCEL/Packet contradiction boundaries are now checked proof-bearing
certificates; the remaining fields are still digest or proof handles in this
pass.
-/

import PNP.ResidualBand
import PNP.ResidualTerminalHResolveZeroSlackSidecar
import PNP.ResidualTerminalBudgetZeroSlackSidecar
import PNP.ResidualTerminalSelectorHBZeroSlackSidecar
import PNP.ResidualTerminalPacketBudgetNoLowerZeroSlackSidecar
import PNP.ResidualTerminalBCELPacketNoLowerZeroSlackSidecar

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
  selectorHBClosure : SelectorHBZeroSlackSidecarCertificate
  packetBudgetNoLower : PacketBudgetNoLowerZeroSlackSidecarCertificate
  bcelContradiction : BCELContradictionCertificate packetBudgetNoLower
  certificateEncodingPolynomial : String
  certificatePolynomialSize : String

/-- Rank-ordered PCCOracle certificate boundary. -/
structure PCCOracleCertificate where
  normalizedInputRecord : String
  hResolve : HResolveSidecarCertificate
  budget : BudgetSidecarCertificate
  selectorHBClosure : SelectorHBZeroSlackSidecarCertificate
  zeroSlack : ZeroSlackCertificate

/-- Exact bounded soundness proposition currently exposed at the report-facing
    ZeroSlack boundary. It is not unconditional ZeroSlack. -/
def zeroSlackSoundnessBoundary (z : ZeroSlackCertificate) : Prop :=
  ¬z.packetBudgetNoLower.family.ConstantActivation

/-- The dependent BCEL sidecar proves the current bounded soundness boundary. -/
theorem zeroSlackSoundnessBoundary_proved (z : ZeroSlackCertificate) :
    zeroSlackSoundnessBoundary z :=
  z.bcelContradiction.not_constant_activation

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
