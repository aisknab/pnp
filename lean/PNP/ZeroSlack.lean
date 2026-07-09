/-
Copyright (c) 2026 PNP Labs.

ZeroSlack and oracle certificate layer for the Lean bridge.

This file replaces the opaque PCCMin string handles with structured certificate
objects for the report's rank-ordered oracle and ZeroSlack contradiction.  The
fields are still digest/ledger handles in this pass, but the route is no longer
represented as a flat string list.
-/

import PNP.ResidualBand

namespace PNP

/-- HResolve sidecar boundary for the oracle. -/
structure HResolveSidecarCertificate where
  noHereditarySidecar : String
  exactMinimumRouteSound : String
  gainRouteSound : String

/-- Budget sidecar boundary for the oracle. -/
structure BudgetSidecarCertificate where
  noBudgetSidecar : String
  exactMinimumRouteSound : String
  gainRouteSound : String

/-- Selector-silence ledger boundary. -/
structure SelectorSilenceCertificate where
  finiteRankList : String
  selectorUniverseEnumerated : String
  realizerLogsTyped : String
  noLowerFaithfulSelector : String

/-- HN/BUD negative-closure boundary. -/
structure HBClosureCertificate where
  blockerGraphAcyclicByRank : String
  hbBlockerGraphAcyclic : String
  selectorSilenceRankComplete : String
  hbNoCircularNegativeClosure : String

/-- The BCEL-to-selector contradiction package used by ZeroSlack. -/
structure BCELContradictionCertificate where
  positiveResidualWitnessYieldsBCELReady : String
  positivePacketYieldsFaithfulSelector : String
  faithfulSelectorRealizerContradiction : String
  zeroSlackPositiveSlackContradictionComplete : String
  zeroSlackContradictionFromPositiveSlack : String

/-- Structured ZeroSlack certificate boundary from report Section 16.

The fields remain handles in this pass.  Later passes should replace them by
actual Lean proofs about terminal MuBridge, SaturatePositive, BCELReady,
BN2--BN6, selector realization, HB closure, and the final contradiction. -/
structure ZeroSlackCertificate where
  normalizedInputRecord : String
  noLowerRouteLedgerComplete : String
  hResolve : HResolveSidecarCertificate
  budget : BudgetSidecarCertificate
  selectorSilence : SelectorSilenceCertificate
  hbClosure : HBClosureCertificate
  bcelContradiction : BCELContradictionCertificate
  certificateEncodingPolynomial : String
  certificatePolynomialSize : String

/-- Rank-ordered PCCOracle certificate boundary. -/
structure PCCOracleCertificate where
  normalizedInputRecord : String
  hResolve : HResolveSidecarCertificate
  budget : BudgetSidecarCertificate
  selectorSilence : SelectorSilenceCertificate
  zeroSlack : ZeroSlackCertificate

/-- Extract the report-facing ZeroSlack soundness handle. -/
def zeroSlackSoundnessHandle (z : ZeroSlackCertificate) : String :=
  z.bcelContradiction.zeroSlackContradictionFromPositiveSlack

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
