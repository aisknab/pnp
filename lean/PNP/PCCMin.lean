/-
Copyright (c) 2026 PNP Labs.

PCCMin layer for the Lean bridge.

This file separates the report's residual-band exact-minimization claim from the
bare statement `ResidualBandExactMinimization ∈ P`.  The concrete checker and
oracle proof are still external to this pass, but the bridge now carries a
structured PCCMin loop certificate and ZeroSlack oracle certificate object.  A
concrete finite-pipeline decider, with its runtime and semantic proofs, is an
explicit certificate field; string metadata can no longer manufacture P
membership.
-/

import PNP.ZeroSlack

namespace PNP

/-- Structured PCCMin loop certificate boundary.

The named fields are still digest/ledger handles in this pass.  Later Lean
passes should replace them by concrete proofs about normalization, gain
descent, rank-ordered PCCOracle, ZeroSlack, exactness, certificate size, and
polynomial runtime.  `residualBandDecider` is different: it is already the
complete concrete proof-bearing decider required by the active complexity
model, and remains part of the explicit external trust boundary. -/
structure PCCMinLoopCertificate where
  algorithmName : String
  oracleCertificate : PCCOracleCertificate
  pccMinReturnsExactMinimum : String
  residualSlackBounded : String
  zeroSlackSound : String
  gainLoopDescends : String
  certificateEncodingPolynomial : String
  certificateSizePolynomial : String
  residualBandDecider : PolyTimeDecider ResidualBandExactMinimization

/-- Machine-readable certificate boundary for the report's PCCMin residual-band
exact-minimization algorithm. -/
structure PCCMinAlgorithmCertificate where
  loopCertificate : PCCMinLoopCertificate

/-- Build the algorithm certificate from its loop certificate. -/
def pccMinAlgorithmCertificateFromLoop
    (loop : PCCMinLoopCertificate) : PCCMinAlgorithmCertificate :=
  { loopCertificate := loop }

/-- Project the supplied proof-bearing finite-pipeline decider; no string
    handle is interpreted as executable evidence. -/
def residualBandDeciderFromPCCMinCertificate
    (cert : PCCMinAlgorithmCertificate) :
    PolyTimeDecider ResidualBandExactMinimization :=
  cert.loopCertificate.residualBandDecider

/-- An accepted PCCMin algorithm certificate exposes residual-band exact
    minimization in the concrete finite-pipeline class P. -/
theorem residual_band_in_p_from_pccmin_certificate
    (cert : PCCMinAlgorithmCertificate) :
    PClass ResidualBandExactMinimization :=
  ⟨residualBandDeciderFromPCCMinCertificate cert⟩

/-- A loop certificate already containing the concrete decider is enough to
    construct the accepted PCCMin algorithm certificate used by the bridge. -/
theorem residual_band_in_p_from_pccmin_loop_certificate
    (loop : PCCMinLoopCertificate) :
    PClass ResidualBandExactMinimization :=
  residual_band_in_p_from_pccmin_certificate
    (pccMinAlgorithmCertificateFromLoop loop)

/-- The report-facing list of checker-visible PCCMin obligations that should be
replaced by concrete Lean proofs in later passes. -/
def pccMinObligationNames : List String := [
  "pccMinReturnsExactMinimum",
  "residualSlackBounded",
  "zeroSlackSound",
  "gainLoopDescends",
  "zeroSlackCertificateEncodingPolynomial",
  "zeroSlackCertificatePolynomialSize"
]

end PNP
