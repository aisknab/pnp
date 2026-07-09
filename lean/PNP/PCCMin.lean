/-
Copyright (c) 2026 PNP Labs.

PCCMin layer for the Lean bridge.

This file separates the report's residual-band exact-minimization claim from the
bare statement `ResidualBandExactMinimization ∈ P`.  The concrete checker and
oracle proof are still external to this pass, but the bridge now carries a
structured PCCMin loop certificate and ZeroSlack oracle certificate object whose
accepted fields are visible to Lean and from which a polynomial decider witness
is constructed.
-/

import PNP.ZeroSlack

namespace PNP

/-- Structured PCCMin loop certificate boundary.

The fields are still digest/ledger handles in this pass.  Later Lean passes
should replace them by concrete proofs about normalization, gain descent,
rank-ordered PCCOracle, ZeroSlack, exactness, certificate size, and polynomial
runtime. -/
structure PCCMinLoopCertificate where
  algorithmName : String
  oracleCertificate : PCCOracleCertificate
  pccMinReturnsExactMinimum : String
  residualSlackBounded : String
  zeroSlackSound : String
  gainLoopDescends : String
  certificateEncodingPolynomial : String
  certificateSizePolynomial : String

/-- Machine-readable certificate boundary for the report's PCCMin residual-band
exact-minimization algorithm. -/
structure PCCMinAlgorithmCertificate where
  loopCertificate : PCCMinLoopCertificate

/-- Build the algorithm certificate from its loop certificate. -/
def pccMinAlgorithmCertificateFromLoop
    (loop : PCCMinLoopCertificate) : PCCMinAlgorithmCertificate :=
  { loopCertificate := loop }

/-- Turn an accepted PCCMin algorithm certificate into the witness-model decider
for residual-band exact minimization. -/
def residualBandDeciderFromPCCMinCertificate
    (cert : PCCMinAlgorithmCertificate) :
    PolyTimeDecider ResidualBandExactMinimization :=
  { code := "PCCMin(" ++ cert.loopCertificate.algorithmName ++ ")" }

/-- An accepted PCCMin algorithm certificate proves residual-band exact
minimization is in P in the witness model. -/
theorem residual_band_in_p_from_pccmin_certificate
    (cert : PCCMinAlgorithmCertificate) :
    PClass ResidualBandExactMinimization :=
  ⟨residualBandDeciderFromPCCMinCertificate cert⟩

/-- A loop certificate is enough to construct the accepted PCCMin algorithm
certificate used by the bridge. -/
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
