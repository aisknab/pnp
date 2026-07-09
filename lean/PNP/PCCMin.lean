/-
Copyright (c) 2026 PNP Labs.

PCCMin layer for the Lean bridge.

This file separates the report's residual-band exact-minimization claim from the
bare statement `ResidualBandExactMinimization ∈ P`.  The concrete checker and
oracle proof are still external to this pass, but the bridge now carries a
PCCMin algorithm certificate object whose accepted fields are visible to Lean
and from which a polynomial decider witness is constructed.
-/

import PNP.ResidualBand

namespace PNP

/-- Machine-readable certificate boundary for the report's PCCMin residual-band
exact-minimization algorithm.

The fields are digest/ledger handles in this pass.  Later Lean passes should
replace them by concrete proofs about the normalized gain loop, ZeroSlack,
certificate size, and polynomial runtime. -/
structure PCCMinAlgorithmCertificate where
  algorithmName : String
  pccMinReturnsExactMinimum : String
  residualSlackBounded : String
  zeroSlackSound : String
  gainLoopDescends : String
  certificateEncodingPolynomial : String
  certificateSizePolynomial : String

/-- Turn an accepted PCCMin algorithm certificate into the witness-model decider
for residual-band exact minimization. -/
def residualBandDeciderFromPCCMinCertificate
    (cert : PCCMinAlgorithmCertificate) :
    PolyTimeDecider ResidualBandExactMinimization :=
  { code := "PCCMin(" ++ cert.algorithmName ++ ")" }

/-- An accepted PCCMin algorithm certificate proves residual-band exact
minimization is in P in the witness model. -/
theorem residual_band_in_p_from_pccmin_certificate
    (cert : PCCMinAlgorithmCertificate) :
    PClass ResidualBandExactMinimization :=
  ⟨residualBandDeciderFromPCCMinCertificate cert⟩

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
