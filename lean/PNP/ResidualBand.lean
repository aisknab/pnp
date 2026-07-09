/-
Copyright (c) 2026 PNP Labs.

Residual-band minimization layer for the Lean bridge.

This file factors the checker-trust bridge through the report's residual-band
exact minimization theorem.  The concrete minimizer, residual-slack bound, and
locked NAND instance construction are still external to this pass, but the Lean
bridge now separates:

  accepted package -> residual-band exact minimization in P
  locked NAND threshold reduces to residual-band exact minimization
  therefore locked NAND threshold is in P
-/

import PNP.LockedNAND

namespace PNP

/-- Decision language representing residual-band exact minimization queries.

A later pass should replace this abstract language handle by a concrete encoding
of direct-wire words, residual-band promises, thresholds, and exact-minimization
answers. -/
constant ResidualBandExactMinimization : Language

/-- Trust object for the reduction from locked NAND threshold instances to the
residual-band exact minimization decision language.

This packages the report facts that locked NAND instances have constant residual
slack and that exact residual-band minimization decides the locked threshold. -/
structure ResidualBandReductionTrust where
  lockedNANDReducesToResidualBand : ReducesToPoly LockedNANDThreshold ResidualBandExactMinimization

/-- If residual-band exact minimization is in P, then the locked NAND threshold
language is in P. -/
theorem locked_nand_in_p_from_residual_band_in_p
    (R : ResidualBandReductionTrust)
    (hResidualInP : PClass ResidualBandExactMinimization) : PClass LockedNANDThreshold :=
  reduction_transports_p_witness_model R.lockedNANDReducesToResidualBand hResidualInP

end PNP
