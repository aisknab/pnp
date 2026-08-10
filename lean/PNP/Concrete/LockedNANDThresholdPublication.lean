/-
Copyright (c) 2026 PNP Labs.

Report-facing publication theorem for the concrete locked-NAND threshold
construction.  This module deliberately stays in the finite bitstring and
charged-pipeline model; it does not transport through the legacy string-handle
complexity bridge.
-/

import PNP.Concrete.CNFToNANDPolynomialReduction

namespace PNP.Main

/-- Every strict encoded CNF input, including malformed bitstrings, is mapped
by one proof-bearing polynomial-time finite pipeline to the concrete locked-
NAND threshold language with exact membership equivalence.

The witness is the composed literal CNF-to-NAND compiler and strict locked-
NAND parser/emitter.  Consequently this theorem links the report-facing name
directly to the concrete target definition, all-input semantics, polynomial
runtime and output-size bounds, rather than to `PNP.LockedNANDThreshold`'s
legacy name-only language handle. -/
theorem locked_nand_threshold :
    PNP.Concrete.ReducesTo
      PNP.Concrete.CNFSAT
      PNP.Concrete.LockedNAND.EncodedLockedNANDThreshold :=
  PNP.Concrete.CNFToNAND.cnfSAT_reducesTo_encodedLockedNANDThreshold

end PNP.Main
