/-
Copyright (c) 2026 PNP Labs.

Locked-NAND reduction layer for the Lean bridge.

This file factors the report bridge through the locked NAND threshold language.
The concrete macro truth tables and threshold proof are still external to this
pass, but the Lean theorem now mirrors the report route:

  accepted package -> locked NAND threshold in P
  SAT reduces to locked NAND threshold
  therefore SAT in P
-/

import PNP.Complexity

namespace PNP

/-- The locked NAND threshold decision language from the report's SAT embedding
section.  Later passes should replace this abstract language handle by a
concrete encoding of locked NAND instances and thresholds. -/
constant LockedNANDThreshold : Language

/-- The locked-NAND SAT-reduction trust object.

This packages the theorem that the report's locked NAND builder is a
polynomial-time many-one reduction from SAT to the locked NAND threshold
language. -/
structure LockedNANDReductionTrust where
  satReducesToLockedNAND : ReducesToPoly SAT LockedNANDThreshold

/-- If the locked NAND threshold language is in P, then SAT is in P. -/
theorem sat_in_p_from_locked_nand_in_p
    (R : LockedNANDReductionTrust)
    (hLockedInP : PClass LockedNANDThreshold) : PClass SAT :=
  reduction_transports_p_witness_model R.satReducesToLockedNAND hLockedInP

end PNP
