/-
Copyright (c) 2026 PNP Labs.

Locked-NAND reduction layer for the Lean bridge.

This file factors the report bridge through the locked NAND threshold language.
The equality, constant, trace-check, final-conjunction, and prefix-conjunction
semantics are now checked concretely in `PNP.LockedNANDMacros` and
`PNP.LockedNANDPrefix`.  The remaining external part of this layer is the
global SAT-instance builder and locked-threshold proof:

  accepted package -> locked NAND threshold in P
  SAT reduces to locked NAND threshold
  therefore SAT in P
-/

import PNP.Complexity
import PNP.LockedNANDMacros
import PNP.LockedNANDPrefix

namespace PNP

/-- The locked NAND threshold decision language from the report's SAT embedding
section.  Later passes should replace this abstract language handle by a
concrete encoding of locked NAND instances and thresholds. -/
constant LockedNANDThreshold : Language

/-- The concrete local macro layer has a Lean-constructed proof certificate. -/
theorem locked_nand_macro_layer_checked : LockedNANDMacroCertificate :=
  lockedNANDMacroCertificate

/-- The concrete prefix-conjunction layer has a Lean-constructed proof
certificate. -/
theorem locked_nand_prefix_layer_checked : LockedNANDPrefixCertificate :=
  lockedNANDPrefixCertificate

/-- The locked-NAND SAT-reduction trust object.

The local macro truth laws and prefix-conjunction exactness are no longer part
of this trust object.  This field now represents the remaining global theorem:
the report's full locked NAND builder is a polynomial-time many-one reduction
from SAT to the locked NAND threshold language. -/
structure LockedNANDReductionTrust where
  satReducesToLockedNAND : ReducesToPoly SAT LockedNANDThreshold

/-- If the locked NAND threshold language is in P, then SAT is in P. -/
theorem sat_in_p_from_locked_nand_in_p
    (R : LockedNANDReductionTrust)
    (hLockedInP : PClass LockedNANDThreshold) : PClass SAT :=
  reduction_transports_p_witness_model R.satReducesToLockedNAND hLockedInP

end PNP
