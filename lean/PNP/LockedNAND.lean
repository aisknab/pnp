/-
Copyright (c) 2026 PNP Labs.

Locked-NAND reduction layer for the Lean bridge.

This file factors the report bridge through the exact concrete locked-NAND
threshold language.  The equality, constant, trace-check, final-conjunction,
and prefix-conjunction semantics are checked concretely in
`PNP.LockedNANDMacros` and `PNP.LockedNANDPrefix`.  The all-bitstring global
SAT-instance builder and locked-threshold reduction are reused from the
concrete finite-pipeline theorem:

  accepted package -> locked NAND threshold in P
  concrete CNFSAT reduces to concrete locked NAND threshold
  therefore SAT in P
-/

import PNP.SAT
import PNP.LockedNANDMacros
import PNP.LockedNANDPrefix
import PNP.Concrete.LockedNANDThresholdPublication

namespace PNP

/-- The report-facing locked-NAND endpoint is definitionally the exact strict
    encoded bitstring predicate used by the concrete reduction. -/
def LockedNANDThreshold : Language :=
  Concrete.LockedNAND.EncodedLockedNANDThreshold

/-- The concrete local macro layer has a Lean-constructed proof certificate. -/
theorem locked_nand_macro_layer_checked : LockedNANDMacroCertificate :=
  lockedNANDMacroCertificate

/-- The concrete prefix-conjunction layer has a Lean-constructed proof
certificate. -/
theorem locked_nand_prefix_layer_checked : LockedNANDPrefixCertificate :=
  lockedNANDPrefixCertificate

/-- The report-facing SAT-to-locked-NAND reduction is exactly the existing
    compiled all-bitstring concrete theorem; no caller trust field remains. -/
theorem sat_reduces_to_locked_nand_checked :
    ReducesToPoly SAT LockedNANDThreshold :=
  Main.locked_nand_threshold

/-- If the locked NAND threshold language is in P, then SAT is in P. -/
theorem sat_in_p_from_locked_nand_in_p
    (hLockedInP : PClass LockedNANDThreshold) : PClass SAT :=
  reduction_transports_p_witness_model
    sat_reduces_to_locked_nand_checked hLockedInP

end PNP
