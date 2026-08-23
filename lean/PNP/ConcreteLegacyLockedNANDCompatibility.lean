/-
Copyright (c) 2026 PNP Labs.

Checked compatibility boundary from the report-facing bridge to the existing
concrete finite-pipeline SAT and locked-NAND construction.  The report-facing
language and complexity names are aliases for concrete predicates and
proof-bearing programs; the locked-NAND endpoint is a definition, and the
SAT-to-target reduction is the already-compiled all-bitstring theorem.

This removes one duplicate project axiom and one caller-supplied reduction
field.  Residual-band reduction, PCCMin/ZeroSlack soundness, checker reflection,
concrete SAT NP-hardness, and the eligible root theorem remain open.
-/

import PNP.Bridge

namespace PNP

/-- The active report-facing SAT endpoint is exactly concrete canonical CNF. -/
theorem report_sat_eq_concrete_cnfsat :
    SAT = Concrete.CNFSAT := rfl

/-- The active report-facing locked-NAND endpoint is exactly the strict
    concrete encoded threshold predicate. -/
theorem report_locked_nand_eq_concrete_threshold :
    LockedNANDThreshold =
      Concrete.LockedNAND.EncodedLockedNANDThreshold := rfl

/-- PCCMin string metadata cannot manufacture a decider: the active projection
    returns exactly the proof-bearing concrete decider stored in the supplied
    loop certificate. -/
theorem pccmin_concrete_decider_projection_exact
    (loop : PCCMinLoopCertificate) :
    residualBandDeciderFromPCCMinCertificate
        (pccMinAlgorithmCertificateFromLoop loop) =
      loop.residualBandDecider := rfl

/-- Named M186 endpoint.  Both language identities, the compiled concrete SAT
    verifier, the compiled all-input reduction, and the resulting P transport
    hold in one concrete finite-pipeline model. -/
theorem concrete_legacy_locked_nand_compatibility_checked_complete :
    SAT = Concrete.CNFSAT ∧
    LockedNANDThreshold =
      Concrete.LockedNAND.EncodedLockedNANDThreshold ∧
    NPClass SAT ∧
    ReducesToPoly SAT LockedNANDThreshold ∧
    (PClass LockedNANDThreshold → PClass SAT) := by
  exact ⟨report_sat_eq_concrete_cnfsat,
    report_locked_nand_eq_concrete_threshold,
    sat_in_np_witness_model,
    sat_reduces_to_locked_nand_checked,
    sat_in_p_from_locked_nand_in_p⟩

end PNP
