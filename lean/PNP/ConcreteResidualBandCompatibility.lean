/-
Copyright (c) 2026 PNP Labs.

Concrete compatibility boundary from the report-facing residual-band name to
the existing encoded direct-wire minimum-threshold predicate.  This removes a
language axiom and a caller-supplied identity reduction.  It does not construct
PCCMin, prove ZeroSlack, or claim polynomial runtime for exhaustive reference
minimization.
-/

import PNP.Bridge

namespace PNP

/-- The report-facing residual-band endpoint is exactly the general concrete
encoded direct-wire minimum-threshold language. -/
theorem report_residual_band_eq_concrete_minimum_threshold :
    ResidualBandExactMinimization =
      Concrete.LockedNAND.EncodedDirectWireMinimumThreshold := rfl

/-- The locked-NAND and residual-band endpoints consume the same canonical
query bytes and exact semantic predicate. -/
theorem report_locked_nand_eq_residual_band :
    LockedNANDThreshold = ResidualBandExactMinimization := rfl

/-- Named M187 endpoint.  The concrete language identity, arbitrary-candidate
semantics, identity polynomial transport, and resulting P transport hold
without the former project axiom or supplied reduction field. -/
theorem concrete_residual_band_compatibility_checked_complete :
    ResidualBandExactMinimization =
        Concrete.LockedNAND.EncodedDirectWireMinimumThreshold ∧
    LockedNANDThreshold = ResidualBandExactMinimization ∧
    (∀ {inputs gates outputs : Nat}
        (candidate : DirectWire.Candidate inputs gates outputs)
        (threshold : Nat),
      ResidualBandExactMinimization
          (Concrete.LockedNAND.encodeLockedInstance
            (Concrete.LockedNAND.RawLockedInstance.ofCandidate
              candidate threshold)) ↔
        threshold + 1 ≤ DirectWire.referenceMinimum
          (DirectWire.Implementation.mk gates candidate)) ∧
    ReducesToPoly LockedNANDThreshold ResidualBandExactMinimization ∧
    (PClass ResidualBandExactMinimization → PClass LockedNANDThreshold) := by
  exact ⟨report_residual_band_eq_concrete_minimum_threshold,
    report_locked_nand_eq_residual_band,
    residual_band_encoded_candidate_iff_reference_minimum,
    locked_nand_reduces_to_residual_band_checked,
    locked_nand_in_p_from_residual_band_in_p⟩

end PNP
