/-
Copyright (c) 2026 PNP Labs.

Residual-band minimization layer for the Lean bridge.

This file factors the checker-trust bridge through the report's residual-band
exact-minimization language.  The language is the concrete fail-closed
direct-wire candidate/threshold predicate already consumed by locked NAND.
The concrete PCCMin algorithm, ZeroSlack proof, residual-slack bound, and
polynomial runtime remain external to this pass, but the Lean bridge now
separates:

  accepted package -> residual-band exact minimization in P
  locked NAND threshold reduces to residual-band exact minimization
  therefore locked NAND threshold is in P
-/

import PNP.LockedNAND

namespace PNP

/-- The report-facing residual-band decision endpoint is the concrete encoded
direct-wire exact-minimum threshold predicate.  Its semantic specification may
use exhaustive finite reference minimization; no polynomial decider follows
from this definition. -/
def ResidualBandExactMinimization : Language :=
  Concrete.LockedNAND.EncodedDirectWireMinimumThreshold

/-- Every intrinsically typed finite candidate has the exact expected
candidate/threshold semantics at the external bitstring boundary. -/
theorem residual_band_encoded_candidate_iff_reference_minimum
    {inputs gates outputs : Nat}
    (candidate : DirectWire.Candidate inputs gates outputs)
    (threshold : Nat) :
    ResidualBandExactMinimization
        (Concrete.LockedNAND.encodeLockedInstance
          (Concrete.LockedNAND.RawLockedInstance.ofCandidate
            candidate threshold)) ↔
      threshold + 1 ≤ DirectWire.referenceMinimum
        (DirectWire.Implementation.mk gates candidate) :=
  Concrete.LockedNAND.encodedDirectWireMinimumThreshold_ofCandidate_iff
    candidate threshold

/-- Locked NAND and the residual-band layer consume the same canonical
candidate/threshold query, so their concrete polynomial transport is the
identity program rather than a caller-supplied trust object. -/
theorem locked_nand_reduces_to_residual_band_checked :
    ReducesToPoly LockedNANDThreshold ResidualBandExactMinimization := by
  exact Concrete.reduction_refl ResidualBandExactMinimization

/-- If residual-band exact minimization is in P, then the locked NAND threshold
language is in P. -/
theorem locked_nand_in_p_from_residual_band_in_p
    (hResidualInP : PClass ResidualBandExactMinimization) : PClass LockedNANDThreshold :=
  reduction_transports_p_witness_model
    locked_nand_reduces_to_residual_band_checked hResidualInP

end PNP
