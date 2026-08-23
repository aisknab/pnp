import PNP.ConcreteResidualBandCompatibility

namespace PNP

example : ResidualBandExactMinimization =
    Concrete.LockedNAND.EncodedDirectWireMinimumThreshold :=
  report_residual_band_eq_concrete_minimum_threshold

example : LockedNANDThreshold = ResidualBandExactMinimization :=
  report_locked_nand_eq_residual_band

example {inputs gates outputs : Nat}
    (candidate : DirectWire.Candidate inputs gates outputs)
    (threshold : Nat) :
    ResidualBandExactMinimization
        (Concrete.LockedNAND.encodeLockedInstance
          (Concrete.LockedNAND.RawLockedInstance.ofCandidate
            candidate threshold)) ↔
      threshold + 1 ≤ DirectWire.referenceMinimum
        (DirectWire.Implementation.mk gates candidate) :=
  residual_band_encoded_candidate_iff_reference_minimum candidate threshold

example : ReducesToPoly LockedNANDThreshold
    ResidualBandExactMinimization :=
  locked_nand_reduces_to_residual_band_checked

example (residualInP : PClass ResidualBandExactMinimization) :
    PClass LockedNANDThreshold :=
  locked_nand_in_p_from_residual_band_in_p residualInP

example
    (pcc : AcceptedGeneratedPackage → PCCMinLoopCertificate)
    (hard : SATHard) : CheckerTrustModel :=
  { pccPackProducesPCCMinLoop := pcc
    satHard := hard }

example :
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
    (PClass ResidualBandExactMinimization → PClass LockedNANDThreshold) :=
  concrete_residual_band_compatibility_checked_complete

end PNP
