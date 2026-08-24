import PNP.ConcreteLegacyLockedNANDCompatibility

namespace PNP

example : SAT = Concrete.CNFSAT :=
  report_sat_eq_concrete_cnfsat

example : LockedNANDThreshold =
    Concrete.LockedNAND.EncodedLockedNANDThreshold :=
  report_locked_nand_eq_concrete_threshold

example : NPClass SAT :=
  sat_in_np_witness_model

example : ReducesToPoly SAT LockedNANDThreshold :=
  sat_reduces_to_locked_nand_checked

example (lockedInP : PClass LockedNANDThreshold) : PClass SAT :=
  sat_in_p_from_locked_nand_in_p lockedInP

example (hard : SATHard) : CheckerTrustModel :=
  { satHard := hard }

example (loop : PCCMinLoopCertificate) :
    residualBandDeciderFromPCCMinCertificate
        (pccMinAlgorithmCertificateFromLoop loop) =
      loop.residualBandDecider :=
  pccmin_concrete_decider_projection_exact loop

example :
    SAT = Concrete.CNFSAT ∧
    LockedNANDThreshold =
      Concrete.LockedNAND.EncodedLockedNANDThreshold ∧
    NPClass SAT ∧
    ReducesToPoly SAT LockedNANDThreshold ∧
    (PClass LockedNANDThreshold → PClass SAT) :=
  concrete_legacy_locked_nand_compatibility_checked_complete

end PNP
