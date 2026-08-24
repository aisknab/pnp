import PNP

namespace PNP

example (loop : PCCMinLoopCertificate) :
    CheckPCCPackexp (GeneratePCCPack loop) = Verdict.accept :=
  check_generated_pcc_pack_exp_accepts loop

example (loop : PCCMinLoopCertificate) :
    (GeneratePCCPack loop).loopCertificate = loop :=
  generated_pcc_pack_loop_certificate_exact loop

example (loop : PCCMinLoopCertificate) :
    CheckPCCPackexp
        { id := "not-the-canonical-generated-id"
          loopCertificate := loop } = Verdict.reject := by
  apply check_pcc_pack_exp_rejects_mismatched_id
  simp [generatedPCCPackId]

example (loop : PCCMinLoopCertificate) :
    AcceptedGeneratedPackage loop :=
  accepted_generated_package loop

example (loop : PCCMinLoopCertificate) : FinalReportAntecedent :=
  ⟨loop, accepted_generated_package loop⟩

example (hard : SATHard) : CheckerTrustModel :=
  { satHard := hard }

example (loop : PCCMinLoopCertificate) :
    PClass ResidualBandExactMinimization :=
  accepted_generated_package_implies_residual_band_in_p loop
    (accepted_generated_package loop)

example (loop : PCCMinLoopCertificate) :
    CheckPCCPackexp (GeneratePCCPack loop) = Verdict.accept ∧
      (GeneratePCCPack loop).loopCertificate = loop ∧
      ∀ pack : PCCPack,
        pack.id ≠ generatedPCCPackId →
          CheckPCCPackexp pack = Verdict.reject :=
  typed_pccpack_reflection_checked_complete loop

end PNP
