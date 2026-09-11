import PNP

namespace PNP

-- These types have no supplied hardness, reduction or reflection parameter.
example : SATHard := sat_np_hard_checked
example : NPComplete SAT := sat_np_complete_checked

example (source : Language) (sourceInNP : NPClass source) :
    ReducesToPoly source SAT :=
  sat_np_hard_checked sourceInNP

example (loop : PCCMinLoopCertificate)
    (accepted : AcceptedGeneratedPackage loop) : PEqualsNP :=
  accepted_generated_package_implies_p_eq_np loop accepted

example : FinalReportAntecedent → FinalReportConsequent :=
  final_report_bridge

-- Acceptance is conditional on an existing complete proof-bearing loop.
example (loop : PCCMinLoopCertificate) : FinalReportAntecedent :=
  ⟨loop, accepted_generated_package loop⟩

example (antecedent : FinalReportAntecedent) :
    ∃ loop : PCCMinLoopCertificate, AcceptedGeneratedPackage loop :=
  antecedent

example (loop : PCCMinLoopCertificate) :
    PolyTimeDecider ResidualBandExactMinimization :=
  loop.residualBandDecider

example : Main.rootTheoremStatus.unconditionalProofPresent = false := rfl
example : Main.rootTheoremStatus.publicTheoremReleased = false :=
  Main.rootTheoremStatus_not_released
example : Main.rootTheoremStatus.externalAssumptionsRemain = true :=
  Main.rootTheoremStatus_has_external_assumptions

end PNP
