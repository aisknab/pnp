/-
Copyright (c) 2026 PNP Labs.

This file is the Lean bridge for the PNP proof-certificate stack.
It intentionally formalizes the theorem boundary, not the entire custom PCC
checker.  The remaining trust base is represented by fields of
`CheckerTrustModel`, so Lean users can see exactly which bridge assumptions
are still external to this formalization pass.
-/

import PNP.LockedNAND
import PNP.SAT

namespace PNP

/-- The executable checker verdict. -/
inductive Verdict where
  | accept
  | reject
  deriving DecidableEq, Repr

/-- The generated proof-carrying package. -/
structure PCCPack where
  id : String

/-- The deterministic package generator named in the report. -/
constant GeneratePCCPack : PCCPack

/-- The package checker named in the report. -/
constant CheckPCCPackexp : PCCPack → Verdict

/-- The antecedent stated by the accepted report. -/
def AcceptedGeneratedPackage : Prop :=
  CheckPCCPackexp GeneratePCCPack = Verdict.accept

/-- The explicit trust model for this Lean bridge.

This pass factors the bridge through the report's locked NAND route and separates
SAT-in-NP from SAT-hardness.  Remaining fields are now:
* `pccPackSoundLockedNAND`: accepted PCC package gives a polynomial decider
  witness for the locked NAND threshold language;
* `lockedNANDReduction`: SAT reduces to the locked NAND threshold language;
* `satHard`: SAT is NP-hard for the witness-model reduction relation.
-/
structure CheckerTrustModel where
  pccPackSoundLockedNAND : AcceptedGeneratedPackage → PClass LockedNANDThreshold
  lockedNANDReduction : LockedNANDReductionTrust
  satHard : SATHard

/-- The accepted package gives SAT in P through the locked NAND threshold route. -/
theorem accepted_generated_package_implies_sat_in_p
    (T : CheckerTrustModel)
    (h : AcceptedGeneratedPackage) : PClass SAT :=
  sat_in_p_from_locked_nand_in_p
    T.lockedNANDReduction
    (T.pccPackSoundLockedNAND h)

/-- Formal version of the report's bridge:
`CheckPCCPackexp(GeneratePCCPack()) = accept` implies `P = NP`, relative to
an explicit checker trust model. -/
theorem accepted_generated_package_implies_p_eq_np
    (T : CheckerTrustModel)
    (h : AcceptedGeneratedPackage) : PEqualsNP :=
  sat_np_complete_and_sat_in_p_implies_p_eq_np
    (sat_np_complete_from_hardness T.satHard)
    (accepted_generated_package_implies_sat_in_p T h)

/-- Report-facing antecedent. -/
def FinalReportAntecedent : Prop := AcceptedGeneratedPackage

/-- Report-facing consequent. -/
def FinalReportConsequent : Prop := PEqualsNP

/-- The final report bridge as a theorem in Lean. -/
theorem final_report_bridge
    (T : CheckerTrustModel) :
    FinalReportAntecedent → FinalReportConsequent :=
  accepted_generated_package_implies_p_eq_np T

/-- A small machine-readable summary object for downstream Lean files. -/
structure LeanBridgeSummary where
  reportCoordinate : String
  antecedentName : String
  consequentName : String
  bridgeTheoremName : String
  dischargedByLean : List String
  externalTrustBase : List String

/-- Summary for the Lean bridge pass. -/
def leanBridgeSummary : LeanBridgeSummary :=
  { reportCoordinate := "PNP-FINAL-PROOF-REPORT-7072F8D"
    antecedentName := "CheckPCCPackexp GeneratePCCPack = Verdict.accept"
    consequentName := "PClass = NPClass"
    bridgeTheoremName := "final_report_bridge"
    dischargedByLean := [
      "Witness-model theorem: P ⊆ NP by embedding a deterministic decider as a nondeterministic verifier",
      "Witness-model theorem: polynomial reductions transport P membership by composing reduction and decider witnesses",
      "Lean theorem: NP-complete language in P implies P = NP",
      "Lean theorem: SAT-in-NP witness plus SAT-hardness gives SAT NP-completeness",
      "Lean theorem: locked NAND threshold in P plus SAT-to-locked-NAND reduction gives SAT ∈ P"
    ]
    externalTrustBase := [
      "Checker soundness: accepted PCCPack implies locked NAND threshold ∈ P",
      "Locked NAND SAT reduction: SAT reduces to the locked NAND threshold language",
      "SAT NP-hardness for the witness-model reduction relation",
      "Semantic adequacy of the witness model relative to a concrete machine model"
    ] }

end PNP
