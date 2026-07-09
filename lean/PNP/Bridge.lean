/-
Copyright (c) 2026 PNP Labs.

This file is the Lean bridge for the PNP proof-certificate stack.
It intentionally formalizes the theorem boundary, not the entire custom PCC
checker.  The remaining trust base is represented by fields of
`CheckerTrustModel`, so Lean users can see exactly which bridge assumptions
are still external to this formalization pass.
-/

import PNP.Complexity

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

This pass has discharged the generic complexity implication into the theorem
`np_complete_in_p_implies_p_eq_np`.  The remaining fields are narrower:
* `pccPackSound`: soundness of the executable PCC package checker;
* `satNPComplete`: the SAT NP-completeness theorem for the chosen definitions;
* `complexityAxioms`: standard closure facts for the abstract P/NP model.
-/
structure CheckerTrustModel where
  pccPackSound : AcceptedGeneratedPackage → PClass SAT
  satNPComplete : NPComplete SAT
  complexityAxioms : StandardComplexityAxioms

/-- Formal version of the report's bridge:
`CheckPCCPackexp(GeneratePCCPack()) = accept` implies `P = NP`, relative to
an explicit checker trust model. -/
theorem accepted_generated_package_implies_p_eq_np
    (T : CheckerTrustModel)
    (h : AcceptedGeneratedPackage) : PEqualsNP :=
  sat_np_complete_and_sat_in_p_implies_p_eq_np
    T.complexityAxioms
    T.satNPComplete
    (T.pccPackSound h)

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
      "Abstract theorem: NP-complete language in P implies P = NP, from standard closure facts"
    ]
    externalTrustBase := [
      "Checker soundness: accepted PCCPack implies SAT ∈ P",
      "SAT NP-completeness for the chosen concrete SAT/P/NP/reduction definitions",
      "Standard complexity closure facts: P ⊆ NP and polynomial reductions transport P membership",
      "Concrete machine-model definitions of P, NP, SAT, and polynomial reduction"
    ] }

end PNP
