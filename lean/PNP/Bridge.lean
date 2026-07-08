/-
Copyright (c) 2026 PNP Labs.

This file is the first Lean bridge for the PNP proof-certificate stack.
It intentionally formalizes the theorem boundary, not the entire custom PCC
checker.  The remaining trust base is represented by fields of
`CheckerTrustModel`, so Lean users can see exactly which bridge assumptions
are still external to this first formalization pass.
-/

namespace PNP

/-- An abstract formal language.  This first bridge pass does not choose a
concrete machine model. -/
structure Language where
  name : String

def ComplexityClass := Language → Prop

/-- The standard complexity classes are represented extensionally as sets of
languages.  Later passes can replace these abstract constants with concrete
machine-model definitions. -/
constant PClass : ComplexityClass
constant NPClass : ComplexityClass

/-- The final theorem statement. -/
def PEqualsNP : Prop := PClass = NPClass

/-- Polynomial-time many-one reduction, kept abstract in this bridge layer. -/
constant ReducesToPoly : Language → Language → Prop

/-- NP-completeness over the abstract reduction relation. -/
structure NPComplete (L : Language) : Prop where
  inNP : NPClass L
  hard : ∀ {A : Language}, NPClass A → ReducesToPoly A L

/-- The SAT language used by the locked-NAND reduction. -/
constant SAT : Language

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

/-- The explicit trust model for this first Lean bridge.

A future pass should replace these fields by proofs:
* `pccPackSound`: soundness of the executable PCC package checker;
* `satNPComplete`: the standard NP-completeness theorem for SAT;
* `npCompleteInPImpliesPEqNP`: the standard complexity implication.
-/
structure CheckerTrustModel where
  pccPackSound : AcceptedGeneratedPackage → PClass SAT
  satNPComplete : NPComplete SAT
  npCompleteInPImpliesPEqNP : ∀ {L : Language}, NPComplete L → PClass L → PEqualsNP

/-- Formal version of the report's bridge:
`CheckPCCPackexp(GeneratePCCPack()) = accept` implies `P = NP`, relative to
an explicit checker trust model. -/
theorem accepted_generated_package_implies_p_eq_np
    (T : CheckerTrustModel)
    (h : AcceptedGeneratedPackage) : PEqualsNP :=
  T.npCompleteInPImpliesPEqNP T.satNPComplete (T.pccPackSound h)

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
  externalTrustBase : List String

/-- Summary for the first Lean bridge pass. -/
def leanBridgeSummary : LeanBridgeSummary :=
  { reportCoordinate := "PNP-FINAL-PROOF-REPORT-7072F8D"
    antecedentName := "CheckPCCPackexp GeneratePCCPack = Verdict.accept"
    consequentName := "PClass = NPClass"
    bridgeTheoremName := "final_report_bridge"
    externalTrustBase := [
      "Checker soundness: accepted PCCPack implies SAT ∈ P",
      "SAT NP-completeness",
      "Complexity implication: NP-complete language in P implies P = NP",
      "Concrete machine-model definitions of P, NP, SAT, and polynomial reduction"
    ] }

end PNP
