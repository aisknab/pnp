/-
Copyright (c) 2026 PNP Labs.

This file is the Lean bridge for the PNP proof-certificate stack.
It intentionally formalizes the theorem boundary, not the entire custom PCC
checker.  The remaining trust base is represented by fields of
`CheckerTrustModel`, so Lean users can see exactly which bridge assumptions
are still external to this formalization pass.
-/

import PNP.PCCMin
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
axiom GeneratePCCPack : PCCPack

/-- The package checker named in the report. -/
axiom CheckPCCPackexp : PCCPack → Verdict

/-- The antecedent stated by the accepted report. -/
def AcceptedGeneratedPackage : Prop :=
  CheckPCCPackexp GeneratePCCPack = Verdict.accept

/-- The explicit trust model for this Lean bridge.

This pass factors the checker-soundness route through a structured PCCMin loop
certificate and rank-ordered ZeroSlack oracle certificate.  The local locked
NAND macro truth laws and the local prefix-conjunction semantics are discharged
separately by `lockedNANDMacroCertificate` and
`lockedNANDPrefixCertificate`. Remaining fields are:
* `pccPackProducesPCCMinLoop`: accepted PCC package emits an accepted PCCMin
  loop certificate with structured ZeroSlack/oracle evidence;
* `satHard`: SAT is NP-hard for the witness-model reduction relation.

The report-facing SAT, locked-NAND, and residual-band languages now reuse the
concrete bitstring predicates.  Their checked all-input or identity polynomial
reductions are compiled directly, so neither reduction remains caller trust.
-/
structure CheckerTrustModel where
  pccPackProducesPCCMinLoop : AcceptedGeneratedPackage → PCCMinLoopCertificate
  satHard : SATHard

/-- The accepted package gives residual-band exact minimization in P through an
accepted structured PCCMin loop certificate. -/
theorem accepted_generated_package_implies_residual_band_in_p
    (T : CheckerTrustModel)
    (h : AcceptedGeneratedPackage) : PClass ResidualBandExactMinimization :=
  residual_band_in_p_from_pccmin_loop_certificate (T.pccPackProducesPCCMinLoop h)

/-- The accepted package gives locked NAND threshold in P through residual-band
exact minimization. -/
theorem accepted_generated_package_implies_locked_nand_in_p
    (T : CheckerTrustModel)
    (h : AcceptedGeneratedPackage) : PClass LockedNANDThreshold :=
  locked_nand_in_p_from_residual_band_in_p
    (accepted_generated_package_implies_residual_band_in_p T h)

/-- The accepted package gives SAT in P through residual-band minimization and
the locked NAND threshold route. -/
theorem accepted_generated_package_implies_sat_in_p
    (T : CheckerTrustModel)
    (h : AcceptedGeneratedPackage) : PClass SAT :=
  sat_in_p_from_locked_nand_in_p
    (accepted_generated_package_implies_locked_nand_in_p T h)

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
      "Concrete finite-pipeline theorem: P ⊆ NP by embedding a deterministic decider as a bounded-certificate verifier",
      "Concrete finite-pipeline theorem: polynomial reductions transport P membership by composing proved function and decision programs",
      "Lean theorem: concrete NP-complete language in P implies mutual inclusion of concrete P and NP",
      "Lean theorem: compiled concrete CNFSAT verifier plus concrete SAT-hardness gives SAT NP-completeness",
      "Lean theorem: concrete equality, constant-one, constant-zero, NAND-trace, and final-conjunction macro semantics",
      "Lean computation: exposed single-instance macro outputs are pairwise distinct, nonconstant, and nonprojection",
      "Lean theorem: two-gate prefix nodes compute conjunction and expose its negation",
      "Lean theorem: the prefix tree covers exactly the supplied check list and is true iff every check is true",
      "Lean theorem: a nonempty n-check prefix tree uses exactly 2(n-1) NAND gates",
      "Lean computation: prefix-node exposed outputs are distinct, nonconstant, and nonprojection",
      "Lean theorem: structured PCCMin loop certificate constructs a residual-band exact-minimization decider witness",
      "Lean theorem: the concrete locked-NAND and residual-band endpoints share one encoded exact-minimum predicate, so identity transport gives locked NAND threshold ∈ P from residual-band membership",
      "Lean theorem: concrete locked NAND threshold in P plus the compiled all-bitstring CNFSAT-to-locked-NAND reduction gives concrete SAT ∈ P"
    ]
    externalTrustBase := [
      "Checker/reflection soundness: accepted PCCPack emits an accepted structured PCCMin loop certificate",
      "Semantic adequacy of PCCMinLoopCertificate and ZeroSlackCertificate fields for the executable PCCMin algorithm",
      "Concrete SAT NP-hardness in the finite-pipeline reduction model"
    ] }

end PNP
