/-
Copyright (c) 2026 PNP Labs.

SAT layer for the report-facing Lean bridge.

The active SAT endpoint is the exact canonical-CNF bitstring predicate from the
concrete finite-pipeline model.  Its NP membership reuses the compiled verifier,
certificate bound, runtime bound, and all-input correctness theorem already
checked there. Its NP-hardness and NP-completeness reuse the complete all-input
Cook-Levin construction; these results do not supply a deterministic SAT decider.
-/

import PNP.Complexity
import PNP.Concrete.CNFWorkUniversalCorrectness
import PNP.Concrete.CookLevinNPCompleteness

namespace PNP

/-- The report-facing SAT language is definitionally the concrete canonical-CNF
    bitstring language. -/
def SAT : Language := Concrete.CNFSAT

/-- The exact compiled concrete SAT verifier, not a string handle. -/
def satVerifierWitness : NondetPolyVerifier SAT :=
  Concrete.FinalUniversalDesign.cnfConcreteVerifier

/-- SAT is in the concrete bounded-certificate NP model. -/
theorem sat_in_np_witness_model : NPClass SAT :=
  ⟨satVerifierWitness⟩

/-- SAT NP-hardness, separated from SAT-in-NP. -/
def SATHard : Prop :=
  ∀ {A : Language}, NPClass A → ReducesToPoly A SAT

/-- Report-facing SAT hardness from the already checked, complete all-input
Cook-Levin reduction. No hardness witness is supplied by the caller. -/
theorem sat_np_hard_checked : SATHard := by
  intro source sourceInNP
  exact Concrete.CookLevin.cnfSAT_np_hard source sourceInNP

/-- Closed report-facing NP-completeness in the same concrete model. This is
not SAT membership in P. -/
theorem sat_np_complete_checked : NPComplete SAT :=
  Concrete.CookLevin.cnfSAT_np_complete

/-- SAT NP-completeness follows from the SAT-in-NP witness plus SAT hardness. -/
def sat_np_complete_from_hardness (hHard : SATHard) : NPComplete SAT :=
  { inNP := sat_in_np_witness_model
    hard := by
      intro A hA
      exact hHard hA }

/-- Concrete SAT NP-completeness plus a concrete SAT decider gives mutual
    inclusion of the concrete P and NP classes. -/
theorem sat_np_complete_and_sat_in_p_implies_p_eq_np
    (hSATComplete : NPComplete SAT)
    (hSATInP : PClass SAT) : PEqualsNP :=
  np_complete_in_p_implies_p_eq_np hSATComplete hSATInP

end PNP
