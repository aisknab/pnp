/-
Copyright (c) 2026 PNP Labs.

Concrete CNFSAT NP-completeness from the complete all-input Cook-Levin
construction and the already checked CNFSAT verifier. This is not a
polynomial-time SAT decision algorithm or a proof of P = NP.
-/
import PNP.Concrete.CookLevinCompleteBuilder
import PNP.Concrete.CNFWorkUniversalCorrectness

namespace PNP.Concrete.CookLevin

/-- Every language in the concrete bounded-certificate NP class reduces to
CNFSAT. The verifier witness comes from NP membership; the reduction is the
complete source-derived machine, not a supplied correctness certificate. -/
theorem cnfSAT_np_hard (source : Language) (sourceInNP : InNP source) :
    ReducesTo source CNFSAT := by
  rcases sourceInNP with ⟨verifier⟩
  exact ⟨polynomialReduction verifier⟩

/-- Closed NP-completeness in the selected concrete finite-machine model.
This packages NP membership and hardness, not CNFSAT membership in P. -/
theorem cnfSAT_np_complete : NPComplete CNFSAT :=
  { inNP := FinalUniversalDesign.cnfSATInNP
    hard := cnfSAT_np_hard }

end PNP.Concrete.CookLevin
