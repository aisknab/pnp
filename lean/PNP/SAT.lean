/-
Copyright (c) 2026 PNP Labs.

SAT layer for the Lean bridge.

This pass keeps the concrete Boolean-formula syntax abstract, but it separates
SAT membership in NP from SAT hardness.  SAT-in-NP is represented by an
explicit verifier witness in the current witness model; NP-hardness remains the
standard reduction theorem to be discharged by a later concrete formalization.
-/

import PNP.Complexity

namespace PNP

/-- A SAT verifier witness in the current witness model.

The witness handle is abstract at this layer.  Later passes should replace this
by concrete CNF syntax, assignment certificates, and a polynomial verifier. -/
def satVerifierWitness : NondetPolyVerifier SAT :=
  { code := "sat-assignment-verifier" }

/-- SAT is in NP in the witness model. -/
theorem sat_in_np_witness_model : NPClass SAT :=
  ⟨satVerifierWitness⟩

/-- SAT NP-hardness, separated from SAT-in-NP. -/
def SATHard : Prop :=
  ∀ {A : Language}, NPClass A → ReducesToPoly A SAT

/-- SAT NP-completeness follows from the SAT-in-NP witness plus SAT hardness. -/
def sat_np_complete_from_hardness (hHard : SATHard) : NPComplete SAT :=
  { inNP := sat_in_np_witness_model
    hard := by
      intro A hA
      exact hHard hA }

end PNP
