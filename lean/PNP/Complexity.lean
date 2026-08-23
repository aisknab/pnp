/-
Copyright (c) 2026 PNP Labs.

Report-facing compatibility names for the concrete finite-pipeline complexity
model.  Earlier reconstruction passes used name-only language and witness
structures here.  The active bridge now reuses the exact bitstring predicates,
finite programs, encoded-size polynomial bounds, and correctness fields from
`PNP.Concrete.Complexity`; it does not manufacture complexity witnesses from
string handles.
-/

import PNP.Concrete.Complexity

namespace PNP

/-- Report-facing language compatibility name.  A language is now the exact
    predicate on finite bitstrings used by the concrete model. -/
abbrev Language := Concrete.Language

/-- Complexity classes remain extensionally represented as predicates on
    concrete languages. -/
abbrev ComplexityClass := Language → Prop

/-- Report-facing compatibility name for a proved concrete polynomial-time
    deterministic decider. -/
abbrev PolyTimeDecider := Concrete.PolynomialTimeDecider

/-- Report-facing compatibility name for a proved bounded-certificate
    concrete polynomial-time verifier. -/
abbrev NondetPolyVerifier := Concrete.PolynomialTimeVerifier

/-- Report-facing compatibility name for a proved concrete polynomial
    many-one reduction. -/
abbrev PolyTimeManyOneReduction := Concrete.PolynomialReduction

/-- P in the report-facing bridge is the concrete finite-pipeline class P. -/
abbrev PClass : ComplexityClass := Concrete.InP

/-- NP in the report-facing bridge is the concrete bounded-certificate class
    NP. -/
abbrev NPClass : ComplexityClass := Concrete.InNP

/-- Polynomial reducibility is the concrete finite-function-pipeline
    relation. -/
abbrev ReducesToPoly := Concrete.ReducesTo

/-- The final compatibility statement is mutual inclusion of the concrete
    finite-pipeline P and NP classes. -/
abbrev PEqualsNP := Concrete.PEqualsNP

/-- NP-completeness is the concrete verifier-and-reduction notion. -/
abbrev NPComplete := Concrete.NPComplete

/-- Embed a concrete deterministic decider as a verifier that ignores its
    certificate. -/
def nondetVerifierFromDecider {L : Language}
    (decision : PolyTimeDecider L) : NondetPolyVerifier L :=
  Concrete.verifierFromDecider decision

/-- Compose a concrete polynomial reduction with a concrete deterministic
    decider for its target language. -/
def deciderFromReduction {A B : Language}
    (reduction : PolyTimeManyOneReduction A B)
    (decision : PolyTimeDecider B) : PolyTimeDecider A := by
  let precomposed :=
    Concrete.PolynomialTimeDecider.precompose reduction.function decision
  exact Concrete.PolynomialTimeDecider.relabel precomposed (by
    intro input
    exact (reduction.correctness input).symm)

/-- Standard closure facts used by the final complexity transport. -/
structure StandardComplexityAxioms : Prop where
  pSubsetNP : ∀ {A : Language}, PClass A → NPClass A
  reductionTransportsP : ∀ {A B : Language},
    ReducesToPoly A B → PClass B → PClass A

/-- Concrete P is contained in concrete NP. -/
theorem p_subset_np_witness_model {A : Language} : PClass A → NPClass A :=
  Concrete.p_subset_np

/-- Concrete polynomial reductions transport concrete P membership. -/
theorem reduction_transports_p_witness_model {A B : Language} :
    ReducesToPoly A B → PClass B → PClass A :=
  Concrete.reduction_transports_p

/-- The standard closure facts are constructed from the concrete model. -/
def standardComplexityAxioms : StandardComplexityAxioms :=
  { pSubsetNP := fun hP => p_subset_np_witness_model hP
    reductionTransportsP := fun hRed hPB =>
      reduction_transports_p_witness_model hRed hPB }

/-- If a concretely NP-complete language has a concrete P decider, concrete P
    and NP mutually include one another. -/
theorem np_complete_in_p_implies_p_eq_np
    {L : Language}
    (hComplete : NPComplete L)
    (hInP : PClass L) : PEqualsNP :=
  Concrete.np_complete_in_p_implies_p_eq_np hComplete hInP

end PNP
