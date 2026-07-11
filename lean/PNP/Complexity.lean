/-
Copyright (c) 2026 PNP Labs.

Witness-level complexity-theory layer for the Lean bridge.

This file still does not choose a concrete Turing-machine or RAM model, but it
no longer leaves the basic class-closure facts as fields of the checker trust
model.  Instead, P, NP, and polynomial reduction are represented by explicit
witness structures, and the usual closure facts are proved by constructing the
corresponding witnesses.
-/

namespace PNP

/-- An abstract formal language.  This pass does not choose a concrete machine
model. -/
structure Language where
  name : String

/-- Complexity classes are represented extensionally as sets of languages. -/
def ComplexityClass := Language → Prop

/-- A polynomial-time deterministic decider witness for a language.

The `code` field is intentionally only a name/handle at this layer. Later
passes should replace it by concrete machine syntax plus a polynomial bound. -/
structure PolyTimeDecider (L : Language) where
  code : String

/-- A polynomial-time nondeterministic verifier witness for a language. -/
structure NondetPolyVerifier (L : Language) where
  code : String

/-- A polynomial-time many-one reduction witness from `A` to `B`. -/
structure PolyTimeManyOneReduction (A B : Language) where
  code : String

/-- P as languages with a deterministic polynomial-time decider witness. -/
def PClass : ComplexityClass := fun L => Nonempty (PolyTimeDecider L)

/-- NP as languages with a nondeterministic polynomial-time verifier witness. -/
def NPClass : ComplexityClass := fun L => Nonempty (NondetPolyVerifier L)

/-- Polynomial-time many-one reduction as a witness relation. -/
def ReducesToPoly (A B : Language) : Prop := Nonempty (PolyTimeManyOneReduction A B)

/-- The final theorem statement. -/
def PEqualsNP : Prop := PClass = NPClass

/-- The legacy SAT label used by the string-handle locked-NAND bridge.

This is deliberately only a named value in the non-authoritative witness
model.  It is not identified with `PNP.Concrete.CNFSAT`, and making the label
concrete does not supply SAT semantics, NP-hardness, or a decision procedure. -/
def SAT : Language := { name := "SAT" }

/-- NP-completeness over the reduction relation. -/
structure NPComplete (L : Language) : Prop where
  inNP : NPClass L
  hard : ∀ {A : Language}, NPClass A → ReducesToPoly A L

/-- Embed a deterministic decider as a nondeterministic verifier that ignores
its certificate. -/
def nondetVerifierFromDecider {L : Language} (d : PolyTimeDecider L) : NondetPolyVerifier L :=
  { code := "ignore-certificate(" ++ d.code ++ ")" }

/-- Compose a many-one reduction to `B` with a deterministic decider for `B`. -/
def deciderFromReduction {A B : Language}
    (r : PolyTimeManyOneReduction A B)
    (d : PolyTimeDecider B) : PolyTimeDecider A :=
  { code := "compose-reduction(" ++ r.code ++ ", " ++ d.code ++ ")" }

/-- Standard closure facts needed for the usual NP-complete-in-P implication. -/
structure StandardComplexityAxioms : Prop where
  pSubsetNP : ∀ {A : Language}, PClass A → NPClass A
  reductionTransportsP : ∀ {A B : Language}, ReducesToPoly A B → PClass B → PClass A

/-- P is a subset of NP in the witness model. -/
theorem p_subset_np_witness_model {A : Language} : PClass A → NPClass A := by
  intro hP
  rcases hP with ⟨d⟩
  exact ⟨nondetVerifierFromDecider d⟩

/-- Polynomial reductions transport membership in P in the witness model. -/
theorem reduction_transports_p_witness_model {A B : Language} :
    ReducesToPoly A B → PClass B → PClass A := by
  intro hRed hPB
  rcases hRed with ⟨r⟩
  rcases hPB with ⟨d⟩
  exact ⟨deciderFromReduction r d⟩

/-- The standard closure facts are theorems for this witness model. -/
def standardComplexityAxioms : StandardComplexityAxioms :=
  { pSubsetNP := fun hP => p_subset_np_witness_model hP
    reductionTransportsP := fun hRed hPB => reduction_transports_p_witness_model hRed hPB }

/-- If an NP-complete language is in P, then P = NP. -/
theorem np_complete_in_p_implies_p_eq_np
    {L : Language}
    (hComplete : NPComplete L)
    (hInP : PClass L) : PEqualsNP := by
  funext A
  apply propext
  constructor
  · intro hP
    exact standardComplexityAxioms.pSubsetNP hP
  · intro hNP
    exact standardComplexityAxioms.reductionTransportsP (hComplete.hard hNP) hInP

/-- SAT-specific form used by the report bridge. -/
theorem sat_np_complete_and_sat_in_p_implies_p_eq_np
    (hSATComplete : NPComplete SAT)
    (hSATInP : PClass SAT) : PEqualsNP :=
  np_complete_in_p_implies_p_eq_np hSATComplete hSATInP

end PNP
