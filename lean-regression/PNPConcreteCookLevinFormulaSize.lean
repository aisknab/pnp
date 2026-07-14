import PNP

namespace PNP.Concrete.CookLevinFormulaSizeRegression

open CookLevin

def inputOnlyVerifier : PolynomialTimeVerifier (fun _ => True) :=
  verifierFromDecider
    (PolynomialTimeDecider.ofMachine acceptAllPolynomialTime)

def pairedVerifier : PolynomialTimeVerifier (fun _ => True) :=
  { program :=
      { inputMode := .paired
        decision := .machine immediateAcceptMachine (.constant 0) }
    certificateBound := .linear 1 1
    runtimeBound := .constant 0
    haltsWithin := by
      intro input certificate hCertificate
      exact Verdict.noConfusion
    runtime_le := by
      intro input certificate hCertificate
      exact Nat.le_refl 0
    accepts_iff := by
      intro input
      constructor
      · intro member
        exact ⟨[], Nat.zero_le _, rfl⟩
      · intro witness
        exact True.intro }

def emptyProblem : VerifierTableauProblem (fun _ => True) :=
  { verifier := inputOnlyVerifier, input := [] }

def oneBitProblem : VerifierTableauProblem (fun _ => True) :=
  { verifier := inputOnlyVerifier, input := [false] }

def oddProblem : VerifierTableauProblem (fun _ => True) :=
  { verifier := pairedVerifier, input := [true, false, true] }

def evenProblem : VerifierTableauProblem (fun _ => True) :=
  { verifier := pairedVerifier, input := [true, true, false, false] }

example : BitString.size emptyProblem.encodedFormula ≤
    (encodedFormulaSizePolynomial emptyProblem.verifier).eval
      (BitString.size emptyProblem.input) :=
  emptyProblem.encodedFormula_size_le

example : BitString.size oneBitProblem.encodedFormula ≤
    (encodedFormulaSizePolynomial oneBitProblem.verifier).eval
      (BitString.size oneBitProblem.input) :=
  oneBitProblem.encodedFormula_size_le

example : BitString.size oddProblem.encodedFormula ≤
    (encodedFormulaSizePolynomial oddProblem.verifier).eval
      (BitString.size oddProblem.input) :=
  oddProblem.encodedFormula_size_le

example : BitString.size evenProblem.encodedFormula ≤
    (encodedFormulaSizePolynomial evenProblem.verifier).eval
      (BitString.size evenProblem.input) :=
  evenProblem.encodedFormula_size_le

example : BitString.size (encodeCNF
    { variableCount := 0, clauses := [] }) = 5 := rfl

example : BitString.size (encodeCNF
    { variableCount := 0, clauses := [[]] }) = 9 := rfl

example : BitString.size (encodeCNF
    { variableCount := 3
      clauses := [[{ positive := true, variableIndex := 2 }]] }) = 23 := rfl

end PNP.Concrete.CookLevinFormulaSizeRegression
