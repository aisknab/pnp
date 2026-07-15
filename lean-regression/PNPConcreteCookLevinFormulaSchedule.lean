import PNP

namespace PNP.Concrete.CookLevinFormulaScheduleRegression

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

example : FormulaSchedule.emit
    ([none, some false, none, some true] : List (Option Bool)) =
    [false, true] := rfl

example : (FormulaSchedule.pad 0 ([] : List Bool)).length = 0 := rfl

example : FormulaSchedule.emit (FormulaSchedule.pad 4 [true, false]) =
    [true, false] := by simp

example : emptyProblem.formulaConstraintSchedule.length =
    emptyProblem.formulaConstraintSlotCount :=
  emptyProblem.formulaConstraintSchedule_length

example : oneBitProblem.formulaClauseSchedule.length =
    oneBitProblem.formulaClauseSlotCount :=
  oneBitProblem.formulaClauseSchedule_length

example : oddProblem.formulaTokenSchedule.length =
    (oddProblem.formulaVariableSlotBound + 1) +
      oddProblem.formulaClauseSlotCount * oddProblem.formulaTokensPerClause + 1 :=
  oddProblem.formulaTokenSchedule_length

example : emptyProblem.formulaBitSchedule.length =
    (encodedFormulaSizePolynomial emptyProblem.verifier).eval
      (BitString.size emptyProblem.input) :=
  emptyProblem.formulaBitSchedule_length

example : oneBitProblem.formulaBitSchedule.length =
    (encodedFormulaSizePolynomial oneBitProblem.verifier).eval
      (BitString.size oneBitProblem.input) :=
  oneBitProblem.formulaBitSchedule_length

example : oddProblem.formulaBitSchedule.length =
    (encodedFormulaSizePolynomial oddProblem.verifier).eval
      (BitString.size oddProblem.input) :=
  oddProblem.formulaBitSchedule_length

example : evenProblem.formulaBitSchedule.length =
    (encodedFormulaSizePolynomial evenProblem.verifier).eval
      (BitString.size evenProblem.input) :=
  evenProblem.formulaBitSchedule_length

example : FormulaSchedule.emit emptyProblem.formulaBitSchedule =
    emptyProblem.encodedFormula :=
  emptyProblem.formulaBitSchedule_emit_eq_encodedFormula

example : FormulaSchedule.emit oneBitProblem.formulaBitSchedule =
    oneBitProblem.encodedFormula :=
  oneBitProblem.formulaBitSchedule_emit_eq_encodedFormula

example : FormulaSchedule.emit oddProblem.formulaBitSchedule =
    oddProblem.encodedFormula :=
  oddProblem.formulaBitSchedule_emit_eq_encodedFormula

example : FormulaSchedule.emit evenProblem.formulaBitSchedule =
    evenProblem.encodedFormula :=
  evenProblem.formulaBitSchedule_emit_eq_encodedFormula

end PNP.Concrete.CookLevinFormulaScheduleRegression
