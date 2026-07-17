import PNP

namespace PNP.Concrete.CookLevinFormulaCursorRegression

open CookLevin
open CookLevin.VerifierTableauProblem

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

example : CookLevin.DirectSlot.pad 2
    (fun index => ([true] : List Bool)[index]?) 0 = some (some true) := rfl

example : CookLevin.DirectSlot.pad 2
    (fun index => ([true] : List Bool)[index]?) 1 = some none := rfl

example : CookLevin.DirectSlot.pad 2
    (fun index => ([true] : List Bool)[index]?) 2 = none := rfl

example (index : Nat) :
    emptyProblem.formulaConstraintSlotDirect index =
      emptyProblem.formulaConstraintSchedule[index]? :=
  emptyProblem.formulaConstraintSlotDirect_eq index

example (index : Nat) :
    oneBitProblem.formulaClauseSlotDirect index =
      oneBitProblem.formulaClauseSchedule[index]? :=
  oneBitProblem.formulaClauseSlotDirect_eq index

example (index : Nat) :
    oddProblem.formulaTokenSlotDirect index =
      oddProblem.formulaTokenSchedule[index]? :=
  oddProblem.formulaTokenSlotDirect_eq index

example (index : Nat) :
    evenProblem.formulaBitSlotDirect index =
      evenProblem.formulaBitSchedule[index]? :=
  evenProblem.formulaBitSlotDirect_eq index

example : emptyProblem.formulaBitSlotCountDirect =
    (encodedFormulaSizePolynomial emptyProblem.verifier).eval
      (BitString.size emptyProblem.input) :=
  emptyProblem.formulaBitSlotCountDirect_eq_polynomial

example : oneBitProblem.formulaBitSlotCountDirect =
    (encodedFormulaSizePolynomial oneBitProblem.verifier).eval
      (BitString.size oneBitProblem.input) :=
  oneBitProblem.formulaBitSlotCountDirect_eq_polynomial

example : oddProblem.formulaBitSlotCountDirect =
    (encodedFormulaSizePolynomial oddProblem.verifier).eval
      (BitString.size oddProblem.input) :=
  oddProblem.formulaBitSlotCountDirect_eq_polynomial

example : evenProblem.formulaBitSlotCountDirect =
    (encodedFormulaSizePolynomial evenProblem.verifier).eval
      (BitString.size evenProblem.input) :=
  evenProblem.formulaBitSlotCountDirect_eq_polynomial

example : FormulaBitCursor.run emptyProblem
      emptyProblem.formulaBitSlotCountDirect FormulaBitCursor.initial =
    (emptyProblem.formulaBitSchedule,
      ⟨emptyProblem.formulaBitSlotCountDirect⟩) :=
  FormulaBitCursor.run_full emptyProblem

example : FormulaTokenCursor.step evenProblem
      ⟨evenProblem.formulaTokenSlotCountDirect⟩ = none :=
  FormulaTokenCursor.step_at_end evenProblem

example (cursor : FormulaTokenCursor)
    (hDone : FormulaTokenCursor.done oneBitProblem cursor) :
    FormulaTokenCursor.step oneBitProblem cursor = none :=
  FormulaTokenCursor.step_of_done oneBitProblem cursor hDone

example (cursor : FormulaTokenCursor)
    (hCursor : cursor.nextSlot < oddProblem.formulaTokenSlotCountDirect) :
    FormulaTokenCursor.step oddProblem cursor =
      some (oddProblem.formulaTokenSchedule.get
          ⟨cursor.nextSlot, by
            rw [← oddProblem.formulaTokenSlotCountDirect_eq]
            exact hCursor⟩,
        ⟨cursor.nextSlot + 1⟩) :=
  FormulaTokenCursor.step_of_lt oddProblem cursor hCursor

example : FormulaBitCursor.run oddProblem
      (oddProblem.formulaBitSlotCountDirect - 1) FormulaBitCursor.initial =
    (oddProblem.formulaBitSchedule.take
      (oddProblem.formulaBitSlotCountDirect - 1),
      ⟨oddProblem.formulaBitSlotCountDirect - 1⟩) :=
  FormulaBitCursor.run_one_step_short oddProblem

example : FormulaBitCursor.step evenProblem
      ⟨evenProblem.formulaBitSlotCountDirect⟩ = none :=
  FormulaBitCursor.step_at_end evenProblem

example : FormulaBitCursor.run oneBitProblem
      (oneBitProblem.formulaBitSlotCountDirect + 7) FormulaBitCursor.initial =
    (oneBitProblem.formulaBitSchedule,
      ⟨oneBitProblem.formulaBitSlotCountDirect⟩) :=
  FormulaBitCursor.run_excess oneBitProblem 7

example : FormulaSchedule.emit
      (FormulaBitCursor.run evenProblem
        evenProblem.formulaBitSlotCountDirect FormulaBitCursor.initial).1 =
    evenProblem.encodedFormula :=
  FormulaBitCursor.run_full_emit_eq_encodedFormula evenProblem

end PNP.Concrete.CookLevinFormulaCursorRegression
