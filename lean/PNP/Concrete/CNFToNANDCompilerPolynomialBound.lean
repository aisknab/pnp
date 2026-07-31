/-
Copyright (c) 2026 PNP Labs.

One closed encoded-input polynomial for the complete CNF-to-NAND compiler.

The outer graph pays for the total parser, one canonical carrier encoding,
one canonical controller execution, and its three literal graph bridges.
Every successful formula-specific charge is transported to the original raw
CNF bit length; malformed inputs stop in the parser and fit the same bound.
-/

import PNP.Concrete.CNFToNANDCompilerTrace
import PNP.Concrete.CNFToNANDControllerPolynomialBound

namespace PNP.Concrete.CNFToNANDCompilerPolynomialBound

open PNP.Concrete

/-! ## Closed polynomial -/

def parserWorkTimePolynomial : NatPolynomial :=
  .add (.mul (.constant 8) .variable) (.constant 32)

theorem parserWorkTimePolynomial_eval (bitLength : Nat) :
    parserWorkTimePolynomial.eval bitLength =
      CNFSourceParser.parserWorkBound bitLength := by
  rfl

/-- The three `+1` terms are the parser-to-carrier,
carrier-to-controller, and controller-to-global-accept/reject bridges. -/
def allInputWorkTimePolynomial : NatPolynomial :=
  .add
    (.add
      (.add parserWorkTimePolynomial
        CNFToNANDCarrierEncoder.workPolynomial)
      CNFToNANDControllerPolynomialBound.controllerWorkTimePolynomial)
    (.constant 3)

def allInputWorkBound (bitLength : Nat) : Nat :=
  CNFSourceParser.parserWorkBound bitLength +
    CNFToNANDCarrierEncoder.workPolynomial.eval bitLength +
    CNFToNANDControllerPolynomialBound.controllerWorkBound bitLength +
    3

theorem allInputWorkTimePolynomial_eval (bitLength : Nat) :
    allInputWorkTimePolynomial.eval bitLength =
      allInputWorkBound bitLength := by
  simp [allInputWorkTimePolynomial, allInputWorkBound,
    parserWorkTimePolynomial_eval,
    CNFToNANDControllerPolynomialBound.controllerWorkTimePolynomial_eval,
    NatPolynomial.eval, Nat.add_assoc]

/-- Six raw transitions implement every work transition. -/
def compiledRawTimePolynomial : NatPolynomial :=
  .mul (.constant 6) allInputWorkTimePolynomial

theorem compiledRawTimePolynomial_eval (bitLength : Nat) :
    compiledRawTimePolynomial.eval bitLength =
      6 * allInputWorkBound bitLength := by
  simp [compiledRawTimePolynomial,
    allInputWorkTimePolynomial_eval]

/-! ## Canonical component accounting -/

theorem formulaTokens_length_le_encodedBits
    (formula : CNFFormula) :
    (CNFToNANDWorkspace.formulaTokens formula).length ≤
      (encodeCNF formula).length := by
  rw [CNFToNANDWorkspace.canonicalEncodedBits_length]
  omega

theorem parserValidWorkSteps_le
    (formula : CNFFormula) :
    CNFSourceParser.validWorkSteps formula ≤
      CNFSourceParser.parserWorkBound
        (encodeCNF formula).length := by
  have wordLength :
      (CNFSourceParser.formulaWord formula).length =
        (CNFToNANDWorkspace.formulaTokens formula).length := by
    have equality := congrArg List.length
      (CNFSourceParser.formulaWord_eq_token_work_symbols formula)
    simpa [CNFToNANDWorkspace.formulaTokens,
      cnfTokenWorkSymbols_length] using equality
  unfold CNFSourceParser.validWorkSteps
    CNFSourceParser.parserWorkBound
  rw [wordLength,
    CNFToNANDWorkspace.canonicalEncodedBits_length]
  omega

theorem carrierCanonicalWorkSteps_le
    (formula : CNFFormula) :
    CNFToNANDCarrierEncoder.canonicalWorkSteps
        (CNFToNANDWorkspace.formulaTokens formula) ≤
      CNFToNANDCarrierEncoder.workPolynomial.eval
        (encodeCNF formula).length := by
  exact Nat.le_trans
    (CNFToNANDCarrierEncoder.canonicalWorkSteps_polynomial_bound
      (CNFToNANDWorkspace.formulaTokens formula))
    (NatPolynomial.eval_mono
      CNFToNANDCarrierEncoder.workPolynomial
      (formulaTokens_length_le_encodedBits formula))

theorem malformedWorkBound_le (bitLength : Nat) :
    CNFSourceParser.parserWorkBound bitLength + 1 ≤
      allInputWorkBound bitLength := by
  unfold allInputWorkBound
  omega

/-- Additive accounting lemma used by the successful outer graph path. -/
theorem canonicalComponents_le
    (formula : CNFFormula)
    (carrierSteps controllerSteps : Nat)
    (carrierBound :
      carrierSteps ≤
        CNFToNANDCarrierEncoder.canonicalWorkSteps
          (CNFToNANDWorkspace.formulaTokens formula))
    (controllerBound :
      controllerSteps ≤
        CNFToNANDControllerPolynomialBound.controllerWorkBound
          (encodeCNF formula).length) :
    CNFSourceParser.validWorkSteps formula + 1 +
          carrierSteps + 1 + controllerSteps + 1 ≤
      allInputWorkBound (encodeCNF formula).length := by
  have parserBound := parserValidWorkSteps_le formula
  have carrierEncodedBound := Nat.le_trans carrierBound
    (carrierCanonicalWorkSteps_le formula)
  unfold allInputWorkBound
  omega

end PNP.Concrete.CNFToNANDCompilerPolynomialBound
