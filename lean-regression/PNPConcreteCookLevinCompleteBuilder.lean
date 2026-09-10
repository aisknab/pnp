/-
Copyright (c) 2026 PNP Labs.
Exact complete-builder and polynomial reduction contracts for M230.
-/
import PNP.Concrete.CookLevinCompleteBuilder

open PNP.Concrete PNP.Concrete.CookLevin

example {language : Language}
    (verifier : PolynomialTimeVerifier language) (input : BitString) :
    boundedDecide (formulaBuilderMachine verifier)
      ((formulaBuilderTimeBound verifier).eval input.length) input = .accept := by
  exact formulaBuilderMachine_accept verifier input

example {language : Language}
    (verifier : PolynomialTimeVerifier language) (input : BitString) :
    machineOutput (formulaBuilderMachine verifier)
      ((formulaBuilderTimeBound verifier).eval input.length) input =
        (VerifierTableauProblem.mk verifier input).encodedFormula := by
  exact formulaBuilderMachine_output verifier input

example {language : Language}
    (verifier : PolynomialTimeVerifier language) (input : BitString) :
    (formulaBuilder verifier).output input =
      (VerifierTableauProblem.mk verifier input).encodedFormula := by
  exact formulaBuilder_output verifier input

example {language : Language}
    (verifier : PolynomialTimeVerifier language) (input : BitString) :
    machineOutput (FunctionProgram.RawRefinement.compile (formulaBuilder verifier).program).machine
      ((FunctionProgram.RawRefinement.compile (formulaBuilder verifier).program).timeBound.eval
        (BitString.size input)) input = (VerifierTableauProblem.mk verifier input).encodedFormula := by
  exact formulaBuilder_rawRefinement_output verifier input

example {language : Language}
    (verifier : PolynomialTimeVerifier language) (input : BitString) :
    (polynomialReduction verifier).function.output input =
      (VerifierTableauProblem.mk verifier input).encodedFormula := by
  exact polynomialReduction_output verifier input

example {language : Language}
    (verifier : PolynomialTimeVerifier language) :
    ∀ input, (polynomialReduction verifier).function.output input =
      (VerifierTableauProblem.mk verifier input).encodedFormula := by
  exact cook_levin_formula_builder_checked_complete verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (formulaBuilder verifier).program =
      .machine (formulaBuilderMachine verifier) (formulaBuilderTimeBound verifier) := rfl

example {language : Language} (verifier : PolynomialTimeVerifier language) (input : BitString) :
    (formulaBuilder verifier).program.Halts input :=
  (formulaBuilder verifier).haltsWithin input

example {language : Language} (verifier : PolynomialTimeVerifier language) (input : BitString) :
    (formulaBuilder verifier).program.chargedSteps input ≤
      (formulaBuilder verifier).runtimeBound.eval (BitString.size input) :=
  (formulaBuilder verifier).runtime_le input

example {language : Language} (verifier : PolynomialTimeVerifier language) (input : BitString) :
    BitString.size ((formulaBuilder verifier).program.eval input) ≤
      (formulaBuilder verifier).outputSizeBound.eval (BitString.size input) :=
  (formulaBuilder verifier).output_size_le input

example {language : Language} (verifier : PolynomialTimeVerifier language) (input : BitString) :
    language input ↔ CNFSAT ((polynomialReduction verifier).function.output input) :=
  (polynomialReduction verifier).correctness input

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (formulaBuilder verifier).output [] =
      (VerifierTableauProblem.mk verifier []).encodedFormula :=
  formulaBuilder_output verifier []

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (formulaBuilder verifier).output [true, false, true] =
      (VerifierTableauProblem.mk verifier [true, false, true]).encodedFormula :=
  formulaBuilder_output verifier [true, false, true]

example {language : Language} (verifier : PolynomialTimeVerifier language) (input : BitString) :
    boundedDecide (formulaBuilderMachine verifier)
      ((formulaBuilderTimeBound verifier).eval input.length) input ≠ .timeout := by
  rw [formulaBuilderMachine_accept]
  decide
