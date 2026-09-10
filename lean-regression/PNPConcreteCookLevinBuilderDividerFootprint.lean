import PNP.Concrete.CookLevinBuilderDividerFootprint

namespace PNP.Concrete.CookLevinBuilderDividerFootprintRegression

open CookLevin CookLevin.BuilderDividerFootprint

example : span .variable 9 = 10 := by decide
example : span (.constant 3) 20 = 4 := by decide
example : span (.add (.constant 2) (.constant 3)) 0 = 13 := by decide
example : span (.mul (.constant 2) (.constant 3)) 0 = 14 := by decide

/-- Equal root values do not imply identical eager intermediate footprints. -/
example :
    span (.add (.constant 0) (.add (.constant 0) (.add (.constant 0) (.constant 1)))) 0 = 11 ∧
    span (.add (.add (.constant 0) (.constant 0)) (.add (.constant 0) (.constant 1))) 0 = 10 := by decide

example : PipelineInputFramer.packedInputCount [] = 0 := by decide
example : PipelineInputFramer.packedInputCount [true] = 1 := by decide
example : PipelineInputFramer.packedInputCount [false, true, false] = 2 := by decide

example (polynomial : NatPolynomial) (input : Nat) :
    (BuilderUnaryPolynomial.scratchWord polynomial input).length = span polynomial input :=
  scratchWord_length_eq_span polynomial input

example {language : Language} (verifier : PolynomialTimeVerifier language) (input : Nat) :
    span (formulaWidthPolynomial verifier) input ≤
      2 * span (formulaVariableCountPolynomial verifier) input :=
  header_span_le_double_variable_span verifier input

example {language : Language} (verifier : PolynomialTimeVerifier language) (input : Nat) :
    input + 1 ≤ span (formulaVariableCountPolynomial verifier) input :=
  input_length_le_variable_span verifier input

example {language : Language} (verifier : PolynomialTimeVerifier language) (input : Nat) :
    2 * span (formulaVariableCountPolynomial verifier) input ≤
      span (BuilderDimensionRegisters.polynomial verifier) input :=
  double_variable_span_le_preparation_span verifier input

example (polynomial : NatPolynomial) (input : Nat) :
    (BuilderUnaryPolynomial.rootPrefixPolynomial polynomial).eval input + polynomial.eval input =
      span polynomial input := rootPrefix_eval_add_eval_eq_span polynomial input

example (input : BitString) : PipelineInputFramer.packedInputCount input ≤ input.length :=
  packedInputCount_le input

example (input : BitString) :
    (PipelineInputFramer.totalInputFramerOutsideLeft input).length ≤ input.length + 1 :=
  framerOutside_length_le input

example {language : Language} (problem : VerifierTableauProblem language) :
    (BuilderCompleteHeader.finalOutside problem).length =
      max (span (formulaWidthPolynomial problem.verifier) problem.input.length + 1)
        (BuilderCompleteHeader.baseOutside problem).length := headerOutside_length problem

example {language : Language} (problem : VerifierTableauProblem language) :
    (BuilderCompleteHeader.finalOutside problem).length ≤
      (BuilderUnaryPolynomial.scratchWord (BuilderDimensionRegisters.polynomial problem.verifier)
        problem.input.length).length + 1 := headerOutside_length_le_preparation problem

example {language : Language} (problem : VerifierTableauProblem language) :
    BuilderCursorSource.preservedTail problem = [] := preservedTail_eq_nil problem

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (BuilderDividerOperands.finalConfiguration problem index remaining output).tape.left = [] :=
  operandFinal_left_eq_nil problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language) :
    (BuilderDividerOperands.fromRawFinal problem).tape.left = [] := fromRawFinal_left_eq_nil problem

end PNP.Concrete.CookLevinBuilderDividerFootprintRegression
