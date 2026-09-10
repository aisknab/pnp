import PNP.Concrete.CookLevinBuilderDimensionRegisters

namespace PNP.Concrete.CookLevinBuilderDimensionRegistersRegression

open CookLevin CookLevin.BuilderDimensionRegisters

-- The zero product preserves a real width register, despite an unchanged root.
example : (preparationPolynomial (.constant 5)
    (.add .variable (.constant 2))).eval 3 = 5 := rfl

example : BuilderUnaryPolynomial.registerValues
    (preparationPolynomial (.constant 5) (.add .variable (.constant 2))) 3 =
      [5, 0, 3, 2, 5, 0, 5] := rfl

example : BuilderUnaryPolynomial.registerValues (.constant 5) 3 ≠
    BuilderUnaryPolynomial.registerValues
      (preparationPolynomial (.constant 5) (.add .variable (.constant 2))) 3 := by
  decide

-- Empty values do not erase the three register separators.
example : dimensionWord 0 0 =
    [BuilderUnaryPolynomial.separatorSymbol,
      BuilderUnaryPolynomial.separatorSymbol,
      BuilderUnaryPolynomial.separatorSymbol] := rfl

example : (dimensionWord 2 5).length = 10 := rfl
example : (dimensionWord 0 0).length = 3 := rfl

example (counter width : NatPolynomial) (input : Nat) :
    (preparationPolynomial counter width).eval input = counter.eval input :=
  preparationPolynomial_eval counter width input

example (counter width : NatPolynomial) (input : Nat) :
    ∃ valuesPrefix,
      BuilderUnaryPolynomial.registerValues
          (preparationPolynomial counter width) input =
        valuesPrefix ++ [width.eval input, 0, counter.eval input] ∧
      valuesPrefix.length = BuilderUnaryPolynomial.nodeCount counter +
        BuilderUnaryPolynomial.nodeCount width :=
  registerValues_layout counter width input

example {language : Language} (problem : VerifierTableauProblem language) :
    (polynomial problem.verifier).eval problem.input.length =
      BuilderFullScheduleCursorController.bodySlotCount problem :=
  polynomial_eval problem

example {language : Language} (problem : VerifierTableauProblem language) :
    (rawTimePolynomial problem.verifier).eval problem.input.length =
      6 * BuilderUnaryPolynomial.workSteps (polynomial problem.verifier) problem.input :=
  rawTimePolynomial_eval problem

-- The all-input contract includes actual execution, tape preservation, and cost.
example {language : Language} (problem : VerifierTableauProblem language)
    (outside : List WorkSymbol) (output : List CNFToken) :
    let program := machine problem.verifier
    let steps := BuilderUnaryPolynomial.workSteps
      (polynomial problem.verifier) problem.input
    let initial := BuilderUnaryPolynomial.initialConfiguration
      (polynomial problem.verifier) problem.input outside output
    let final := BuilderUnaryPolynomial.finalConfiguration
      (polynomial problem.verifier) problem.input outside output
    ∃ valuesPrefix,
      workRunExact? program steps initial = some final ∧
      run (compileWorkMachine program) (6 * steps)
          (encodeWorkConfiguration initial) = encodeWorkConfiguration final ∧
      final.tape = BuilderTokenAppender.workspaceTape problem.input
        ((valuesPrefix ++ dimensionWord problem.formulaClauseSlotsPerConstraint
          (BuilderFullScheduleCursorController.bodySlotCount problem)) ++
          BuilderUnaryPolynomial.scratchEndSymbol :: outside.drop
            ((BuilderUnaryPolynomial.scratchWord (polynomial problem.verifier)
              problem.input.length).length + 1)) output ∧
      6 * steps = (rawTimePolynomial problem.verifier).eval problem.input.length :=
  construct_dimensions problem outside output

end PNP.Concrete.CookLevinBuilderDimensionRegistersRegression
