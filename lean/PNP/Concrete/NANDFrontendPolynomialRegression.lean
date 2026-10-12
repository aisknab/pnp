import PNP.Concrete.NANDFrontendPolynomial

namespace PNP.Concrete.NANDFrontend

open BitRegister

example (input : BitString) :
    polynomial.output input = (frontendFinal (initialRegisters input)).output := polynomial_output input
example (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 9 sourceFuel).eval input.length) input = .accept :=
  polynomial_machine_accepts input
example (input : BitString) :
    (polynomial.output input).length ≤ input.length + sourceFuel.eval input.length :=
  polynomial_output_length input
example : polynomial.output [] = [false] := polynomial_empty
example (n : Nat) : sourceFuel.eval n = frontendBudget n := sourceFuel_eval n

#print axioms sourceFuel_eval
#print axioms frontend_padded
#print axioms acceptsWithin
#print axioms polynomial
#print axioms polynomial_program
#print axioms polynomial_output
#print axioms polynomial_machine_accepts
#print axioms polynomial_output_length
#print axioms polynomial_empty

end PNP.Concrete.NANDFrontend
