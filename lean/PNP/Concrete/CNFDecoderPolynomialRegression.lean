import PNP.Concrete.CNFDecoderPolynomial

namespace PNP.Concrete.CNFRegisterDecoder

example : sourceFuel.eval 0 = 16 := rfl
example (length : Nat) : sourceFuel.eval length = 6 * length + 16 := sourceFuel_eval length
example : BitRegister.CompilerIO.AcceptsWithin program sourceFuel := acceptsWithin
example :
    polynomial.program =
      .machine (BitRegister.CompilerIO.rawMachine program)
        (BitRegister.CompilerIO.runtimePolynomial 3 sourceFuel) := polynomial_program
example (input : BitString) :
    polynomial.output input = resultData (decodeEncodedCNF input) := polynomial_output input
example (formula : CNFFormula) :
    polynomial.output (encodeCNF formula) = true :: formulaData formula := polynomial_canonical formula
example (input : BitString) (invalid : decodeEncodedCNF input = none) :
    polynomial.output input = [false] := polynomial_malformed input invalid
example (input : BitString) :
    boundedDecide (BitRegister.CompilerIO.rawMachine program)
      ((BitRegister.CompilerIO.runtimePolynomial 3 sourceFuel).eval input.length) input = .accept :=
  polynomial_machine_accepts input
example (input : BitString) :
    (polynomial.output input).length ≤ input.length + 1 := polynomial_output_length input
example : polynomial.output [] = [false] := polynomial_malformed [] rfl
example : polynomial.output [false] = [false] := polynomial_malformed [false] rfl
example : polynomial.output [false, false, true, false] = [false] :=
  polynomial_malformed [false, false, true, false] rfl
example : polynomial.output [false, false, true, false, true] = [false] :=
  polynomial_malformed [false, false, true, false, true] rfl
example : polynomial.output [false, false, true, false, false, false, false] = [false] :=
  polynomial_malformed [false, false, true, false, false, false, false] rfl
example : polynomial.output (encodeCNF ⟨0, [[], []]⟩) = true :: formulaData ⟨0, [[], []]⟩ :=
  polynomial_canonical ⟨0, [[], []]⟩
example : polynomial.output (encodeCNF ⟨0, [[⟨true, 3⟩]]⟩) =
    true :: formulaData ⟨0, [[⟨true, 3⟩]]⟩ :=
  polynomial_canonical ⟨0, [[⟨true, 3⟩]]⟩

#print axioms sourceFuel_eval
#print axioms acceptsWithin
#print axioms polynomial
#print axioms polynomial_program
#print axioms polynomial_output
#print axioms polynomial_canonical
#print axioms polynomial_malformed
#print axioms polynomial_machine_accepts
#print axioms polynomial_output_length

end PNP.Concrete.CNFRegisterDecoder
