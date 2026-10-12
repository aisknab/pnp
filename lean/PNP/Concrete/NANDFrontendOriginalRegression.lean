import PNP.Concrete.NANDFrontendOriginal

namespace PNP.Concrete.NANDFrontend

example (input : BitString) : sourcePolynomial.output input = sourceData input :=
  sourcePolynomial_output input
example (input : BitString) (malformed : decodeEncodedCNF input = none) :
    sourcePolynomial.output input = [false] := sourcePolynomial_malformed input malformed
example (input : BitString) (original : CNFFormula) (decoded : decodeEncodedCNF input = some original) :
    sourcePolynomial.output input =
      recordData original.variableCount (formula (CNFToNAND.compileFormula original)) :=
  sourcePolynomial_decoded input original decoded
example : sourcePolynomial.output [] = [false] :=
  sourcePolynomial_malformed [] rfl
example (input : BitString) :
    machineOutput sourceRawRefinement.machine
      (sourceRawRefinement.timeBound.eval (BitString.size input)) input = sourceData input :=
  sourceMachine_output input
example (input : BitString) :
    boundedDecide sourceRawRefinement.machine
      (sourceRawRefinement.timeBound.eval (BitString.size input)) input ≠ .timeout :=
  sourceMachine_halts input
example (input : BitString) :
    BitString.size (machineOutput sourceRawRefinement.machine
      (sourceRawRefinement.timeBound.eval (BitString.size input)) input) ≤
        sourcePolynomial.outputSizeBound.eval (BitString.size input) :=
  sourceMachine_output_size input

#print axioms sourcePolynomial
#print axioms sourcePolynomial_program
#print axioms sourcePolynomial_output
#print axioms sourcePolynomial_malformed
#print axioms sourcePolynomial_decoded
#print axioms rawRefinement
#print axioms sourceRawRefinement
#print axioms sourceMachine_output
#print axioms sourceMachine_halts
#print axioms sourceMachine_output_size

end PNP.Concrete.NANDFrontend
