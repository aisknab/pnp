import PNP.Concrete.NormalizerMatchingValuePolynomial

namespace PNP.Concrete.NormalizerBlocks

example (input : BitString) : MatchingValue.sourceSteps input + 1 ≤ MatchingValue.sourceFuel.eval input.length :=
  MatchingValue.sourceSteps_bound input
example (input : BitString) :
    boundedDecide (BitRegister.CompilerIO.rawMachine MatchingValue.program)
      ((BitRegister.CompilerIO.runtimePolynomial 9 MatchingValue.sourceFuel).eval input.length) input = .accept :=
  MatchingValue.polynomial_accepts input
example (input : BitString) :
    (MatchingValue.polynomial.output input).length ≤ input.length + MatchingValue.sourceFuel.eval input.length :=
  MatchingValue.polynomial_output_length input

#print axioms MatchingValue.finish_exec
#print axioms MatchingValue.start_exec
#print axioms MatchingValue.block_exec
#print axioms MatchingValue.initial_registers
#print axioms MatchingValue.closed_run
#print axioms MatchingValue.sourceSteps_bound
#print axioms MatchingValue.padded_run
#print axioms MatchingValue.acceptsWithin
#print axioms MatchingValue.polynomial_program
#print axioms MatchingValue.polynomial_output
#print axioms MatchingValue.polynomial_accepts
#print axioms MatchingValue.polynomial_output_length

end PNP.Concrete.NormalizerBlocks
