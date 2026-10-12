import PNP.Concrete.NormalizerOwnerPolynomial

namespace PNP.Concrete.NormalizerBlocks

open BitRegister

example (input : BitString) : TableOwner.sourceSteps input + 1 ≤ 16 * input.length + 22 :=
  TableOwner.sourceSteps_bound input
example (input : BitString) : TableOwner.polynomial.output input = (TableOwner.result input).state.output :=
  TableOwner.polynomial_output input
example (input : BitString) :
    boundedDecide (CompilerIO.rawMachine TableOwner.program)
      ((CompilerIO.runtimePolynomial 9 TableOwner.sourceFuel).eval input.length) input = .accept :=
  TableOwner.polynomial_accepts input
example (input : BitString) :
    (TableOwner.polynomial.output input).length ≤ input.length + TableOwner.sourceFuel.eval input.length :=
  TableOwner.polynomial_output_length input

#print axioms TableOwner.block_exec
#print axioms TableOwner.initial_registers
#print axioms TableOwner.closed_run
#print axioms TableOwner.sourceSteps_bound
#print axioms TableOwner.padded_run
#print axioms TableOwner.acceptsWithin
#print axioms TableOwner.polynomial_program
#print axioms TableOwner.polynomial_output
#print axioms TableOwner.polynomial_accepts
#print axioms TableOwner.polynomial_output_length

end PNP.Concrete.NormalizerBlocks
