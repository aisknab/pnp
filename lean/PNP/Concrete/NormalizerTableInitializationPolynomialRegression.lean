import PNP.Concrete.NormalizerTableInitializationPolynomial

namespace PNP.Concrete.NormalizerBlocks

example (input : BitString) :
    Exec TableInit.block (Occurrence.initialRegisters input).store (TableInit.sourceSteps input)
      (TableInit.result input).store := TableInit.block_exec input
example (input : BitString) :
    TableInit.sourceSteps input + 1 ≤ TableInit.sourceFuel.eval input.length := TableInit.sourceSteps_bound input
example (input : BitString) :
    TableInit.polynomial.output input = (TableInit.result input).output := TableInit.polynomial_output input
example (input : BitString) :
    boundedDecide (BitRegister.CompilerIO.rawMachine TableInit.program)
      ((BitRegister.CompilerIO.runtimePolynomial 9 TableInit.sourceFuel).eval input.length) input = .accept :=
  TableInit.polynomial_accepts input
example (input : BitString) :
    (TableInit.polynomial.output input).length ≤ input.length + TableInit.sourceFuel.eval input.length :=
  TableInit.polynomial_output_length input

#print axioms TableInit.header_exec
#print axioms TableInit.headerFuel_bound
#print axioms TableInit.count_length_bound
#print axioms TableInit.front_exec
#print axioms TableInit.frontFuel_bound
#print axioms TableInit.block_exec
#print axioms TableInit.closed_run
#print axioms TableInit.sourceSteps_bound
#print axioms TableInit.padded_run
#print axioms TableInit.acceptsWithin
#print axioms TableInit.polynomial_program
#print axioms TableInit.polynomial_output
#print axioms TableInit.polynomial_accepts
#print axioms TableInit.polynomial_output_length

end PNP.Concrete.NormalizerBlocks
