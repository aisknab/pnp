import PNP.Concrete.NormalizerTablePolynomial

namespace PNP.Concrete.NormalizerBlocks

example (input : BitString) :
    Exec TableWrite.block (Occurrence.initialRegisters input).store (TableWrite.sourceSteps input)
      (TableWrite.result input).store := TableWrite.block_exec input
example (input : BitString) :
    TableWrite.sourceSteps input + 1 ≤ TableWrite.sourceFuel.eval input.length := TableWrite.sourceSteps_bound input
example (input : BitString) :
    TableWrite.polynomial.output input = (TableWrite.result input).output := TableWrite.polynomial_output input
example (input : BitString) :
    boundedDecide (BitRegister.CompilerIO.rawMachine TableWrite.program)
      ((BitRegister.CompilerIO.runtimePolynomial 9 TableWrite.sourceFuel).eval input.length) input = .accept :=
  TableWrite.polynomial_accepts input
example (input : BitString) :
    (TableWrite.polynomial.output input).length ≤ input.length + TableWrite.sourceFuel.eval input.length :=
  TableWrite.polynomial_output_length input

#print axioms TableWrite.prepare_exec
#print axioms TableWrite.headers_exec
#print axioms TableWrite.headerFuel_bound
#print axioms TableWrite.prepared_input_bound
#print axioms TableWrite.prepared_target_bound
#print axioms TableWrite.front_exec
#print axioms TableWrite.frontFuel_bound
#print axioms TableWrite.pack_exec
#print axioms TableWrite.block_exec
#print axioms TableWrite.closed_run
#print axioms TableWrite.sourceSteps_bound
#print axioms TableWrite.padded_run
#print axioms TableWrite.acceptsWithin
#print axioms TableWrite.polynomial_program
#print axioms TableWrite.polynomial_output
#print axioms TableWrite.polynomial_accepts
#print axioms TableWrite.polynomial_output_length

end PNP.Concrete.NormalizerBlocks
