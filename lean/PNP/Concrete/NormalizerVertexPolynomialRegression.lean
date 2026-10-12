import PNP.Concrete.NormalizerVertexPolynomial

namespace PNP.Concrete.NormalizerBlocks

example (input : BitString) : SearchVertices.sourceSteps input + 1 ≤ SearchVertices.sourceFuel.eval input.length :=
  SearchVertices.sourceSteps_bound input
example (input : BitString) :
    boundedDecide (BitRegister.CompilerIO.rawMachine SearchVertices.program)
      ((BitRegister.CompilerIO.runtimePolynomial 9 SearchVertices.sourceFuel).eval input.length) input = .accept :=
  SearchVertices.polynomial_accepts input
example (input : BitString) :
    (SearchVertices.polynomial.output input).length ≤ input.length + SearchVertices.sourceFuel.eval input.length :=
  SearchVertices.polynomial_output_length input

#print axioms SearchVertices.front_exec
#print axioms SearchVertices.frontSteps_bound
#print axioms SearchVertices.sourceFuel_eval
#print axioms SearchVertices.block_exec
#print axioms SearchVertices.initial_registers
#print axioms SearchVertices.closed_run
#print axioms SearchVertices.sourceSteps_bound
#print axioms SearchVertices.padded_run
#print axioms SearchVertices.acceptsWithin
#print axioms SearchVertices.polynomial_program
#print axioms SearchVertices.polynomial_output
#print axioms SearchVertices.polynomial_accepts
#print axioms SearchVertices.polynomial_output_length

end PNP.Concrete.NormalizerBlocks
