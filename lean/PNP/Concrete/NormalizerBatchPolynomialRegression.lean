import PNP.Concrete.NormalizerBatchPolynomial

namespace PNP.Concrete.NormalizerBlocks

open BitRegister

example (input : BitString) : BatchPacket.sourceSteps input + 1 ≤ BatchPacket.sourceFuel.eval input.length :=
  BatchPacket.sourceSteps_bound input
example (input : BitString) : BatchPacket.polynomial.output input = (BatchPacket.result input).table :=
  BatchPacket.polynomial_output input
example (input : BitString) :
    boundedDecide (CompilerIO.rawMachine BatchPacket.program)
      ((CompilerIO.runtimePolynomial 11 BatchPacket.sourceFuel).eval input.length) input = .accept :=
  BatchPacket.polynomial_accepts input
example (input : BitString) :
    (BatchPacket.polynomial.output input).length ≤ input.length + BatchPacket.sourceFuel.eval input.length :=
  BatchPacket.polynomial_output_length input
example : BatchPacket.sourceFuel.eval 0 = 3760 := rfl

#print axioms BatchPacket.tableBound_mono
#print axioms BatchPacket.totalCostBound_mono
#print axioms BatchPacket.sourceFuel_eval
#print axioms BatchPacket.block_exec
#print axioms BatchPacket.closed_run
#print axioms BatchPacket.sourceSteps_bound
#print axioms BatchPacket.padded_run
#print axioms BatchPacket.acceptsWithin
#print axioms BatchPacket.polynomial_program
#print axioms BatchPacket.polynomial_output
#print axioms BatchPacket.polynomial_accepts
#print axioms BatchPacket.polynomial_output_length

end PNP.Concrete.NormalizerBlocks
