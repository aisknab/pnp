import PNP.Concrete.NormalizerSourceRecoveryPolynomial
namespace PNP.Concrete.NormalizerBlocks
example (input : BitString) :
    SourceRecovery.sourceSteps input+1 ≤ SourceRecovery.sourceFuel.eval input.length :=
  SourceRecovery.sourceSteps_bound input
example (input : BitString) :
    boundedDecide (BitRegister.CompilerIO.rawMachine SourceRecovery.program)
      ((BitRegister.CompilerIO.runtimePolynomial 36 SourceRecovery.sourceFuel).eval input.length) input = .accept :=
  SourceRecovery.polynomial_accepts input
example (n : Nat) : SourceRecovery.resultSize.eval n = n+SourceRecovery.sourceFuel.eval n := rfl
#print axioms SourceRecovery.block_exec
#print axioms SourceRecovery.initial_registers
#print axioms SourceRecovery.closed_run
#print axioms SourceRecovery.recoverySteps_input_bound
#print axioms SourceRecovery.sourceSteps_bound
#print axioms SourceRecovery.result_bounded
#print axioms SourceRecovery.padded_run
#print axioms SourceRecovery.acceptsWithin
#print axioms SourceRecovery.polynomial
#print axioms SourceRecovery.polynomial_program
#print axioms SourceRecovery.polynomial_output
#print axioms SourceRecovery.polynomial_accepts
#print axioms SourceRecovery.polynomial_output_length
#print axioms SourceRecovery.result_output_length
#print axioms SourceRecovery.machine_output
end PNP.Concrete.NormalizerBlocks
