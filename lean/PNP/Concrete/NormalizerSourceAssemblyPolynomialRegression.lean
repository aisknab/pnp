import PNP.Concrete.NormalizerSourceAssemblyPolynomial
namespace PNP.Concrete.NormalizerBlocks
open BitRegister
example (input : BitString) : SourceAssembly.sourceSteps input+1 ≤ SourceAssembly.sourceFuel.eval input.length :=
  SourceAssembly.sourceSteps_bound input
example (input : BitString) :
    boundedDecide (CompilerIO.rawMachine SourceAssembly.program)
      ((CompilerIO.runtimePolynomial 38 SourceAssembly.sourceFuel).eval input.length) input = .accept :=
  SourceAssembly.polynomial_accepts input
example (input : BitString) :
    (SourceAssembly.polynomial.output input).length ≤ input.length+SourceAssembly.sourceFuel.eval input.length :=
  SourceAssembly.polynomial_output_length input
#print axioms SourceAssembly.check_exec
#print axioms SourceAssembly.block_exec
#print axioms SourceAssembly.initial_registers
#print axioms SourceAssembly.initial_bounded
#print axioms SourceAssembly.closed_run
#print axioms SourceAssembly.sourceSteps_bound
#print axioms SourceAssembly.result_bounded
#print axioms SourceAssembly.padded_run
#print axioms SourceAssembly.acceptsWithin
#print axioms SourceAssembly.polynomial
#print axioms SourceAssembly.polynomial_program
#print axioms SourceAssembly.polynomial_output
#print axioms SourceAssembly.polynomial_accepts
#print axioms SourceAssembly.polynomial_output_length
#print axioms SourceAssembly.result_recovery
#print axioms SourceAssembly.machine_output
end PNP.Concrete.NormalizerBlocks
