import PNP.Concrete.NormalizerSourceCheckPolynomial
namespace PNP.Concrete.NormalizerBlocks
open BitRegister
example (input : BitString) : SourceCheck.candidate (SourceCheck.result input) =
    (SourceCandidate.result input).registers.output := SourceCheck.result_candidate input
example (input : BitString) : SourceCacheDriver.rows (SourceCheck.result input) =
    SourceCacheDriver.rows (SourceCandidate.result input) := (SourceCheck.result_cache input).2.1
example (input : BitString) : (SourceCheck.result input).store.Bounded
    (SourceCheck.resultSize.eval input.length) := SourceCheck.result_bounded input
#print axioms SourceCheck.block_exec
#print axioms SourceCheck.closed_run
#print axioms SourceCheck.deriveSteps_input_bound
#print axioms SourceCheck.sourceSteps_bound
#print axioms SourceCheck.result_bounded
#print axioms SourceCheck.padded_run
#print axioms SourceCheck.acceptsWithin
#print axioms SourceCheck.polynomial_program
#print axioms SourceCheck.polynomial_output
#print axioms SourceCheck.polynomial_accepts
#print axioms SourceCheck.polynomial_output_length
#print axioms SourceCheck.result_data
#print axioms SourceCheck.result_cache
#print axioms SourceCheck.result_candidate
#print axioms SourceCheck.machine_output
end PNP.Concrete.NormalizerBlocks
