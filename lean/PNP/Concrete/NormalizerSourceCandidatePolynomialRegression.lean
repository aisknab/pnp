import PNP.Concrete.NormalizerSourceCandidatePolynomial
namespace PNP.Concrete.NormalizerBlocks
example (input : BitString) : (SourceCandidate.result input).store.Bounded (SourceCandidate.resultSize.eval input.length) :=
  SourceCandidate.result_bounded input
example (input : BitString) : SourceCandidate.sourceSteps input + 1 ≤ SourceCandidate.sourceFuel.eval input.length :=
  SourceCandidate.sourceSteps_bound input
example (input : BitString) :
    (SourceCandidate.polynomial.output input).length = (SourceCacheDriver.columns (SourceCacheDriver.result input)).length :=
  SourceCandidate.polynomial_candidate_length input
#print axioms SourceCandidate.block_exec
#print axioms SourceCandidate.closed_run
#print axioms SourceCandidate.sourceSteps_bound
#print axioms SourceCandidate.result_bounded
#print axioms SourceCandidate.padded_run
#print axioms SourceCandidate.acceptsWithin
#print axioms SourceCandidate.polynomial_program
#print axioms SourceCandidate.polynomial_output
#print axioms SourceCandidate.polynomial_accepts
#print axioms SourceCandidate.polynomial_output_length
#print axioms SourceCandidate.result_data
#print axioms SourceCandidate.result_cache
#print axioms SourceCandidate.result_output_length
#print axioms SourceCandidate.polynomial_candidate_length
#print axioms SourceCandidate.machine_output
end PNP.Concrete.NormalizerBlocks
