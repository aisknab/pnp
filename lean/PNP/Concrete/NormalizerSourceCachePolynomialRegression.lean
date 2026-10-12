import PNP.Concrete.NormalizerSourceCachePolynomial

namespace PNP.Concrete.NormalizerBlocks

example (input : BitString) : Exec SourceCacheDriver.block (CutDriver.initial input).store
    (SourceCacheDriver.sourceSteps input) (SourceCacheDriver.result input).store :=
  SourceCacheDriver.block_exec input
example (input : BitString) :
    SourceCacheDriver.polynomial.output input = SourceCacheDriver.slots (SourceCacheDriver.result input) :=
  SourceCacheDriver.polynomial_slots input
example (input : BitString) :
    (SourceCacheDriver.result input).store.Bounded (SourceCacheDriver.resultSize.eval input.length) :=
  SourceCacheDriver.result_bounded input

#print axioms SourceCacheDriver.derive_exec
#print axioms SourceCacheDriver.derived_frame
#print axioms SourceCacheDriver.derived_dimensions
#print axioms SourceCacheDriver.derived_cache
#print axioms SourceCacheDriver.derived_slots
#print axioms SourceCacheDriver.deriveSteps_bound
#print axioms SourceCacheDriver.block_exec
#print axioms SourceCacheDriver.closed_run
#print axioms SourceCacheDriver.sourceSteps_bound
#print axioms SourceCacheDriver.result_bounded
#print axioms SourceCacheDriver.padded_run
#print axioms SourceCacheDriver.acceptsWithin
#print axioms SourceCacheDriver.polynomial_program
#print axioms SourceCacheDriver.polynomial_output
#print axioms SourceCacheDriver.polynomial_accepts
#print axioms SourceCacheDriver.polynomial_output_length
#print axioms SourceCacheDriver.result_data
#print axioms SourceCacheDriver.result_dimensions
#print axioms SourceCacheDriver.result_cache
#print axioms SourceCacheDriver.polynomial_slots
#print axioms SourceCacheDriver.machine_slots

end PNP.Concrete.NormalizerBlocks
