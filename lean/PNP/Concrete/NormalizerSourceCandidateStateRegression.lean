import PNP.Concrete.NormalizerSourceCandidateState
namespace PNP.Concrete.NormalizerBlocks
example (r : SourceCandidate.State) :
    (SourceCandidate.derived r).registers.output.length = (SourceCacheDriver.columns r).length :=
  SourceCandidate.derived_output_length r
example (r : SourceCandidate.State) : SourceCacheDriver.slots (SourceCandidate.derived r) = SourceCacheDriver.slots r :=
  (SourceCandidate.derived_cache r).2.2.1
example (r : SourceCandidate.State) :
    Exec SourceCandidate.derive r.store (SourceCandidate.deriveSteps r) (SourceCandidate.derived r).store :=
  SourceCandidate.derive_exec r
#print axioms SourceCandidate.bitsView_store
#print axioms SourceCandidate.withBits_store
#print axioms SourceCandidate.bitsView_withBits
#print axioms SourceCandidate.withBits_registers
#print axioms SourceCandidate.withBits_frame
#print axioms SourceCandidate.withBits_cache
#print axioms SourceCandidate.liftBits_exec
#print axioms SourceCandidate.bitsView_bounded
#print axioms SourceCandidate.loadData_exec
#print axioms SourceCandidate.ready_fields
#print axioms SourceCandidate.derive_exec
#print axioms SourceCandidate.derived_frame
#print axioms SourceCandidate.derived_cache
#print axioms SourceCandidate.derived_output_length
#print axioms SourceCandidate.derived_canonical
#print axioms SourceCandidate.deriveBound_eval
#print axioms SourceCandidate.deriveSteps_bound
end PNP.Concrete.NormalizerBlocks
