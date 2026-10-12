import PNP.Concrete.NormalizerSourceCheckState
namespace PNP.Concrete.NormalizerBlocks
open BitRegister
example (r : CutDriver.State) : SourceCheck.candidate (SourceCheck.saved r) = r.registers.output := rfl
example (r : CutDriver.State) : SourceCheck.candidate (SourceCheck.derived r) = r.registers.output :=
  SourceCheck.derived_candidate r
example (r : CutDriver.State) : SourceCacheDriver.literals (SourceCheck.derived r) = SourceCacheDriver.literals r :=
  (SourceCheck.derived_cache r).2.2.2.2.2
#print axioms SourceCheck.save_exec
#print axioms SourceCheck.loadData_exec
#print axioms SourceCheck.prepare_exec
#print axioms SourceCheck.prepared_fields
#print axioms SourceCheck.prepared_frame
#print axioms SourceCheck.prepared_cache
#print axioms SourceCheck.derive_exec
#print axioms SourceCheck.derived_frame
#print axioms SourceCheck.derived_cache
#print axioms SourceCheck.derived_candidate
#print axioms SourceCheck.derived_canonical
#print axioms SourceCheck.deriveSteps_bound
end PNP.Concrete.NormalizerBlocks
