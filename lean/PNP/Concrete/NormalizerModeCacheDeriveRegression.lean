import PNP.Concrete.NormalizerModeCacheDerive

namespace PNP.Concrete.NormalizerBlocks

example (r : CutDriver.State) : Exec ModeCacheDriver.derive r.store (ModeCacheDriver.deriveSteps r) (ModeCacheDriver.derived r).store :=
  ModeCacheDriver.derive_exec r
example (r : CutDriver.State) : ModeCacheDriver.owners (ModeCacheDriver.derived r) = r.registers.output :=
  (ModeCacheDriver.derived_cache r).1
example (r : CutDriver.State) : ModeCacheDriver.literals (ModeCacheDriver.derived r) = ModeCacheDriver.literals r :=
  (ModeCacheDriver.derived_cache r).2

#print axioms ModeCacheDriver.stash_exec
#print axioms ModeCacheDriver.loadData_exec
#print axioms ModeCacheDriver.setup_exec
#print axioms ModeCacheDriver.ready_fields
#print axioms ModeCacheDriver.ready_cache
#print axioms ModeCacheDriver.ready_frame
#print axioms ModeCacheDriver.derive_exec
#print axioms ModeCacheDriver.derived_cache
#print axioms ModeCacheDriver.derived_frame
#print axioms ModeCacheDriver.derived_output
#print axioms ModeCacheDriver.deriveSteps_bound

end PNP.Concrete.NormalizerBlocks
