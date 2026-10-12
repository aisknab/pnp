import PNP.Concrete.NormalizerOwnerCacheDerive

namespace PNP.Concrete.NormalizerBlocks

example (r : CutDriver.State) :
    OwnerCacheDriver.literals (OwnerCacheDriver.derived r) = r.registers.output :=
  OwnerCacheDriver.derived_literals r
example (r : CutDriver.State) :
    (OwnerCacheDriver.derived r).core.table = r.core.table ∧
    (OwnerCacheDriver.derived r).variables = r.variables :=
  ⟨(OwnerCacheDriver.derived_frame r).2.2.1,(OwnerCacheDriver.derived_frame r).2.2.2.2.2⟩
example (r : CutDriver.State) (bound : Nat) (bounded : r.store.Bounded bound) :
    OwnerCacheDriver.deriveSteps r ≤ OwnerCacheDriver.deriveBound.eval bound :=
  OwnerCacheDriver.deriveSteps_bound r bound bounded

#print axioms OwnerCacheDriver.stash_exec
#print axioms OwnerCacheDriver.loadData_exec
#print axioms OwnerCacheDriver.setup_exec
#print axioms OwnerCacheDriver.ready_fields
#print axioms OwnerCacheDriver.derive_exec
#print axioms OwnerCacheDriver.derived_literals
#print axioms OwnerCacheDriver.derived_frame
#print axioms OwnerCacheDriver.derived_output
#print axioms OwnerCacheDriver.deriveSteps_bound

end PNP.Concrete.NormalizerBlocks
