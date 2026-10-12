import PNP.Concrete.NormalizerCacheOwnerQuery

namespace PNP.Concrete.NormalizerBlocks

example : CacheOwner.value [none,some 7,some 7] [⟨true,2⟩,⟨true,1⟩] 7 = some 1 := rfl
example : CacheOwner.value [some 7] [⟨true,1⟩] 7 = none := rfl
example : CacheOwner.value [none,some 2] [⟨true,1⟩] 7 = none := rfl
example (r : DenseClauses.State) : Exec CacheOwner.lookup r.store (CacheOwner.lookupFuel r) (CacheOwner.looked r).store :=
  CacheOwner.lookup_exec r

#print axioms CacheOwner.original_exec
#print axioms CacheOwner.original_canonical
#print axioms CacheOwner.dense_exec
#print axioms CacheOwner.choose_exec
#print axioms CacheOwner.lookup_exec
#print axioms CacheOwner.lookup_fields
#print axioms CacheOwner.lookupFuel_bound
#print axioms CacheOwner.lookup_output_bound
#print axioms CacheOwner.lookup_canonical

end PNP.Concrete.NormalizerBlocks
