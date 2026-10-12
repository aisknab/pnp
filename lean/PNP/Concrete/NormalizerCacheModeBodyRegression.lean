import PNP.Concrete.NormalizerCacheModeBody

namespace PNP.Concrete.NormalizerBlocks

example (r : CacheMode.State) : Exec CacheMode.body r.store (CacheMode.bodyFuel r) (CacheMode.bodyResult r).store :=
  CacheMode.body_exec r
example : CacheMode.value [some 8] [⟨false,8⟩] [[⟨true,0⟩,⟨false,0⟩,⟨true,0⟩]] 0 0 = some 0 := rfl
example : CacheMode.value [none] [⟨false,8⟩] [[⟨true,0⟩,⟨false,0⟩,⟨true,0⟩]] 0 0 = none := rfl
example : CacheMode.value [some 9] [⟨false,8⟩] [[⟨true,0⟩,⟨false,0⟩,⟨true,0⟩]] 0 0 = none := rfl

#print axioms CacheMode.emitNone_exec
#print axioms CacheMode.choose_exec
#print axioms CacheMode.chosen_fields
#print axioms CacheMode.chooseFuel_bound
#print axioms CacheMode.chosen_output_length
#print axioms CacheMode.mode_exec
#print axioms CacheMode.mode_fields
#print axioms CacheMode.modeFuel_bound
#print axioms CacheMode.mode_canonical
#print axioms CacheMode.body_exec
#print axioms CacheMode.body_fields
#print axioms CacheMode.bodyFuel_bound
#print axioms CacheMode.body_canonical

end PNP.Concrete.NormalizerBlocks
