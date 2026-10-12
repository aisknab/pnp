import PNP.Concrete.NormalizerCacheSlots

namespace PNP.Concrete.NormalizerBlocks

example : CacheSlots.values [some 2,none,some 1] [⟨true,2⟩,⟨true,0⟩,⟨true,2⟩] = [some 1,some 2,some 1] := rfl
example : CacheSlots.values [some 2,none,some 1] [⟨true,1⟩,⟨true,4⟩] = [none,none] := rfl
example : CacheSlots.values [] [] = [] := rfl
example (r : DenseClauses.State) : Exec CacheSlots.call r.store (CacheSlots.callSteps r) (CacheSlots.called r).store :=
  CacheSlots.call_exec r

#print axioms CacheSlots.body_exec
#print axioms CacheSlots.body_fields
#print axioms CacheSlots.bodyFuel_bound
#print axioms CacheSlots.body_buffer
#print axioms CacheSlots.operation
#print axioms CacheSlots.call_exec
#print axioms CacheSlots.callSteps_bound
#print axioms CacheSlots.prefix_values
#print axioms CacheSlots.called_canonical

end PNP.Concrete.NormalizerBlocks
