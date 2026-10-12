import PNP.Concrete.NormalizerCacheSlotChoose

namespace PNP.Concrete.NormalizerBlocks

example : CacheSlot.value 7 7 7 = 0 := rfl
example : CacheSlot.value 4 7 7 = 1 := rfl
example : CacheSlot.value 4 5 7 = 2 := rfl
example (r : DenseClauses.State) :
    Exec CacheSlot.choose r.store (CacheSlot.chooseFuel r) (CacheSlot.chosen r).store :=
  CacheSlot.choose_exec r
example (r : DenseClauses.State) : (CacheSlot.chosen r).registers.output.length ≤ 3 :=
  CacheSlot.chosen_output_length r

#print axioms CacheSlot.emitFirst_exec
#print axioms CacheSlot.emitMiddle_exec
#print axioms CacheSlot.emitLast_exec
#print axioms CacheSlot.secondChoice_exec
#print axioms CacheSlot.second_exec
#print axioms CacheSlot.firstChoice_exec
#print axioms CacheSlot.choose_exec
#print axioms CacheSlot.chooseFuel_bound
#print axioms CacheSlot.chosen_fields
#print axioms CacheSlot.chosen_output_length
#print axioms CacheSlot.chosen_canonical

end PNP.Concrete.NormalizerBlocks
