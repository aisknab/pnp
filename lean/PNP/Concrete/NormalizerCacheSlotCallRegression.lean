import PNP.Concrete.NormalizerCacheSlotCall

namespace PNP.Concrete.NormalizerBlocks

example (r : DenseClauses.State) :
    Exec CacheSlot.call r.store (CacheSlot.callFuel r) (CacheSlot.called r).store :=
  CacheSlot.call_exec r
example (r : DenseClauses.State) : CacheSlot.callFuel r ≤ 14 * r.registers.output.length + 68 :=
  CacheSlot.callFuel_bound r
example : CacheSlot.encodedValue [⟨false,8⟩,⟨true,8⟩,⟨false,1⟩] 8 = 0 := by
  rw [CacheSlot.encodedValue_cons_cons]
  rfl
example : CacheSlot.encodedValue [⟨true,8⟩,⟨false,9⟩,⟨true,1⟩] 9 = 1 := by
  rw [CacheSlot.encodedValue_cons_cons]
  rfl
example : CacheSlot.encodedValue [⟨true,8⟩,⟨false,9⟩,⟨true,1⟩] 1 = 2 := by
  rw [CacheSlot.encodedValue_cons_cons]
  rfl

#print axioms CacheSlot.chosen_output
#print axioms CacheSlot.prepare_exec
#print axioms CacheSlot.call_exec
#print axioms CacheSlot.callFuel_bound
#print axioms CacheSlot.called_fields
#print axioms CacheSlot.called_output_length
#print axioms CacheSlot.called_canonical
#print axioms CacheSlot.encodedValue_cons_cons

end PNP.Concrete.NormalizerBlocks
