import PNP.Concrete.NormalizerCacheModeQuery

namespace PNP.Concrete.NormalizerBlocks

example : CacheMode.transportedValue [none,some 8] [⟨false,4⟩,⟨false,8⟩] 1 = some 1 := rfl
example : CacheMode.transportedValue [none,some 8] [⟨false,4⟩] 1 = none := rfl
example : CacheMode.transportedValue [none,some 8] [⟨false,8⟩] 0 = none := rfl
example (r : CacheMode.State) :
    Exec CacheMode.chooseSlot r.store (CacheMode.chooseSlotFuel r) (CacheMode.slotChosen r).store :=
  CacheMode.chooseSlot_exec r

#print axioms CacheMode.transport_exec
#print axioms CacheMode.transported_fields
#print axioms CacheMode.transportFuel_bound
#print axioms CacheMode.transported_canonical
#print axioms CacheMode.loadClause_exec
#print axioms CacheMode.readClause_exec
#print axioms CacheMode.loadTarget_exec
#print axioms CacheMode.chooseSlot_exec
#print axioms CacheMode.slotChosen_fields
#print axioms CacheMode.chooseSlotFuel_bound
#print axioms CacheMode.slotChosen_output_length
#print axioms CacheMode.slotChosen_canonical

end PNP.Concrete.NormalizerBlocks
