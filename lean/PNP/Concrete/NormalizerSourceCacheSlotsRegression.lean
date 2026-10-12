import PNP.Concrete.NormalizerSourceCacheSlots

namespace PNP.Concrete.NormalizerBlocks

example (r : CutDriver.State) : Exec SourceCacheDriver.deriveSlots r.store (SourceCacheDriver.slotsSteps r)
    (SourceCacheDriver.slotsDerived r).store := SourceCacheDriver.deriveSlots_exec r
example (r : CutDriver.State) : SourceCacheDriver.modes (SourceCacheDriver.slotsDerived r) = r.registers.output :=
  (SourceCacheDriver.slotsDerived_cache r).1
example (r : CutDriver.State) : SourceCacheDriver.owners (SourceCacheDriver.slotsDerived r) = SourceCacheDriver.owners r :=
  (SourceCacheDriver.slotsDerived_cache r).2.1

#print axioms SourceCacheDriver.stashModes_exec
#print axioms SourceCacheDriver.withDense_cache
#print axioms SourceCacheDriver.loadSlots_exec
#print axioms SourceCacheDriver.setupSlots_exec
#print axioms SourceCacheDriver.slotsReady_fields
#print axioms SourceCacheDriver.slotsReady_frame
#print axioms SourceCacheDriver.deriveSlots_exec
#print axioms SourceCacheDriver.slotsDerived_cache
#print axioms SourceCacheDriver.slotsDerived_frame
#print axioms SourceCacheDriver.slotsDerived_output
#print axioms SourceCacheDriver.slotsSteps_bound

end PNP.Concrete.NormalizerBlocks
