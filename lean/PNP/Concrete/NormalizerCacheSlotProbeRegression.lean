import PNP.Concrete.NormalizerCacheSlotProbe

namespace PNP.Concrete.NormalizerBlocks

example (r : DenseClauses.State) :
    Exec CacheSlot.probe r.store (CacheSlot.probeFuel r) (CacheSlot.probed r).store :=
  CacheSlot.probe_exec r
example (r : DenseClauses.State) :
    (CacheSlot.probed r).core.pending.length ≤ r.core.pending.length :=
  CacheSlot.probed_pending_bound r
example (r : DenseClauses.State) (suffix : BitString)
    (p : r.core.pending = NANDFrontend.literalBits false 7 ++ suffix)
    (i : r.index = List.replicate 7 true) :
    (CacheSlot.probed r).registers.output = [true] :=
  (CacheSlot.probed_canonical r ⟨false,7⟩ suffix 7 p i).1
example (r : DenseClauses.State) (suffix : BitString)
    (p : r.core.pending = NANDFrontend.literalBits true 7 ++ suffix)
    (i : r.index = List.replicate 3 true) :
    (CacheSlot.probed r).registers.output = [false] :=
  (CacheSlot.probed_canonical r ⟨true,7⟩ suffix 3 p i).1

#print axioms CacheSlot.readLiteral_exec
#print axioms CacheSlot.comparison_exec
#print axioms CacheSlot.compared_output
#print axioms CacheSlot.comparisonFuel_bound
#print axioms CacheSlot.probe_exec
#print axioms CacheSlot.probed_fields
#print axioms CacheSlot.probed_output
#print axioms CacheSlot.probeFuel_bound
#print axioms CacheSlot.probed_pending_bound
#print axioms CacheSlot.probed_canonical

end PNP.Concrete.NormalizerBlocks
