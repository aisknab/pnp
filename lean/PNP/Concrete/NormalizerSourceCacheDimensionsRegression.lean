import PNP.Concrete.NormalizerSourceCacheDimensions

namespace PNP.Concrete.NormalizerBlocks

example (r : CutDriver.State) : Exec SourceCacheDriver.finishData r.store
    (SourceCacheDriver.finishSteps r) (SourceCacheDriver.dataFinished r).store :=
  SourceCacheDriver.finishData_exec r
example (r : CutDriver.State) : SourceCacheDriver.slots (SourceCacheDriver.dataFinished r) = r.registers.output :=
  (SourceCacheDriver.dataFinished_fields r).2.2.1
example : ClauseCount.count (SearchVertices.encodeVertices [⟨true,0⟩,⟨false,27⟩,⟨true,4⟩]) = 3 :=
  SourceCacheDriver.count_vertices _

#print axioms SourceCacheDriver.prepareCount_exec
#print axioms SourceCacheDriver.count_exec
#print axioms SourceCacheDriver.countFuel_bound
#print axioms SourceCacheDriver.saveCount_exec
#print axioms SourceCacheDriver.measure_exec
#print axioms SourceCacheDriver.stashSlots_exec
#print axioms SourceCacheDriver.finishData_exec
#print axioms SourceCacheDriver.dataFinished_fields
#print axioms SourceCacheDriver.dataFinished_frame
#print axioms SourceCacheDriver.finishSteps_bound
#print axioms SourceCacheDriver.count_vertices

end PNP.Concrete.NormalizerBlocks
