import PNP.Concrete.NormalizerExplorationData

namespace PNP.Concrete.NormalizerBlocks
open ExplorationData
example : Removes ⟨true, 2⟩ [⟨false, 1⟩, ⟨true, 2⟩, ⟨false, 1⟩] [⟨false, 1⟩, ⟨false, 1⟩] :=
  .skip _ (.head _)
example : (UnseenData.entry ⟨false, 7⟩).length = 22 := by decide
example : (TraceData.row (⟨true, 3⟩, some ⟨false, 5⟩) []).length = 13 := by decide
example : (TraceData.row (⟨true, 3⟩, none) []).length = 6 := by decide

#print axioms ExplorationData.Removes.member
#print axioms ExplorationData.Removes.subset
#print axioms ExplorationData.Removes.length
#print axioms ExplorationData.Removes.prefixed
#print axioms ExplorationData.Removes.bounds
#print axioms ExplorationData.entry_length
#print axioms ExplorationData.prefix_length
#print axioms ExplorationData.vertices_length
#print axioms ExplorationData.row_length
#print axioms ExplorationData.trace_length

end PNP.Concrete.NormalizerBlocks
