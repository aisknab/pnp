import PNP.Concrete.NormalizerExplorationInitialize

namespace PNP.Concrete.NormalizerBlocks
open Exploration
example : sourceLimit (encode 3 [[], [⟨true, 2⟩]] [none, some 2]) = 5 := by decide
example : sourceVertices (encode 1 [[], []] [none, none]) = [⟨true, 0⟩, ⟨true, 1⟩, ⟨false, 0⟩] := by decide
example : (initialized []).core.pending = [true, false] := by decide
example : (initialized [true]).core.trace = [] := by decide

#print axioms Exploration.initialize_exec
#print axioms Exploration.initialized_fields
#print axioms Exploration.sourceLimit_bound
#print axioms Exploration.range_vertices_bound
#print axioms Exploration.initialized_within
#print axioms Exploration.initial_bounded
#print axioms Exploration.beforeVerticesFuel_bound
#print axioms Exploration.initial_ranges_bound
#print axioms Exploration.initializeFuel_bound

end PNP.Concrete.NormalizerBlocks
