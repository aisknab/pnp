import PNP.Concrete.NormalizerExplorationLoader

namespace PNP.Concrete.NormalizerBlocks
open Exploration
example : sourceCount (encode 3 [[], [⟨true, 2⟩]] [none, some 2]) = 2 := by decide
example : (loaded (encode 3 [[], [⟨true, 2⟩]] [none, some 2])).core.parent.targetIndex = [true, true, true] := by decide
example : (loaded (encode 3 [[], [⟨true, 2⟩]] [none, some 2])).core.trace = [] := by decide
example : (loaded []).core.parent.currentIndex = [] := by decide

#print axioms Exploration.readWidth_exec
#print axioms Exploration.countFormula_exec
#print axioms Exploration.counted_result
#print axioms Exploration.loader_exec
#print axioms Exploration.loaded_fields
#print axioms Exploration.source_sizes
#print axioms Exploration.loaderFuel_bound
#print axioms Exploration.source_canonical

end PNP.Concrete.NormalizerBlocks
