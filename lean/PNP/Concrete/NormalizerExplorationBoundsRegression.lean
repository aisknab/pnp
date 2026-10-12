import PNP.Concrete.NormalizerExplorationBounds

namespace PNP.Concrete.NormalizerBlocks
open Exploration
example : unseenBytes 0 = 2 := by decide
example : traceBytes 0 = 0 := by decide
example : (ParentQuery.answer (some (some ⟨true, 3⟩))).length = 6 := by decide
example : workBound 0 0 0 > 0 := by decide

#print axioms Exploration.Within.bytes
#print axioms Exploration.parent_index
#print axioms Exploration.parent_answer_length
#print axioms Exploration.trace_cons_bound
#print axioms Exploration.within_step
#print axioms Exploration.extraction_bound
#print axioms Exploration.choose_bound
#print axioms Exploration.bodyFuel_bound

end PNP.Concrete.NormalizerBlocks
