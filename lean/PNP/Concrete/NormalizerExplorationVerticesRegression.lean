import PNP.Concrete.NormalizerExplorationVertices

namespace PNP.Concrete.NormalizerBlocks
open Exploration
example : (verticesBuilt (budgeted (loaded (encode 2 [[], []] [none, none])))).core.pending =
    SearchVertices.encodeVertices [⟨true, 0⟩, ⟨true, 1⟩, ⟨false, 0⟩, ⟨false, 1⟩] := by decide
example : (verticesBuilt (budgeted (loaded (encode 0 [] [])))).core.pending = [true, false] := by decide
example : (verticesBuilt (budgeted (loaded (encode 2 [[]] [none])))).remaining = [true, true, true] := by decide

#print axioms Exploration.verticesPrefix_exec
#print axioms Exploration.buildVertices_exec
#print axioms Exploration.verticesBuilt_frame
#print axioms Exploration.leftBuilt_buffer
#print axioms Exploration.rightBuilt_buffer
#print axioms Exploration.verticesBuilt_pending
#print axioms Exploration.verticesPrefixFuel_bound
#print axioms Exploration.verticesFuel_bound

end PNP.Concrete.NormalizerBlocks
