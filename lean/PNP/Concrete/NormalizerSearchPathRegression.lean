import PNP.Concrete.NormalizerSearchPath
namespace PNP.Concrete.NormalizerBlocks
def searchPathFixture : Search.State :=
  Search.selected (Search.seenDerived (Search.explored (Exploration.encode 1 [[⟨true, 0⟩]] [none])))
example : (Search.reconstructed searchPathFixture).registers.output = PathData.answer (some [⟨false, 0⟩, ⟨true, 0⟩]) := by decide
example : (Search.reconstructed searchPathFixture).parent.graph.core.matching = TableOwner.answer (some 0) := by decide
#print axioms Search.pathTarget_exec
#print axioms Search.preparePath_exec
#print axioms Search.findPath_exec
#print axioms Search.reconstruct_exec
#print axioms Search.reconstructed_frame
#print axioms Search.reconstructed_canonical
end PNP.Concrete.NormalizerBlocks
