import PNP.Concrete.NormalizerPathPack
namespace PNP.Concrete.NormalizerBlocks
def pathPackFixture (flag : Bool) : TracePath.State :=
  ⟨{ParentQuery.initial [] with output := [flag]}, (PathData.encode [⟨false, 1⟩, ⟨true, 0⟩]).reverse, []⟩
example : (TracePath.finished (pathPackFixture true)).registers.output = PathData.answer (some [⟨false, 1⟩, ⟨true, 0⟩]) := by decide
example : (TracePath.finished (pathPackFixture false)).registers.output = PathData.answer none := by decide
#print axioms TracePath.packSuccess_exec
#print axioms TracePath.packFailure_exec
#print axioms TracePath.finish_exec
#print axioms TracePath.finishFuel_bound
#print axioms TracePath.finished_output
#print axioms TracePath.finished_preserves
end PNP.Concrete.NormalizerBlocks
