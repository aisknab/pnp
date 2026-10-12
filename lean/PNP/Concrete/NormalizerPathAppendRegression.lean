import PNP.Concrete.NormalizerPathAppend
namespace PNP.Concrete.NormalizerBlocks
def pathAppendFixture : TracePath.State :=
  ⟨{ParentQuery.initial [] with currentIndex := [true, true], pending := [false]}, [true, false], [true]⟩
example : (TracePath.nodeAppended pathAppendFixture).buffer = [false, true, true, false, true, false] := by decide
example : (TracePath.nodeAppended pathAppendFixture).core.pending = [false] := by decide
example : (TracePath.nodeAppended pathAppendFixture).parentBytes = [true] := by decide
#print axioms TracePath.appendTag_exec
#print axioms TracePath.saveBuffer_exec
#print axioms TracePath.appendNode_exec
#print axioms TracePath.nodeAppended_buffer
#print axioms TracePath.nodeAppended_preserves
#print axioms TracePath.nodeAppended_canonical
end PNP.Concrete.NormalizerBlocks
