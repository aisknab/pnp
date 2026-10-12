import PNP.Concrete.NormalizerPathCanonical
namespace PNP.Concrete.NormalizerBlocks
def pathCanonicalFixture (trace : List TraceData.Row) (target : CNFLiteral) : TracePath.State :=
  ⟨{ParentQuery.initial [] with pending := TraceData.encode trace, targetIndex := List.replicate target.variableIndex true, targetTag := [target.positive], output := [false]}, [], []⟩
example : TracePath.observation (TracePath.whole (pathCanonicalFixture [(⟨false, 1⟩, some ⟨true, 0⟩), (⟨true, 0⟩, none)] ⟨false, 1⟩)).state = PathData.answer (some [⟨false, 1⟩, ⟨true, 0⟩]) := by decide
example : TracePath.observation (TracePath.whole (pathCanonicalFixture [(⟨true, 0⟩, none), (⟨false, 1⟩, some ⟨true, 0⟩)] ⟨false, 1⟩)).state = PathData.answer none := by decide
example : TracePath.observation (TracePath.whole (pathCanonicalFixture [(⟨false, 1⟩, some ⟨false, 1⟩), (⟨false, 1⟩, none)] ⟨false, 1⟩)).state = PathData.answer (some [⟨false, 1⟩, ⟨false, 1⟩]) := by decide
#print axioms TracePath.accumulated_follow
#print axioms TracePath.scan_canonical
#print axioms TracePath.whole_canonical
end PNP.Concrete.NormalizerBlocks
