import PNP.Concrete.NormalizerPathSemantics
namespace PNP.Concrete.NormalizerBlocks
def pathSemanticsFixture : TracePath.State :=
  ⟨{ParentQuery.initial [] with pending := TraceData.row (⟨false, 1⟩, none) [], targetIndex := [true], targetTag := [false], output := [false]}, [], []⟩
example : TracePath.observation (TracePath.bodyResult pathSemanticsFixture) = PathData.answer (some [⟨false, 1⟩]) := by decide
example : TracePath.observation pathSemanticsFixture = PathData.answer none := by decide
#print axioms TracePath.body_on_row
#print axioms TracePath.accepted_root
#print axioms TracePath.accepted_parent
#print axioms TracePath.body_row_root
#print axioms TracePath.body_row_parent
#print axioms TracePath.append_accumulator
end PNP.Concrete.NormalizerBlocks
