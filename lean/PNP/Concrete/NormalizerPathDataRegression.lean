import PNP.Concrete.NormalizerPathData

namespace PNP.Concrete.NormalizerBlocks
example : TracePath.value [(⟨true, 0⟩, none)] ⟨false, 0⟩ = none := by decide
example : TracePath.value [(⟨false, 1⟩, none), (⟨true, 0⟩, some ⟨false, 1⟩)] ⟨true, 0⟩ = none := by decide
example : TracePath.value [(⟨true, 0⟩, some ⟨true, 0⟩)] ⟨true, 0⟩ = none := by decide
example : TracePath.value [(⟨true, 0⟩, some ⟨true, 0⟩), (⟨true, 0⟩, none)] ⟨true, 0⟩ =
    some [⟨true, 0⟩, ⟨true, 0⟩] := by decide
example : TracePath.value [(⟨false, 2⟩, some ⟨true, 0⟩), (⟨true, 0⟩, none)] ⟨false, 2⟩ =
    some [⟨false, 2⟩, ⟨true, 0⟩] := by decide

#print axioms TraceMember.same_true_iff
#print axioms PathData.vertex_append
#print axioms PathData.encode_append
#print axioms PathData.vertex_reverse
#print axioms PathData.encode_cons_reverse
#print axioms PathData.answer_none_distinct

end PNP.Concrete.NormalizerBlocks
