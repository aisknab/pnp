import PNP.Concrete.NormalizerSearchOutput
namespace PNP.Concrete.NormalizerBlocks
example : Search.answer (.terminal []) = [false] := by decide
example : Search.answer (.augment 2 []) = [true, true, true, false] := by decide
example : Search.value 1 [[⟨true, 0⟩]] [none] = .augment 0 [⟨false, 0⟩, ⟨true, 0⟩] := by decide
example : (PathData.answer (none : Option (List CNFLiteral))).tail = PathData.encode [] := by decide
#print axioms Search.path_answer_tail
#print axioms Search.prepareAugmentPrefix_exec
#print axioms Search.prepareAugment_exec
#print axioms Search.prependIndex_exec
#print axioms Search.finishAugment_exec
#print axioms Search.packAugment_exec
#print axioms Search.augmentPacked_output
#print axioms Search.packTerminal_exec
#print axioms Search.augment_exec
#print axioms Search.augmented_canonical
#print axioms Search.decideResult_exec
#print axioms Search.decided_canonical
end PNP.Concrete.NormalizerBlocks
