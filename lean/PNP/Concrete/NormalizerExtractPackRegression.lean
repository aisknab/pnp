import PNP.Concrete.NormalizerExtractPack

namespace PNP.Concrete.NormalizerBlocks
open Extraction
def extractionPackFixture (parent : Option CNFLiteral) : State :=
  ⟨⟨{ParentQuery.initial [] with output := ParentQuery.answer (some parent)}, []⟩,
    [true, false], [false, true], [], [], []⟩
example : (remainingPacked (extractionPackFixture none)).registers.input = [true, false, true, false] := by decide
example : (parentPacked (extractionPackFixture none)).registers.input = [false] := by decide
example : (parentPacked (extractionPackFixture (some ⟨false, 3⟩))).registers.input =
    TraceData.predecessor (some ⟨false, 3⟩) [] := by decide
example : (parentPacked (extractionPackFixture (some ⟨true, 0⟩))).registers.input =
    TraceData.predecessor (some ⟨true, 0⟩) [] := by decide

#print axioms Extraction.packRemaining_exec
#print axioms Extraction.remainingPacked_input
#print axioms Extraction.pushSign_exec
#print axioms Extraction.prepend_exec
#print axioms Extraction.parentSome_exec
#print axioms Extraction.chooseParent_exec
#print axioms Extraction.packParent_exec
#print axioms Extraction.parentPacked_input
#print axioms Extraction.parentPacked_fields
#print axioms Extraction.packParentFuel_bound

end PNP.Concrete.NormalizerBlocks
