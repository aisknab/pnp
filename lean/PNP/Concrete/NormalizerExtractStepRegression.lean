import PNP.Concrete.NormalizerExtractStep

namespace PNP.Concrete.NormalizerBlocks
open Extraction
def extractionStepFixture (vertices : List CNFLiteral) : State :=
  ⟨⟨ParentQuery.loaded (ParentQuery.encode ⟨false, 0⟩ [] [none] []), []⟩,
    SearchVertices.encodeVertices vertices, [], [], [true], []⟩
example : (bodyResult (extractionStepFixture [])).active = [] := by decide
example : (bodyResult (extractionStepFixture [⟨true, 0⟩, ⟨false, 1⟩])).parent.output = [true, false] := by decide
example : (bodyResult (extractionStepFixture [⟨true, 0⟩, ⟨false, 1⟩])).active = [] := by decide
example : (bodyResult (extractionStepFixture [⟨false, 3⟩, ⟨true, 0⟩])).skipped =
    (UnseenData.entry ⟨false, 3⟩).reverse := by decide
example : (bodyResult (extractionStepFixture [⟨false, 3⟩, ⟨true, 0⟩])).pending =
    SearchVertices.encodeVertices [⟨true, 0⟩] := by decide

#print axioms Extraction.choose_exec
#print axioms Extraction.queryFuel_bound
#print axioms Extraction.visit_exec
#print axioms Extraction.body_exec
#print axioms Extraction.visitFuel_bound
#print axioms Extraction.bodyFuel_bound
#print axioms Extraction.visit_fields
#print axioms Extraction.body_preserves
#print axioms Extraction.body_progress
#print axioms Extraction.body_size
#print axioms Extraction.stepBound_mono

end PNP.Concrete.NormalizerBlocks
