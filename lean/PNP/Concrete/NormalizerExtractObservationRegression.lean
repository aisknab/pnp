import PNP.Concrete.NormalizerExtractObservation

namespace PNP.Concrete.NormalizerBlocks
open Extraction
def extractionObservationFixture (vertices : List CNFLiteral) : State :=
  ⟨⟨ParentQuery.loaded (ParentQuery.encode ⟨false, 0⟩ [] [none] []), []⟩,
    SearchVertices.encodeVertices vertices, [], [], [true], []⟩
example : observation (whole (extractionObservationFixture [⟨false, 2⟩, ⟨true, 0⟩, ⟨false, 7⟩])).state =
    answer (some ((⟨true, 0⟩, none), [⟨false, 2⟩, ⟨false, 7⟩])) := by decide
example : observation (whole (extractionObservationFixture [⟨false, 2⟩])).state = answer none := by decide
example : parentBytes (ParentQuery.answer (some (some ⟨false, 4⟩))) [true, false] =
    TraceData.predecessor (some ⟨false, 4⟩) [true, false] := by decide

#print axioms Extraction.parentBytes_canonical
#print axioms Extraction.observation_none
#print axioms Extraction.observation_some
#print axioms Extraction.query_after_read
#print axioms Extraction.body_cons
#print axioms Extraction.body_missing
#print axioms Extraction.body_found

end PNP.Concrete.NormalizerBlocks
