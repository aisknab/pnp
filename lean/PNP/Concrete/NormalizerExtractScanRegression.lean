import PNP.Concrete.NormalizerExtractScan

namespace PNP.Concrete.NormalizerBlocks
open Extraction
def extractionScanFixture (vertices : List CNFLiteral) : State :=
  ⟨⟨ParentQuery.loaded (ParentQuery.encode ⟨false, 0⟩ [] [none] []), []⟩,
    SearchVertices.encodeVertices vertices, [], [], [true], []⟩
example : (whole (extractionScanFixture [])).state.active = [] := by decide
example : (whole (extractionScanFixture [⟨false, 2⟩, ⟨true, 0⟩, ⟨false, 7⟩])).state.parent.targetIndex = [] := by decide
example : (whole (extractionScanFixture [⟨false, 2⟩, ⟨true, 0⟩, ⟨false, 7⟩])).state.pending =
    SearchVertices.encodeVertices [⟨false, 7⟩] := by decide
example : (whole (extractionScanFixture [⟨false, 2⟩, ⟨false, 7⟩])).state.parent.output = [false] := by decide
example : (whole {extractionScanFixture [] with pending := [false, true, true]}).state.active = [] := by decide

#print axioms Extraction.scan_empty
#print axioms Extraction.scan_step
#print axioms Extraction.scan_exec
#print axioms Extraction.scan_fuel_bound
#print axioms Extraction.scan_stopped
#print axioms Extraction.scan_preserves
#print axioms Extraction.whole_exec
#print axioms Extraction.whole_fuel_bound
#print axioms Extraction.whole_stopped

end PNP.Concrete.NormalizerBlocks
