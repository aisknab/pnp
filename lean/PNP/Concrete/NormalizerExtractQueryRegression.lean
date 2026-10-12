import PNP.Concrete.NormalizerExtractQuery

namespace PNP.Concrete.NormalizerBlocks
open Extraction

def extractionQueryFixture (vertex : CNFLiteral) : State :=
  ⟨⟨ParentQuery.loaded (ParentQuery.encode vertex [] [none] []), []⟩, [true, false], [], [], [true], []⟩
example : (queried (extractionQueryFixture ⟨true, 0⟩)).parent.output = [true, false] := by decide
example : (queried (extractionQueryFixture ⟨false, 0⟩)).parent.output = [false] := by decide
example : (appended (extractionQueryFixture ⟨false, 2⟩)).skipped =
    (UnseenData.entry ⟨false, 2⟩).reverse := by decide

#print axioms ParentQuery.phase_preserves
#print axioms Eligibility.phase_preserves
#print axioms Extraction.query_exec
#print axioms Extraction.query_fields
#print axioms Extraction.query_canonical
#print axioms Extraction.emitTagged_exec
#print axioms Extraction.appendSkipped_exec
#print axioms Extraction.append_fields
#print axioms Extraction.append_canonical

end PNP.Concrete.NormalizerBlocks
