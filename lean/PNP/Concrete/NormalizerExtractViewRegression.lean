import PNP.Concrete.NormalizerExtractView

namespace PNP.Concrete.NormalizerBlocks
open Extraction
example : view (answer none) = none := by decide
example : view (answer (some ((⟨true, 2⟩, none), [⟨false, 1⟩]))) =
    some ((⟨true, 2⟩, none), SearchVertices.encodeVertices [⟨false, 1⟩]) := by decide
example : view (answer (some ((⟨false, 7⟩, some ⟨true, 3⟩), [⟨false, 2⟩]))) =
    some ((⟨false, 7⟩, some ⟨true, 3⟩), SearchVertices.encodeVertices [⟨false, 2⟩]) := by decide

#print axioms Extraction.readParent_canonical
#print axioms Extraction.view_answer
#print axioms Extraction.selection_matching
#print axioms Extraction.whole_outcome

end PNP.Concrete.NormalizerBlocks
