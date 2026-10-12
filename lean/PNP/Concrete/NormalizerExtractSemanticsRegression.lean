import PNP.Concrete.NormalizerExtractSemantics

namespace PNP.Concrete.NormalizerBlocks
open Extraction
example : value [] [none, none] [] [⟨false, 3⟩, ⟨true, 1⟩, ⟨true, 0⟩] =
    some ((⟨true, 1⟩, none), [⟨false, 3⟩, ⟨true, 0⟩]) := by decide
example : value [[⟨true, 2⟩]] [none] [(⟨true, 0⟩, none)] [⟨true, 0⟩, ⟨false, 2⟩] =
    some ((⟨false, 2⟩, some ⟨true, 0⟩), [⟨true, 0⟩]) := by decide
example : value [] [none] [(⟨true, 0⟩, none)] [⟨true, 0⟩, ⟨false, 2⟩] = none := by decide

#print axioms Extraction.retain_nil
#print axioms Extraction.retain_cons
#print axioms Extraction.canonical_active
#print axioms Extraction.scan_canonical
#print axioms Extraction.whole_canonical

end PNP.Concrete.NormalizerBlocks
