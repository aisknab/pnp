import PNP.Concrete.NormalizerCompactLiteral

namespace PNP.Concrete.NormalizerBlocks

example (r : CompactClause.State) (suffix : BitString)
    (pending : r.pending = NANDFrontend.literalBits false 7 ++ suffix)
    (variables : r.variables = SearchVertices.encodeVertices [⟨false,2⟩,⟨false,7⟩]) :
    (CompactClause.compacted r).buffer = (NANDFrontend.literalBits false 1).reverse ++ r.buffer := by
  exact CompactClause.compacted_buffer r ⟨false,7⟩ [⟨false,2⟩,⟨false,7⟩] suffix pending variables

example (r : CompactClause.State) (suffix : BitString)
    (pending : r.pending = NANDFrontend.literalBits true 4 ++ suffix)
    (variables : r.variables = SearchVertices.encodeVertices [⟨false,2⟩,⟨false,7⟩]) :
    (CompactClause.compacted r).buffer = r.buffer := by
  have checked := CompactClause.compacted_buffer r ⟨true,4⟩ [⟨false,2⟩,⟨false,7⟩] suffix pending variables
  exact checked

example (r : CompactClause.State) (suffix : BitString)
    (pending : r.pending = NANDFrontend.literalBits true 0 ++ suffix) :
    (CompactClause.compacted r).pending = suffix :=
  CompactClause.compacted_suffix r ⟨true,0⟩ suffix pending

#print axioms CompactClause.body_exec
#print axioms CompactClause.compacted_fields
#print axioms CompactClause.bodyFuel_bound
#print axioms CompactClause.compacted_buffer
#print axioms CompactClause.compacted_suffix

end PNP.Concrete.NormalizerBlocks
