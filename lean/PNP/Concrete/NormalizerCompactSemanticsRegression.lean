import PNP.Concrete.NormalizerCompactSemantics

namespace PNP.Concrete.NormalizerBlocks

example :
    CompactClause.value [⟨false,2⟩,⟨false,7⟩]
      [⟨true,7⟩,⟨false,3⟩,⟨false,2⟩,⟨false,7⟩] =
      [⟨true,1⟩,⟨false,0⟩,⟨false,1⟩] := rfl

example (vertices literals : List CNFLiteral) (r : CompactClause.State)
    (pending : r.pending = (Occurrence.encodeQuery 0 literals).tail)
    (variables : r.variables = SearchVertices.encodeVertices vertices) :
    (CompactClause.whole r).state.buffer =
      (CompactClause.bits (CompactClause.value vertices literals)).reverse ++ r.buffer := by
  apply CompactClause.whole_buffer vertices literals r
  · exact pending.trans (CompactClause.occurrence_data literals)
  · exact variables

example (r : CompactClause.State)
    (pending : r.pending = [true,false])
    (variables : r.variables = SearchVertices.encodeVertices []) :
    (CompactClause.whole r).state.buffer = r.buffer :=
  CompactClause.whole_buffer [] [] r pending variables

#print axioms CompactClause.bits_cons
#print axioms CompactClause.value_bits_cons
#print axioms CompactClause.scan_buffer
#print axioms CompactClause.whole_buffer
#print axioms CompactClause.occurrence_data

end PNP.Concrete.NormalizerBlocks
