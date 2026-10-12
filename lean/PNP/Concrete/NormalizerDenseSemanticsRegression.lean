import PNP.Concrete.NormalizerDenseSemantics

namespace PNP.Concrete.NormalizerBlocks

example :
    DenseClauses.value [[⟨true,2⟩],[⟨false,7⟩,⟨true,3⟩],[]]
      [⟨false,7⟩,⟨false,2⟩] [⟨true,1⟩,⟨true,0⟩,⟨true,2⟩] =
      [[⟨false,0⟩],[⟨true,1⟩],[]] := rfl

example :
    DenseClauses.value [[⟨true,2⟩]] [⟨false,2⟩] [⟨true,3⟩,⟨true,0⟩,⟨true,0⟩] =
      [[],[⟨true,0⟩],[⟨true,0⟩]] := rfl

example (formula : List (List CNFLiteral)) (vertices selected : List CNFLiteral)
    (r : DenseClauses.State)
    (remaining : r.remaining = SearchVertices.encodeVertices selected)
    (variables : r.core.variables = SearchVertices.encodeVertices vertices)
    (original : r.formula = GraphQuery.clauseData formula) :
    (DenseClauses.whole r).state.core.buffer =
      (DenseClauses.prefixBits (DenseClauses.value formula vertices selected)).reverse ++ r.core.buffer :=
  DenseClauses.whole_buffer formula vertices selected r remaining variables original

#print axioms DenseClauses.stepped_cons
#print axioms DenseClauses.step_canonical
#print axioms DenseClauses.remaining_nonempty
#print axioms DenseClauses.scan_buffer
#print axioms DenseClauses.whole_buffer
#print axioms DenseClauses.prefix_data

end PNP.Concrete.NormalizerBlocks
