import PNP.Concrete.NormalizerOwnerVertices

namespace PNP.Concrete.NormalizerBlocks

example :
    TableOwner.polynomial.output
      (TableOwner.encodeVertexQuery 7 [⟨false,2⟩,⟨false,7⟩,⟨false,9⟩]) =
      [true,true] := by
  rw [TableOwner.vertices_polynomial_canonical]
  rfl

example :
    TableOwner.polynomial.output
      (TableOwner.encodeVertexQuery 7 [⟨true,2⟩,⟨false,7⟩,⟨true,7⟩]) =
      [true,true] := by
  rw [TableOwner.vertices_polynomial_canonical]
  rfl

example :
    TableOwner.polynomial.output
      (TableOwner.encodeVertexQuery 0 [⟨false,0⟩,⟨true,0⟩]) = [true] := by
  rw [TableOwner.vertices_polynomial_canonical]
  rfl

example :
    TableOwner.polynomial.output
      (TableOwner.encodeVertexQuery 7 [⟨false,2⟩,⟨true,6⟩,⟨false,9⟩]) = [false] := by
  rw [TableOwner.vertices_polynomial_canonical]
  rfl

example (target : Nat) :
    TableOwner.polynomial.output (TableOwner.encodeVertexQuery target []) = [false] := by
  rw [TableOwner.vertices_polynomial_canonical]
  rfl

example :
    (TableOwner.queryResult (TableOwner.prepared (List.replicate 7 true)
      (SearchVertices.encodeVertices [⟨false,9⟩,⟨true,7⟩]))).state.output = [true,true] := by
  rw [TableOwner.prepared_vertices]
  rfl

#print axioms TableOwner.tokenScan_tagged_entry
#print axioms TableOwner.tokenScan_vertices_correct
#print axioms TableOwner.prepared_vertices
#print axioms TableOwner.vertices_block_exec
#print axioms TableOwner.vertices_polynomial_canonical
#print axioms TableOwner.vertices_machine_canonical
#print axioms TableOwner.polynomial_accepts
#print axioms TableOwner.polynomial_output_length

end PNP.Concrete.NormalizerBlocks
