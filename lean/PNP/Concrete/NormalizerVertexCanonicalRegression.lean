import PNP.Concrete.NormalizerVertexCanonical

namespace PNP.Concrete.NormalizerBlocks

example (clauses variables : Nat) (suffix : BitString) :
    SearchVertices.polynomial.output (SearchVertices.encodeCounts clauses variables suffix) =
      SearchVertices.encodeVertices (SearchVertices.vertices clauses variables) :=
  SearchVertices.polynomial_canonical clauses variables suffix
example (clauses variables : Nat) (suffix : BitString) :
    machineOutput (BitRegister.CompilerIO.rawMachine SearchVertices.program)
      ((BitRegister.CompilerIO.runtimePolynomial 9 SearchVertices.sourceFuel).eval
        (SearchVertices.encodeCounts clauses variables suffix).length)
      (SearchVertices.encodeCounts clauses variables suffix) =
        SearchVertices.encodeVertices (SearchVertices.vertices clauses variables) :=
  SearchVertices.machine_canonical clauses variables suffix
example (suffix : BitString) :
    SearchVertices.polynomial.output (SearchVertices.encodeCounts 0 0 suffix) = [true,false] := by
  rw [SearchVertices.polynomial_canonical]
  rfl
example (suffix : BitString) :
    SearchVertices.polynomial.output (SearchVertices.encodeCounts 2 3 suffix) =
      SearchVertices.encodeVertices [⟨true,0⟩,⟨true,1⟩,⟨false,0⟩,⟨false,1⟩,⟨false,2⟩] := by
  rw [SearchVertices.polynomial_canonical]
  rfl
example (clauses variables : Nat) : (SearchVertices.vertices clauses variables).length = clauses + variables :=
  SearchVertices.vertices_length clauses variables

#print axioms SearchVertices.clauseList_append
#print axioms SearchVertices.encoded_vertices
#print axioms SearchVertices.front_canonical_excess
#print axioms SearchVertices.polynomial_canonical
#print axioms SearchVertices.machine_canonical
#print axioms SearchVertices.rangeData_finRange
#print axioms SearchVertices.rangeData_length
#print axioms SearchVertices.vertices_length

end PNP.Concrete.NormalizerBlocks
