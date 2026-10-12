import PNP.Concrete.NormalizerEdgePolynomial

namespace PNP.Concrete.NormalizerBlocks

example (first second : CNFLiteral) (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries) :
    EdgeKinds.polynomial.output (EdgeKinds.encode first second clauses entries) = [EdgeKinds.value first second clauses entries] :=
  EdgeKinds.polynomial_canonical first second clauses entries
example (input : BitString) :
    EdgeKinds.sourceSteps input + 1 ≤ 817 * input.length + 1173 := EdgeKinds.sourceSteps_bound input
example : EdgeKinds.polynomial.output (EdgeKinds.encode ⟨true, 0⟩ ⟨false, 2⟩ [[⟨false, 2⟩]] [none]) = [true] := by
  rw [EdgeKinds.polynomial_canonical]
  rfl
example : EdgeKinds.polynomial.output (EdgeKinds.encode ⟨true, 0⟩ ⟨false, 2⟩ [[⟨false, 2⟩]] [some 2]) = [false] := by
  rw [EdgeKinds.polynomial_canonical]
  rfl
example : EdgeKinds.polynomial.output (EdgeKinds.encode ⟨false, 2⟩ ⟨true, 0⟩ [[]] [some 2]) = [true] := by
  rw [EdgeKinds.polynomial_canonical]
  rfl
example : EdgeKinds.polynomial.output (EdgeKinds.encode ⟨false, 1⟩ ⟨true, 0⟩ [[⟨true, 1⟩]] [some 2]) = [false] := by
  rw [EdgeKinds.polynomial_canonical]
  rfl
example : EdgeKinds.polynomial.output (EdgeKinds.encode ⟨true, 0⟩ ⟨true, 0⟩ [[⟨true, 0⟩]] [none]) = [false] := by
  rw [EdgeKinds.polynomial_canonical]
  rfl
example : EdgeKinds.polynomial.output (EdgeKinds.encode ⟨false, 0⟩ ⟨false, 0⟩ [[⟨true, 0⟩]] [some 0]) = [false] := by
  rw [EdgeKinds.polynomial_canonical]
  rfl
example : EdgeKinds.polynomial.output [] = [false] := by
  rw [EdgeKinds.polynomial_output]
  rfl
example : EdgeKinds.polynomial.output [true] = [false] := by
  rw [EdgeKinds.polynomial_output]
  rfl

#print axioms EdgeKinds.block_exec
#print axioms EdgeKinds.closed_run
#print axioms EdgeKinds.sourceSteps_bound
#print axioms EdgeKinds.padded_run
#print axioms EdgeKinds.polynomial_program
#print axioms EdgeKinds.polynomial_output
#print axioms EdgeKinds.polynomial_accepts
#print axioms EdgeKinds.polynomial_output_length
#print axioms EdgeKinds.polynomial_canonical
#print axioms EdgeKinds.machine_output
#print axioms EdgeKinds.machine_canonical

end PNP.Concrete.NormalizerBlocks
