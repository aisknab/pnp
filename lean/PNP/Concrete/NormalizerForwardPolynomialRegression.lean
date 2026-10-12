import PNP.Concrete.NormalizerForwardPolynomial

namespace PNP.Concrete.NormalizerBlocks

example (target index : Nat) (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries) :
    ForwardEdge.polynomial.output (ForwardEdge.encode target index clauses entries) =
      [ForwardEdge.value target index clauses entries] :=
  ForwardEdge.polynomial_canonical target index clauses entries
example (input : BitString) :
    ForwardEdge.sourceSteps input + 1 ≤ 817 * input.length + 1164 := ForwardEdge.sourceSteps_bound input
example : ForwardEdge.polynomial.output (ForwardEdge.encode 1 0 [[⟨false, 1⟩]] [none]) = [true] := by
  rw [ForwardEdge.polynomial_canonical]
  rfl
example : ForwardEdge.polynomial.output (ForwardEdge.encode 1 0 [[⟨false, 1⟩]] [some 1]) = [false] := by
  rw [ForwardEdge.polynomial_canonical]
  rfl
example : ForwardEdge.polynomial.output (ForwardEdge.encode 1 0 [[⟨true, 0⟩]] [some 0]) = [false] := by
  rw [ForwardEdge.polynomial_canonical]
  rfl
example : ForwardEdge.polynomial.output (ForwardEdge.encode 1 3 [[⟨true, 1⟩]] []) = [false] := by
  rw [ForwardEdge.polynomial_canonical]
  rfl
example : ForwardEdge.polynomial.output (ForwardEdge.encode 0 0 [[⟨true, 0⟩, ⟨false, 0⟩]] []) = [true] := by
  rw [ForwardEdge.polynomial_canonical]
  rfl
example : ForwardEdge.polynomial.output [] = [false] := by
  rw [ForwardEdge.polynomial_output]
  rfl

#print axioms ForwardEdge.phase_exec
#print axioms ForwardEdge.phaseFuel_bound
#print axioms ForwardEdge.phase_output
#print axioms ForwardEdge.block_exec
#print axioms ForwardEdge.closed_run
#print axioms ForwardEdge.sourceSteps_bound
#print axioms ForwardEdge.padded_run
#print axioms ForwardEdge.polynomial_program
#print axioms ForwardEdge.polynomial_output
#print axioms ForwardEdge.polynomial_accepts
#print axioms ForwardEdge.polynomial_output_length
#print axioms ForwardEdge.polynomial_canonical
#print axioms ForwardEdge.machine_output
#print axioms ForwardEdge.machine_canonical

end PNP.Concrete.NormalizerBlocks
