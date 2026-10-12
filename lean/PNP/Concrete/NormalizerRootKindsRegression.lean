import PNP.Concrete.NormalizerRootKinds

namespace PNP.Concrete.NormalizerBlocks

example (vertex : CNFLiteral) (entries : MatchingTable.Entries) :
    RootKinds.polynomial.output (RootKinds.encode vertex entries) = [RootKinds.value vertex entries] :=
  RootKinds.polynomial_canonical vertex entries
example (input : BitString) :
    RootKinds.sourceSteps input + 1 ≤ 339 * input.length + 625 := RootKinds.sourceSteps_bound input
example : RootKinds.polynomial.output (RootKinds.encode ⟨true, 1⟩ [some 2, none]) = [true] := by
  rw [RootKinds.polynomial_canonical]
  rfl
example : RootKinds.polynomial.output (RootKinds.encode ⟨true, 0⟩ [some 2, none]) = [false] := by
  rw [RootKinds.polynomial_canonical]
  rfl
example : RootKinds.polynomial.output (RootKinds.encode ⟨false, 1⟩ [some 2, none]) = [false] := by
  rw [RootKinds.polynomial_canonical]
  rfl
example : RootKinds.polynomial.output (RootKinds.encode ⟨true, 4⟩ []) = [true] := by
  rw [RootKinds.polynomial_canonical]
  rfl
example : RootKinds.polynomial.output [] = [false] := by
  rw [RootKinds.polynomial_output]
  rfl
example : RootKinds.polynomial.output [true] = [true] := by
  rw [RootKinds.polynomial_output]
  rfl

#print axioms RootKinds.block_exec
#print axioms RootKinds.sourceSteps_bound
#print axioms RootKinds.closed_run
#print axioms RootKinds.padded_run
#print axioms RootKinds.polynomial_program
#print axioms RootKinds.polynomial_output
#print axioms RootKinds.polynomial_accepts
#print axioms RootKinds.polynomial_output_length
#print axioms RootKinds.polynomial_canonical
#print axioms RootKinds.machine_output
#print axioms RootKinds.machine_canonical

end PNP.Concrete.NormalizerBlocks
