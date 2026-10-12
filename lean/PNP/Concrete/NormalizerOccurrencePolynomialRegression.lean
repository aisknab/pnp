import PNP.Concrete.NormalizerOccurrencePolynomial

namespace PNP.Concrete.NormalizerBlocks

open BitRegister

example (input : BitString) :
    Exec Occurrence.block (Occurrence.initialRegisters input).store
      (Occurrence.sourceSteps input) (Occurrence.result input).state.store := Occurrence.block_exec input
example (input : BitString) :
    BitRegister.run Occurrence.program (Occurrence.sourceSteps input + 1)
      (BitRegister.initial Occurrence.program input) = ⟨.accepted, (Occurrence.result input).state.store⟩ :=
  Occurrence.closed_run input
example (input : BitString) :
    Occurrence.sourceSteps input + 1 ≤ 16 * input.length + 22 := Occurrence.sourceSteps_bound input
example (input : BitString) :
    Occurrence.polynomial.output input = (Occurrence.result input).state.output := Occurrence.polynomial_output input
example : Occurrence.polynomial.output [] = [false] := by rw [Occurrence.polynomial_output]; rfl
example : Occurrence.polynomial.output (Occurrence.encodeQuery 0 [⟨false, 0⟩, ⟨true, 0⟩]) = [true, false] := by
  rw [Occurrence.polynomial_output]
  rfl
example : Occurrence.polynomial.output (Occurrence.encodeQuery 2 [⟨false, 0⟩, ⟨true, 2⟩]) = [true, true] := by
  rw [Occurrence.polynomial_output]
  rfl
example : Occurrence.polynomial.output (Occurrence.encodeQuery 3 [⟨true, 1⟩, ⟨false, 2⟩]) = [false] := by
  rw [Occurrence.polynomial_output]
  rfl
example : Occurrence.polynomial.output [true, true, true] = [false] := by
  rw [Occurrence.polynomial_output]
  rfl

#print axioms Occurrence.block_exec
#print axioms Occurrence.initial_registers
#print axioms Occurrence.closed_run
#print axioms Occurrence.sourceSteps_bound
#print axioms Occurrence.padded_run
#print axioms Occurrence.acceptsWithin
#print axioms Occurrence.polynomial
#print axioms Occurrence.polynomial_program
#print axioms Occurrence.polynomial_output
#print axioms Occurrence.polynomial_accepts
#print axioms Occurrence.polynomial_output_length

end PNP.Concrete.NormalizerBlocks
