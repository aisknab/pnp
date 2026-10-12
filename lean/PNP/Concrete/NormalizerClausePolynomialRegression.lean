import PNP.Concrete.NormalizerClausePolynomial

namespace PNP.Concrete.NormalizerBlocks

open BitRegister

example (input : BitString) :
    BitRegister.run ClauseQuery.program (ClauseQuery.sourceSteps input + 1)
      (BitRegister.initial ClauseQuery.program input) = ⟨.accepted, (ClauseQuery.result input).store⟩ :=
  ClauseQuery.closed_run input
example (input : BitString) : ClauseQuery.sourceSteps input + 1 ≤ 84 * input.length + 148 :=
  ClauseQuery.sourceSteps_bound input
example (input : BitString) : ClauseQuery.polynomial.output input = (ClauseQuery.result input).output :=
  ClauseQuery.polynomial_output input
example : ClauseQuery.polynomial.output (ClauseQuery.encodeQuery 2 1 [[], [⟨true, 2⟩, ⟨false, 2⟩]]) =
    Occurrence.encodeQuery 2 [⟨true, 2⟩, ⟨false, 2⟩] := by rw [ClauseQuery.polynomial_output]; rfl
example : ClauseQuery.polynomial.output (ClauseQuery.encodeQuery 3 0 [[], [⟨true, 2⟩]]) =
    Occurrence.encodeQuery 3 [] := by rw [ClauseQuery.polynomial_output]; rfl
example : ClauseQuery.polynomial.output (ClauseQuery.encodeQuery 3 4 [[], [⟨true, 2⟩]]) =
    Occurrence.encodeQuery 3 [] := by rw [ClauseQuery.polynomial_output]; rfl
example : ClauseQuery.polynomial.output [] = [false, true, false] := by rw [ClauseQuery.polynomial_output]; rfl

#print axioms ClauseQuery.save_exec
#print axioms ClauseQuery.prepare_exec
#print axioms ClauseQuery.front_exec
#print axioms ClauseQuery.frontFuel_bound
#print axioms ClauseQuery.block_exec
#print axioms ClauseQuery.initial_registers
#print axioms ClauseQuery.closed_run
#print axioms ClauseQuery.sourceSteps_bound
#print axioms ClauseQuery.padded_run
#print axioms ClauseQuery.acceptsWithin
#print axioms ClauseQuery.polynomial
#print axioms ClauseQuery.polynomial_program
#print axioms ClauseQuery.polynomial_output
#print axioms ClauseQuery.polynomial_accepts
#print axioms ClauseQuery.polynomial_output_length

end PNP.Concrete.NormalizerBlocks
