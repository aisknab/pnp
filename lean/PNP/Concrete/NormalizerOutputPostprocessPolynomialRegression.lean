import PNP.Concrete.NormalizerOutputPostprocessPolynomial
namespace PNP.Concrete.NormalizerBlocks
example : OutputPostprocess.polynomial.output [] = [false,false,false] := by
  rw [OutputPostprocess.polynomial_output]
  exact OutputPostprocess.malformed_output [] rfl
example (rest : BitString) : OutputPostprocess.polynomial.output (false::rest) = [false,false,false] := by
  rw [OutputPostprocess.polynomial_output]
  exact OutputPostprocess.malformed_output (false::rest) rfl
example (input : BitString) :
    (OutputPostprocess.polynomial.output input).length ≤
      input.length+OutputPostprocess.sourceFuel.eval input.length :=
  OutputPostprocess.polynomial_output_length input
#print axioms OutputPostprocess.ready_bounded
#print axioms OutputPostprocess.checkerInput_length
#print axioms OutputPostprocess.checkSteps_bound
#print axioms OutputPostprocess.checked_bounded
#print axioms OutputPostprocess.dispatchSteps_bound
#print axioms OutputPostprocess.validSteps_bound
#print axioms OutputPostprocess.sourceSteps_bound
#print axioms OutputPostprocess.result_bounded
#print axioms OutputPostprocess.padded_run
#print axioms OutputPostprocess.polynomial_program
#print axioms OutputPostprocess.polynomial_output
#print axioms OutputPostprocess.polynomial_accepts
#print axioms OutputPostprocess.polynomial_output_length
#print axioms OutputPostprocess.machine_output
end PNP.Concrete.NormalizerBlocks
