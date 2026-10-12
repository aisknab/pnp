import PNP.Concrete.NormalizerCutSelectionPolynomial
namespace PNP.Concrete.NormalizerBlocks
example (tag : Bool) (trace : List TraceData.Row) :
    (CutSelection.polynomial tag).output (CutSelection.encode 0 trace) = [true,false] := by
  rw [CutSelection.polynomial_canonical]
  rfl
example (count : Nat) :
    (CutSelection.polynomial false).output (CutSelection.encode count []) =
      SearchVertices.encodeVertices (CutSelection.selected false [] count 0) :=
  CutSelection.polynomial_canonical false count []
example (tag : Bool) (input : BitString) :
    ((CutSelection.polynomial tag).output input).length ≤ input.length + CutSelection.sourceFuel.eval input.length :=
  CutSelection.polynomial_output_length tag input
#print axioms CutSelection.finish_exec
#print axioms CutSelection.block_exec
#print axioms CutSelection.closed_run
#print axioms CutSelection.sourceSteps_bound
#print axioms CutSelection.padded_run
#print axioms CutSelection.acceptsWithin
#print axioms CutSelection.polynomial_program
#print axioms CutSelection.polynomial_output
#print axioms CutSelection.polynomial_accepts
#print axioms CutSelection.polynomial_output_length
#print axioms CutSelection.result_canonical
#print axioms CutSelection.polynomial_canonical
#print axioms CutSelection.machine_output
#print axioms CutSelection.machine_canonical
end PNP.Concrete.NormalizerBlocks
