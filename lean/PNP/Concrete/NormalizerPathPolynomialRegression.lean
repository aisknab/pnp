import PNP.Concrete.NormalizerPathPolynomial
namespace PNP.Concrete.NormalizerBlocks
example : (TracePath.result (TracePath.encode ⟨false, 1⟩ [(⟨false, 1⟩, some ⟨true, 0⟩), (⟨true, 0⟩, none)])).registers.output = PathData.answer (some [⟨false, 1⟩, ⟨true, 0⟩]) := by decide
example : (TracePath.result (TracePath.encode ⟨false, 1⟩ [(⟨true, 0⟩, none), (⟨false, 1⟩, some ⟨true, 0⟩)])).registers.output = PathData.answer none := by decide
example : (TracePath.result [true, true, true]).registers.output = [false] := by decide
example (target : CNFLiteral) (trace : List TraceData.Row) :
    TracePath.polynomial.output (TracePath.encode target trace) = PathData.answer (TracePath.value trace target) :=
  TracePath.polynomial_canonical target trace
#print axioms TracePath.block_exec
#print axioms TracePath.closed_run
#print axioms TracePath.loaded_bounded
#print axioms TracePath.sourceSteps_bound
#print axioms TracePath.padded_run
#print axioms TracePath.acceptsWithin
#print axioms TracePath.polynomial_program
#print axioms TracePath.polynomial_output
#print axioms TracePath.polynomial_accepts
#print axioms TracePath.polynomial_output_length
#print axioms TracePath.polynomial_canonical
#print axioms TracePath.machine_canonical
end PNP.Concrete.NormalizerBlocks
