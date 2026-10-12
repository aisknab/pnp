import PNP.Concrete.NormalizerCutPolynomial
namespace PNP.Concrete.NormalizerBlocks
example (width : Nat) (formula : List (List CNFLiteral)) :
    CutDriver.polynomial.output (MatchingDriver.encode width formula) =
      CutDriver.canonicalPacket width formula := CutDriver.polynomial_canonical width formula
example (input : BitString) :
    (CutDriver.polynomial.output input).length ≤ input.length + CutDriver.sourceFuel.eval input.length :=
  CutDriver.polynomial_output_length input
example (width : Nat) (formula : List (List CNFLiteral)) :
    (CutDriver.result (MatchingDriver.encode width formula)).core.width = List.replicate width true :=
  (CutDriver.result_data width formula).widthRead
#print axioms CutDriver.block_exec
#print axioms CutDriver.closed_run
#print axioms CutDriver.sourceSteps_bound
#print axioms CutDriver.padded_run
#print axioms CutDriver.acceptsWithin
#print axioms CutDriver.polynomial_program
#print axioms CutDriver.polynomial_output
#print axioms CutDriver.polynomial_accepts
#print axioms CutDriver.polynomial_output_length
#print axioms CutDriver.result_data
#print axioms CutDriver.result_canonical
#print axioms CutDriver.polynomial_canonical
#print axioms CutDriver.machine_output
#print axioms CutDriver.machine_canonical
end PNP.Concrete.NormalizerBlocks
