import PNP.Concrete.NormalizerPreparedPolynomial

namespace PNP.Concrete.NormalizerBlocks

example (input : BitString) :
    (PreparedDriver.result input).store.Bounded (PreparedDriver.resultSize.eval input.length) :=
  PreparedDriver.result_bounded input

example (width : Nat) (formula : List (List CNFLiteral)) :
    CutDriver.Canonical width formula (PreparedDriver.result (MatchingDriver.encode width formula)) :=
  PreparedDriver.result_data width formula

example (width : Nat) (formula : List (List CNFLiteral)) :
    PreparedDriver.polynomial.output (MatchingDriver.encode width formula) =
      GraphQuery.clauseData (PreparedDriver.denseValue width formula) :=
  PreparedDriver.polynomial_canonical width formula

#print axioms PreparedDriver.block_exec
#print axioms PreparedDriver.initial_registers
#print axioms PreparedDriver.closed_run
#print axioms PreparedDriver.sourceSteps_bound
#print axioms PreparedDriver.result_bounded
#print axioms PreparedDriver.padded_run
#print axioms PreparedDriver.acceptsWithin
#print axioms PreparedDriver.polynomial_program
#print axioms PreparedDriver.polynomial_output
#print axioms PreparedDriver.polynomial_accepts
#print axioms PreparedDriver.polynomial_output_length
#print axioms PreparedDriver.result_data
#print axioms PreparedDriver.result_canonical
#print axioms PreparedDriver.polynomial_canonical
#print axioms PreparedDriver.machine_canonical

end PNP.Concrete.NormalizerBlocks
