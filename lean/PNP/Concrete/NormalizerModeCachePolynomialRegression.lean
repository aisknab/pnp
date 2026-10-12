import PNP.Concrete.NormalizerModeCachePolynomial

namespace PNP.Concrete.NormalizerBlocks

example (input : BitString) : Exec ModeCacheDriver.block (CutDriver.initial input).store
    (ModeCacheDriver.sourceSteps input) (ModeCacheDriver.result input).store := ModeCacheDriver.block_exec input
example (input : BitString) : ModeCacheDriver.owners (ModeCacheDriver.result input) =
    (OwnerCacheDriver.result input).registers.output := ModeCacheDriver.result_owners input
example (width : Nat) (formula : List (List CNFLiteral)) :
    ModeCacheDriver.polynomial.output (MatchingDriver.encode width formula) =
      MatchingTable.encode (ModeCacheDriver.modeValues width formula) :=
  ModeCacheDriver.polynomial_canonical width formula

#print axioms ModeCacheDriver.block_exec
#print axioms ModeCacheDriver.closed_run
#print axioms ModeCacheDriver.deriveSteps_input_bound
#print axioms ModeCacheDriver.sourceSteps_bound
#print axioms ModeCacheDriver.result_bounded
#print axioms ModeCacheDriver.padded_run
#print axioms ModeCacheDriver.acceptsWithin
#print axioms ModeCacheDriver.polynomial_program
#print axioms ModeCacheDriver.polynomial_output
#print axioms ModeCacheDriver.polynomial_accepts
#print axioms ModeCacheDriver.polynomial_output_length
#print axioms ModeCacheDriver.result_data
#print axioms ModeCacheDriver.result_owners
#print axioms ModeCacheDriver.result_literals
#print axioms ModeCacheDriver.result_owners_canonical
#print axioms ModeCacheDriver.result_literals_canonical
#print axioms ModeCacheDriver.result_canonical
#print axioms ModeCacheDriver.polynomial_canonical
#print axioms ModeCacheDriver.machine_canonical

end PNP.Concrete.NormalizerBlocks
