import PNP.Concrete.NormalizerOwnerCachePolynomial

namespace PNP.Concrete.NormalizerBlocks

example (input : BitString) :
    (OwnerCacheDriver.result input).store.Bounded (OwnerCacheDriver.resultSize.eval input.length) :=
  OwnerCacheDriver.result_bounded input

example (width : Nat) (formula : List (List CNFLiteral)) :
    CutDriver.Canonical width formula (OwnerCacheDriver.result (MatchingDriver.encode width formula)) :=
  OwnerCacheDriver.result_data width formula

example (width : Nat) (formula : List (List CNFLiteral)) :
    OwnerCacheDriver.polynomial.output (MatchingDriver.encode width formula) =
      MatchingTable.encode (OwnerCacheDriver.ownerValues width formula) :=
  OwnerCacheDriver.polynomial_canonical width formula

#print axioms OwnerCacheDriver.block_exec
#print axioms OwnerCacheDriver.initial_registers
#print axioms OwnerCacheDriver.closed_run
#print axioms OwnerCacheDriver.sourceSteps_bound
#print axioms OwnerCacheDriver.result_bounded
#print axioms OwnerCacheDriver.padded_run
#print axioms OwnerCacheDriver.acceptsWithin
#print axioms OwnerCacheDriver.polynomial_program
#print axioms OwnerCacheDriver.polynomial_output
#print axioms OwnerCacheDriver.polynomial_accepts
#print axioms OwnerCacheDriver.polynomial_output_length
#print axioms OwnerCacheDriver.result_literals
#print axioms OwnerCacheDriver.result_literals_canonical
#print axioms OwnerCacheDriver.result_data
#print axioms OwnerCacheDriver.result_canonical
#print axioms OwnerCacheDriver.polynomial_canonical
#print axioms OwnerCacheDriver.machine_canonical

end PNP.Concrete.NormalizerBlocks
