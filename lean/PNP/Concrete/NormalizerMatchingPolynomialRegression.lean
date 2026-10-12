import PNP.Concrete.NormalizerMatchingPolynomial
namespace PNP.Concrete.NormalizerBlocks
example (input : BitString) : MatchingDriver.sourceSteps input + 1 ≤ MatchingDriver.sourceFuel.eval input.length :=
  MatchingDriver.sourceSteps_bound input
example (input : BitString) :
    boundedDecide (BitRegister.CompilerIO.rawMachine MatchingDriver.program)
      ((BitRegister.CompilerIO.runtimePolynomial 33 MatchingDriver.sourceFuel).eval input.length) input = .accept :=
  MatchingDriver.polynomial_accepts input
example (v : Nat) (cs : List (List CNFLiteral)) :
    MatchingDriver.polynomial.output (MatchingDriver.encode v cs) =
      MatchingTable.encode (MatchingLoop.fullTable v cs) := MatchingDriver.polynomial_canonical v cs
#print axioms MatchingDriver.scan_fuel_bound
#print axioms MatchingDriver.sourceSteps_bound
#print axioms MatchingDriver.padded_run
#print axioms MatchingDriver.acceptsWithin
#print axioms MatchingDriver.polynomial_program
#print axioms MatchingDriver.polynomial_output
#print axioms MatchingDriver.polynomial_accepts
#print axioms MatchingDriver.polynomial_output_length
#print axioms MatchingDriver.polynomial_table_bound
#print axioms MatchingDriver.polynomial_canonical
#print axioms MatchingDriver.machine_output
#print axioms MatchingDriver.machine_canonical
end PNP.Concrete.NormalizerBlocks
