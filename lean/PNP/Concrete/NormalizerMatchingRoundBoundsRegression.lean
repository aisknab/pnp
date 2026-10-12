import PNP.Concrete.NormalizerMatchingRoundBounds
namespace PNP.Concrete.NormalizerBlocks
example (bound : Nat) (r : MatchingDriver.State) (data : MatchingDriver.Within bound r) :
    MatchingDriver.bodyFuel r ≤ MatchingDriver.roundPolynomial.eval bound :=
  MatchingDriver.bodyFuel_bound bound r data
example (input : BitString) :
    MatchingDriver.bodyFuel (MatchingDriver.initialized input) ≤
      MatchingDriver.roundPolynomial.eval (6 * input.length + 6) :=
  MatchingDriver.bodyFuel_bound _ _ (MatchingDriver.initialized_within input)
#print axioms MatchingDriver.search_input_bound
#print axioms MatchingDriver.searchSteps_bound
#print axioms MatchingDriver.search_output_bound
#print axioms MatchingDriver.route_tail_bound
#print axioms MatchingDriver.advanceFuel_bound
#print axioms MatchingDriver.bodyFuel_bound
end PNP.Concrete.NormalizerBlocks
