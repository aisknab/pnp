import PNP.Concrete.NormalizerMatchingRawInvariant
namespace PNP.Concrete.NormalizerBlocks
example (input : BitString) :
    MatchingDriver.Within (6 * input.length + 6) (MatchingDriver.initialized input) :=
  MatchingDriver.initialized_within input
example (bound : Nat) (r : MatchingDriver.State) (data : MatchingDriver.Within bound r) :
    MatchingDriver.Within bound (MatchingDriver.whole r).state := MatchingDriver.whole_within bound r data
#print axioms MatchingDriver.Within.table_bytes
#print axioms MatchingDriver.body_table_within
#print axioms MatchingDriver.Within.body
#print axioms MatchingDriver.initialized_within
#print axioms MatchingDriver.scan_within
#print axioms MatchingDriver.whole_within
#print axioms MatchingDriver.result_table_bound
end PNP.Concrete.NormalizerBlocks
