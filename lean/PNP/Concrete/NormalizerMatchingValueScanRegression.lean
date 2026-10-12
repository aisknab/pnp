import PNP.Concrete.NormalizerMatchingValueScan

namespace PNP.Concrete.NormalizerBlocks

example (input : BitString) (r : Occurrence.Registers) :
    Exec MatchingValue.loop ({r with input := input, active := [true]}).store
      (MatchingValue.scan input r).fuel (MatchingValue.scan input r).state.store := MatchingValue.scan_exec input r
example (input : BitString) (r : Occurrence.Registers) :
    (MatchingValue.scan input r).fuel ≤ 3 * input.length + 6 := MatchingValue.scan_fuel_bound input r
example (input : BitString) (r : Occurrence.Registers) :
    (MatchingValue.scan input r).state.active = [] := MatchingValue.scan_stopped input r
example (count : Nat) (tail : BitString) (r : Occurrence.Registers) :
    (MatchingValue.scan (List.replicate (2 * count) true ++ false :: tail) r).state.output =
      List.replicate count true ++ r.output := MatchingValue.scan_true_pairs count tail r

#print axioms MatchingValue.scan_exec
#print axioms MatchingValue.scan_fuel_bound
#print axioms MatchingValue.scan_stopped
#print axioms MatchingValue.scan_true_pairs

end PNP.Concrete.NormalizerBlocks
