import PNP.Concrete.NormalizerMatchingValueOperations

namespace PNP.Concrete.NormalizerBlocks

example (r : Occurrence.Registers) :
    Exec MatchingValue.pair ({r with input := []}).store 2 ({r with input := [], active := []}).store :=
  MatchingValue.pair_empty_exec r
example (r : Occurrence.Registers) (rest : BitString) :
    Exec MatchingValue.pair ({r with input := false :: rest}).store 2
      ({r with input := false :: rest, active := []}).store := MatchingValue.pair_false_exec r rest
example (r : Occurrence.Registers) (rest : BitString) :
    Exec MatchingValue.pair ({r with input := true :: false :: rest}).store 4
      ({r with input := false :: rest, active := []}).store := MatchingValue.pair_true_false_exec r rest
example (r : Occurrence.Registers) (rest : BitString) :
    Exec MatchingValue.pair ({r with input := true :: true :: rest}).store 5
      ({r with input := rest, output := true :: r.output}).store := MatchingValue.pair_true_true_exec r rest

#print axioms MatchingValue.pair_empty_exec
#print axioms MatchingValue.pair_false_exec
#print axioms MatchingValue.pair_true_empty_exec
#print axioms MatchingValue.pair_true_false_exec
#print axioms MatchingValue.pair_true_true_exec

end PNP.Concrete.NormalizerBlocks
