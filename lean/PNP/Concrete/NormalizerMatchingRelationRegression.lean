import PNP.Concrete.NormalizerMatchingRelation

namespace PNP.Concrete.NormalizerBlocks

example (value index : Nat) (entries : MatchingTable.Entries) :
    MatchingRelation.polynomial.output (MatchingRelation.encodeQuery value index entries) =
      [MatchingTable.read entries index == some value] := MatchingRelation.polynomial_canonical value index entries
example (input : BitString) :
    boundedDecide MatchingRelation.rawRefinement.machine
      (MatchingRelation.rawRefinement.timeBound.eval (BitString.size input)) input ≠ .timeout :=
  MatchingRelation.machine_halts input
example : MatchingRelation.polynomial.output (MatchingRelation.encodeQuery 5 1 [some 2, some 5]) = [true] := by
  rw [MatchingRelation.polynomial_canonical]
  rfl
example : MatchingRelation.polynomial.output (MatchingRelation.encodeQuery 2 1 [some 2, some 5]) = [false] := by
  rw [MatchingRelation.polynomial_canonical]
  rfl
example : MatchingRelation.polynomial.output (MatchingRelation.encodeQuery 0 0 [none, some 0]) = [false] := by
  rw [MatchingRelation.polynomial_canonical]
  rfl

#print axioms MatchingRelation.entry_matches
#print axioms MatchingRelation.polynomial_program
#print axioms MatchingRelation.polynomial_output
#print axioms MatchingRelation.polynomial_canonical
#print axioms MatchingRelation.machine_output
#print axioms MatchingRelation.machine_canonical
#print axioms MatchingRelation.machine_halts
#print axioms MatchingRelation.machine_output_size

end PNP.Concrete.NormalizerBlocks
