import PNP.Concrete.NormalizerMatchingRead

namespace PNP.Concrete.NormalizerBlocks

example (index : Nat) (entries : MatchingTable.Entries) :
    MatchingRead.polynomial.output (MatchingRead.encodeQuery index entries) =
      TableOwner.answer (MatchingTable.read entries index) := MatchingRead.polynomial_canonical index entries
example (input : BitString) :
    boundedDecide MatchingRead.rawRefinement.machine
      (MatchingRead.rawRefinement.timeBound.eval (BitString.size input)) input ≠ .timeout :=
  MatchingRead.machine_halts input
example : MatchingRead.polynomial.output (MatchingRead.encodeQuery 1 [some 7, none, some 2]) = [false] := by
  rw [MatchingRead.polynomial_canonical]
  rfl
example : MatchingRead.polynomial.output (MatchingRead.encodeQuery 2 [some 7, none, some 2]) = [true,true,true] := by
  rw [MatchingRead.polynomial_canonical]
  rfl
example : MatchingRead.polynomial.output (MatchingRead.encodeQuery 9 [some 7]) = [false] := by
  rw [MatchingRead.polynomial_canonical]
  rfl

#print axioms MatchingRead.polynomial_program
#print axioms MatchingRead.polynomial_output
#print axioms MatchingRead.polynomial_canonical
#print axioms MatchingRead.machine_output
#print axioms MatchingRead.machine_canonical
#print axioms MatchingRead.machine_halts
#print axioms MatchingRead.machine_output_size

end PNP.Concrete.NormalizerBlocks
