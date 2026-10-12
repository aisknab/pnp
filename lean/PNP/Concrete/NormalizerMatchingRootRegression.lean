import PNP.Concrete.NormalizerMatchingRoot

namespace PNP.Concrete.NormalizerBlocks

example (index : Nat) (entries : MatchingTable.Entries) :
    MatchingRoot.polynomial.output (MatchingRead.encodeQuery index entries) =
      [(MatchingTable.read entries index).isNone] := MatchingRoot.polynomial_canonical index entries
example (input : BitString) :
    boundedDecide MatchingRoot.rawRefinement.machine
      (MatchingRoot.rawRefinement.timeBound.eval (BitString.size input)) input ≠ .timeout :=
  MatchingRoot.machine_halts input
example : MatchingRoot.polynomial.output (MatchingRead.encodeQuery 1 [some 0, none]) = [true] := by
  rw [MatchingRoot.polynomial_canonical]
  rfl
example : MatchingRoot.polynomial.output (MatchingRead.encodeQuery 0 [some 0, none]) = [false] := by
  rw [MatchingRoot.polynomial_canonical]
  rfl

#print axioms MatchingRoot.polynomial_program
#print axioms MatchingRoot.polynomial_output
#print axioms MatchingRoot.polynomial_canonical
#print axioms MatchingRoot.machine_output
#print axioms MatchingRoot.machine_canonical
#print axioms MatchingRoot.machine_halts
#print axioms MatchingRoot.machine_output_size

end PNP.Concrete.NormalizerBlocks
