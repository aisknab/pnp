import PNP.Concrete.NormalizerMatchingValueCanonical

namespace PNP.Concrete.NormalizerBlocks

example (value : Option Nat) :
    MatchingValue.polynomial.output (Occurrence.encodeQuery 0 (MatchingTable.entryClause value)) =
      TableOwner.answer value := MatchingValue.polynomial_canonical value
example (value : Option Nat) :
    machineOutput (BitRegister.CompilerIO.rawMachine MatchingValue.program)
      ((BitRegister.CompilerIO.runtimePolynomial 9 MatchingValue.sourceFuel).eval
        (Occurrence.encodeQuery 0 (MatchingTable.entryClause value)).length)
      (Occurrence.encodeQuery 0 (MatchingTable.entryClause value)) = TableOwner.answer value :=
  MatchingValue.machine_canonical value
example : MatchingValue.polynomial.output (Occurrence.encodeQuery 0 []) = [false] :=
  MatchingValue.polynomial_canonical none
example (value : Nat) :
    MatchingValue.polynomial.output (Occurrence.encodeQuery 0 [⟨true,value⟩]) =
      true :: List.replicate value true := MatchingValue.polynomial_canonical (some value)

#print axioms MatchingValue.present_encoding
#print axioms MatchingValue.polynomial_canonical
#print axioms MatchingValue.machine_canonical

end PNP.Concrete.NormalizerBlocks
