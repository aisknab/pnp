import PNP.Concrete.NormalizerTableCanonical

namespace PNP.Concrete.NormalizerBlocks

example (entries : MatchingTable.Entries) (index value : Nat) :
    TableWrite.polynomial.output (TableWrite.encodeWrite index value entries) =
      MatchingTable.encode (MatchingTable.write entries index value) := TableWrite.polynomial_canonical entries index value
example (entries : MatchingTable.Entries) (index value : Nat) :
    machineOutput (BitRegister.CompilerIO.rawMachine TableWrite.program)
      ((BitRegister.CompilerIO.runtimePolynomial 9 TableWrite.sourceFuel).eval
        (TableWrite.encodeWrite index value entries).length)
      (TableWrite.encodeWrite index value entries) =
        MatchingTable.encode (MatchingTable.write entries index value) := TableWrite.machine_canonical entries index value
example (entries : MatchingTable.Entries) (index first last : Nat) :
    TableWrite.polynomial.output (TableWrite.encodeWrite index last (MatchingTable.write entries index first)) =
      MatchingTable.encode (MatchingTable.write entries index last) := TableWrite.repeated_index_last_wins entries index first last
example : TableWrite.polynomial.output (TableWrite.encodeWrite 1 3 [none, some 4, none]) =
    MatchingTable.encode [none, some 3, none] := TableWrite.polynomial_canonical _ _ _
example : TableWrite.polynomial.output (TableWrite.encodeWrite 3 9 [none, some 4]) =
    MatchingTable.encode [none, some 4] := TableWrite.polynomial_canonical _ _ _
example : TableWrite.polynomial.output (TableWrite.encodeWrite 0 7 []) =
    MatchingTable.encode [] := TableWrite.polynomial_canonical _ _ _

#print axioms TableWrite.canonical_block_exec
#print axioms TableWrite.packed_canonical
#print axioms TableWrite.polynomial_canonical
#print axioms TableWrite.machine_canonical
#print axioms TableWrite.repeated_index_last_wins

end PNP.Concrete.NormalizerBlocks
