import PNP.Concrete.NormalizerTableInitializationCanonical

namespace PNP.Concrete.NormalizerBlocks

example (count : Nat) (suffix : BitString) :
    TableInit.polynomial.output (TableInit.encodeCount count suffix) =
      MatchingTable.encode (List.replicate count none) := TableInit.polynomial_canonical count suffix
example (count : Nat) (suffix : BitString) :
    machineOutput (BitRegister.CompilerIO.rawMachine TableInit.program)
      ((BitRegister.CompilerIO.runtimePolynomial 9 TableInit.sourceFuel).eval
        (TableInit.encodeCount count suffix).length)
      (TableInit.encodeCount count suffix) = MatchingTable.encode (List.replicate count none) :=
  TableInit.machine_canonical count suffix
example : TableInit.polynomial.output (TableInit.encodeCount 0 []) = MatchingTable.encode [] :=
  TableInit.polynomial_canonical 0 []
example : TableInit.polynomial.output (TableInit.encodeCount 3 [true, false, true]) =
    MatchingTable.encode [none, none, none] := TableInit.polynomial_canonical 3 _
example (count : Nat) (first second : BitString) :
    TableInit.polynomial.output (TableInit.encodeCount count first) =
      TableInit.polynomial.output (TableInit.encodeCount count second) := by
  rw [TableInit.polynomial_canonical, TableInit.polynomial_canonical]

#print axioms TableInit.canonical_block_exec
#print axioms TableInit.canonical_bytes
#print axioms TableInit.polynomial_canonical
#print axioms TableInit.machine_canonical

end PNP.Concrete.NormalizerBlocks
