import PNP.Concrete.NormalizerOwnerCanonical

namespace PNP.Concrete.NormalizerBlocks

open BitRegister

example (target : Nat) (entries : MatchingTable.Entries) :
    TableOwner.polynomial.output (TableOwner.encodeQuery target entries) =
      TableOwner.answer (TableOwner.owner entries target) := TableOwner.polynomial_canonical target entries
example (target : Nat) (entries : MatchingTable.Entries) :
    machineOutput (CompilerIO.rawMachine TableOwner.program)
      ((CompilerIO.runtimePolynomial 9 TableOwner.sourceFuel).eval (TableOwner.encodeQuery target entries).length)
      (TableOwner.encodeQuery target entries) = TableOwner.answer (TableOwner.owner entries target) :=
  TableOwner.machine_canonical target entries
example (target : Nat) (rest : MatchingTable.Entries) :
    TableOwner.polynomial.output (TableOwner.encodeQuery target (some target :: rest)) = [true] :=
  TableOwner.first_entry target rest
example (target : Nat) : TableOwner.polynomial.output (TableOwner.encodeQuery target []) = [false] :=
  TableOwner.polynomial_canonical target []

#print axioms TableOwner.canonical_block_exec
#print axioms TableOwner.polynomial_canonical
#print axioms TableOwner.machine_canonical
#print axioms TableOwner.first_entry

end PNP.Concrete.NormalizerBlocks
