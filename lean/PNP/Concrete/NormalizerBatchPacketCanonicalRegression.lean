import PNP.Concrete.NormalizerBatchPacketCanonical

namespace PNP.Concrete.NormalizerBlocks

open BitRegister

example (data suffix : BitString) :
    (BatchPacket.loaded (TableInit.encodeCount data.length (data ++ suffix))).pending = suffix ∧
      (BatchPacket.loaded (TableInit.encodeCount data.length (data ++ suffix))).table = data :=
  BatchPacket.loaded_canonical data suffix
example (entries : MatchingTable.Entries) (updates : List (Nat × Nat)) :
    BatchPacket.polynomial.output (BatchPacket.encode entries updates) =
      MatchingTable.encode (MatchingTable.writeAll entries updates) :=
  BatchPacket.polynomial_canonical entries updates
example (entries : MatchingTable.Entries) (updates : List (Nat × Nat)) :
    machineOutput (CompilerIO.rawMachine BatchPacket.program)
      ((CompilerIO.runtimePolynomial 11 BatchPacket.sourceFuel).eval (BatchPacket.encode entries updates).length)
      (BatchPacket.encode entries updates) = MatchingTable.encode (MatchingTable.writeAll entries updates) :=
  BatchPacket.machine_canonical entries updates
example (entries : MatchingTable.Entries) :
    BatchPacket.polynomial.output (BatchPacket.encode entries []) = MatchingTable.encode entries :=
  BatchPacket.empty_updates_preserve entries
example (entries : MatchingTable.Entries) (index first last : Nat) :
    BatchPacket.polynomial.output (BatchPacket.encode entries [(index,first),(index,last)]) =
      MatchingTable.encode (MatchingTable.write entries index last) :=
  BatchPacket.repeated_index_last_wins entries index first last

#print axioms BatchPacket.header_canonical
#print axioms BatchPacket.taken_canonical
#print axioms BatchPacket.core_canonical
#print axioms BatchPacket.loaded_canonical
#print axioms BatchPacket.polynomial_canonical
#print axioms BatchPacket.machine_canonical
#print axioms BatchPacket.empty_updates_preserve
#print axioms BatchPacket.repeated_index_last_wins

end PNP.Concrete.NormalizerBlocks
