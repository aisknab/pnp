import PNP.Concrete.NormalizerBatchCanonicalBody

namespace PNP.Concrete.NormalizerBlocks

example (index value : Nat) (rest : BitString) :
    TableWrite.prepared (TableBatch.encodePair index value rest) = TableBatch.decoded index value rest :=
  TableBatch.headers_canonical index value rest
example (entries : MatchingTable.Entries) (index value : Nat) :
    (TableWrite.packed (TableWrite.queryResult
      {TableWrite.writeInitial index value with input := MatchingTable.encode entries}).state).output =
        MatchingTable.encode (MatchingTable.write entries index value) := TableBatch.scan_pack_canonical entries index value
example (r : TableBatch.State) (entries : MatchingTable.Entries) (index value : Nat) (rest : BitString)
    (pending : r.pending = TableBatch.encodePair index value rest) (table : r.table = MatchingTable.encode entries) :
    (TableBatch.result r).pending = rest ∧
      (TableBatch.result r).table = MatchingTable.encode (MatchingTable.write entries index value) :=
  TableBatch.body_canonical r entries index value rest pending table

#print axioms TableBatch.registers_eq_of_store
#print axioms TableBatch.headers_canonical
#print axioms TableBatch.scan_pack_canonical
#print axioms TableBatch.body_canonical

end PNP.Concrete.NormalizerBlocks
