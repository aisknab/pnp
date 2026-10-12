import PNP.Concrete.NormalizerBatchCanonical

namespace PNP.Concrete.NormalizerBlocks

example (updates : List (Nat × Nat)) (entries : MatchingTable.Entries) :
    (TableBatch.whole (TableBatch.initial (TableBatch.encodeUpdates updates) (MatchingTable.encode entries))).state.table =
      MatchingTable.encode (MatchingTable.writeAll entries updates) := TableBatch.whole_canonical updates entries
example (entries : MatchingTable.Entries) (index first last : Nat) :
    (TableBatch.whole (TableBatch.initial (TableBatch.encodeUpdates [(index,first),(index,last)])
      (MatchingTable.encode entries))).state.table = MatchingTable.encode (MatchingTable.write entries index last) :=
  TableBatch.repeated_index_last_wins entries index first last
example (table : BitString) :
    (TableBatch.whole (TableBatch.initial (TableBatch.encodeUpdates []) table)).state.table = table :=
  TableBatch.empty_updates_preserve table
example :
    (TableBatch.whole (TableBatch.initial (TableBatch.encodeUpdates [(1,2),(0,7),(1,3)])
      (MatchingTable.encode [none,some 4,none]))).state.table = MatchingTable.encode [some 7,some 3,none] :=
  TableBatch.whole_canonical _ _
example :
    (TableBatch.whole (TableBatch.initial (TableBatch.encodeUpdates [(2,8),(0,4)])
      (MatchingTable.encode [none]))).state.table = MatchingTable.encode [some 4] :=
  TableBatch.whole_canonical _ _

#print axioms TableBatch.encodePair_length
#print axioms TableBatch.encodePair_nonempty
#print axioms TableBatch.run_canonical
#print axioms TableBatch.whole_canonical
#print axioms TableBatch.empty_updates_preserve
#print axioms TableBatch.repeated_index_last_wins

end PNP.Concrete.NormalizerBlocks
