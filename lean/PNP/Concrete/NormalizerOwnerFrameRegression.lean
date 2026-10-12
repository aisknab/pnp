import PNP.Concrete.NormalizerOwnerFrame

namespace PNP.Concrete.NormalizerBlocks

example (r : Occurrence.Registers) : (TableOwner.queryResult r).state.target = r.target :=
  TableOwner.query_target r
example (target : Nat) (entries : MatchingTable.Entries) :
    (TableOwner.queryResult (TableOwner.prepared (List.replicate target true)
      (MatchingTable.encode entries))).state.output = TableOwner.answer (TableOwner.owner entries target) :=
  TableOwner.prepared_canonical target entries
example (input target : BitString) :
    (TableOwner.queryResult (TableOwner.prepared target input)).state.target = target :=
  TableOwner.query_target _

#print axioms TableOwner.pair_target
#print axioms TableOwner.scan_target
#print axioms TableOwner.query_target
#print axioms TableOwner.prepared_canonical

end PNP.Concrete.NormalizerBlocks
