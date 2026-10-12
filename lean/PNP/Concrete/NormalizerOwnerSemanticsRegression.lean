import PNP.Concrete.NormalizerOwnerSemantics

namespace PNP.Concrete.NormalizerBlocks

example (entries : MatchingTable.Entries) (target index : Nat) (remaining excess sign : BitString) :
    (TableOwner.tokenScan (encodeClauseListTokens (MatchingTable.clauses entries) ++ [.finish])
      (Occurrence.waiting target remaining excess sign (List.replicate index true))).output =
      TableOwner.answer (TableOwner.ownerFrom index entries target) :=
  TableOwner.tokenScan_table_correct entries target index remaining excess sign
example : TableOwner.owner [none,some 4,some 4] 4 = some 1 := rfl
example : TableOwner.owner [some 4,none,some 4] 4 = some 0 := rfl
example : TableOwner.owner [none,some 3] 4 = none := rfl

#print axioms TableOwner.tokenScan_empty_entry
#print axioms TableOwner.tokenScan_present_entry
#print axioms TableOwner.tokenScan_table_correct

end PNP.Concrete.NormalizerBlocks
