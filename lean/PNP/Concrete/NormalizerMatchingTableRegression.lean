import PNP.Concrete.NormalizerMatchingTable

namespace PNP.Concrete.NormalizerBlocks

example (entries : MatchingTable.Entries) (index : Nat) :
    ClauseQuery.polynomial.output (ClauseQuery.encodeQuery 0 index (MatchingTable.clauses entries)) =
      Occurrence.encodeQuery 0 (MatchingTable.entryClause (MatchingTable.read entries index)) :=
  MatchingTable.read_query entries index
example (entries : MatchingTable.Entries) (index value : Nat) :
    (MatchingTable.write entries index value).length = entries.length :=
  MatchingTable.write_length entries index value
example (entries : MatchingTable.Entries) (index first last : Nat) :
    MatchingTable.write (MatchingTable.write entries index first) index last =
      MatchingTable.write entries index last := MatchingTable.write_last_wins entries index first last
example : MatchingTable.writeAll [none, some 4, none] [(1, 2), (0, 7), (1, 3)] =
    [some 7, some 3, none] := rfl
example : MatchingTable.write [none, some 4] 2 9 = [none, some 4] := rfl
example : MatchingTable.read [none, some 4] 1 = some 4 := rfl

#print axioms MatchingTable.clauses_read
#print axioms MatchingTable.read_query
#print axioms MatchingTable.write_length
#print axioms MatchingTable.write_eq_set
#print axioms MatchingTable.clauses_write
#print axioms MatchingTable.write_last_wins
#print axioms MatchingTable.writeAll_length
#print axioms MatchingTable.read_write

end PNP.Concrete.NormalizerBlocks
