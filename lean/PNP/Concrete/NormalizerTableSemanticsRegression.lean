import PNP.Concrete.NormalizerTableSemantics

namespace PNP.Concrete.NormalizerBlocks

example (clauses : List (List CNFLiteral)) (index value : Nat) (buffer : BitString) (r : Occurrence.Registers) :
    (TableWrite.tokenScan (encodeClauseListTokens clauses ++ [.finish])
      (TableWrite.tableState index value buffer [] r)).excess =
      (encodeTokenPairs (encodeClauseListTokens (clauses.set index [⟨true, value⟩]) ++ [.finish])).reverse ++ buffer :=
  TableWrite.tokenScan_clauseList clauses index value buffer r
example (entries : MatchingTable.Entries) (index value : Nat) (buffer : BitString) (r : Occurrence.Registers) :
    (TableWrite.tokenScan (encodeClauseListTokens (MatchingTable.clauses entries) ++ [.finish])
      (TableWrite.tableState index value buffer [] r)).excess =
      (MatchingTable.encode (MatchingTable.write entries index value)).reverse ++ buffer :=
  TableWrite.tokenScan_table entries index value buffer r

#print axioms TableWrite.tokenScan_clauseList
#print axioms TableWrite.tokenScan_table

end PNP.Concrete.NormalizerBlocks
