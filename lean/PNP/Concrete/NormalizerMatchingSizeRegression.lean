import PNP.Concrete.NormalizerMatchingSize
namespace PNP.Concrete.NormalizerBlocks
example : (MatchingTable.encode [some 3,none]).length = 20 := by decide
example (variables : Nat) (clauses : List (List CNFLiteral)) :
    (MatchingTable.encode (MatchingLoop.fullTable variables clauses)).length ≤
      MatchingLoop.tableBytes clauses.length (clauses.length + variables) :=
  MatchingLoop.fullTable_bytes variables clauses
example (variables : Nat) (clauses : List (List CNFLiteral)) (fuel : Nat) :
    (MatchingTable.encode (MatchingLoop.finish variables clauses fuel (List.replicate clauses.length none))).length ≤
      MatchingLoop.tableBytes clauses.length (clauses.length + variables) := by
  simpa only [List.length_replicate] using MatchingLoop.finish_bytes variables clauses fuel
    (List.replicate clauses.length none) (MatchingLoop.empty_bound _ _)
#print axioms MatchingLoop.unary_token_length
#print axioms MatchingLoop.entry_token_bound
#print axioms MatchingLoop.table_token_bound
#print axioms MatchingLoop.table_bytes
#print axioms MatchingLoop.finish_bytes
#print axioms MatchingLoop.fullTable_bytes
#print axioms MatchingLoop.path_bytes
#print axioms MatchingLoop.search_packet_length
#print axioms MatchingLoop.augmentation_packet_length
end PNP.Concrete.NormalizerBlocks
