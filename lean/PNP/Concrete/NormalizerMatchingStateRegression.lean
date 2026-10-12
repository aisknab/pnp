import PNP.Concrete.NormalizerMatchingState
namespace PNP.Concrete.NormalizerBlocks
example (r : MatchingDriver.State) :
    (MatchingDriver.searchResult r).table = r.table := (MatchingDriver.searchResult_frame r).2.2.1
example (v : Nat) (cs : List (List CNFLiteral)) (t : MatchingTable.Entries) :
    MatchingDriver.searchPacket (List.replicate v true) (GraphQuery.clauseData cs) (MatchingTable.encode t) =
      Exploration.encode v cs t := MatchingDriver.searchPacket_canonical v cs t
#print axioms MatchingDriver.liftSearch_exec
#print axioms MatchingDriver.liftCore_exec
#print axioms MatchingDriver.packSearch_exec
#print axioms MatchingDriver.searchPacked_input
#print axioms MatchingDriver.searchPacked_frame
#print axioms MatchingDriver.searchPacket_canonical
#print axioms MatchingDriver.search_exec
#print axioms MatchingDriver.searchResult_output
#print axioms MatchingDriver.searchResult_frame
end PNP.Concrete.NormalizerBlocks
