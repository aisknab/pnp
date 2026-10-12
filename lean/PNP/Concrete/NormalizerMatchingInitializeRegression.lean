import PNP.Concrete.NormalizerMatchingInitialize
namespace PNP.Concrete.NormalizerBlocks
example (v : Nat) (cs : List (List CNFLiteral)) :
    (MatchingDriver.initialized (MatchingDriver.encode v cs)).table = MatchingTable.encode (List.replicate cs.length none) :=
  (MatchingDriver.initialized_canonical v cs).1.table
example (v : Nat) (cs : List (List CNFLiteral)) :
    (MatchingDriver.initialized (MatchingDriver.encode v cs)).remaining.length = cs.length + 1 :=
  (MatchingDriver.initialized_canonical v cs).2
#print axioms MatchingDriver.loadMetadata_exec
#print axioms MatchingDriver.saveMetadata_exec
#print axioms MatchingDriver.captured_fields
#print axioms MatchingDriver.buildEmpty_exec
#print axioms MatchingDriver.emptyReady_table
#print axioms MatchingDriver.emptyReady_frame
#print axioms MatchingDriver.initialize_exec
#print axioms MatchingDriver.initialized_fields
#print axioms MatchingDriver.initializeFuel_bound
#print axioms MatchingDriver.input_fields
#print axioms MatchingDriver.initialized_canonical
end PNP.Concrete.NormalizerBlocks
