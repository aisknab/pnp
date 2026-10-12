import PNP.Concrete.NormalizerMatchingAdvance
namespace PNP.Concrete.NormalizerBlocks
example (r : MatchingDriver.State) :
    (MatchingDriver.advanced r).remaining = r.remaining := (MatchingDriver.advanced_frame r).2.2
example (r : MatchingDriver.State) (entries : MatchingTable.Entries) (i : Nat) (path : List CNFLiteral)
    (table : r.table = MatchingTable.encode entries)
    (response : r.registers.output = Search.answer (.augment i path)) :
    (MatchingDriver.advanced r).table = MatchingTable.encode (MatchingTable.writeAll entries (PathPairs.value path)) :=
  MatchingDriver.advanced_canonical r entries i path table response
#print axioms MatchingDriver.readRouteCore_exec
#print axioms MatchingDriver.readRoute_exec
#print axioms MatchingDriver.packAugmentation_exec
#print axioms MatchingDriver.augmentationPacked_input
#print axioms MatchingDriver.augmentationPacked_frame
#print axioms MatchingDriver.augmentationPacked_canonical
#print axioms MatchingDriver.runAugmentation_exec
#print axioms MatchingDriver.saveTable_exec
#print axioms MatchingDriver.advance_exec
#print axioms MatchingDriver.advanced_frame
#print axioms MatchingDriver.advanced_canonical
end PNP.Concrete.NormalizerBlocks
