import PNP.Concrete.NormalizerMatchingCalls
namespace PNP.Concrete.NormalizerBlocks
example (r : Search.State) : Exec MatchingCall.resetSearch r.store 29 (Search.initial r.registers.input).store :=
  MatchingCall.resetSearch_exec r
example (r : Augmentation.State) : Exec MatchingCall.resetAugmentation r.store 13
    (Augmentation.initial r.pairs.core.input).store := MatchingCall.resetAugmentation_exec r
example (r : Search.State) (xs : MatchingTable.Entries) (path : List CNFLiteral)
    (input : r.registers.input = Augmentation.encode xs path) :
    (MatchingCall.augmented r).registers.output = MatchingTable.encode (MatchingTable.writeAll xs (PathPairs.value path)) :=
  MatchingCall.augmented_canonical r xs path input
#print axioms MatchingCall.resetSearch_exec
#print axioms MatchingCall.search_exec
#print axioms MatchingCall.searchFuel_bound
#print axioms MatchingCall.searched_canonical
#print axioms MatchingCall.resetAugmentation_exec
#print axioms MatchingCall.augmentationPrefix_exec
#print axioms MatchingCall.augmentation_store
#print axioms MatchingCall.withAugmentation_store
#print axioms MatchingCall.augmentation_exec
#print axioms MatchingCall.augmentationFuel_bound
#print axioms MatchingCall.augmented_canonical
end PNP.Concrete.NormalizerBlocks
