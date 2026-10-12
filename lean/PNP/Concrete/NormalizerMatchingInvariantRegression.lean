import PNP.Concrete.NormalizerMatchingInvariant
namespace PNP.Concrete.NormalizerBlocks
example : MatchingTable.writeAll [none,none] [(0,3),(0,1),(9,5)] = [some 1,none] := by decide
example (count limit : Nat) : MatchingLoop.EntriesBound limit (List.replicate count none) :=
  MatchingLoop.empty_bound count limit
example : TracePath.value [(⟨false,2⟩,some ⟨true,8⟩)] ⟨false,2⟩ = none := by decide
#print axioms MatchingLoop.path_range
#print axioms MatchingLoop.path_default_range
#print axioms MatchingLoop.pairs_range
#print axioms MatchingLoop.empty_bound
#print axioms MatchingLoop.write_bound
#print axioms MatchingLoop.writeAll_bound
#print axioms MatchingLoop.search_augmentation_bound
end PNP.Concrete.NormalizerBlocks
