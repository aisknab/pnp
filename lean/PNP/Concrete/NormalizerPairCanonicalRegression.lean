import PNP.Concrete.NormalizerPairCanonical
namespace PNP.Concrete.NormalizerBlocks
example (xs : List CNFLiteral) : PathPairs.value xs = PathPairs.headUpdates xs ++ PathPairs.value (PathPairs.nextVertices xs) := PathPairs.value_split xs
example : PathPairs.value [⟨false,0⟩,⟨true,2⟩,⟨false,1⟩,⟨true,2⟩] = [(2,0),(2,1)] := by decide
example : PathPairs.value [⟨false,0⟩,⟨true,2⟩,⟨false,1⟩] = [(2,0)] := by decide
#print axioms PathPairs.value_split
#print axioms PathPairs.encodeUpdates_append
#print axioms PathPairs.body_canonical
#print axioms PathPairs.encode_empty
#print axioms PathPairs.scan_buffer
#print axioms PathPairs.whole_buffer
end PNP.Concrete.NormalizerBlocks
