import PNP.Concrete.NormalizerAugmentationPolynomial
namespace PNP.Concrete.NormalizerBlocks
example : (Augmentation.result (Augmentation.encode [none] [⟨false,2⟩,⟨true,0⟩])).pairs.core.output =
    MatchingTable.encode [some 2] := by decide
example : (Augmentation.result (Augmentation.encode [some 1] [])).pairs.core.output =
    MatchingTable.encode [some 1] := by decide
example (entries : MatchingTable.Entries) (xs : List CNFLiteral) :
    Augmentation.polynomial.output (Augmentation.encode entries xs) =
      MatchingTable.encode (MatchingTable.writeAll entries (PathPairs.value xs)) :=
  Augmentation.polynomial_canonical entries xs
#print axioms Augmentation.loader_exec
#print axioms Augmentation.block_exec
#print axioms Augmentation.closed_run
#print axioms Augmentation.loaded_bounded
#print axioms Augmentation.sourceSteps_bound
#print axioms Augmentation.padded_run
#print axioms Augmentation.acceptsWithin
#print axioms Augmentation.polynomial_program
#print axioms Augmentation.polynomial_output
#print axioms Augmentation.polynomial_accepts
#print axioms Augmentation.polynomial_output_length
#print axioms Augmentation.polynomial_canonical
#print axioms Augmentation.machine_output
#print axioms Augmentation.machine_canonical
end PNP.Concrete.NormalizerBlocks
