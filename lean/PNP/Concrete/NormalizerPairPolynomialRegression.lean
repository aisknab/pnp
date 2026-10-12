import PNP.Concrete.NormalizerPairPolynomial
namespace PNP.Concrete.NormalizerBlocks
example : (PathPairs.result []).core.output = [] := by decide
example : (PathPairs.result [false,true]).core.output = [] := by decide
example : (PathPairs.result (PathData.encode [⟨false,1⟩,⟨true,2⟩])).core.output = TableBatch.encodeUpdates [(2,1)] := by decide
example (xs : List CNFLiteral) : PathPairs.polynomial.output (PathData.encode xs) =
    TableBatch.encodeUpdates (PathPairs.value xs) := PathPairs.polynomial_canonical xs
#print axioms PathPairs.loader_exec
#print axioms PathPairs.block_exec
#print axioms PathPairs.closed_run
#print axioms PathPairs.loaded_bounded
#print axioms PathPairs.sourceSteps_bound
#print axioms PathPairs.padded_run
#print axioms PathPairs.acceptsWithin
#print axioms PathPairs.polynomial_program
#print axioms PathPairs.polynomial_output
#print axioms PathPairs.polynomial_accepts
#print axioms PathPairs.polynomial_output_length
#print axioms PathPairs.polynomial_canonical
#print axioms PathPairs.machine_output
#print axioms PathPairs.machine_canonical
end PNP.Concrete.NormalizerBlocks
