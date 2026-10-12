import PNP.Concrete.NormalizerOriginalPolynomial
namespace PNP.Concrete.NormalizerBlocks
example (input : BitString) (invalid : decodeEncodedCNF input = none) :
    OriginalNormalizer.polynomial.output input = [false,false,false] :=
  OriginalNormalizer.polynomial_malformed input invalid
example (input : BitString) (F : CNFFormula) (decoded : decodeEncodedCNF input = some F) :
    OriginalNormalizer.polynomial.output input = OriginalNormalizer.decodedPacket F :=
  OriginalNormalizer.polynomial_decoded input F decoded
example (input : BitString) :
    boundedDecide OriginalNormalizer.rawRefinement.machine
      (OriginalNormalizer.rawRefinement.timeBound.eval (BitString.size input)) input ≠ .timeout :=
  OriginalNormalizer.machine_halts input
#print axioms OriginalNormalizer.polynomial_program
#print axioms OriginalNormalizer.polynomial_output
#print axioms OriginalNormalizer.polynomial_malformed
#print axioms OriginalNormalizer.polynomial_decoded
#print axioms OriginalNormalizer.outputRawRefinement
#print axioms OriginalNormalizer.rawRefinement
#print axioms OriginalNormalizer.machine_output
#print axioms OriginalNormalizer.machine_halts
#print axioms OriginalNormalizer.machine_output_size
#print axioms OriginalNormalizer.machine_malformed
#print axioms OriginalNormalizer.machine_decoded
end PNP.Concrete.NormalizerBlocks
