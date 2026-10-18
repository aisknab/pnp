import PNP.Concrete.ResidualReduction.SourceNativeEnvelopePolynomial
import PNP.Concrete.SerializedNormalizer

/-! Complete original-input polynomial reduction-history construction.
Normalization and native-packet reduction are composed through their verified
literal-machine refinements. Every input bitstring is covered. A residual
output is still a stopped core, not an unsatisfiability verdict or a solver. -/

namespace PNP.Concrete.ResidualReduction.SourceReductionPolynomial
open PNP.Concrete PNP.Concrete.NativeNormalization NativeBitCodec

def polynomial : PolynomialTimeFunction :=
  PolynomialTimeFunction.compose SerializedNormalizer.polynomial SourceNativeEnvelopePolynomial.polynomial
private theorem output_projection (input : BitString) : polynomial.output input =
    (PolynomialTimeFunction.compose SerializedNormalizer.polynomial
      SourceNativeEnvelopePolynomial.polynomial).output input := rfl
private theorem program_projection : polynomial.program =
    .compose SerializedNormalizer.polynomial.program SourceNativeEnvelopePolynomial.polynomial.program := rfl

/-- No caller-supplied validity, family, history, or correctness premise. -/
theorem polynomial_output (input : BitString) : polynomial.output input = SourceEncoding.sourceEncode input := by
  rw [output_projection,PolynomialTimeFunction.compose_output,WholePacketSourceBridge.polynomial_source]
  exact SourceNativeEnvelopePolynomial.polynomial_canonical (NativeSerializedNormalizer.packet input)

def rawRefinement : FunctionProgram.RawRefinement polynomial.program := by
  rw [program_projection]
  exact FunctionProgram.RawRefinement.compose SerializedNormalizer.rawRefinement
    SourceNativeEnvelopePolynomial.rawRefinement
def output (input : BitString) : BitString :=
  machineOutput rawRefinement.machine (rawRefinement.timeBound.eval (BitString.size input)) input

theorem output_eq (input : BitString) : output input = SourceEncoding.sourceEncode input :=
  (rawRefinement.output_eq input (polynomial.haltsWithin input)).trans (polynomial_output input)
theorem halts (input : BitString) :
    boundedDecide rawRefinement.machine
      (rawRefinement.timeBound.eval (BitString.size input)) input ≠ .timeout :=
  rawRefinement.haltsWithin input (polynomial.haltsWithin input)
theorem output_size (input : BitString) :
    BitString.size (output input) ≤ polynomial.outputSizeBound.eval (BitString.size input) :=
  FunctionProgram.RawRefinement.output_size_le polynomial rawRefinement input
theorem encoded_size (input : BitString) :
    (output input).length ≤ SourceEncoding.sourceOutputPolynomial.eval input.length := by
  rw [output_eq]
  exact SourceEncoding.source_encoded_bound input

theorem malformed_output (input : BitString)
    (packet : NativeSerializedNormalizer.packet input = .malformed) : output input = [false] := by
  rw [output_eq,SourceEncoding.sourceEncode,packet]
  rfl
theorem model_output (input assignment : BitString)
    (packet : NativeSerializedNormalizer.packet input = .model assignment) :
    output input = [true,false] ++ (listCodec bitCodec).encode assignment := by
  rw [output_eq,SourceEncoding.sourceEncode,packet]
  rfl
theorem system_output (input : BitString) (c : Nat) (D : NativeSparseSystem.System c)
    (packet : NativeSerializedNormalizer.packet input = .system c D) :
    output input = [true,true] ++ natural (2 * c) ++ SourceEncoding.dataCodec.encode
      (SourceEncoding.toData (SourceChain.reduce (2 * c) (NativeSource.family D))) := by
  rw [output_eq,SourceEncoding.sourceEncode,packet]
  rfl

end PNP.Concrete.ResidualReduction.SourceReductionPolynomial
