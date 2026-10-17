import PNP.Concrete.ResidualReduction.SourceMenuRawBridge

/-! All-bitstring specification for the source-derived menu constructor.
Successful output uses the existing dimension/matrix-list codec. Malformed
source packets return the single-bit absent marker, never a partial menu. -/

namespace PNP.Concrete.ResidualReduction.SourceMenuInput
open PNP.Concrete
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding (codec)
open PNP.Concrete.ResidualReduction.SourceChain (sourceMenu)

def answer (input : BitString) : BitString :=
  match codec.decode input with
  | none => [false]
  | some ⟨n, F⟩ => MatrixInputEncoding.codec.encode ⟨n, sourceMenu F⟩

theorem answer_canonical (n : Nat) (F : Family n) :
    answer (codec.encode ⟨n, F⟩) = MatrixInputEncoding.codec.encode ⟨n, sourceMenu F⟩ := by
  simp only [answer, SourceMatrixEncoding.roundtrip]
theorem answer_malformed (input : BitString) (invalid : codec.decode input = none) :
    answer input = [false] := by simp only [answer, invalid]
theorem decoded_answer (n : Nat) (F : Family n) :
    MatrixInputEncoding.codec.decode (answer (codec.encode ⟨n, F⟩)) = some ⟨n, sourceMenu F⟩ := by
  rw [answer_canonical]
  exact MatrixInputEncoding.roundtrip n (sourceMenu F)

theorem answer_length (input : BitString) : (answer input).length ≤ 7 * input.length + 2 := by
  cases decoded : codec.decode input with
  | none =>
    rw [answer_malformed input decoded]
    simp only [List.length_cons, List.length_nil]
    omega
  | some problem =>
    rcases problem with ⟨n, F⟩
    have bytes := (SourceMatrixEncoding.canonical input ⟨n, F⟩).mp decoded
    rw [← bytes, answer_canonical, MatrixInputEncoding.codec_length]
    have dimension := SourceMatrixEncoding.dimension_bound n F
    have count := SourceChain.sourceMenu_length_le F
    have rows := SourceMatrixEncoding.rowCount_bound n F
    have payload := SourceMenuBudget.output_original_bound F
    rw [MatrixInstructions.matrixBits_length] at payload
    omega

end PNP.Concrete.ResidualReduction.SourceMenuInput
