import PNP.Concrete.ResidualReduction.SourceMatrixBudget
import PNP.Concrete.ResidualReduction.MatrixInputHeaders

/-! Fail-closed classification of the original family packet. Every complete
fixed-width payload is actual source-row data. The constructive existence
proof below justifies the byte-level validator; it is not an executable
coefficient oracle or a supplied semantic correctness certificate. -/

namespace PNP.Concrete.ResidualReduction.SourceFamilyInput
open PNP.Concrete
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixInputFields
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding

theorem row_prefix_exists (n : Nat) (bits : BitString) (enough : 2 * n + 3 ≤ bits.length) :
    ∃ r : Row n, ∃ suffix, bits = rowWord r ++ suffix := by
  cases bits with
  | nil => exfalso; simp only [List.length_nil] at enough; omega
  | cons selected rest =>
    have leftEnough : n + 1 ≤ rest.length := by simp only [List.length_cons] at enough; omega
    obtain ⟨left, tail, first⟩ := MatrixInputEncoding.affine_prefix_exists n rest leftEnough
    have firstLength := congrArg List.length first
    simp only [List.length_append, affineWord_length] at firstLength
    have rightEnough : n + 1 ≤ tail.length := by simp only [List.length_cons] at enough; omega
    obtain ⟨right, suffix, second⟩ := MatrixInputEncoding.affine_prefix_exists n tail rightEnough
    refine ⟨⟨selected, left, right⟩, suffix, ?_⟩
    rw [first, second]
    simp only [rowWord, List.cons_append, List.append_assoc]

theorem payload_complete (n count : Nat) (bits : BitString)
    (length : bits.length = (2 * n + 3) * count) :
    ∃ F : Family n, F.length = count ∧ familyBits F = bits := by
  induction count generalizing bits with
  | zero =>
    cases bits with
    | nil => exact ⟨[], rfl, rfl⟩
    | cons b rest => exfalso; simp only [List.length_cons, Nat.mul_zero] at length; omega
  | succ count ih =>
    have enough : 2 * n + 3 ≤ bits.length := by
      calc
        2 * n + 3 = (2 * n + 3) * 1 := (Nat.mul_one _).symm
        _ ≤ (2 * n + 3) * (count + 1) := Nat.mul_le_mul_left _ (by omega)
        _ = bits.length := length.symm
    obtain ⟨r, suffix, split⟩ := row_prefix_exists n bits enough
    have splitLength := congrArg List.length split
    simp only [List.length_append, rowWord_length] at splitLength
    have tailLength : suffix.length = (2 * n + 3) * count := by
      rw [Nat.mul_succ] at length
      omega
    obtain ⟨F, countEq, bytes⟩ := ih suffix tailLength
    refine ⟨r :: F, ?_, ?_⟩
    · simp only [List.length_cons, countEq]
    · rw [familyBits, bytes]
      exact split.symm

theorem canonical_fields (n : Nat) (F : Family n) :
    fields (codec.encode ⟨n, F⟩) = ⟨n, F.length, familyBits F, true⟩ := by
  rw [codec_bits]
  simp only [fields, MatrixStrictHeader.scan_canonical]

theorem decode_none_header (input : BitString) (failed : (fields input).terminated = false) :
    codec.decode input = none := by
  cases parsed : codec.decode input with
  | none => rfl
  | some problem =>
    rcases problem with ⟨n, F⟩
    have bytes := (canonical input ⟨n, F⟩).mp parsed
    rw [← bytes, canonical_fields] at failed
    cases failed

theorem decode_none_length (input : BitString)
    (wrong : (fields input).payload.length ≠ (2 * (fields input).dimension + 3) * (fields input).rows) :
    codec.decode input = none := by
  cases parsed : codec.decode input with
  | none => rfl
  | some problem =>
    rcases problem with ⟨n, F⟩
    have bytes := (canonical input ⟨n, F⟩).mp parsed
    rw [← bytes, canonical_fields] at wrong
    exact (wrong (familyBits_length F)).elim

theorem valid_payload (input : BitString) (success : (fields input).terminated = true)
    (length : (fields input).payload.length = (2 * (fields input).dimension + 3) * (fields input).rows) :
    ∃ F : Family (fields input).dimension, F.length = (fields input).rows ∧
      familyBits F = (fields input).payload ∧ codec.encode ⟨(fields input).dimension, F⟩ = input := by
  obtain ⟨F, count, bytes⟩ := payload_complete (fields input).dimension (fields input).rows
    (fields input).payload length
  refine ⟨F, count, bytes, ?_⟩
  rw [codec_bits, count, bytes]
  exact (MatrixInputFields.split input success).symm

def matrixEncoded (input : BitString) : BitString :=
  match codec.decode input with
  | none => [false]
  | some ⟨_, F⟩ => affineMatrixPacket F

theorem matrixEncoded_canonical (n : Nat) (F : Family n) :
    matrixEncoded (codec.encode ⟨n, F⟩) = affineMatrixPacket F := by
  simp only [matrixEncoded, roundtrip]
theorem matrixEncoded_malformed (input : BitString) (invalid : codec.decode input = none) :
    matrixEncoded input = [false] := by simp only [matrixEncoded, invalid]

end PNP.Concrete.ResidualReduction.SourceFamilyInput
