import PNP.Concrete.ResidualReduction.SourceDirectionEncoding
import PNP.Concrete.ResidualReduction.SourceFamilyInput

/-! Exact classification of the original combined direction packet. Normals
-- occupy a counted prefix; the remaining unary header and family must consume
-- the whole tail. No supplied basis or correctness certificate is accepted. -/

namespace PNP.Concrete.ResidualReduction.SourceDirectionInput
open PNP.Concrete
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding (familyBits familyBits_length)
open PNP.Concrete.ResidualReduction.SourceDirectionEncoding
open PNP.Concrete.ResidualReduction.MatrixStrictHeader

def first (input : BitString) : MatrixInputFields.Fields := MatrixInputFields.fields input
def normalSize (input : BitString) : Nat := ((first input).dimension + 1) * (first input).rows
def normalBytes (input : BitString) : BitString := (first input).payload.take (normalSize input)
def familyTail (input : BitString) : BitString := (first input).payload.drop (normalSize input)
def header (input : BitString) : Header := scan (familyTail input)
def Valid (input : BitString) : Prop :=
  (first input).terminated = true ∧ normalSize input ≤ (first input).payload.length ∧
    (header input).terminated = true ∧
      (header input).rest.length = (2 * (first input).dimension + 3) * (header input).count

theorem canonical_first (n : Nat) (F : Family n) (U : System n) :
    first (codec.encode ⟨n, U, F⟩) =
      ⟨n, U.length, matrixBits U ++ (natural F.length ++ familyBits F), true⟩ := by
  rw [codec_bits]
  simp only [first, MatrixInputFields.fields, scan_canonical]
theorem canonical_normalBytes (n : Nat) (F : Family n) (U : System n) :
    normalBytes (codec.encode ⟨n, U, F⟩) = matrixBits U := by
  simp only [normalBytes, normalSize, canonical_first]
  rw [← matrixBits_length U, List.take_left]
theorem canonical_familyTail (n : Nat) (F : Family n) (U : System n) :
    familyTail (codec.encode ⟨n, U, F⟩) = natural F.length ++ familyBits F := by
  simp only [familyTail, normalSize, canonical_first]
  rw [← matrixBits_length U, List.drop_left]
theorem canonical_header (n : Nat) (F : Family n) (U : System n) :
    header (codec.encode ⟨n, U, F⟩) = ⟨F.length, familyBits F, true⟩ := by
  simp only [header, canonical_familyTail, scan_canonical]

theorem valid_canonical (n : Nat) (F : Family n) (U : System n) :
    Valid (codec.encode ⟨n, U, F⟩) := by
  unfold Valid
  simp only [normalSize, canonical_first, canonical_header]
  refine ⟨True.intro, ?_, True.intro, familyBits_length F⟩
  rw [← matrixBits_length U, List.length_append]
  omega

theorem family_split (input : BitString) (success : (header input).terminated = true) :
    familyTail input = natural (header input).count ++ (header input).rest := by
  have parsed : BitString.decodeLength (familyTail input) =
      some ((header input).count, (header input).rest) := by
    rw [scan_parse]
    change (if (header input).terminated then some ((header input).count, (header input).rest) else none) = _
    rw [success]
    rfl
  exact (natural_sound (familyTail input) (header input).count (header input).rest parsed).symm

theorem valid_input (input : BitString) (valid : Valid input) :
    ∃ U : System (first input).dimension, ∃ F : Family (first input).dimension,
      U.length = (first input).rows ∧ F.length = (header input).count ∧
        matrixBits U = normalBytes input ∧ familyBits F = (header input).rest ∧
          codec.encode ⟨(first input).dimension, U, F⟩ = input := by
  have length : (normalBytes input).length = ((first input).dimension + 1) * (first input).rows := by
    simp only [normalBytes, List.length_take]
    exact Nat.min_eq_left valid.2.1
  obtain ⟨U, rows, normal⟩ := MatrixInputEncoding.payload_complete
    (first input).dimension (first input).rows (normalBytes input) length
  obtain ⟨F, count, family⟩ := SourceFamilyInput.payload_complete
    (first input).dimension (header input).count (header input).rest valid.2.2.2
  refine ⟨U, F, rows, count, normal, family, ?_⟩
  rw [codec_bits, rows, count, normal, family, ← family_split input valid.2.2.1]
  have joined : normalBytes input ++ familyTail input = (first input).payload :=
    List.take_append_drop (normalSize input) (first input).payload
  rw [joined]
  exact (MatrixInputFields.split input valid.1).symm

theorem valid_iff_decodable (input : BitString) :
    Valid input ↔ ∃ problem, codec.decode input = some problem := by
  constructor
  · intro valid
    obtain ⟨U, F, _, _, _, _, bytes⟩ := valid_input input valid
    exact ⟨⟨(first input).dimension, U, F⟩, (canonical input _).mpr bytes⟩
  · rintro ⟨⟨n, U, F⟩, decoded⟩
    have bytes := (canonical input ⟨n, U, F⟩).mp decoded
    rw [← bytes]
    exact valid_canonical n F U

theorem decode_none_not_valid (input : BitString) (invalid : ¬ Valid input) :
    codec.decode input = none := by
  cases decoded : codec.decode input with
  | none => rfl
  | some problem => exact (invalid ((valid_iff_decodable input).mpr ⟨problem, decoded⟩)).elim
theorem decode_none_header (input : BitString) (bad : (first input).terminated = false) :
    codec.decode input = none := by
  apply decode_none_not_valid input
  intro valid
  have flag := valid.1
  rw [bad] at flag
  cases flag
theorem decode_none_normals (input : BitString) (bad : ¬ normalSize input ≤ (first input).payload.length) :
    codec.decode input = none := decode_none_not_valid input (fun valid => bad valid.2.1)
theorem decode_none_family_header (input : BitString) (bad : (header input).terminated = false) :
    codec.decode input = none := by
  apply decode_none_not_valid input
  intro valid
  have flag := valid.2.2.1
  rw [bad] at flag
  cases flag
theorem decode_none_family_length (input : BitString)
    (bad : (header input).rest.length ≠ (2 * (first input).dimension + 3) * (header input).count) :
    codec.decode input = none := decode_none_not_valid input (fun valid => bad valid.2.2.2)

theorem size_bounds (input : BitString) :
    (first input).dimension ≤ input.length ∧ (first input).rows ≤ input.length ∧
      (header input).count ≤ input.length ∧ (normalBytes input).length ≤ input.length ∧
        (familyTail input).length ≤ input.length ∧ (header input).rest.length ≤ input.length := by
  have top := MatrixInputFields.size_bounds input
  have bottom := scan_size (familyTail input)
  have tail : (familyTail input).length ≤ input.length := by
    simp only [familyTail, List.length_drop]
    dsimp only [first] at *
    omega
  refine ⟨top.1, top.2.1, ?_, ?_, tail, ?_⟩
  · change (scan (familyTail input)).count ≤ input.length
    omega
  · simp only [normalBytes, List.length_take]
    dsimp only [first] at *
    omega
  · change (scan (familyTail input)).rest.length ≤ input.length
    omega

def directionEncoded (input : BitString) : BitString :=
  match codec.decode input with
  | none => [false]
  | some ⟨n, U, F⟩ => (MatrixSolutionEncoding.solutionCodec n).encode (some (directionSpace F U))
theorem directionEncoded_canonical (n : Nat) (F : Family n) (U : System n) :
    directionEncoded (codec.encode ⟨n, U, F⟩) =
      (MatrixSolutionEncoding.solutionCodec n).encode (some (directionSpace F U)) := by
  simp only [directionEncoded, roundtrip]
theorem directionEncoded_malformed (input : BitString) (invalid : codec.decode input = none) :
    directionEncoded input = [false] := by simp only [directionEncoded, invalid]

end PNP.Concrete.ResidualReduction.SourceDirectionInput
