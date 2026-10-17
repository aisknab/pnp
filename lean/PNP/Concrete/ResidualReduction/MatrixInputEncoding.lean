import PNP.Concrete.ResidualReduction.MatrixSolutionInstructions

/-! Canonical encoded input for the complete finite linear solver. Both the
dimension and row count are explicit unary fields, followed by exactly the
coefficient matrix. An empty matrix therefore does not hide an unbounded
dimension. These are representation and parsing facts, not execution oracles. -/

namespace PNP.Concrete.ResidualReduction.MatrixInputEncoding
open PNP.Concrete
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding

abbrev Problem := (n : Nat) × System n

def codec : Codec Problem :=
  SourceEncoding.dependentCodec natCodec (fun n => listCodec (SourceEncoding.affineCodec n))

theorem seq_matrix {n : Nat} (rows : System n) :
    encodeSeq (SourceEncoding.affineCodec n).encode rows = matrixBits rows := by
  induction rows with
  | nil => rfl
  | cons a rows ih =>
    change affineWord a ++ encodeSeq (SourceEncoding.affineCodec n).encode rows =
      affineWord a ++ matrixBits rows
    rw [ih]

theorem codec_bits (n : Nat) (rows : System n) :
    codec.encode ⟨n, rows⟩ = natural n ++ (natural rows.length ++ matrixBits rows) := by
  change natural n ++ (natural rows.length ++ encodeSeq (SourceEncoding.affineCodec n).encode rows) = _
  rw [seq_matrix]

theorem codec_length (n : Nat) (rows : System n) :
    (codec.encode ⟨n, rows⟩).length = (n + 1) + (rows.length + 1) + (n + 1) * rows.length := by
  rw [codec_bits]
  simp only [List.length_append, natural_length, matrixBits_length]
  omega

theorem dimension_bound (n : Nat) (rows : System n) :
    n ≤ (codec.encode ⟨n, rows⟩).length := by rw [codec_length]; omega

theorem rowCount_bound (n : Nat) (rows : System n) :
    rows.length ≤ (codec.encode ⟨n, rows⟩).length := by rw [codec_length]; omega

theorem payload_bound (n : Nat) (rows : System n) :
    (matrixBits rows).length ≤ (codec.encode ⟨n, rows⟩).length := by
  rw [matrixBits_length, codec_length]
  omega

theorem roundtrip (n : Nat) (rows : System n) : codec.decode (codec.encode ⟨n, rows⟩) = some ⟨n, rows⟩ :=
  PNP.Concrete.NativeNormalization.NativeBitCodec.decode_encode codec _

theorem canonical (bits : BitString) (problem : Problem) :
    codec.decode bits = some problem ↔ codec.encode problem = bits :=
  PNP.Concrete.NativeNormalization.NativeBitCodec.decode_eq_some_iff codec bits problem

theorem affine_prefix_exists (n : Nat) (bits : BitString) (enough : n + 1 ≤ bits.length) :
    ∃ a : Affine n, ∃ rest, bits = affineWord a ++ rest := by
  induction n generalizing bits with
  | zero =>
    cases bits with
    | nil => exfalso; simp only [List.length_nil] at enough; omega
    | cons b rest => exact ⟨b, rest, rfl⟩
  | succ n ih =>
    cases bits with
    | nil => exfalso; simp only [List.length_nil] at enough; omega
    | cons b rest =>
      have tailEnough : n + 1 ≤ rest.length := by
        simp only [List.length_cons] at enough
        omega
      obtain ⟨a, suffix, split⟩ := ih rest tailEnough
      refine ⟨(b, a), suffix, ?_⟩
      rw [split]
      rfl

/-- Every complete fixed-width bit payload is actual coefficient data. No
semantic family, satisfiability witness, or validation certificate is supplied. -/
theorem payload_complete (n count : Nat) (bits : BitString)
    (length : bits.length = (n + 1) * count) :
    ∃ rows : System n, rows.length = count ∧ matrixBits rows = bits := by
  induction count generalizing bits with
  | zero =>
    cases bits with
    | nil => exact ⟨[], rfl, rfl⟩
    | cons b rest =>
      exfalso; simp only [List.length_cons, Nat.mul_zero] at length; omega
  | succ count ih =>
    have enough : n + 1 ≤ bits.length := by
      calc
        n + 1 = (n + 1) * 1 := (Nat.mul_one _).symm
        _ ≤ (n + 1) * (count + 1) := Nat.mul_le_mul_left _ (by omega)
        _ = bits.length := length.symm
    obtain ⟨a, rest, split⟩ := affine_prefix_exists n bits enough
    have splitLength := congrArg List.length split
    simp only [List.length_append, affineWord_length] at splitLength
    have restLength : rest.length = (n + 1) * count := by
      have total : (n + 1) + rest.length = (n + 1) * count + (n + 1) := by
        calc
          (n + 1) + rest.length = bits.length := splitLength.symm
          _ = (n + 1) * (count + 1) := length
          _ = (n + 1) * count + (n + 1) := Nat.mul_succ _ _
      omega
    obtain ⟨rows, rowCount, payload⟩ := ih rest restLength
    refine ⟨a :: rows, ?_, ?_⟩
    · simp only [List.length_cons, rowCount]
    · rw [matrixBits, payload]
      exact split.symm

def solveEncoded (input : BitString) : BitString :=
  match codec.decode input with
  | none => [false]
  | some ⟨n, rows⟩ => (solutionCodec n).encode (solve n rows)

theorem solveEncoded_valid (n : Nat) (rows : System n) :
    solveEncoded (codec.encode ⟨n, rows⟩) = (solutionCodec n).encode (solve n rows) := by
  simp only [solveEncoded, roundtrip]

end PNP.Concrete.ResidualReduction.MatrixInputEncoding
