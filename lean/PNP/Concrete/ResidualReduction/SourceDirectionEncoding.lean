import PNP.Concrete.ResidualReduction.SourcePolarFamilyInstructions
import PNP.Concrete.ResidualReduction.MatrixKernelSolver

/-! Original source data for the shared direction-space construction. The
packet records one explicit dimension, the original normals, and the source
family. It contains neither a kernel basis nor a correctness certificate. -/

namespace PNP.Concrete.ResidualReduction.SourceDirectionEncoding
open PNP.Concrete
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding (familyBits)

abbrev Problem := (n : Nat) × (System n × Family n)
def codec : Codec Problem := SourceEncoding.dependentCodec natCodec fun n =>
  pairCodec (listCodec (SourceEncoding.affineCodec n)) (SourceEncoding.familyCodec n)

theorem codec_bits (n : Nat) (F : Family n) (U : System n) :
    codec.encode ⟨n, U, F⟩ = natural n ++ (natural U.length ++
      (matrixBits U ++ (natural F.length ++ familyBits F))) := by
  change natural n ++ ((natural U.length ++ encodeSeq (SourceEncoding.affineCodec n).encode U) ++
    (natural F.length ++ encodeSeq (SourceEncoding.rowCodec n).encode F)) = _
  rw [MatrixInputEncoding.seq_matrix, SourceMatrixEncoding.familyBits_encode]
  simp only [List.append_assoc]

theorem codec_length (n : Nat) (F : Family n) (U : System n) :
    (codec.encode ⟨n, U, F⟩).length = (n + 1) + (U.length + 1) + (n + 1) * U.length +
      (F.length + 1) + (2 * n + 3) * F.length := by
  rw [codec_bits]
  simp only [List.length_append, natural_length, matrixBits_length, SourceMatrixEncoding.familyBits_length]
  omega

theorem dimension_bound (n : Nat) (F : Family n) (U : System n) :
    n ≤ (codec.encode ⟨n, U, F⟩).length := by rw [codec_length]; omega
theorem normals_bound (n : Nat) (F : Family n) (U : System n) :
    U.length ≤ (codec.encode ⟨n, U, F⟩).length := by rw [codec_length]; omega
theorem family_bound (n : Nat) (F : Family n) (U : System n) :
    F.length ≤ (codec.encode ⟨n, U, F⟩).length := by rw [codec_length]; omega
theorem normals_payload_bound (n : Nat) (F : Family n) (U : System n) :
    (matrixBits U).length ≤ (codec.encode ⟨n, U, F⟩).length := by
  rw [matrixBits_length, codec_length]; omega
theorem family_payload_bound (n : Nat) (F : Family n) (U : System n) :
    (familyBits F).length ≤ (codec.encode ⟨n, U, F⟩).length := by
  rw [SourceMatrixEncoding.familyBits_length, codec_length]; omega
theorem normals_packet_bound (n : Nat) (F : Family n) (U : System n) :
    (MatrixInputEncoding.codec.encode ⟨n, U⟩).length ≤ (codec.encode ⟨n, U, F⟩).length := by
  rw [MatrixInputEncoding.codec_length, codec_length]; omega

theorem roundtrip (n : Nat) (F : Family n) (U : System n) :
    codec.decode (codec.encode ⟨n, U, F⟩) = some ⟨n, U, F⟩ := decode_encode codec _
theorem canonical (input : BitString) (problem : Problem) :
    codec.decode input = some problem ↔ codec.encode problem = input :=
  decode_eq_some_iff codec input problem

theorem matrixBits_append {n : Nat} (U V : System n) :
    matrixBits (U ++ V) = matrixBits U ++ matrixBits V := by
  induction U with
  | nil => rfl
  | cons a U ih => simp only [List.cons_append, matrixBits, ih, List.append_assoc]

def rowBound (L : Nat) : Nat := L + L * L
def matrixPacketBound (L : Nat) : Nat := (L + 1) + (rowBound L + 1) + (L + 1) * rowBound L

theorem direction_count_bound (n : Nat) (F : Family n) (U : System n) :
    (directionSystem F U).length ≤ rowBound (codec.encode ⟨n, U, F⟩).length := by
  have count := directionSystem_size_bound F U
  have original := normals_bound n F U
  have product := Nat.mul_le_mul (family_bound n F U) (dimension_bound n F U)
  unfold rowBound
  omega

theorem direction_packet_bound (n : Nat) (F : Family n) (U : System n) :
    (MatrixInputEncoding.codec.encode ⟨n, directionSystem F U⟩).length ≤
      matrixPacketBound (codec.encode ⟨n, U, F⟩).length := by
  have dimension := dimension_bound n F U
  have count := direction_count_bound n F U
  have payload := Nat.mul_le_mul (Nat.succ_le_succ dimension) count
  rw [MatrixInputEncoding.codec_length]
  simp only [Nat.succ_eq_add_one] at payload
  unfold matrixPacketBound
  omega

end PNP.Concrete.ResidualReduction.SourceDirectionEncoding
