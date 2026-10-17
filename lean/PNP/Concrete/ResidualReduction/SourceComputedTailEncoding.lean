import PNP.Concrete.ResidualReduction.SourceTailNormal
import PNP.Concrete.ResidualReduction.SourceQuadraticEncoding
import PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
import PNP.Concrete.ResidualReduction.SourceComputedContract

/-! A reversible byte representation of the existing checked tail candidate.
The input contains the original optional normal pair and actual quadratic
coefficients. Encoding a computed candidate does not discharge its separate
coefficient equality gate or assert that an arbitrary candidate is valid. -/

namespace PNP.Concrete.ResidualReduction.SourceComputedTailEncoding
open PNP.Concrete PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceClosure
open PNP.Concrete.ResidualReduction.SourceBalance
open PNP.Concrete.ResidualReduction.MatrixInstructions

def codec (n : Nat) : Codec (TailForm n) :=
  mappedCodec
    (pairCodec (MatrixSolutionEncoding.optionCodec
      (pairCodec (SourceEncoding.affineCodec n) (SourceEncoding.affineCodec n)))
      (SourceEncoding.affineCodec n))
    (fun p => match p.1 with
      | none => .affine p.2
      | some (a,b) => .plane a b p.2)
    (fun t => match t with
      | .affine u => (none,u)
      | .plane a b u => (some (a,b),u))
    (by intro t; cases t <;> rfl)
    (by rintro ⟨normals,u⟩; cases normals with
        | none => rfl
        | some p => rcases p with ⟨a,b⟩; rfl)

theorem affine_bytes {n : Nat} (u : Affine n) :
    (codec n).encode (.affine u) = false :: affineWord u := rfl
theorem plane_bytes {n : Nat} (a b u : Affine n) :
    (codec n).encode (.plane a b u) =
      true :: (affineWord a ++ (affineWord b ++ affineWord u)) := by
  change (true :: (affineWord a ++ affineWord b)) ++ affineWord u = _
  simp only [List.cons_append,List.append_assoc]
theorem roundtrip {n : Nat} (t : TailForm n) :
    (codec n).decode ((codec n).encode t) = some t := decode_encode _ _
theorem bytes_bound {n : Nat} (t : TailForm n) :
    ((codec n).encode t).length ≤ 3 * (n + 1) + 1 := by
  cases t with
  | affine u =>
    rw [affine_bytes]
    simp only [List.length_cons,affineWord_length]
    omega
  | plane a b u =>
    rw [plane_bytes]
    simp only [List.length_cons,List.length_append,affineWord_length]
    omega

def inputCodec (n : Nat) :
    Codec (Option (Affine (n + 1) × Affine (n + 1)) × Quadratic n) :=
  pairCodec (MatrixSolutionEncoding.optionCodec
    (pairCodec (SourceEncoding.affineCodec (n + 1)) (SourceEncoding.affineCodec (n + 1))))
    (SourceQuadraticEncoding.codec n)
def packet {n : Nat} (q : Quadratic n)
    (normals : Option (Affine (n + 1) × Affine (n + 1))) : BitString :=
  (inputCodec n).encode (normals,q)

theorem packet_none {n : Nat} (q : Quadratic n) :
    packet q none = false :: SourceQuadraticEncoding.word q := rfl
theorem packet_some {n : Nat} (q : Quadratic n) (a b : Affine (n + 1)) :
    packet q (some (a,b)) =
      true :: (affineWord a ++ (affineWord b ++ SourceQuadraticEncoding.word q)) := by
  change (true :: (affineWord a ++ affineWord b)) ++ SourceQuadraticEncoding.word q = _
  simp only [List.cons_append,List.append_assoc]
theorem packet_none_length {n : Nat} (q : Quadratic n) :
    (packet q none).length = quadraticBits n + 1 := by
  simp only [packet_none,List.length_cons,SourceQuadraticEncoding.word_length]
theorem packet_some_length {n : Nat} (q : Quadratic n) (a b : Affine (n + 1)) :
    (packet q (some (a,b))).length = quadraticBits n + 2 * n + 5 := by
  simp only [packet_some,List.length_cons,List.length_append,affineWord_length,
    SourceQuadraticEncoding.word_length]
  omega
theorem packet_roundtrip {n : Nat} (q : Quadratic n)
    (normals : Option (Affine (n + 1) × Affine (n + 1))) :
    (inputCodec n).decode (packet q normals) = some (normals,q) := decode_encode _ _

def computed {n : Nat} (q : Quadratic n) (k : Fin (n + 1)) :
    Option (Affine (n + 1) × Affine (n + 1)) → TailForm n
  | none => .affine (affinePart q)
  | some (a,b) => .plane (tailNormal k a) (tailNormal k b)
      (planeRemainder q (tailNormal k a) (tailNormal k b))

theorem computed_eq {n : Nat} (F : Family (n + 1)) (w : Point F.length)
    (c : Fin (n + 1) × Point n) (normals : Option (Affine (n + 1) × Affine (n + 1))) :
    computed (scalar (chartRows (markSource F w) c.1 c.2)).2 c.1 normals =
      computedTail F w c normals := rfl

end PNP.Concrete.ResidualReduction.SourceComputedTailEncoding
