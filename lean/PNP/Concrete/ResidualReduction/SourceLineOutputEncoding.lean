import PNP.Concrete.ResidualReduction.SourceLineWitnessBudget

/-! Canonical optional encoding of the complete line witness. Its joint prefix
contains source weights and the covector, followed by the original-coordinate
direction. The codec is reversible at every fixed pair of dimensions. -/

namespace PNP.Concrete.ResidualReduction.SourceLineOutput
open PNP.Concrete PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceLine
open PNP.Concrete.ResidualReduction.SourceDirections

def recordCodec (n m : Nat) : Codec (LineWitness n m) :=
  mappedCodec (pairCodec (SourceEncoding.pointCodec (n + m)) (SourceEncoding.pointCodec n))
    (fun p => ⟨(splitPoint m p.1).1, (splitPoint m p.1).2, p.2⟩)
    (fun w => (appendPoint m w.weights w.beta, w.direction))
    (by intro w; cases w; simp only [split_append])
    (by rintro ⟨x, y⟩; simp only [append_split])
def codec (n m : Nat) : Codec (Option (LineWitness n m)) := MatrixSolutionEncoding.optionCodec (recordCodec n m)

theorem point_append_bytes (m : Nat) {n : Nat} (x : Point m) (y : Point n) :
    (SourceEncoding.pointCodec (n + m)).encode (appendPoint m x y) =
      (SourceEncoding.pointCodec m).encode x ++ (SourceEncoding.pointCodec n).encode y := by
  induction m with
  | zero => cases x; rfl
  | succ m ih =>
    rcases x with ⟨b, x⟩
    change b :: (SourceEncoding.pointCodec (n + m)).encode (appendPoint m x y) =
      b :: ((SourceEncoding.pointCodec m).encode x ++ (SourceEncoding.pointCodec n).encode y)
    rw [ih]
theorem some_bytes {n m : Nat} (w : LineWitness n m) :
    (codec n m).encode (some w) =
      true :: ((SourceEncoding.pointCodec m).encode w.weights ++
        ((SourceEncoding.pointCodec n).encode w.beta ++ (SourceEncoding.pointCodec n).encode w.direction)) := by
  change true :: ((SourceEncoding.pointCodec (n + m)).encode (appendPoint m w.weights w.beta) ++
    (SourceEncoding.pointCodec n).encode w.direction) = _
  rw [point_append_bytes, List.append_assoc]
theorem none_bytes (n m : Nat) : (codec n m).encode none = [false] := rfl
theorem lift_bytes {n : Nat} (F : Family n) (a : Affine n)
    (p : Point (n + F.length) × Point (directionSpace F [a]).parameters) :
    (codec n F.length).encode (some (liftLine F a p)) =
      true :: ((SourceEncoding.pointCodec (n + F.length)).encode p.1 ++
        (SourceEncoding.pointCodec n).encode ((directionSpace F [a]).direction p.2)) := by
  change true :: ((SourceEncoding.pointCodec (n + F.length)).encode
    (appendPoint F.length (splitPoint F.length p.1).1 (splitPoint F.length p.1).2) ++ _) = _
  rw [append_split]
  rfl
theorem bytes_bound {n m : Nat} (w : Option (LineWitness n m)) :
    ((codec n m).encode w).length ≤ m + 2 * n + 1 := by
  cases w with
  | none => rw [none_bytes]; simp only [List.length_cons, List.length_nil]; omega
  | some w =>
    rw [some_bytes]
    simp only [List.length_cons, List.length_append, SourceEncoding.point_length]
    omega
theorem roundtrip {n m : Nat} (w : Option (LineWitness n m)) :
    (codec n m).decode ((codec n m).encode w) = some w := decode_encode _ _

end PNP.Concrete.ResidualReduction.SourceLineOutput
