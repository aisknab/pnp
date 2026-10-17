import PNP.Concrete.ResidualReduction.SourceSelectorDispatch

/-! Canonical optional selected-choice bytes. The optional pair of normals
comes before source weights and direction. A line covector is encoded as its
actual homogeneous affine normal, using the proved coordinate identity. -/

namespace PNP.Concrete.ResidualReduction.SourceChoiceEncoding
open PNP.Concrete PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceLine
open PNP.Concrete.ResidualReduction.SourceWitnessSelection
open PNP.Concrete.ResidualReduction.MatrixInstructions

def recordCodec (n m : Nat) : Codec (Choice n m) :=
  mappedCodec
    (pairCodec (MatrixSolutionEncoding.optionCodec
      (pairCodec (SourceEncoding.affineCodec n) (SourceEncoding.affineCodec n)))
      (pairCodec (SourceEncoding.pointCodec m) (SourceEncoding.pointCodec n)))
    (fun p => ⟨p.2.1,p.2.2,p.1⟩)
    (fun w => (w.normals,(w.weights,w.direction)))
    (by intro w; cases w; rfl)
    (by rintro ⟨normals,weights,direction⟩; rfl)
def codec (n m : Nat) : Codec (Option (Choice n m)) :=
  MatrixSolutionEncoding.optionCodec (recordCodec n m)

theorem none_bytes (n m : Nat) : (codec n m).encode none = [false] := rfl
theorem affine_bytes {n m : Nat} (w : Point m × Point n) :
    (codec n m).encode (some (affineChoice w)) =
      true :: false :: ((SourceEncoding.pointCodec m).encode w.1 ++
        (SourceEncoding.pointCodec n).encode w.2) := rfl
theorem plane_bytes {n m : Nat} (p : Affine n × Affine n) (w : Point m × Point n) :
    (codec n m).encode (some (planeChoice p w)) =
      true :: true :: (affineWord p.1 ++ (affineWord p.2 ++
        ((SourceEncoding.pointCodec m).encode w.1 ++ (SourceEncoding.pointCodec n).encode w.2))) := by
  change true :: ((true :: (affineWord p.1 ++ affineWord p.2)) ++
    ((SourceEncoding.pointCodec m).encode w.1 ++ (SourceEncoding.pointCodec n).encode w.2)) = _
  simp only [List.cons_append,List.append_assoc]
theorem line_bytes {n m : Nat} (a : Affine n) (w : LineWitness n m) :
    (codec n m).encode (some (lineChoice a w)) =
      true :: true :: (affineWord a ++ ((SourceEncoding.pointCodec n).encode w.beta ++
        (false :: ((SourceEncoding.pointCodec m).encode w.weights ++
          (SourceEncoding.pointCodec n).encode w.direction)))) := by
  change (codec n m).encode
    (some (planeChoice (a,SourceClosure.betaNormal w.beta) (w.weights,w.direction))) = _
  rw [plane_bytes,SourceLineMatrix.betaNormal_word]
  simp only [List.append_assoc,List.singleton_append]

theorem roundtrip {n m : Nat} (w : Option (Choice n m)) :
    (codec n m).decode ((codec n m).encode w) = some w := decode_encode _ _
theorem bytes_bound {n m : Nat} (w : Option (Choice n m)) :
    ((codec n m).encode w).length ≤ m + 3 * n + 4 := by
  cases w with
  | none => rw [none_bytes]; simp only [List.length_cons,List.length_nil]; omega
  | some w =>
    rcases w with ⟨weights,direction,normals⟩
    cases normals with
    | none =>
      change ((codec n m).encode (some (affineChoice (weights,direction)))).length ≤ _
      rw [affine_bytes]
      simp only [List.length_cons,List.length_append,SourceEncoding.point_length]
      omega
    | some p =>
      change ((codec n m).encode (some (planeChoice p (weights,direction)))).length ≤ _
      rw [plane_bytes]
      simp only [List.length_cons,List.length_append,SourceEncoding.point_length,affineWord_length]
      omega

theorem selected_bytes {n : Nat} (F : Family n) :
    (codec n F.length).encode (SourceSelectorResult.choice (SourceSelectorResult.select F)) =
      (codec n F.length).encode (choose F) := by rw [SourceSelectorResult.select_choice]
theorem selected_output_bound {n : Nat} (F : Family n) :
    ((codec n F.length).encode (choose F)).length ≤
      4 * (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length + 4 := by
  have size := bytes_bound (choose F)
  have dimension := SourceMatrixEncoding.dimension_bound n F
  have rows := SourceMatrixEncoding.rowCount_bound n F
  omega

end PNP.Concrete.ResidualReduction.SourceChoiceEncoding
