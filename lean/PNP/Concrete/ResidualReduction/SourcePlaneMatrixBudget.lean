import PNP.Concrete.ResidualReduction.SourcePlaneMatrixConstruction

/-! Original-source encoded-size bounds for the complete prepared plane
matrix constructor. They include materializing the extra source row, the
full all-coordinate matrix construction, padding projection and reordering.
Raw input validation and the final query are not silently included. -/

namespace PNP.Concrete.ResidualReduction.SourcePlaneMatrixBudget
open PNP.Concrete
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourcePlaneMatrix
open PNP.Concrete.ResidualReduction.SourcePlaneMatrixConstruction
open PNP.Concrete.ResidualReduction.SourceDirectionEncoding (codec)

theorem payloadBudget_mono {n N rows R : Nat} (dimension : n ≤ N) (count : rows ≤ R) :
    SourceMatrixConstruction.payloadBudget n rows ≤ SourceMatrixConstruction.payloadBudget N R := by
  have coefficient : 24 * n + 62 ≤ 24 * N + 62 := by omega
  have rowWork := Nat.mul_le_mul coefficient count
  have columnWork := Nat.mul_le_mul (Nat.add_le_add_right rowWork 6) dimension
  have allWork := Nat.mul_le_mul (Nat.add_le_add_right columnWork 7) dimension
  have data := Nat.mul_le_mul (Nat.add_le_add_right count 1) (Nat.mul_le_mul dimension dimension)
  unfold SourceMatrixConstruction.payloadBudget
  omega

def projectionBudget (L : Nat) : Nat := (9 * (L + 1) + 4) * (L * L) + 2
def budget (L : Nat) : Nat :=
  (8 * L + 9) + (SourceMatrixConstruction.payloadBudget L (L + 1) + (4 + projectionBudget L))
def matrixPolynomial : NatPolynomial :=
  .add (.add
    (.mul (.add (.mul (.add (.mul (.add (.mul (.constant 24) .variable) (.constant 62))
      (.add .variable (.constant 1))) (.constant 6)) .variable) (.constant 7)) .variable)
    (.mul (.constant 4) (.mul (.add (.add .variable (.constant 1)) (.constant 1)) (.mul .variable .variable))))
    (.constant 7)
def projectionPolynomial : NatPolynomial :=
  .add (.mul (.add (.mul (.constant 9) (.add .variable (.constant 1))) (.constant 4))
    (.mul .variable .variable)) (.constant 2)
def costPolynomial : NatPolynomial :=
  .add (.add (.mul (.constant 8) .variable) (.constant 9))
    (.add matrixPolynomial (.add (.constant 4) projectionPolynomial))
theorem matrixPolynomial_eval (L : Nat) :
    matrixPolynomial.eval L = SourceMatrixConstruction.payloadBudget L (L + 1) := rfl
theorem projectionPolynomial_eval (L : Nat) : projectionPolynomial.eval L = projectionBudget L := rfl
theorem costPolynomial_eval (L : Nat) : costPolynomial.eval L = budget L := rfl

theorem original_input_bound {n : Nat} (F : Family n) (alpha beta : Affine n) :
    fuel F alpha beta ≤ costPolynomial.eval (codec.encode ⟨n, [alpha, beta], F⟩).length := by
  let L := (codec.encode ⟨n, [alpha, beta], F⟩).length
  have hn : n ≤ L := SourceDirectionEncoding.dimension_bound n F [alpha, beta]
  have hm : F.length ≤ L := SourceDirectionEncoding.family_bound n F [alpha, beta]
  have hs : (SourceMatrixEncoding.familyBits F).length ≤ L :=
    SourceDirectionEncoding.family_payload_bound n F [alpha, beta]
  have augment : SourcePlaneMatrixAugmentation.fuel F ≤ 8 * L + 9 :=
    Nat.add_le_add_right (Nat.mul_le_mul_left 8 hs) 9
  have matrix : SourceMatrixConstruction.payloadFuel n (F.length + 1) ≤
      SourceMatrixConstruction.payloadBudget L (L + 1) := by
    have built := SourceMatrixConstruction.payloadFuel_bound (augmented F alpha beta)
    rw [augmented_length] at built
    exact Nat.le_trans built (payloadBudget_mono hn (Nat.add_le_add_right hm 1))
  have projection : SourcePlaneMatrixProjection.fuel F.length (SourcePlane.planeRows F alpha beta) ≤ projectionBudget L := by
    unfold SourcePlaneMatrixProjection.fuel projectionBudget
    rw [SourcePlane.planeRows_length]
    exact Nat.add_le_add_right
      (Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 9 (Nat.add_le_add_right hm 1)) 4)
        (Nat.mul_le_mul hn hn)) 2
  rw [costPolynomial_eval]
  exact Nat.add_le_add augment (Nat.add_le_add matrix (Nat.add_le_add_left projection 4))
theorem original_output_bound {n : Nat} (F : Family n) (alpha beta : Affine n) :
    ((result F alpha beta).store.get 8).length ≤
      ((codec.encode ⟨n, [alpha, beta], F⟩).length + 1) *
        ((codec.encode ⟨n, [alpha, beta], F⟩).length * (codec.encode ⟨n, [alpha, beta], F⟩).length) := by
  rw [output_length]
  exact Nat.mul_le_mul (Nat.add_le_add_right (SourceDirectionEncoding.family_bound n F [alpha, beta]) 1)
    (Nat.mul_le_mul (SourceDirectionEncoding.dimension_bound n F [alpha, beta])
      (SourceDirectionEncoding.dimension_bound n F [alpha, beta]))

end PNP.Concrete.ResidualReduction.SourcePlaneMatrixBudget
