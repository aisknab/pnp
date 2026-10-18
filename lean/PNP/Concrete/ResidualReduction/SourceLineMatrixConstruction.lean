import PNP.Concrete.ResidualReduction.SourceLineMatrixAugmentation
import PNP.Concrete.ResidualReduction.SourcePlaneMatrixBudget

/-! Exact prepared construction of the complete rank-one query matrix.
All n*n equations and the original weight/covector coordinate order are
preserved. The source-instruction fuel and serialized output have explicit
polynomial bounds in the original packet size. Raw parsing, the compiler's
word-copy cost, and the subsequent constrained solver/search remain distinct
obligations; this is not a complete line-query runtime theorem. -/

namespace PNP.Concrete.ResidualReduction.SourceLineMatrixConstruction
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceLineMatrix
open PNP.Concrete.ResidualReduction.SourceLineMatrixAugmentation
open PNP.Concrete.ResidualReduction.SourcePlaneMatrixAugmentation (State lift15 lift15_exec)
open PNP.Concrete.ResidualReduction.SourceDirectionEncoding (codec)

def result {n : Nat} (F : Family n) (alpha : Affine n) : State :=
  ⟨⟨SourceMatrixConstruction.ready (augmented F alpha) n 0 0 0
    (matrixBits (SourceLine.rankOneRows F alpha)), List.replicate F.length true⟩, affineWord alpha⟩
theorem payload_exec {n : Nat} (F : Family n) (alpha : Affine n) :
    Exec (lift15 SourceMatrixConstruction.payload) (augmentedInput F alpha).store
      (SourceMatrixConstruction.payloadFuel n (F.length + n)) (result F alpha).store := by
  have checked := lift15_exec SourceMatrixConstruction.payload (augmentedInput F alpha) _ _
    (SourceMatrixConstruction.payload_exec (augmented F alpha))
  simpa only [augmented_length, augmented_matrix, augmentedInput, loaded, result] using checked

def block : Block 17 := .seq SourceLineMatrixAugmentation.block (lift15 SourceMatrixConstruction.payload)
def fuel {n : Nat} (F : Family n) (alpha : Affine n) : Nat :=
  SourceLineMatrixAugmentation.fuel F alpha + SourceMatrixConstruction.payloadFuel n (F.length + n)
theorem block_exec {n : Nat} (F : Family n) (alpha : Affine n) :
    Exec block (start F alpha).store (fuel F alpha) (result F alpha).store :=
  Exec.seq (SourceLineMatrixAugmentation.block_exec F alpha) (payload_exec F alpha)
theorem result_output {n : Nat} (F : Family n) (alpha : Affine n) :
    (result F alpha).store.get 8 = matrixBits (SourceLine.rankOneRows F alpha) := rfl
theorem retained_normal {n : Nat} (F : Family n) (alpha : Affine n) :
    (result F alpha).store.get 16 = affineWord alpha := rfl
theorem retained_source_count {n : Nat} (F : Family n) (alpha : Affine n) :
    (result F alpha).store.get 15 = List.replicate F.length true := rfl
theorem retained_dimension {n : Nat} (F : Family n) (alpha : Affine n) :
    (result F alpha).store.get 9 = List.replicate n true := rfl
theorem output_length {n : Nat} (F : Family n) (alpha : Affine n) :
    ((result F alpha).store.get 8).length = (n + F.length + 1) * (n * n) := by
  rw [result_output, matrixBits_length, SourceLine.rankOneRows_length]
def program : Program 17 := block.program 0 8
theorem program_run {n : Nat} (F : Family n) (alpha : Affine n) :
    BitRegister.run program (fuel F alpha + 1) ⟨.running 0, (start F alpha).store⟩ =
      ⟨.accepted, (result F alpha).store⟩ := (block_exec F alpha).program_run 0 8

def augmentedSizeBudget (L : Nat) : Nat := (2 * L + 3) * (2 * L)
def augmentationBudget (L : Nat) : Nat :=
  (4 * L + 4) + (((8 * L + 13) * L + 1) + (4 * augmentedSizeBudget L + 6))
def budget (L : Nat) : Nat := augmentationBudget L + SourceMatrixConstruction.payloadBudget L (2 * L)
def augmentedSizePolynomial : NatPolynomial :=
  .mul (.add (.mul (.constant 2) .variable) (.constant 3)) (.mul (.constant 2) .variable)
def augmentationPolynomial : NatPolynomial :=
  .add (.add (.mul (.constant 4) .variable) (.constant 4))
    (.add (.add (.mul (.add (.mul (.constant 8) .variable) (.constant 13)) .variable) (.constant 1))
      (.add (.mul (.constant 4) augmentedSizePolynomial) (.constant 6)))
def matrixPolynomial : NatPolynomial :=
  .add (.add
    (.mul (.add (.mul (.add (.mul (.add (.mul (.constant 24) .variable) (.constant 62))
      (.mul (.constant 2) .variable)) (.constant 6)) .variable) (.constant 7)) .variable)
    (.mul (.constant 4) (.mul (.add (.mul (.constant 2) .variable) (.constant 1)) (.mul .variable .variable))))
    (.constant 7)
def costPolynomial : NatPolynomial := .add augmentationPolynomial matrixPolynomial
theorem augmentedSizePolynomial_eval (L : Nat) :
    augmentedSizePolynomial.eval L = augmentedSizeBudget L := rfl
theorem augmentationPolynomial_eval (L : Nat) :
    augmentationPolynomial.eval L = augmentationBudget L := rfl
theorem matrixPolynomial_eval (L : Nat) :
    matrixPolynomial.eval L = SourceMatrixConstruction.payloadBudget L (2 * L) := rfl
theorem costPolynomial_eval (L : Nat) : costPolynomial.eval L = budget L := rfl

theorem augmented_rows_bound {n : Nat} (F : Family n) (alpha : Affine n) :
    (augmented F alpha).length ≤ 2 * (codec.encode ⟨n, [alpha], F⟩).length := by
  have hn := SourceDirectionEncoding.dimension_bound n F [alpha]
  have hm := SourceDirectionEncoding.family_bound n F [alpha]
  rw [augmented_length]
  omega
theorem augmented_size_bound {n : Nat} (F : Family n) (alpha : Affine n) :
    (SourceMatrixEncoding.familyBits (augmented F alpha)).length ≤
      augmentedSizeBudget (codec.encode ⟨n, [alpha], F⟩).length := by
  have hn := SourceDirectionEncoding.dimension_bound n F [alpha]
  rw [SourceMatrixEncoding.familyBits_length]
  exact Nat.mul_le_mul (by omega) (augmented_rows_bound F alpha)
theorem augmentation_bound {n : Nat} (F : Family n) (alpha : Affine n) :
    SourceLineMatrixAugmentation.fuel F alpha ≤ augmentationBudget (codec.encode ⟨n, [alpha], F⟩).length := by
  let L := (codec.encode ⟨n, [alpha], F⟩).length
  have hn : n ≤ L := SourceDirectionEncoding.dimension_bound n F [alpha]
  have hs : (SourceMatrixEncoding.familyBits F).length ≤ L :=
    SourceDirectionEncoding.family_payload_bound n F [alpha]
  have loop : SourceLineMatrixRows.loopFuel n 0 n ≤ (8 * L + 13) * L + 1 :=
    Nat.le_trans (SourceLineMatrixRows.loopFuel_bound n n 0 (by omega))
      (Nat.add_le_add_right (Nat.mul_le_mul (by omega) hn) 1)
  have bytes := augmented_size_bound F alpha
  have source := Nat.mul_le_mul_left 4 hs
  have extra := Nat.mul_le_mul_left 4 bytes
  dsimp only [L] at loop
  unfold SourceLineMatrixAugmentation.fuel augmentationBudget
  omega
theorem original_input_bound {n : Nat} (F : Family n) (alpha : Affine n) :
    fuel F alpha ≤ costPolynomial.eval (codec.encode ⟨n, [alpha], F⟩).length := by
  have matrix := SourceMatrixConstruction.payloadFuel_bound (augmented F alpha)
  have bounded := SourcePlaneMatrixBudget.payloadBudget_mono
    (SourceDirectionEncoding.dimension_bound n F [alpha]) (augmented_rows_bound F alpha)
  rw [augmented_length] at matrix bounded
  rw [costPolynomial_eval]
  exact Nat.add_le_add (augmentation_bound F alpha) (Nat.le_trans matrix bounded)
theorem original_output_bound {n : Nat} (F : Family n) (alpha : Affine n) :
    ((result F alpha).store.get 8).length ≤
      (2 * (codec.encode ⟨n, [alpha], F⟩).length + 1) *
        ((codec.encode ⟨n, [alpha], F⟩).length * (codec.encode ⟨n, [alpha], F⟩).length) := by
  have hn := SourceDirectionEncoding.dimension_bound n F [alpha]
  have hm := SourceDirectionEncoding.family_bound n F [alpha]
  rw [output_length]
  exact Nat.mul_le_mul (by omega) (Nat.mul_le_mul hn hn)

end PNP.Concrete.ResidualReduction.SourceLineMatrixConstruction
