import PNP.Concrete.ResidualReduction.SourceMenuFromFamily
import PNP.Concrete.ResidualReduction.SourceMatrixEncoding

/-! Polynomial instruction and output-size bounds measured from the original
source packet, not from a supplied menu. These account for candidate generation
and the complete insertion fold. Raw-input validation and compiler word-copying
costs still require their own execution linkage. -/

namespace PNP.Concrete.ResidualReduction.SourceMenuBudget
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceChain
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding (codec)

def insertionPolynomial : NatPolynomial :=
  .mul (.add (.mul (.constant 80) (.linear 1 1)) (.constant 80)) (.linear 3 1)
def stepPolynomial : NatPolynomial :=
  .add (.add (.mul (.constant 9) (.linear 1 1)) (.constant 5))
    (.add (.constant 5) (.add insertionPolynomial (.constant 9)))
def sortPolynomial : NatPolynomial :=
  .add (.mul (.add stepPolynomial (.constant 1)) (.linear 3 0)) (.constant 1)
def costPolynomial : NatPolynomial :=
  .add (.add (.mul (.linear 43 53) .variable) (.constant 7))
    (.add (.constant 3) sortPolynomial)

theorem costPolynomial_eval (L : Nat) :
    costPolynomial.eval L = SourceMenuFromFamily.bound L L := by
  simp only [costPolynomial, sortPolynomial, stepPolynomial, insertionPolynomial,
    NatPolynomial.eval_add, NatPolynomial.eval_linear,
    NatPolynomial.eval, Nat.one_mul, Nat.add_zero,
    SourceMenuFromFamily.bound, SourceMenuSort.bound, SourceMenuSortStep.bound,
    SourceMenuSortStep.loadCost, SourceMenuInsertion.bound, Nat.mul_zero, Nat.add_zero]

theorem bounded_cost (n m L : Nat) (dimension : n ≤ L) (rows : m ≤ L) :
    SourceMenuFromFamily.bound n m ≤ costPolynomial.eval L := by
  have inserted := Nat.mul_le_mul
    (show 80 * (n + 1) + 80 ≤ 80 * (L + 1) + 80 by omega)
    (show 3 * m + 1 ≤ 3 * L + 1 by omega)
  have step : SourceMenuSortStep.bound n (3 * m) ≤ SourceMenuSortStep.bound L (3 * L) := by
    simp only [SourceMenuSortStep.bound, SourceMenuSortStep.loadCost,
      SourceMenuInsertion.bound, Nat.mul_zero, Nat.add_zero]
    omega
  have sorted := Nat.mul_le_mul (Nat.add_le_add_right step 1)
    (show 3 * m ≤ 3 * L by omega)
  have generated := Nat.mul_le_mul (show 43 * n + 53 ≤ 43 * L + 53 by omega) rows
  rw [costPolynomial_eval]
  unfold SourceMenuFromFamily.bound SourceMenuSort.bound
  omega

theorem original_input_bound {n : Nat} (F : Family n) :
    SourceMenuFromFamily.bound n F.length ≤ costPolynomial.eval (codec.encode ⟨n, F⟩).length :=
  bounded_cost n F.length _ (SourceMatrixEncoding.dimension_bound n F)
    (SourceMatrixEncoding.rowCount_bound n F)

theorem output_original_bound {n : Nat} (F : Family n) :
    (matrixBits (sourceMenu F)).length ≤ 3 * (codec.encode ⟨n, F⟩).length := by
  have output := SourceMenuFromFamily.output_bound F
  have row := Nat.mul_le_mul_right F.length (show n + 1 ≤ 2 * n + 3 by omega)
  have payload : (n + 1) * F.length ≤ (codec.encode ⟨n, F⟩).length := by
    rw [SourceMatrixEncoding.codec_length]
    omega
  have total := Nat.mul_le_mul_left 3 payload
  have same : (n + 1) * (3 * F.length) = 3 * ((n + 1) * F.length) := by
    rw [Nat.mul_left_comm]
  rw [same] at output
  exact Nat.le_trans output total

theorem block_original_bound {n : Nat} (F : Family n)
    (s : SourceMenuCompare.Saved) (t : SourceMenuSortStep.Held) :
    ∃ used last held, Exec SourceMenuFromFamily.block (SourceMenuFromFamily.initial F s t) used
      (SourceMenuFromFamily.terminal F last held) ∧
      used ≤ costPolynomial.eval (codec.encode ⟨n, F⟩).length := by
  obtain ⟨used, last, held, checked, bound⟩ := SourceMenuFromFamily.block_exec F s t
  exact ⟨used, last, held, checked, Nat.le_trans bound (original_input_bound F)⟩

theorem program_original_bound {n : Nat} (F : Family n)
    (s : SourceMenuCompare.Saved) (t : SourceMenuSortStep.Held) :
    ∃ used last held,
      BitRegister.run SourceMenuFromFamily.program (used + 1) ⟨.running 0, SourceMenuFromFamily.initial F s t⟩ =
        ⟨.accepted, SourceMenuFromFamily.terminal F last held⟩ ∧
      (SourceMenuFromFamily.terminal F last held).get 7 = matrixBits (sourceMenu F) ∧
      used + 1 ≤ costPolynomial.eval (codec.encode ⟨n, F⟩).length + 1 := by
  obtain ⟨used, last, held, checked, output, bound⟩ := SourceMenuFromFamily.program_run F s t
  exact ⟨used, last, held, checked, output,
    Nat.le_trans bound (Nat.add_le_add_right (original_input_bound F) 1)⟩

end PNP.Concrete.ResidualReduction.SourceMenuBudget
