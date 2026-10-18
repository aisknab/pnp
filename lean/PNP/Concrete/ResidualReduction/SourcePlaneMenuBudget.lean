import PNP.Concrete.ResidualReduction.SourcePlaneMenu
import PNP.Concrete.ResidualReduction.SourceMenuBudget

/-! Polynomial instruction and output bounds for the complete ordered pair
constructor. Counts are derived from the source family, not supplied as runtime
or coverage certificates. Compiler word-copy costs remain a separate boundary. -/

namespace PNP.Concrete.ResidualReduction.SourcePlaneMenuBudget
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceChain
open PNP.Concrete.ResidualReduction.SourcePlaneMenuBytes
open PNP.Concrete.ResidualReduction.SourcePlaneMenu
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding (codec)

def scanPolynomial : NatPolynomial :=
  .add (.mul (.add (.mul (.constant 50) (.linear 1 1)) (.constant 41)) (.linear 3 0)) (.constant 1)
def stepPolynomial : NatPolynomial :=
  .add (.add (.mul (.constant 9) (.linear 1 1)) (.constant 5))
    (.add (.constant 3) (.add scanPolynomial (.constant 3)))
def loopPolynomial : NatPolynomial :=
  .add (.mul (.add stepPolynomial (.constant 1)) (.linear 3 0)) (.constant 1)
def outputPolynomial : NatPolynomial :=
  .mul (.mul (.constant 2) (.linear 1 1)) (.mul (.linear 3 0) (.linear 3 0))
def costPolynomial : NatPolynomial :=
  .add (.constant 1) (.add loopPolynomial (.add (.mul (.constant 4) outputPolynomial) (.constant 4)))

theorem costPolynomial_eval (L : Nat) : costPolynomial.eval L = bound L (3 * L) := by
  simp only [costPolynomial, loopPolynomial, stepPolynomial, scanPolynomial, outputPolynomial,
    NatPolynomial.eval_add, NatPolynomial.eval_linear, NatPolynomial.eval, Nat.add_zero,
    Nat.one_mul, Nat.add_assoc,
    bound, loopBound, stepBound, SourceMenuSortStep.loadCost,
    SourcePlaneMenuScan.bound, SourcePlaneMenuScan.stepBound]

theorem outputPolynomial_eval (L : Nat) :
    outputPolynomial.eval L = (2 * (L + 1)) * ((3 * L) * (3 * L)) := by
  simp only [outputPolynomial, NatPolynomial.eval_linear, NatPolynomial.eval, Nat.add_zero, Nat.one_mul]

theorem bounded_output (n k L : Nat) (dimension : n ≤ L) (records : k ≤ 3 * L) :
    (2 * (n + 1)) * (k * k) ≤ outputPolynomial.eval L := by
  rw [outputPolynomial_eval]
  exact Nat.mul_le_mul (by omega) (Nat.mul_le_mul records records)

theorem bounded_cost (n k L : Nat) (dimension : n ≤ L) (records : k ≤ 3 * L) :
    bound n k ≤ costPolynomial.eval L := by
  have inner := Nat.mul_le_mul
    (show SourcePlaneMenuScan.stepBound n + 1 ≤ SourcePlaneMenuScan.stepBound L + 1 by
      unfold SourcePlaneMenuScan.stepBound; omega) records
  have step : stepBound n k ≤ stepBound L (3 * L) := by
    simp only [stepBound, SourceMenuSortStep.loadCost, SourcePlaneMenuScan.bound]
    omega
  have outer := Nat.mul_le_mul (Nat.add_le_add_right step 1) records
  have bytes := bounded_output n k L dimension records
  rw [outputPolynomial_eval] at bytes
  have copied := Nat.mul_le_mul_left 4 bytes
  rw [costPolynomial_eval]
  unfold bound loopBound
  omega

theorem original_input_bound {n : Nat} (F : Family n) :
    bound n (sourceMenu F).length ≤ costPolynomial.eval (codec.encode ⟨n, F⟩).length := by
  have count := sourceMenu_length_le F
  have rows := SourceMatrixEncoding.rowCount_bound n F
  exact bounded_cost n (sourceMenu F).length _
    (SourceMatrixEncoding.dimension_bound n F) (by omega)

theorem output_original_bound {n : Nat} (F : Family n) :
    (pairBits (planeMenu (sourceMenu F))).length ≤
      outputPolynomial.eval (codec.encode ⟨n, F⟩).length := by
  have count := sourceMenu_length_le F
  have rows := SourceMatrixEncoding.rowCount_bound n F
  exact Nat.le_trans (menu_bytes_length (sourceMenu F))
    (bounded_output n (sourceMenu F).length _ (SourceMatrixEncoding.dimension_bound n F) (by omega))

theorem block_original_bound {n : Nat} (F : Family n)
    (s : SourceMenuCompare.Saved) (t : Held) :
    ∃ used last held, Exec block (full (initial (sourceMenu F) []) s t) used
      (full (result (sourceMenu F)) last ⟨held, MatrixInstructions.matrixBits (sourceMenu F)⟩) ∧
      used ≤ costPolynomial.eval (codec.encode ⟨n, F⟩).length := by
  obtain ⟨used, last, held, checked, budget⟩ :=
    block_exec (sourceMenu F) (SourceMenuOrder.source_menu_homogeneous F) s t
  exact ⟨used, last, held, checked, Nat.le_trans budget (original_input_bound F)⟩

end PNP.Concrete.ResidualReduction.SourcePlaneMenuBudget
