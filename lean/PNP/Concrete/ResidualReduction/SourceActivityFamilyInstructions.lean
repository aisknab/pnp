import PNP.Concrete.ResidualReduction.SourceActivityRowInstructions
import PNP.Concrete.ResidualReduction.SourcePolarFamilyInstructions

/-! Construct all activity coefficients of an arbitrary source family and
direction map. The existing source-row loader and final reordering routine
are reused. Every row and parameter coefficient is charged, including empty
and zero-dimensional cases. A source-derived caller must compute the map. -/

namespace PNP.Concrete.ResidualReduction.SourceActivityFamilyInstructions
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.SourceActivityMapAlgebra
open PNP.Concrete.ResidualReduction.SourcePolarRowInstructions (start)
open PNP.Concrete.ResidualReduction.SourcePolarFamilyInstructions
  (State ready load loadFuel load_exec lift lift_exec reorder reorder_exec)

def row : Block 18 := .seq load (lift SourceActivityRowInstructions.block)
theorem row_exec {n k : Nat} (r : Row n) (m : AffineMap n k) (suffix output : BitString) :
    Exec row (ready n k (mapBits m) (rowWord r ++ suffix) output).store
      (loadFuel n + SourceActivityRowInstructions.fuel k r)
      (ready n k (mapBits m) suffix
        ((bits (aConstant r.left) (aConstant r.right)
          (pullback r.left m) (pullback r.right m)).reverse ++ output)).store :=
  Exec.seq (load_exec r m suffix output)
    (lift_exec SourceActivityRowInstructions.block ⟨start r m output, suffix⟩ _ _
      (SourceActivityRowInstructions.block_exec r m output))

def loop : Block 18 := .loop 17 row
def loopFuel {n : Nat} (k : Nat) : Family n → Nat
  | [] => 1
  | r :: F => 1 + ((loadFuel n + SourceActivityRowInstructions.fuel k r) + loopFuel k F)
theorem loop_exec {n : Nat} (F : Family n) (s : Space n) (output : BitString) :
    Exec loop (ready n s.parameters (mapBits s.forms) (familyBits F) output).store
      (loopFuel s.parameters F)
      (ready n s.parameters (mapBits s.forms) [] ((sourceBits F s).reverse ++ output)).store := by
  induction F generalizing output with
  | nil => exact Exec.loopStop rfl
  | cons r F ih =>
    have first := row_exec r s.forms (familyBits F) output
    have rest := ih ((bits (aConstant r.left) (aConstant r.right)
      (pullback r.left s.forms) (pullback r.right s.forms)).reverse ++ output)
    have checked := Exec.loopStep (source := (17 : Fin 18)) rfl first rest
    simpa only [loop, loopFuel, familyBits, sourceBits, List.flatMap_cons,
      List.reverse_append, List.append_assoc] using checked

theorem rowFuel_bound {n k : Nat} (r : Row n) :
    loadFuel n + SourceActivityRowInstructions.fuel k r ≤ 130 * (k + 2) * (n + 1) := by
  have bound := SourceActivityRowInstructions.fuel_bound (k := k) r
  simp only [loadFuel, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.mul_assoc, Nat.mul_comm k n] at *
  omega
theorem loopFuel_bound {n : Nat} (k : Nat) (F : Family n) :
    loopFuel k F ≤ (130 * (k + 2) * (n + 1) + 1) * F.length + 1 := by
  induction F with
  | nil => simp only [loopFuel, List.length_nil, Nat.mul_zero, Nat.zero_add, Nat.le_refl]
  | cons r F ih =>
    have one := rowFuel_bound (k := k) r
    have arithmetic (C m x y : Nat) (hx : x ≤ C) (hy : y ≤ (C + 1) * m + 1) :
        1 + (x + y) ≤ (C + 1) * (m + 1) + 1 := by
      rw [Nat.mul_succ]
      omega
    exact arithmetic (130 * (k + 2) * (n + 1)) F.length
      (loadFuel n + SourceActivityRowInstructions.fuel k r) (loopFuel k F) one ih

def block : Block 18 := .seq loop reorder
def fuel {n : Nat} (F : Family n) (s : Space n) : Nat :=
  loopFuel s.parameters F + (4 * (sourceBits F s).length + 3)
theorem block_exec {n : Nat} (F : Family n) (s : Space n) :
    Exec block (ready n s.parameters (mapBits s.forms) (familyBits F) []).store
      (fuel F s) (ready n s.parameters (mapBits s.forms) [] (sourceBits F s)).store := by
  have rows := loop_exec F s []
  simp only [List.append_nil] at rows
  exact Exec.seq rows (reorder_exec n s.parameters (mapBits s.forms) (sourceBits F s))
theorem matrix_exec {n : Nat} (F : Family n) (s : Space n) :
    Exec block (ready n s.parameters (mapBits s.forms) (familyBits F) []).store
      (fuel F s) (ready n s.parameters (mapBits s.forms) []
        (coefficientMatrixBits (activityMatrix s F))).store := by
  simpa only [sourceBits_matrix] using block_exec F s
theorem fuel_bound {n : Nat} (F : Family n) (s : Space n) :
    fuel F s ≤ (130 * (s.parameters + 2) * (n + 1) + 1) * F.length + 1 +
      (4 * (F.length * s.parameters) + 3) := by
  unfold fuel
  rw [sourceBits_length]
  exact Nat.add_le_add_right (loopFuel_bound s.parameters F) _
def program : Program 18 := block.program 0 8
theorem program_run {n : Nat} (F : Family n) (s : Space n) :
    BitRegister.run program (fuel F s + 1)
      ⟨.running 0, (ready n s.parameters (mapBits s.forms) (familyBits F) []).store⟩ =
        ⟨.accepted, (ready n s.parameters (mapBits s.forms) [] (sourceBits F s)).store⟩ :=
  (block_exec F s).program_run 0 8

end PNP.Concrete.ResidualReduction.SourceActivityFamilyInstructions
