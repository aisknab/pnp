import PNP.Concrete.ResidualReduction.SourceActivityCoefficientInstructions
import PNP.Concrete.ResidualReduction.SourcePolarRowInstructions

/-! The complete activity coefficient row: compute both factor pullbacks,
read the original factor constants and scan all parameter coordinates. This
reuses the existing fixed register frame and returns it in its idle layout. -/

namespace PNP.Concrete.ResidualReduction.SourceActivityRowInstructions
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.SourceActivityMapAlgebra
open PNP.Concrete.ResidualReduction.SourcePolarPairInstructions (State working lift lift_exec)
open PNP.Concrete.ResidualReduction.SourcePolarRowInstructions
  (idle start prepareLeft prepareRight prepareRows finish finish_exec)

def block : Block 17 := .seq prepareLeft <|
  .seq (lift MatrixPivotMapInstructions.block) <| .seq prepareRight <|
    .seq (lift MatrixPivotMapInstructions.block) <| .seq prepareRows <|
      .seq SourceActivityCoefficientInstructions.block finish
def fuel {n : Nat} (k : Nat) (row : Row n) : Nat :=
  2 + (MatrixPivotMapInstructions.fuel k row.left +
    (4 + (MatrixPivotMapInstructions.fuel k row.right +
      (2 + (SourceActivityCoefficientInstructions.fuel n k + 5)))))

theorem block_exec {n k : Nat} (row : Row n) (m : AffineMap n k) (output : BitString) :
    Exec block (start row m output).store (fuel k row)
      (idle n (k + 1) (mapBits m)
        ((bits (aConstant row.left) (aConstant row.right)
          (pullback row.left m) (pullback row.right m)).reverse ++ output)).store := by
  let before := start row m output
  let leftReady := {before with core := MatrixPivotMapInstructions.start row.left m []}
  let leftDone := {before with core := {base (k + 1) [] with output := affineWord (pullback row.left m)}}
  let rightReady := {before with core := MatrixPivotMapInstructions.start row.right m [], leftCoefficients := affineWord (pullback row.left m)}
  let rightDone := {rightReady with core := {base (k + 1) [] with output := affineWord (pullback row.right m)}}
  let coefficients := working (k + 1) row (pullback row.left m) (pullback row.right m) (mapBits m) output output
  let result := (bits (aConstant row.left) (aConstant row.right) (pullback row.left m) (pullback row.right m)).reverse ++ output
  have first : Exec prepareLeft before.store 2 leftReady.store := Exec.seq (.action _ _) (.action _ _)
  have leftCore : Exec MatrixPivotMapInstructions.block leftReady.core.store
      (MatrixPivotMapInstructions.fuel k row.left) leftDone.core.store := by
    simpa only [leftReady, leftDone, List.append_nil] using
      MatrixPivotMapInstructions.construct_exec row.left m []
  have left := lift_exec MatrixPivotMapInstructions.block leftReady _ leftDone.core leftCore
  have second : Exec prepareRight leftDone.store 4 rightReady.store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
  have rightCore : Exec MatrixPivotMapInstructions.block rightReady.core.store
      (MatrixPivotMapInstructions.fuel k row.right) rightDone.core.store := by
    simpa only [rightReady, rightDone, List.append_nil] using
      MatrixPivotMapInstructions.construct_exec row.right m []
  have right := lift_exec MatrixPivotMapInstructions.block rightReady _ rightDone.core rightCore
  have third : Exec prepareRows rightDone.store 2 coefficients.store := Exec.seq (.action _ _) (.action _ _)
  have activity := SourceActivityCoefficientInstructions.block_exec (k + 1) row
    (pullback row.left m) (pullback row.right m) (mapBits m) output output
  have finished := finish_exec (k + 1) row (aConstant (pullback row.left m))
    (aConstant (pullback row.right m)) (mapBits m) result output
  exact Exec.seq first (Exec.seq left (Exec.seq second (Exec.seq right
    (Exec.seq third (Exec.seq activity finished)))))

theorem space_exec {n : Nat} (row : Row n) (s : Space n) (output : BitString) :
    Exec block (start row s.forms output).store (fuel s.parameters row)
      (idle n (s.parameters + 1) (mapBits s.forms)
        (((List.finRange s.parameters).map (activityCoefficients row s)).reverse ++ output)).store := by
  simpa only [bits_pullback] using block_exec row s.forms output
theorem fuel_bound {n k : Nat} (row : Row n) :
    fuel k row ≤ 100 * (k + 2) * (n + 1) := by
  have left := MatrixPivotMapInstructions.fuel_bound k row.left
  have right := MatrixPivotMapInstructions.fuel_bound k row.right
  simp only [fuel, SourceActivityCoefficientInstructions.fuel, Nat.mul_add, Nat.add_mul,
    Nat.mul_one, Nat.mul_assoc, Nat.mul_comm k n] at *
  omega

end PNP.Concrete.ResidualReduction.SourceActivityRowInstructions
