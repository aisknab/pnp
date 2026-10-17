import PNP.Concrete.ResidualReduction.SourcePolarPairInstructions

/-! Construct all basis-indexed polar rows of one arbitrary source row.
Both pullbacks are computed by the literal affine-composition machine before
the coefficient sweep. The map remains an explicit input to this component;
the complete source-derived caller must charge its kernel computation too. -/

namespace PNP.Concrete.ResidualReduction.SourcePolarRowInstructions
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.SourcePolarRowAlgebra
open PNP.Concrete.ResidualReduction.SourcePolarPairInstructions

def idle (n width : Nat) (map output : BitString) : State :=
  ⟨{base width [] with output := output}, List.replicate n true, [], [], [], [], [], map, []⟩
def start {n k : Nat} (row : Row n) (m : AffineMap n k) (output : BitString) : State :=
  {idle n (k + 1) (mapBits m) [] with left := affineWord row.left, right := affineWord row.right, pending := List.replicate k true, savedOutput := output}

def prepareLeft : Block 17 := .seq (.action (.copy 0 15)) (.action (.copy 6 10))
def prepareRight : Block 17 := .seq (.action (.copy 12 8)) <|
  .seq (.action (.clear 8)) <| .seq (.action (.copy 0 15)) (.action (.copy 6 11))
def prepareRows : Block 17 := .seq (.action (.copy 13 8)) (.action (.copy 8 16))
def finish : Block 17 := .seq (.action (.clear 10)) <|
  .seq (.action (.clear 11)) <| .seq (.action (.clear 12)) <|
    .seq (.action (.clear 13)) (.action (.clear 16))

theorem finish_exec {n : Nat} (width : Nat) (row : Row n) (a b : Bool)
    (map output saved : BitString) :
    Exec finish (working (k := 0) width row a b map output saved).store 5
      (idle n width map output).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _)
    (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))))

def block : Block 17 := .seq prepareLeft <|
  .seq (lift MatrixPivotMapInstructions.block) <| .seq prepareRight <|
    .seq (lift MatrixPivotMapInstructions.block) <| .seq prepareRows <|
      .seq SourcePolarPairInstructions.loop finish

def fuel {n : Nat} (k : Nat) (row : Row n) : Nat :=
  2 + (MatrixPivotMapInstructions.fuel k row.left +
    (4 + (MatrixPivotMapInstructions.fuel k row.right +
      (2 + (SourcePolarPairInstructions.fuel n k + 5)))))

theorem block_exec {n k : Nat} (row : Row n) (m : AffineMap n k) (output : BitString) :
    Exec block (start row m output).store (fuel k row)
      (idle n (k + 1) (mapBits m)
        ((matrixBits (pairRows row (pullback row.left m) (pullback row.right m))).reverse ++ output)).store := by
  let before := start row m output
  let leftReady := {before with core := MatrixPivotMapInstructions.start row.left m []}
  let leftDone := {before with core := {base (k + 1) [] with output := affineWord (pullback row.left m)}}
  let rightReady := {before with core := MatrixPivotMapInstructions.start row.right m [], leftCoefficients := affineWord (pullback row.left m)}
  let rightDone := {rightReady with core := {base (k + 1) [] with output := affineWord (pullback row.right m)}}
  let coefficients := working (k + 1) row (pullback row.left m) (pullback row.right m) (mapBits m) output output
  let result := (matrixBits (pairRows row (pullback row.left m) (pullback row.right m))).reverse ++ output
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
  have rows := SourcePolarPairInstructions.loop_exec (k + 1) row (pullback row.left m)
    (pullback row.right m) (mapBits m) output output
  have finished := finish_exec (k + 1) row (aConstant (pullback row.left m))
    (aConstant (pullback row.right m)) (mapBits m) result output
  exact Exec.seq first (Exec.seq left (Exec.seq second (Exec.seq right
    (Exec.seq third (Exec.seq rows finished)))))

theorem space_exec {n : Nat} (row : Row n) (s : Space n) (output : BitString) :
    Exec block (start row s.forms output).store (fuel s.parameters row)
      (idle n (s.parameters + 1) (mapBits s.forms)
        ((matrixBits ((List.finRange s.parameters).map fun j =>
          polarForm row (s.direction (unitPoint _ j)))).reverse ++ output)).store := by
  simpa only [pairRows_pullback] using block_exec row s.forms output

theorem fuel_bound {n k : Nat} (row : Row n) :
    fuel k row ≤ 100 * (k + 2) * (n + 1) := by
  have left := MatrixPivotMapInstructions.fuel_bound k row.left
  have right := MatrixPivotMapInstructions.fuel_bound k row.right
  simp only [fuel, SourcePolarPairInstructions.fuel, Nat.mul_add, Nat.add_mul,
    Nat.mul_one, Nat.mul_assoc, Nat.mul_comm k n] at *
  omega

def program : Program 17 := block.program 0 8
theorem program_run {n k : Nat} (row : Row n) (m : AffineMap n k) (output : BitString) :
    BitRegister.run program (fuel k row + 1) ⟨.running 0, (start row m output).store⟩ =
      ⟨.accepted, (idle n (k + 1) (mapBits m)
        ((matrixBits (pairRows row (pullback row.left m) (pullback row.right m))).reverse ++ output)).store⟩ :=
  (block_exec row m output).program_run 0 8

end PNP.Concrete.ResidualReduction.SourcePolarRowInstructions
