import PNP.Concrete.ResidualReduction.SourcePlaneMatrixBudget

/-! Solve the plane constraints actually constructed from the source. The
handoff preserves the original dimension and normal words and invokes the
existing complete solver, including inconsistency and full map reconstruction.
This is a prepared source-to-solution phase, not the final activity search or
a claim that every residual input has a useful contraction. -/

namespace PNP.Concrete.ResidualReduction.SourcePlaneSolver
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.SourcePlaneMatrixAugmentation
open PNP.Concrete.ResidualReduction.SourceDirectionEncoding (codec)

def solver (r : State) : MatrixReconstruction.State := r.core.core.core
def setSolver (r : State) (value : MatrixReconstruction.State) : State :=
  {r with core := {r.core with core := {r.core.core with core := value}}}
def lift12 (body : Block 12) : Block 17 := lift16 (SourceMatrixPacket.lift12 body)
theorem lift12_exec (body : Block 12) (r : State) (fuel : Nat) (after : MatrixReconstruction.State)
    (checked : Exec body (solver r).store fuel after.store) :
    Exec (lift12 body) r.store fuel (setSolver r after).store :=
  lift16_exec _ r fuel _ (SourceMatrixPacket.lift12_exec body r.core fuel after checked)

def saved {n : Nat} (F : Family n) (a b : Affine n) : State :=
  let r := SourcePlaneMatrixConstruction.result F a b
  {r with core := {r.core with core := {r.core.core with outer := List.replicate n true}}}
def ready {n : Nat} (F : Family n) (a b : Affine n) : State :=
  setSolver (saved F a b) (MatrixSolutionInstructions.start F.length (SourcePlane.planeRows F a b))
def result {n : Nat} (F : Family n) (a b : Affine n) : State :=
  setSolver (saved F a b) (MatrixSolutionInstructions.result F.length (SourcePlane.planeRows F a b))
def copyData : Block 17 := .seq (.action (.copy 0 8)) <|
  .seq (.action (.copy 7 8)) (.action (.clear 8))
def counters : Block 17 := .seq (.action (.copy 1 15)) <|
  .seq (.action (.copy 9 15)) (.action (.clear 10))
def prepare : Block 17 := .seq (.action (.copy 13 9)) (.seq copyData counters)
theorem prepare_exec {n : Nat} (F : Family n) (a b : Affine n) :
    Exec prepare (SourcePlaneMatrixConstruction.result F a b).store 7 (ready F a b).store := by
  let moved := setRegisters (saved F a b)
    {registers (saved F a b) with input := matrixBits (SourcePlane.planeRows F a b), reserved := matrixBits (SourcePlane.planeRows F a b), output := []}
  have dimension : Exec (.action (.copy (13 : Fin 17) 9))
      (SourcePlaneMatrixConstruction.result F a b).store 1 (saved F a b).store := .action _ _
  have data : Exec copyData (saved F a b).store 3 moved.store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have reset : Exec counters moved.store 3 (ready F a b).store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  exact Exec.seq dimension (Exec.seq data reset)
theorem solve_exec {n : Nat} (F : Family n) (a b : Affine n) :
    Exec (lift12 MatrixSolutionInstructions.phase) (ready F a b).store
      (MatrixSolutionInstructions.phaseFuel F.length (SourcePlane.planeRows F a b)) (result F a b).store :=
  lift12_exec _ (ready F a b) _ _ (MatrixSolutionInstructions.phase_exec F.length (SourcePlane.planeRows F a b))

def block : Block 17 := .seq SourcePlaneMatrixConstruction.block <|
  .seq prepare (lift12 MatrixSolutionInstructions.phase)
def fuel {n : Nat} (F : Family n) (a b : Affine n) : Nat :=
  SourcePlaneMatrixConstruction.fuel F a b +
    (7 + MatrixSolutionInstructions.phaseFuel F.length (SourcePlane.planeRows F a b))
theorem block_exec {n : Nat} (F : Family n) (a b : Affine n) :
    Exec block (start F a b).store (fuel F a b) (result F a b).store :=
  Exec.seq (SourcePlaneMatrixConstruction.block_exec F a b) (Exec.seq (prepare_exec F a b) (solve_exec F a b))
theorem result_output {n : Nat} (F : Family n) (a b : Affine n) :
    (result F a b).store.get 8 = (solutionCodec F.length).encode (solve F.length (SourcePlane.planeRows F a b)) :=
  MatrixSolutionInstructions.result_output F.length (SourcePlane.planeRows F a b)
theorem retained_dimension {n : Nat} (F : Family n) (a b : Affine n) :
    (result F a b).store.get 13 = List.replicate n true := rfl
theorem retained_normals {n : Nat} (F : Family n) (a b : Affine n) :
    (result F a b).store.get 16 = matrixBits [a, b] := rfl
theorem retained_source_count {n : Nat} (F : Family n) (a b : Affine n) :
    (result F a b).store.get 15 = List.replicate F.length true := rfl
def program : Program 17 := block.program 0 8
theorem program_run {n : Nat} (F : Family n) (a b : Affine n) :
    BitRegister.run program (fuel F a b + 1) ⟨.running 0, (start F a b).store⟩ =
      ⟨.accepted, (result F a b).store⟩ := (block_exec F a b).program_run 0 8

def solverBudget (L : Nat) : Nat :=
  80 * L * L * (L * L + 1) + 5 * (L * L) +
    (50 * (L + 2) * (L + 1) + 1) * L + 3 * L + 20
def solverPolynomial : NatPolynomial :=
  .add (.add (.add (.add
    (.mul (.mul (.mul (.constant 80) .variable) .variable) (.add (.mul .variable .variable) (.constant 1)))
    (.mul (.constant 5) (.mul .variable .variable)))
    (.mul (.add (.mul (.mul (.constant 50) (.add .variable (.constant 2)))
      (.add .variable (.constant 1))) (.constant 1)) .variable))
    (.mul (.constant 3) .variable)) (.constant 20)
def costPolynomial : NatPolynomial := .add SourcePlaneMatrixBudget.costPolynomial
  (.add (.constant 7) solverPolynomial)
theorem solverPolynomial_eval (L : Nat) : solverPolynomial.eval L = solverBudget L := rfl
theorem original_solver_bound {n : Nat} (F : Family n) (a b : Affine n) :
    MatrixSolutionInstructions.phaseFuel F.length (SourcePlane.planeRows F a b) ≤
      solverBudget (codec.encode ⟨n, [a, b], F⟩).length := by
  let L := (codec.encode ⟨n, [a, b], F⟩).length
  have hm : F.length ≤ L := SourceDirectionEncoding.family_bound n F [a, b]
  have hn : n ≤ L := SourceDirectionEncoding.dimension_bound n F [a, b]
  have rows : (SourcePlane.planeRows F a b).length ≤ L * L := by
    rw [SourcePlane.planeRows_length]
    exact Nat.mul_le_mul hn hn
  have elimination := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 80 hm) hm)
    (Nat.add_le_add_right rows 1)
  have rowWork := Nat.mul_le_mul_left 5 rows
  have reconstruction := Nat.mul_le_mul
    (Nat.add_le_add_right (Nat.mul_le_mul (Nat.mul_le_mul_left 50 (Nat.add_le_add_right hm 2))
      (Nat.add_le_add_right hm 1)) 1) hm
  have linear := Nat.mul_le_mul_left 3 hm
  have checked := MatrixSolutionInstructions.phaseFuel_bound F.length (SourcePlane.planeRows F a b)
  exact Nat.le_trans checked
    (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add
      (Nat.add_le_add elimination rowWork) reconstruction) linear) 20)
theorem original_input_bound {n : Nat} (F : Family n) (a b : Affine n) :
    fuel F a b ≤ costPolynomial.eval (codec.encode ⟨n, [a, b], F⟩).length := by
  have construction := SourcePlaneMatrixBudget.original_input_bound F a b
  have solving := original_solver_bound F a b
  simp only [costPolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant, solverPolynomial_eval]
  exact Nat.add_le_add construction (Nat.add_le_add_left solving 7)

end PNP.Concrete.ResidualReduction.SourcePlaneSolver
