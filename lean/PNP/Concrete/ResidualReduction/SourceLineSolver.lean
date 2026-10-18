import PNP.Concrete.ResidualReduction.SourceLineSolverHandoff

/-! Solve the complete source-derived rank-one equations with the original
column and basis order. The output is the full computed kernel map, not a
supplied solution. Bounds cover equation construction, the dimension handoff,
elimination and reconstruction. This prepared register-level phase does not
include the two bilinear matrices, constrained selection, raw parsing or the
compiler's word-copy overhead. -/

namespace PNP.Concrete.ResidualReduction.SourceLineSolver
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.SourceLine
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.SourcePlaneMatrixAugmentation (State)
open PNP.Concrete.ResidualReduction.SourcePlaneSolver (solver setSolver lift12 lift12_exec)
open PNP.Concrete.ResidualReduction.SourceLineMatrixAugmentation (start)
open PNP.Concrete.ResidualReduction.SourceDirectionEncoding (codec)

theorem constraint_homogeneous {n : Nat} (F : Family n) (alpha : Affine n) (x y : Point n) :
    homogeneousRow (polarConstraint F alpha x y) = polarConstraint F alpha x y := by
  apply SourceBalance.affine_eval_ext
  intro w
  simp only [homogeneousRow_eval, polarConstraint, linearForm_constant, Bool.xor_false]
theorem homogeneous_rows {n : Nat} (F : Family n) (alpha : Affine n) :
    homogeneous (rankOneRows F alpha) = rankOneRows F alpha := by
  simp only [rankOneRows, homogeneous, List.map_flatMap, List.map_map,
    Function.comp_def, constraint_homogeneous]
theorem solve_kernel {n : Nat} (F : Family n) (alpha : Affine n) :
    solve (n + F.length) (rankOneRows F alpha) = some (kernelSpace (rankOneRows F alpha)) := by
  have checked := kernelSpace_spec (rankOneRows F alpha)
  rw [homogeneous_rows] at checked
  exact checked

def result {n : Nat} (F : Family n) (alpha : Affine n) : State :=
  setSolver (saved F alpha)
    (MatrixSolutionInstructions.result (n + F.length) (rankOneRows F alpha))
theorem solve_exec {n : Nat} (F : Family n) (alpha : Affine n) :
    Exec (lift12 MatrixSolutionInstructions.phase) (ready F alpha).store
      (MatrixSolutionInstructions.phaseFuel (n + F.length) (rankOneRows F alpha)) (result F alpha).store :=
  lift12_exec _ (ready F alpha) _ _
    (MatrixSolutionInstructions.phase_exec (n + F.length) (rankOneRows F alpha))
def block : Block 17 := .seq SourceLineMatrixConstruction.block <|
  .seq prepare (lift12 MatrixSolutionInstructions.phase)
def fuel {n : Nat} (F : Family n) (alpha : Affine n) : Nat :=
  SourceLineMatrixConstruction.fuel F alpha +
    (prepareFuel n + MatrixSolutionInstructions.phaseFuel (n + F.length) (rankOneRows F alpha))
theorem block_exec {n : Nat} (F : Family n) (alpha : Affine n) :
    Exec block (start F alpha).store (fuel F alpha) (result F alpha).store :=
  Exec.seq (SourceLineMatrixConstruction.block_exec F alpha) (Exec.seq (prepare_exec F alpha) (solve_exec F alpha))
theorem result_output {n : Nat} (F : Family n) (alpha : Affine n) :
    (result F alpha).store.get 8 =
      (solutionCodec (n + F.length)).encode (solve (n + F.length) (rankOneRows F alpha)) :=
  MatrixSolutionInstructions.result_output (n + F.length) (rankOneRows F alpha)
theorem result_kernel_output {n : Nat} (F : Family n) (alpha : Affine n) :
    (result F alpha).store.get 8 =
      (solutionCodec (n + F.length)).encode (some (kernelSpace (rankOneRows F alpha))) := by
  rw [result_output, solve_kernel]
theorem result_solver {n : Nat} (F : Family n) (alpha : Affine n) :
    solver (result F alpha) = MatrixSolutionSerialization.result (kernelSpace (rankOneRows F alpha)) := by
  have checked := MatrixKernelSolver.result_eq (n + F.length) (rankOneRows F alpha)
  rw [homogeneous_rows] at checked
  exact checked
theorem retained_dimension {n : Nat} (F : Family n) (alpha : Affine n) :
    (result F alpha).store.get 13 = List.replicate n true := rfl
theorem retained_normal {n : Nat} (F : Family n) (alpha : Affine n) :
    (result F alpha).store.get 16 = affineWord alpha := rfl
theorem retained_source_count {n : Nat} (F : Family n) (alpha : Affine n) :
    (result F alpha).store.get 15 = List.replicate F.length true := rfl
theorem exact_decoded_kernel {n : Nat} (F : Family n) (alpha : Affine n) :
    (solutionCodec (n + F.length)).decode ((result F alpha).store.get 8) =
      some (some (kernelSpace (rankOneRows F alpha))) := by
  rw [result_kernel_output]
  exact solution_roundtrip _ _
theorem kernel_exact {n : Nat} (F : Family n) (alpha : Affine n) (w : Point (n + F.length)) :
    (∀ x y, weightedPolar F (splitPoint F.length w).1 x y =
      wedge alpha (splitPoint F.length w).2 x y) ↔
      ∃ z, (kernelSpace (rankOneRows F alpha)).direction z = w :=
  (rankOneRows_iff F alpha w).symm.trans (kernelSpace_iff (rankOneRows F alpha) w)
def program : Program 17 := block.program 0 8
theorem program_run {n : Nat} (F : Family n) (alpha : Affine n) :
    BitRegister.run program (fuel F alpha + 1) ⟨.running 0, (start F alpha).store⟩ =
      ⟨.accepted, (result F alpha).store⟩ := (block_exec F alpha).program_run 0 8

def solverBudget (L : Nat) : Nat :=
  80 * (2 * L) * (2 * L) * (L * L + 1) + 5 * (L * L) +
    (50 * (2 * L + 2) * (2 * L + 1) + 1) * (2 * L) + 3 * (2 * L) + 20
def jointSizePolynomial : NatPolynomial := .mul (.constant 2) .variable
def solverPolynomial : NatPolynomial :=
  .add (.add (.add (.add
    (.mul (.mul (.mul (.constant 80) jointSizePolynomial) jointSizePolynomial)
      (.add (.mul .variable .variable) (.constant 1)))
    (.mul (.constant 5) (.mul .variable .variable)))
    (.mul (.add (.mul (.mul (.constant 50) (.add jointSizePolynomial (.constant 2)))
      (.add jointSizePolynomial (.constant 1))) (.constant 1)) jointSizePolynomial))
    (.mul (.constant 3) jointSizePolynomial)) (.constant 20)
def costPolynomial : NatPolynomial := .add SourceLineMatrixConstruction.costPolynomial
  (.add (.linear 3 7) solverPolynomial)
theorem solverPolynomial_eval (L : Nat) : solverPolynomial.eval L = solverBudget L := rfl
theorem original_solver_bound {n : Nat} (F : Family n) (alpha : Affine n) :
    MatrixSolutionInstructions.phaseFuel (n + F.length) (rankOneRows F alpha) ≤
      solverBudget (codec.encode ⟨n, [alpha], F⟩).length := by
  let L := (codec.encode ⟨n, [alpha], F⟩).length
  have hn : n ≤ L := SourceDirectionEncoding.dimension_bound n F [alpha]
  have hm : F.length ≤ L := SourceDirectionEncoding.family_bound n F [alpha]
  have hj : n + F.length ≤ 2 * L := by omega
  have rows : (rankOneRows F alpha).length ≤ L * L := by
    rw [rankOneRows_length]
    exact Nat.mul_le_mul hn hn
  have elimination := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 80 hj) hj)
    (Nat.add_le_add_right rows 1)
  have rowWork := Nat.mul_le_mul_left 5 rows
  have reconstruction := Nat.mul_le_mul
    (Nat.add_le_add_right (Nat.mul_le_mul (Nat.mul_le_mul_left 50 (Nat.add_le_add_right hj 2))
      (Nat.add_le_add_right hj 1)) 1) hj
  have linear := Nat.mul_le_mul_left 3 hj
  exact Nat.le_trans (MatrixSolutionInstructions.phaseFuel_bound (n + F.length) (rankOneRows F alpha))
    (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add
      (Nat.add_le_add elimination rowWork) reconstruction) linear) 20)
theorem original_input_bound {n : Nat} (F : Family n) (alpha : Affine n) :
    fuel F alpha ≤ costPolynomial.eval (codec.encode ⟨n, [alpha], F⟩).length := by
  have construction := SourceLineMatrixConstruction.original_input_bound F alpha
  have solving := original_solver_bound F alpha
  have handoff : prepareFuel n ≤ 3 * (codec.encode ⟨n, [alpha], F⟩).length + 7 :=
    Nat.add_le_add_right (Nat.mul_le_mul_left 3 (SourceDirectionEncoding.dimension_bound n F [alpha])) 7
  simp only [costPolynomial, NatPolynomial.eval_add, NatPolynomial.eval_linear, solverPolynomial_eval]
  exact Nat.add_le_add construction (Nat.add_le_add handoff solving)
theorem original_output_bound {n : Nat} (F : Family n) (alpha : Affine n) :
    ((result F alpha).store.get 8).length ≤
      (2 * (codec.encode ⟨n, [alpha], F⟩).length + 1) *
        (2 * (codec.encode ⟨n, [alpha], F⟩).length + 1) + 1 := by
  have hn := SourceDirectionEncoding.dimension_bound n F [alpha]
  have hm := SourceDirectionEncoding.family_bound n F [alpha]
  have hj : n + F.length + 1 ≤ 2 * (codec.encode ⟨n, [alpha], F⟩).length + 1 := by omega
  rw [result_output]
  exact Nat.le_trans (solve_solution_bound (n + F.length) (rankOneRows F alpha))
    (Nat.add_le_add_right (Nat.mul_le_mul hj hj) 1)

end PNP.Concrete.ResidualReduction.SourceLineSolver
