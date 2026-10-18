import PNP.Concrete.ResidualReduction.SourceLinePullbackInstructions

/-! Original-input bounds for the entire prepared pullback construction:
source direction and query matrices, rank-one equations and elimination,
the exact empty-system kernel, all transfers and both coefficient transforms.
These count source instructions, not a completed raw line-query machine or
the entire residual-contraction algorithm. -/

namespace PNP.Concrete.ResidualReduction.SourceLinePullback
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.SourceLineQueryMatrixAlgebra (coefficientMatrixBits_length)
open PNP.Concrete.ResidualReduction.SourceDirectionEncoding (codec)

def solverCostPolynomial : NatPolynomial :=
  .add (.add (.add (.add
    (.mul (.mul (.mul (.constant 80) .variable) .variable) (.add .variable (.constant 1)))
    (.mul (.constant 5) .variable))
    (.mul (.add (.mul (.mul (.constant 50) (.add .variable (.constant 2)))
      (.add .variable (.constant 1))) (.constant 1)) .variable))
    (.mul (.constant 3) .variable)) (.constant 20)
theorem solverCostPolynomial_eval (L : Nat) :
    solverCostPolynomial.eval L = MatrixEncodedSolver.solverBound L := rfl
theorem right_original_bound {n : Nat} (F : Family n) (alpha : Affine n) :
    rightFuel F alpha ≤ solverCostPolynomial.eval (codec.encode ⟨n, [alpha], F⟩).length := by
  rw [solverCostPolynomial_eval]
  exact MatrixEncodedSolver.solver_bound (directionSpace F [alpha]).parameters []
    (codec.encode ⟨n, [alpha], F⟩).length (SourceLineQueryMatrices.parameter_bound F alpha) (Nat.zero_le _)
theorem pull_original_bound {n : Nat} (F : Family n) (alpha : Affine n) :
    pullFuel F alpha ≤ SourceBilinearPullback.costPolynomial.eval
      (2 * (codec.encode ⟨n, [alpha], F⟩).length) :=
  SourceBilinearPullback.original_line_bound F alpha

def costPolynomial : NatPolynomial :=
  .add (.add SourceLineQueryMatrices.costPolynomial SourceLineSolver.costPolynomial)
    (.add solverCostPolynomial
      (.add (.mul (.constant 2) (NatPolynomial.substitute SourceBilinearPullback.costPolynomial
        (.mul (.constant 2) .variable))) (.constant 68)))
theorem original_input_bound {n : Nat} (F : Family n) (alpha : Affine n) :
    fuel F alpha ≤ costPolynomial.eval (codec.encode ⟨n, [alpha], F⟩).length := by
  have matrices := SourceLineQueryMatrices.original_input_bound F alpha
  have left := SourceLineSolver.original_input_bound F alpha
  have right := right_original_bound F alpha
  have transformed := pull_original_bound F alpha
  simp only [costPolynomial, NatPolynomial.eval_add, NatPolynomial.eval_mul,
    NatPolynomial.eval_constant, NatPolynomial.eval_variable, NatPolynomial.eval_substitute]
  unfold fuel kernelsFuel
  omega

theorem left_parameter_bound {n : Nat} (F : Family n) (alpha : Affine n) :
    (leftSpace F alpha).parameters ≤ 2 * (codec.encode ⟨n, [alpha], F⟩).length := by
  have computed := kernelSpace_parameter_bound (SourceLine.rankOneRows F alpha)
  have dimension := SourceDirectionEncoding.dimension_bound n F [alpha]
  have family := SourceDirectionEncoding.family_bound n F [alpha]
  change (kernelSpace (SourceLine.rankOneRows F alpha)).parameters ≤ _
  omega
theorem right_parameter_bound {n : Nat} (F : Family n) (alpha : Affine n) :
    (rightSpace F alpha).parameters ≤ (codec.encode ⟨n, [alpha], F⟩).length :=
  Nat.le_trans (kernelSpace_parameter_bound ([] : System (directionSpace F [alpha]).parameters))
    (SourceLineQueryMatrices.parameter_bound F alpha)
private theorem transformed_size_bound {n : Nat} (F : Family n) (alpha : Affine n) :
    (leftSpace F alpha).parameters * (rightSpace F alpha).parameters ≤
      2 * ((codec.encode ⟨n, [alpha], F⟩).length * (codec.encode ⟨n, [alpha], F⟩).length) := by
  have checked := Nat.mul_le_mul (left_parameter_bound F alpha) (right_parameter_bound F alpha)
  simpa only [Nat.mul_assoc] using checked
theorem normal_output_bound {n : Nat} (F : Family n) (alpha : Affine n) :
    ((result F alpha).get 36).length ≤
      2 * ((codec.encode ⟨n, [alpha], F⟩).length * (codec.encode ⟨n, [alpha], F⟩).length) := by
  rw [result_normal, coefficientMatrixBits_length]
  exact transformed_size_bound F alpha
theorem activity_output_bound {n : Nat} (F : Family n) (alpha : Affine n) :
    ((result F alpha).get 37).length ≤
      2 * ((codec.encode ⟨n, [alpha], F⟩).length * (codec.encode ⟨n, [alpha], F⟩).length) := by
  rw [result_activity, coefficientMatrixBits_length]
  exact transformed_size_bound F alpha

theorem program_original_bound {n : Nat} (F : Family n) (alpha : Affine n) :
    ∃ steps ≤ costPolynomial.eval (codec.encode ⟨n, [alpha], F⟩).length + 1,
      BitRegister.run program steps ⟨.running 0, start F alpha⟩ =
        ⟨.accepted, result F alpha⟩ :=
  ⟨fuel F alpha + 1, Nat.add_le_add_right (original_input_bound F alpha) 1, program_run F alpha⟩

end PNP.Concrete.ResidualReduction.SourceLinePullback
