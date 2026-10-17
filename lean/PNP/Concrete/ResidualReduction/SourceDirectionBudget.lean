import PNP.Concrete.ResidualReduction.SourceDirectionInstructions

/-! The complete prepared direction construction has a source-instruction
bound in the length of its original encoded family and normals. Both actual
kernels and every generated coefficient are charged. A separate raw parser
and CompilerIO theorem are still required for the all-bitstring machine. -/

namespace PNP.Concrete.ResidualReduction.SourceDirectionBudget
open PNP.Concrete
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.SourceDirectionEncoding
open PNP.Concrete.ResidualReduction.SourceDirectionInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding

def familyBudget (L : Nat) : Nat :=
  (130 * (L + 2) * (L + 1) + 1) * L + 1 + (4 * ((L + 1) * (L * L)) + 3)
def budget (L : Nat) : Nat :=
  MatrixKernelSolver.sourceFuel.eval L + 5 + familyBudget L + (4 * L + 8) +
    MatrixKernelSolver.sourceFuel.eval (matrixPacketBound L)

theorem kernel_bound (n : Nat) (U : System n) :
    kernelFuel n U ≤ MatrixKernelSolver.sourceFuel.eval (MatrixInputEncoding.codec.encode ⟨n, U⟩).length := by
  have computed := MatrixKernelSolver.consumer_bound n U
  rw [MatrixKernelSolver.sourceFuel_eval]
  unfold kernelFuel MatrixKernelSolver.sourceBudget
  omega

theorem family_bound {n : Nat} (F : Family n) (U : System n) :
    SourcePolarFamilyInstructions.fuel F (kernelSpace U) ≤
      familyBudget (codec.encode ⟨n, U, F⟩).length := by
  let L := (codec.encode ⟨n, U, F⟩).length
  have hn : n ≤ L := dimension_bound n F U
  have hm : F.length ≤ L := SourceDirectionEncoding.family_bound n F U
  have hk : (kernelSpace U).parameters ≤ L := Nat.le_trans (kernelSpace_parameter_bound U) hn
  have coefficient : 130 * ((kernelSpace U).parameters + 2) * (n + 1) ≤ 130 * (L + 2) * (L + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 130 (Nat.add_le_add_right hk 2)) (Nat.add_le_add_right hn 1)
  have scan := Nat.mul_le_mul (Nat.add_le_add_right coefficient 1) hm
  have payload := Nat.mul_le_mul (Nat.add_le_add_right hn 1) (Nat.mul_le_mul hm hk)
  exact Nat.le_trans (SourcePolarFamilyInstructions.fuel_bound F (kernelSpace U))
    (Nat.add_le_add (Nat.add_le_add_right scan 1) (Nat.add_le_add_right (Nat.mul_le_mul_left 4 payload) 3))

theorem fuel_bound {n : Nat} (F : Family n) (U : System n) :
    fuel F U ≤ budget (codec.encode ⟨n, U, F⟩).length := by
  have first := Nat.le_trans (kernel_bound n U)
    (NatPolynomial.eval_mono MatrixKernelSolver.sourceFuel (normals_packet_bound n F U))
  have second := Nat.le_trans (kernel_bound n (directionSystem F U))
    (NatPolynomial.eval_mono MatrixKernelSolver.sourceFuel (direction_packet_bound n F U))
  have constructed := family_bound F U
  have normalBytes := normals_payload_bound n F U
  unfold fuel budget
  omega

def rowPolynomial : NatPolynomial := .add .variable (.mul .variable .variable)
def matrixPolynomial : NatPolynomial :=
  .add (.add (.add .variable (.constant 1)) (.add rowPolynomial (.constant 1)))
    (.mul (.add .variable (.constant 1)) rowPolynomial)
theorem rowPolynomial_eval (L : Nat) : rowPolynomial.eval L = rowBound L := rfl
theorem matrixPolynomial_eval (L : Nat) : matrixPolynomial.eval L = matrixPacketBound L := rfl

def familyPolynomial : NatPolynomial :=
  .add (.add (.mul (.add (.mul (.mul (.constant 130) (.add .variable (.constant 2)))
    (.add .variable (.constant 1))) (.constant 1)) .variable) (.constant 1))
    (.add (.mul (.constant 4) (.mul (.add .variable (.constant 1)) (.mul .variable .variable))) (.constant 3))
theorem familyPolynomial_eval (L : Nat) : familyPolynomial.eval L = familyBudget L := rfl

/-- A finite polynomial expression, not a claim about a supplied cost oracle.
It bounds this prepared phase only; parser costs must be added by its caller. -/
def costPolynomial : NatPolynomial :=
  .add (.add (.add (.add MatrixKernelSolver.sourceFuel (.constant 5)) familyPolynomial)
    (.add (.mul (.constant 4) .variable) (.constant 8)))
    (NatPolynomial.substitute MatrixKernelSolver.sourceFuel matrixPolynomial)
theorem costPolynomial_eval (L : Nat) : costPolynomial.eval L = budget L := by
  simp only [costPolynomial, NatPolynomial.eval_add, NatPolynomial.eval_mul,
    NatPolynomial.eval_variable, NatPolynomial.eval_constant, NatPolynomial.eval_substitute,
    matrixPolynomial_eval, familyPolynomial_eval, budget]
theorem original_input_bound {n : Nat} (F : Family n) (U : System n) :
    fuel F U ≤ costPolynomial.eval (codec.encode ⟨n, U, F⟩).length := by
  rw [costPolynomial_eval]
  exact fuel_bound F U

theorem output_bound {n : Nat} (F : Family n) (U : System n) :
    ((result F U).store.get 8).length ≤
      ((codec.encode ⟨n, U, F⟩).length + 1) * ((codec.encode ⟨n, U, F⟩).length + 1) + 1 := by
  rw [result_output]
  have checked := solve_solution_bound n (homogeneous (directionSystem F U))
  rw [kernelSpace_spec] at checked
  have dimension := Nat.add_le_add_right (dimension_bound n F U) 1
  exact Nat.le_trans checked (Nat.add_le_add_right (Nat.mul_le_mul dimension dimension) 1)

end PNP.Concrete.ResidualReduction.SourceDirectionBudget
