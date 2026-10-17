import PNP.Concrete.ResidualReduction.MatrixHomogeneousInstructions
import PNP.Concrete.ResidualReduction.MatrixInputConsumer
import PNP.Concrete.ResidualReduction.MatrixPolynomialSolver

/-! All-input polynomial computation of the exact homogeneous kernel space.
The source coefficients are parsed and homogenized by literal instructions,
then passed to the existing checked solver. The exact computed basis order is
preserved. This is a shared component of direction construction, not the whole
source direction space, contraction algorithm or a global proof gate. -/

namespace PNP.Concrete.ResidualReduction.MatrixKernelSolver
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.MatrixInputEncoding
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.MatrixReconstruction (State)

def consumer : Block 12 := .seq MatrixHomogeneous.block MatrixSolutionInstructions.phase
def value (n : Nat) (rows : System n) : BitString := (solutionCodec n).encode (some (kernelSpace rows))
def answer (input : BitString) : BitString := MatrixInputConsumer.encodedValue value input
def block : Block 12 := MatrixInputConsumer.block consumer
def consumerBudget (L : Nat) : Nat := (9 * L + 5) + MatrixEncodedSolver.solverBound L
def sourceBudget (L : Nat) : Nat := MatrixInputConsumer.loadBudget L + consumerBudget L

theorem computedSpace_eq (n : Nat) (rows : System n) :
    MatrixReconstruction.computedSpace n (homogeneous rows) = kernelSpace rows := by
  have exactSpace := MatrixReconstruction.computedSpace_exact n (homogeneous rows)
  rw [kernelSpace_spec] at exactSpace
  cases feasible : satisfies (MatrixSweep.residue n (homogeneous rows)) () with
  | false => rw [feasible] at exactSpace; cases exactSpace
  | true => rw [feasible] at exactSpace; exact (Option.some.inj exactSpace).symm
theorem result_eq (n : Nat) (rows : System n) :
    MatrixSolutionInstructions.result n (homogeneous rows) = MatrixSolutionSerialization.result (kernelSpace rows) := by
  simp only [MatrixSolutionInstructions.result, kernelSpace_spec, Option.isSome, if_true, computedSpace_eq]

theorem consumer_exec (n : Nat) (rows : System n) :
    Exec consumer (MatrixSolutionInstructions.start n rows).store
      (MatrixHomogeneous.fuel n rows + MatrixSolutionInstructions.phaseFuel n (homogeneous rows))
      (MatrixSolutionSerialization.result (kernelSpace rows)).store := by
  rw [← result_eq]
  exact Exec.seq (MatrixHomogeneous.block_exec n rows) (MatrixSolutionInstructions.phase_exec n (homogeneous rows))
theorem consumer_bound (n : Nat) (rows : System n) :
    MatrixHomogeneous.fuel n rows + MatrixSolutionInstructions.phaseFuel n (homogeneous rows) ≤
      consumerBudget (codec.encode ⟨n, rows⟩).length := by
  have homogenize := MatrixHomogeneous.fuel_bound n rows
  have count : (homogeneous rows).length ≤ (codec.encode ⟨n, rows⟩).length := by
    simpa only [homogeneous, List.length_map] using rowCount_bound n rows
  have solve := MatrixEncodedSolver.solver_bound n (homogeneous rows) (codec.encode ⟨n, rows⟩).length
    (dimension_bound n rows) count
  exact Nat.add_le_add homogenize solve
theorem consumer_ready (n : Nat) (rows : System n) :
    ∃ used : Nat, ∃ after : State, Exec consumer (MatrixSolutionInstructions.start n rows).store used after.store ∧
      used ≤ consumerBudget (codec.encode ⟨n, rows⟩).length ∧ after.core.output = value n rows := by
  refine ⟨MatrixHomogeneous.fuel n rows + MatrixSolutionInstructions.phaseFuel n (homogeneous rows),
    MatrixSolutionSerialization.result (kernelSpace rows), consumer_exec n rows, consumer_bound n rows, ?_⟩
  have output := MatrixSolutionInstructions.result_output n (homogeneous rows)
  rw [result_eq, kernelSpace_spec] at output
  exact output
theorem block_exec (input : BitString) :
    ∃ used : Nat, ∃ after : State, Exec block (MatrixInputHeaders.start input).store used after.store ∧
      used ≤ sourceBudget input.length ∧ after.core.output = answer input :=
  MatrixInputConsumer.block_exec consumer value consumerBudget consumer_ready input

def program : Program 12 := block.program 0 8
def sourceFuel : NatPolynomial := .add MatrixPolynomialSolver.sourceFuel (.linear 9 5)
theorem sourceFuel_eval (L : Nat) : sourceFuel.eval L = sourceBudget L + 1 := by
  simp only [sourceFuel, NatPolynomial.eval_add, NatPolynomial.eval_linear, MatrixPolynomialSolver.sourceFuel_eval,
    MatrixEncodedSolver.sourceBudget, sourceBudget, MatrixInputConsumer.loadBudget, consumerBudget] <;> omega
private theorem initial_eq (input : BitString) :
    BitRegister.initial program input = ⟨.running 0, (MatrixInputHeaders.start input).store⟩ := rfl
theorem source_result (input : BitString) :
    ∃ after : State, CompilerIO.sourceResult program (sourceFuel.eval input.length) input =
      ⟨.accepted, after.store⟩ ∧ after.core.output = answer input := by
  obtain ⟨fuel, after, checked, bound, output⟩ := block_exec input
  have run : BitRegister.run program (fuel + 1) (BitRegister.initial program input) = ⟨.accepted, after.store⟩ := by
    rw [initial_eq]
    exact checked.program_run 0 8
  have enough : fuel + 1 ≤ sourceFuel.eval input.length := by rw [sourceFuel_eval]; omega
  have slack : sourceFuel.eval input.length = (fuel + 1) + (sourceFuel.eval input.length - (fuel + 1)) := by omega
  refine ⟨after, ?_, output⟩
  unfold CompilerIO.sourceResult
  rw [slack, BitRegister.run_add, run, BitRegister.run_accepted]
theorem acceptsWithin : CompilerIO.AcceptsWithin program sourceFuel := by
  intro input
  obtain ⟨after, run, _⟩ := source_result input
  rw [run]
theorem source_output (input : BitString) :
    (CompilerIO.sourceResult program (sourceFuel.eval input.length) input).store.get 8 = answer input := by
  obtain ⟨after, run, output⟩ := source_result input
  rw [run]
  exact output

def polynomial : PolynomialTimeFunction := CompilerIO.compilePolynomial program sourceFuel acceptsWithin
theorem polynomial_program : polynomial.program =
    .machine (CompilerIO.rawMachine program) (CompilerIO.runtimePolynomial 12 sourceFuel) :=
  CompilerIO.compilePolynomial_program program sourceFuel acceptsWithin
private theorem output_projection (input : BitString) : polynomial.output input =
    (CompilerIO.compilePolynomial program sourceFuel acceptsWithin).output input := rfl
theorem polynomial_output (input : BitString) : polynomial.output input = answer input := by
  rw [output_projection, CompilerIO.compilePolynomial_output]
  exact source_output input
theorem polynomial_canonical (n : Nat) (rows : System n) :
    polynomial.output (codec.encode ⟨n, rows⟩) = (solutionCodec n).encode (some (kernelSpace rows)) := by
  rw [polynomial_output, answer, MatrixInputConsumer.encodedValue, roundtrip]
  rfl
theorem polynomial_malformed (input : BitString) (invalid : codec.decode input = none) :
    polynomial.output input = [false] := by
  rw [polynomial_output, answer, MatrixInputConsumer.encodedValue, invalid]
theorem exact_decoded_kernel (n : Nat) (rows : System n) :
    (solutionCodec n).decode (polynomial.output (codec.encode ⟨n, rows⟩)) = some (some (kernelSpace rows)) := by
  rw [polynomial_canonical]
  exact solution_roundtrip n _
theorem polynomial_machine_accepts (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 12 sourceFuel).eval input.length) input = .accept :=
  CompilerIO.compilePolynomial_accepts program sourceFuel acceptsWithin input
theorem polynomial_output_bound (input : BitString) :
    (polynomial.output input).length ≤ (input.length + 1) * (input.length + 1) + 1 := by
  cases decoded : codec.decode input with
  | none => rw [polynomial_malformed input decoded]; simp only [List.length_cons, List.length_nil]; omega
  | some problem =>
    rcases problem with ⟨n, rows⟩
    have bytes := (canonical input ⟨n, rows⟩).mp decoded
    rw [← bytes, polynomial_canonical]
    have bound := solve_solution_bound n (homogeneous rows)
    rw [kernelSpace_spec] at bound
    have dimension := Nat.succ_le_succ (dimension_bound n rows)
    exact Nat.le_trans bound (Nat.add_le_add_right (Nat.mul_le_mul dimension dimension) 1)

end PNP.Concrete.ResidualReduction.MatrixKernelSolver
