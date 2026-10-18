import PNP.Concrete.ResidualReduction.MatrixEncodedSolver
import PNP.Concrete.BitRegisterCompilerIOPolynomial

/-! An all-input concrete polynomial-time binary linear solver. The executable
object is a literal raw machine compiled from one fixed finite register program.
Its accepting-fuel proof includes strict parsing, all malformed branches,
elimination, construction of the full solution map, and canonical serialization.
This solves linear matrices, not the global source-contraction or SAT problem. -/

namespace PNP.Concrete.ResidualReduction.MatrixPolynomialSolver
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixReconstruction
open PNP.Concrete.ResidualReduction.MatrixInputEncoding
open PNP.Concrete.ResidualReduction.MatrixEncodedSolver

def program : Program 12 := MatrixEncodedSolver.block.program 0 8

/-- Includes the final accept instruction. Word-copy costs are accounted for
by the literal compiler's separate raw-machine polynomial, not treated as free. -/
def sourceFuel : NatPolynomial :=
  .add (.add
    (.mul (.constant 130) (.mul .variable (.mul .variable .variable)))
    (.mul (.constant 238) (.mul .variable .variable))) (.linear 133 57)

theorem sourceFuel_eval (length : Nat) : sourceFuel.eval length = sourceBudget length + 1 := by
  simp only [sourceFuel, NatPolynomial.eval_add, NatPolynomial.eval_mul,
    NatPolynomial.eval_constant, NatPolynomial.eval_variable, NatPolynomial.eval_linear,
    sourceBudget, solverBound, MatrixInputPayload.fuel,
    Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul, Nat.mul_assoc]
  omega

private theorem initial_eq (input : BitString) :
    BitRegister.initial program input = ⟨.running 0, (MatrixInputHeaders.start input).store⟩ := rfl

theorem source_result (input : BitString) :
    ∃ after : State, CompilerIO.sourceResult program (sourceFuel.eval input.length) input =
      ⟨.accepted, after.store⟩ ∧ after.core.output = solveEncoded input := by
  obtain ⟨fuel, after, checked, bound, output⟩ := MatrixEncodedSolver.block_exec input
  have run : BitRegister.run program (fuel + 1) (BitRegister.initial program input) =
      ⟨.accepted, after.store⟩ := by
    rw [initial_eq]
    exact checked.program_run 0 8
  have enough : fuel + 1 ≤ sourceFuel.eval input.length := by rw [sourceFuel_eval]; omega
  have slack : sourceFuel.eval input.length =
      (fuel + 1) + (sourceFuel.eval input.length - (fuel + 1)) := by omega
  refine ⟨after, ?_, output⟩
  unfold CompilerIO.sourceResult
  rw [slack, BitRegister.run_add, run, BitRegister.run_accepted]

theorem acceptsWithin : CompilerIO.AcceptsWithin program sourceFuel := by
  intro input
  obtain ⟨after, run, _⟩ := source_result input
  rw [run]

theorem source_output (input : BitString) :
    (CompilerIO.sourceResult program (sourceFuel.eval input.length) input).store.get 8 =
      solveEncoded input := by
  obtain ⟨after, run, output⟩ := source_result input
  rw [run]
  exact output

def polynomial : PolynomialTimeFunction :=
  CompilerIO.compilePolynomial program sourceFuel acceptsWithin

theorem polynomial_program :
    polynomial.program =
      .machine (CompilerIO.rawMachine program) (CompilerIO.runtimePolynomial 12 sourceFuel) :=
  CompilerIO.compilePolynomial_program program sourceFuel acceptsWithin

private theorem output_projection (input : BitString) :
    polynomial.output input =
      (CompilerIO.compilePolynomial program sourceFuel acceptsWithin).output input := rfl

theorem polynomial_output (input : BitString) : polynomial.output input = solveEncoded input := by
  rw [output_projection, CompilerIO.compilePolynomial_output]
  exact source_output input

theorem polynomial_canonical (n : Nat) (rows : System n) :
    polynomial.output (codec.encode ⟨n, rows⟩) =
      (MatrixSolutionEncoding.solutionCodec n).encode (solve n rows) := by
  rw [polynomial_output, solveEncoded_valid]

theorem polynomial_malformed (input : BitString) (invalid : codec.decode input = none) :
    polynomial.output input = [false] := by
  rw [polynomial_output, solveEncoded, invalid]

theorem polynomial_machine_accepts (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 12 sourceFuel).eval input.length) input = .accept :=
  CompilerIO.compilePolynomial_accepts program sourceFuel acceptsWithin input

theorem polynomial_output_bound (input : BitString) :
    (polynomial.output input).length ≤ input.length + sourceFuel.eval input.length :=
  CompilerIO.compilePolynomial_output_length_le program sourceFuel acceptsWithin input

end PNP.Concrete.ResidualReduction.MatrixPolynomialSolver
