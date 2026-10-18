import PNP.Concrete.ResidualReduction.SourceEncodedMatrix
import PNP.Concrete.BitRegisterCompilerIOPolynomial

/-! All-input polynomial-time construction of the exact source affine-mask
matrix. The executable object is the literal compiled finite-register machine.
Parsing, malformed input, all coefficient scans, both coordinate loops and
serialization are covered. This is not the complete contraction search or
a global SAT algorithm. -/

namespace PNP.Concrete.ResidualReduction.SourcePolynomialMatrix
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceMatrixPacket (State)
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.SourceFamilyInput (matrixEncoded)
open PNP.Concrete.ResidualReduction.SourceEncodedMatrix

def program : Program 16 := SourceEncodedMatrix.block.program 0 8

/-- The final accept instruction is included. The literal compiler separately
charges the full raw-machine cost of copying and manipulating encoded words. -/
def sourceFuel : NatPolynomial :=
  .add (.add (.add
    (.mul (.constant 24) (.mul .variable (.mul .variable (.mul .variable .variable))))
    (.mul (.constant 66) (.mul .variable (.mul .variable .variable))))
    (.mul (.constant 32) (.mul .variable .variable))) (.linear 57 58)

theorem sourceFuel_eval (length : Nat) : sourceFuel.eval length = sourceBudget length + 1 := by
  simp only [sourceFuel, NatPolynomial.eval_add, NatPolynomial.eval_mul,
    NatPolynomial.eval_constant, NatPolynomial.eval_variable, NatPolynomial.eval_linear,
    sourceBudget, SourceFamilyLoader.fuel, SourceMatrixPacket.budget,
    SourceMatrixConstruction.payloadBudget, SourceMatrixPacket.headerFuel,
    Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
  omega

private theorem initial_eq (input : BitString) :
    BitRegister.initial program input = ⟨.running 0, (SourceFamilyLoader.rawStart input).store⟩ := rfl

theorem source_result (input : BitString) :
    ∃ after : State, CompilerIO.sourceResult program (sourceFuel.eval input.length) input =
      ⟨.accepted, after.store⟩ ∧ after.core.core.core.output = matrixEncoded input := by
  obtain ⟨fuel, after, checked, bound, output⟩ := SourceEncodedMatrix.block_exec input
  have run : BitRegister.run program (fuel + 1) (BitRegister.initial program input) =
      ⟨.accepted, after.store⟩ := by
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
    (CompilerIO.sourceResult program (sourceFuel.eval input.length) input).store.get 8 = matrixEncoded input := by
  obtain ⟨after, run, output⟩ := source_result input
  rw [run]
  exact output

def polynomial : PolynomialTimeFunction := CompilerIO.compilePolynomial program sourceFuel acceptsWithin
theorem polynomial_program : polynomial.program =
    .machine (CompilerIO.rawMachine program) (CompilerIO.runtimePolynomial 16 sourceFuel) :=
  CompilerIO.compilePolynomial_program program sourceFuel acceptsWithin
private theorem output_projection (input : BitString) : polynomial.output input =
    (CompilerIO.compilePolynomial program sourceFuel acceptsWithin).output input := rfl
theorem polynomial_output (input : BitString) : polynomial.output input = matrixEncoded input := by
  rw [output_projection, CompilerIO.compilePolynomial_output]
  exact source_output input
theorem polynomial_canonical (n : Nat) (F : Family n) :
    polynomial.output (codec.encode ⟨n, F⟩) = affineMatrixPacket F := by
  rw [polynomial_output, SourceFamilyInput.matrixEncoded_canonical]
theorem polynomial_malformed (input : BitString) (invalid : codec.decode input = none) :
    polynomial.output input = [false] := by
  rw [polynomial_output, SourceFamilyInput.matrixEncoded_malformed input invalid]
theorem polynomial_machine_accepts (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 16 sourceFuel).eval input.length) input = .accept :=
  CompilerIO.compilePolynomial_accepts program sourceFuel acceptsWithin input
theorem polynomial_output_bound (input : BitString) :
    (polynomial.output input).length ≤ input.length + sourceFuel.eval input.length :=
  CompilerIO.compilePolynomial_output_length_le program sourceFuel acceptsWithin input

end PNP.Concrete.ResidualReduction.SourcePolynomialMatrix
