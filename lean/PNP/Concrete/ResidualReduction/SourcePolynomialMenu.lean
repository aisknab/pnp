import PNP.Concrete.ResidualReduction.SourceMenuRawQuery
import PNP.Concrete.ResidualReduction.SourcePolynomialDirection

/-! One uniformly polynomial concrete machine builds the exact source-derived
normal menu on every input bitstring. The bound includes raw parsing, sorting,
counted serialization and compiler word-copy costs. This prepares candidates;
it is neither the complete contraction algorithm nor a solver for stopped cores. -/

namespace PNP.Concrete.ResidualReduction.SourcePolynomialMenu
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding (codec)
open PNP.Concrete.ResidualReduction.SourceMenuInput (answer)

def program : Program 16 := SourceMenuRaw.block.program 0 8
/-- Includes all raw-input branches and the final accepting instruction. -/
def sourceFuel : NatPolynomial := .add
  (.add SourcePolynomialDirection.familyPayload
    (.add SourceMenuBudget.costPolynomial SourceMenuSerialization.costPolynomial)) (.linear 18 44)

theorem sourceFuel_eval (L : Nat) : sourceFuel.eval L = SourceMenuRaw.sourceBudget L + 1 := by
  simp only [sourceFuel, NatPolynomial.eval_add, NatPolynomial.eval_linear,
    SourcePolynomialDirection.familyPayload_eval, SourceMenuRaw.sourceBudget, SourceMenuRaw.constructBudget]
  omega

private theorem initial_eq (input : BitString) :
    BitRegister.initial program input = ⟨.running 0, (SourceFamilyLoader.rawStart input).store⟩ := rfl
theorem source_result (input : BitString) :
    ∃ after : Store 16, CompilerIO.sourceResult program (sourceFuel.eval input.length) input =
      ⟨.accepted, after⟩ ∧ after.get 8 = answer input := by
  obtain ⟨used, after, checked, bound, output⟩ := SourceMenuRaw.block_exec input
  have run : BitRegister.run program (used + 1) (BitRegister.initial program input) = ⟨.accepted, after⟩ := by
    rw [initial_eq]
    exact checked.program_run 0 8
  have enough : used + 1 ≤ sourceFuel.eval input.length := by rw [sourceFuel_eval]; omega
  have slack : sourceFuel.eval input.length = (used + 1) + (sourceFuel.eval input.length - (used + 1)) := by omega
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
    .machine (CompilerIO.rawMachine program) (CompilerIO.runtimePolynomial 16 sourceFuel) :=
  CompilerIO.compilePolynomial_program program sourceFuel acceptsWithin
private theorem output_projection (input : BitString) : polynomial.output input =
    (CompilerIO.compilePolynomial program sourceFuel acceptsWithin).output input := rfl
theorem polynomial_output (input : BitString) : polynomial.output input = answer input := by
  rw [output_projection, CompilerIO.compilePolynomial_output]
  exact source_output input
theorem polynomial_canonical (n : Nat) (F : Family n) :
    polynomial.output (codec.encode ⟨n, F⟩) =
      MatrixInputEncoding.codec.encode ⟨n, SourceChain.sourceMenu F⟩ := by
  rw [polynomial_output, SourceMenuInput.answer_canonical]
theorem polynomial_malformed (input : BitString) (invalid : codec.decode input = none) :
    polynomial.output input = [false] := by
  rw [polynomial_output, SourceMenuInput.answer_malformed input invalid]
theorem exact_decoded_menu (n : Nat) (F : Family n) :
    MatrixInputEncoding.codec.decode (polynomial.output (codec.encode ⟨n, F⟩)) =
      some ⟨n, SourceChain.sourceMenu F⟩ := by
  rw [polynomial_canonical]
  exact MatrixInputEncoding.roundtrip n (SourceChain.sourceMenu F)
theorem polynomial_machine_accepts (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 16 sourceFuel).eval input.length) input = .accept :=
  CompilerIO.compilePolynomial_accepts program sourceFuel acceptsWithin input
theorem polynomial_output_bound (input : BitString) :
    (polynomial.output input).length ≤ 7 * input.length + 2 := by
  rw [polynomial_output]
  exact SourceMenuInput.answer_length input

end PNP.Concrete.ResidualReduction.SourcePolynomialMenu
