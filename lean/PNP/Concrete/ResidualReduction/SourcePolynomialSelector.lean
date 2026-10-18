import PNP.Concrete.ResidualReduction.SourceRawSelector
import PNP.Concrete.ResidualReduction.SourcePolynomialDirection

/-! The complete source-derived affine-first selector as one fixed concrete
polynomial-time function on arbitrary bitstrings. The compiler bound includes
register word-copy costs. This selects the exact existing contraction choice;
executing the successor and the whole contraction history remain separate. -/

namespace PNP.Concrete.ResidualReduction.SourcePolynomialSelector
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding (codec)
open PNP.Concrete.ResidualReduction.SourceRawSelector (answer)

def program : Program 48 := SourceRawSelector.block.program 0 8
def sourceFuel : NatPolynomial :=
  .add (.add SourcePolynomialDirection.familyPayload SourceRawSelector.processPolynomial) (.linear 11 37)

theorem sourceFuel_eval (L : Nat) : sourceFuel.eval L = SourceRawSelector.sourceBudget L + 1 := by
  simp only [sourceFuel,NatPolynomial.eval_add,NatPolynomial.eval_linear,
    SourcePolynomialDirection.familyPayload_eval,SourceRawSelector.sourceBudget]
  omega

private theorem initial_eq (input : BitString) :
    BitRegister.initial program input = ⟨.running 0,SourceSelectorInput.rawStart input⟩ := rfl
theorem source_result (input : BitString) :
    ∃ after : Store 48, CompilerIO.sourceResult program (sourceFuel.eval input.length) input =
      ⟨.accepted,after⟩ ∧ after.get 8 = answer input := by
  obtain ⟨used,after,checked,bound,output⟩ := SourceRawSelector.block_exec input
  have run : BitRegister.run program (used + 1) (BitRegister.initial program input) = ⟨.accepted,after⟩ := by
    rw [initial_eq]
    exact checked.program_run 0 8
  have enough : used + 1 ≤ sourceFuel.eval input.length := by rw [sourceFuel_eval]; omega
  have slack : sourceFuel.eval input.length = (used + 1) + (sourceFuel.eval input.length - (used + 1)) := by omega
  refine ⟨after,?_,output⟩
  unfold CompilerIO.sourceResult
  rw [slack,BitRegister.run_add,run,BitRegister.run_accepted]

theorem acceptsWithin : CompilerIO.AcceptsWithin program sourceFuel := by
  intro input
  obtain ⟨after,run,_⟩ := source_result input
  rw [run]
theorem source_output (input : BitString) :
    (CompilerIO.sourceResult program (sourceFuel.eval input.length) input).store.get 8 = answer input := by
  obtain ⟨after,run,output⟩ := source_result input
  rw [run]
  exact output

def polynomial : PolynomialTimeFunction := CompilerIO.compilePolynomial program sourceFuel acceptsWithin
theorem polynomial_program : polynomial.program =
    .machine (CompilerIO.rawMachine program) (CompilerIO.runtimePolynomial 48 sourceFuel) :=
  CompilerIO.compilePolynomial_program program sourceFuel acceptsWithin
private theorem output_projection (input : BitString) : polynomial.output input =
    (CompilerIO.compilePolynomial program sourceFuel acceptsWithin).output input := rfl
theorem polynomial_output (input : BitString) : polynomial.output input = answer input := by
  rw [output_projection,CompilerIO.compilePolynomial_output]
  exact source_output input
theorem polynomial_canonical (n : Nat) (F : Family n) :
    polynomial.output (codec.encode ⟨n,F⟩) =
      (SourceChoiceEncoding.codec n F.length).encode (SourceWitnessSelection.choose F) := by
  rw [polynomial_output,SourceRawSelector.answer_canonical]
theorem polynomial_malformed (input : BitString) (invalid : codec.decode input = none) :
    polynomial.output input = [false] := by
  rw [polynomial_output,SourceRawSelector.answer_malformed input invalid]
theorem exact_decoded_choice (n : Nat) (F : Family n) :
    (SourceChoiceEncoding.codec n F.length).decode (polynomial.output (codec.encode ⟨n,F⟩)) =
      some (SourceWitnessSelection.choose F) := by
  rw [polynomial_canonical]
  exact SourceChoiceEncoding.roundtrip _

/-- Exact connection to the original global step. This equality does not
assert a runtime bound for the still-semantic successor construction. -/
theorem global_step_exact {n : Nat} (F : Family (n + 1)) :
    (((SourceChoiceEncoding.codec (n + 1) F.length).decode
      (polynomial.output (codec.encode ⟨n + 1,F⟩))).getD none).bind (SourceWitnessSelection.build F) =
      SourceChain.globalStep F := by
  rw [exact_decoded_choice]
  exact (SourceWitnessSelection.global_exact F).symm

theorem polynomial_machine_accepts (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 48 sourceFuel).eval input.length) input = .accept :=
  CompilerIO.compilePolynomial_accepts program sourceFuel acceptsWithin input
theorem polynomial_output_bound (input : BitString) :
    (polynomial.output input).length ≤ 4 * input.length + 4 := by
  rw [polynomial_output]
  exact SourceRawSelector.answer_length input

end PNP.Concrete.ResidualReduction.SourcePolynomialSelector
