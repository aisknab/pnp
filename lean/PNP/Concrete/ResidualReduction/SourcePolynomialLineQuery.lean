import PNP.Concrete.ResidualReduction.SourceLineRawQuery
import PNP.Concrete.ResidualReduction.SourcePolynomialDirection

/-! A uniformly polynomial finite machine for the exact source-derived line
query. The bound includes every raw-input branch, computed matrix and map,
ordered witness search, original-coordinate lift, canonical output encoding
and the concrete compiler's word-copying costs. This is one query, not the
complete contraction algorithm, a complete SAT solver or global ZeroSlack. -/

namespace PNP.Concrete.ResidualReduction.SourcePolynomialLineQuery
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceLine
open PNP.Concrete.ResidualReduction.SourceDirectionEncoding
open PNP.Concrete.ResidualReduction.SourceLineInput (answer)

def program : Program 38 := SourceLineRaw.block.program 0 8
/-- Includes the normal-count transfer and the final accepting instruction. -/
def sourceFuel : NatPolynomial := .add
  (.add (.add SourcePolynomialDirection.normalPayload SourcePolynomialDirection.familyPayload)
    SourceLinePreparedQuery.costPolynomial) (.linear 23 81)
theorem sourceFuel_eval (L : Nat) : sourceFuel.eval L = SourceLineRaw.sourceBudget L + 1 := by
  simp only [sourceFuel, NatPolynomial.eval_add, NatPolynomial.eval_linear,
    SourcePolynomialDirection.normalPayload_eval, SourcePolynomialDirection.familyPayload_eval,
    SourceLineRaw.sourceBudget, SourceLineRaw.selectionBudget, SourceLineRaw.normalBudget,
    SourceLineRaw.familyBudget, SourceLineRaw.completionBudget, SourceLineRaw.constructBudget]
  omega

private theorem initial_eq (input : BitString) :
    BitRegister.initial program input = ⟨.running 0, SourceLineRaw.start input⟩ := rfl
theorem source_result (input : BitString) :
    ∃ after : Store 38, CompilerIO.sourceResult program (sourceFuel.eval input.length) input =
      ⟨.accepted, after⟩ ∧ after.get 8 = answer input := by
  obtain ⟨fuel, after, checked, bound, output⟩ := SourceLineRaw.block_exec input
  have run : BitRegister.run program (fuel + 1) (BitRegister.initial program input) = ⟨.accepted, after⟩ := by
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
    .machine (CompilerIO.rawMachine program) (CompilerIO.runtimePolynomial 38 sourceFuel) :=
  CompilerIO.compilePolynomial_program program sourceFuel acceptsWithin
private theorem output_projection (input : BitString) : polynomial.output input =
    (CompilerIO.compilePolynomial program sourceFuel acceptsWithin).output input := rfl
theorem polynomial_output (input : BitString) : polynomial.output input = answer input := by
  rw [output_projection, CompilerIO.compilePolynomial_output]
  exact source_output input
theorem polynomial_canonical (n : Nat) (F : Family n) (a : Affine n) :
    polynomial.output (codec.encode ⟨n, [a], F⟩) =
      (SourceLineOutput.codec n F.length).encode (sourceLineQuery F a) := by
  rw [polynomial_output, SourceLineInput.answer_single]
theorem polynomial_malformed (input : BitString) (invalid : codec.decode input = none) :
    polynomial.output input = [false] := by
  rw [polynomial_output, SourceLineInput.answer_malformed input invalid]
theorem polynomial_wrong_count (n : Nat) (F : Family n) (U : System n) (wrong : U.length ≠ 1) :
    polynomial.output (codec.encode ⟨n, U, F⟩) = [false] := by
  rw [polynomial_output, SourceLineInput.answer_wrong_count n F U wrong]
theorem polynomial_machine_accepts (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 38 sourceFuel).eval input.length) input = .accept :=
  CompilerIO.compilePolynomial_accepts program sourceFuel acceptsWithin input
theorem polynomial_output_bound (input : BitString) :
    (polynomial.output input).length ≤ 3 * input.length + 1 := by
  rw [polynomial_output]
  exact SourceLineInput.answer_length input

theorem exact_decoded_query (n : Nat) (F : Family n) (a : Affine n) :
    (SourceLineOutput.codec n F.length).decode (polynomial.output (codec.encode ⟨n, [a], F⟩)) =
      some (sourceLineQuery F a) := by
  rw [polynomial_canonical]
  exact SourceLineOutput.roundtrip _
theorem polynomial_sound {n : Nat} (F : Family n) (a : Affine n) (w : LineWitness n F.length)
    (returned : (SourceLineOutput.codec n F.length).decode
      (polynomial.output (codec.encode ⟨n, [a], F⟩)) = some (some w)) :
    LineGood F a w := by
  rw [exact_decoded_query] at returned
  exact sourceLineQuery_sound F a w (Option.some.inj returned)
theorem polynomial_complete {n : Nat} (F : Family n) (a : Affine n)
    (existsWitness : ∃ w, LineGood F a w) :
    ∃ w, (SourceLineOutput.codec n F.length).decode
      (polynomial.output (codec.encode ⟨n, [a], F⟩)) = some (some w) := by
  obtain ⟨w, found⟩ := sourceLineQuery_complete F a existsWitness
  exact ⟨w, by rw [exact_decoded_query, found]⟩
/-- Failure excludes this stated line activity only, not all contraction
routes, satisfiability, global minimality or ZeroSlack. -/
theorem polynomial_none_iff {n : Nat} (F : Family n) (a : Affine n) :
    (SourceLineOutput.codec n F.length).decode
      (polynomial.output (codec.encode ⟨n, [a], F⟩)) = some none ↔ ¬ ∃ w, LineGood F a w := by
  rw [exact_decoded_query]
  constructor
  · intro missing
    exact (sourceLineQuery_none_iff F a).mp (Option.some.inj missing)
  · intro absent
    rw [(sourceLineQuery_none_iff F a).mpr absent]

end PNP.Concrete.ResidualReduction.SourcePolynomialLineQuery
