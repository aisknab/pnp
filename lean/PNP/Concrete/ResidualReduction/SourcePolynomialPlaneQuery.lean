import PNP.Concrete.ResidualReduction.SourcePlaneRawQuery
import PNP.Concrete.ResidualReduction.SourcePolynomialDirection

/-! A uniformly polynomial finite machine for the exact source-derived plane
query. The bound includes original raw input parsing, wrong-count rejection,
all computed matrices and searches, the original-coordinate witness lift,
output serialization and the concrete compiler's word-copying costs.
This is one query, not the complete contraction loop or global ZeroSlack. -/

namespace PNP.Concrete.ResidualReduction.SourcePolynomialPlaneQuery
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourcePlane
open PNP.Concrete.ResidualReduction.SourceDirectionEncoding
open PNP.Concrete.ResidualReduction.SourcePlaneInput (answer)

def program : Program 29 := SourcePlaneRaw.block.program 0 8
/-- Includes the normal-count transfer and final accepting instruction. -/
def sourceFuel : NatPolynomial := .add
  (.add (.add SourcePolynomialDirection.normalPayload SourcePolynomialDirection.familyPayload)
    SourcePlanePreparedQuery.costPolynomial) (.linear 23 83)
theorem sourceFuel_eval (L : Nat) : sourceFuel.eval L = SourcePlaneRaw.sourceBudget L + 1 := by
  simp only [sourceFuel, NatPolynomial.eval_add, NatPolynomial.eval_linear,
    SourcePolynomialDirection.normalPayload_eval, SourcePolynomialDirection.familyPayload_eval,
    SourcePlaneRaw.sourceBudget, SourcePlaneRaw.selectionBudget, SourcePlaneRaw.normalBudget,
    SourcePlaneRaw.familyBudget, SourcePlaneRaw.completionBudget, SourcePlaneRaw.constructBudget]
  omega

private theorem initial_eq (input : BitString) :
    BitRegister.initial program input = ⟨.running 0, SourcePlaneRaw.start input⟩ := rfl
theorem source_result (input : BitString) :
    ∃ after : Store 29, CompilerIO.sourceResult program (sourceFuel.eval input.length) input =
      ⟨.accepted, after⟩ ∧ after.get 8 = answer input := by
  obtain ⟨fuel, after, checked, bound, output⟩ := SourcePlaneRaw.block_exec input
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
    .machine (CompilerIO.rawMachine program) (CompilerIO.runtimePolynomial 29 sourceFuel) :=
  CompilerIO.compilePolynomial_program program sourceFuel acceptsWithin
private theorem output_projection (input : BitString) : polynomial.output input =
    (CompilerIO.compilePolynomial program sourceFuel acceptsWithin).output input := rfl
theorem polynomial_output (input : BitString) : polynomial.output input = answer input := by
  rw [output_projection, CompilerIO.compilePolynomial_output]
  exact source_output input
theorem polynomial_canonical (n : Nat) (F : Family n) (a b : Affine n) :
    polynomial.output (codec.encode ⟨n, [a, b], F⟩) =
      (SourceAffineOutput.witnessCodec F.length n).encode (sourcePlaneQuery F a b) := by
  rw [polynomial_output, SourcePlaneInput.answer_pair]
theorem polynomial_malformed (input : BitString) (invalid : codec.decode input = none) :
    polynomial.output input = [false] := by
  rw [polynomial_output, SourcePlaneInput.answer_malformed input invalid]
theorem polynomial_wrong_count (n : Nat) (F : Family n) (U : System n) (wrong : U.length ≠ 2) :
    polynomial.output (codec.encode ⟨n, U, F⟩) = [false] := by
  rw [polynomial_output, SourcePlaneInput.answer_wrong_count n F U wrong]
theorem polynomial_machine_accepts (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 29 sourceFuel).eval input.length) input = .accept :=
  CompilerIO.compilePolynomial_accepts program sourceFuel acceptsWithin input
theorem polynomial_output_bound (input : BitString) :
    (polynomial.output input).length ≤ 2 * input.length + 1 := by
  rw [polynomial_output]
  exact SourcePlaneInput.answer_length input

theorem exact_decoded_query (n : Nat) (F : Family n) (a b : Affine n) :
    (SourceAffineOutput.witnessCodec F.length n).decode (polynomial.output (codec.encode ⟨n, [a, b], F⟩)) =
      some (sourcePlaneQuery F a b) := by
  rw [polynomial_canonical]
  exact PNP.Concrete.NativeNormalization.NativeBitCodec.decode_encode _ _
theorem polynomial_sound {n : Nat} (F : Family n) (a b : Affine n) (w : Point F.length × Point n)
    (returned : (SourceAffineOutput.witnessCodec F.length n).decode
      (polynomial.output (codec.encode ⟨n, [a, b], F⟩)) = some (some w)) :
    PlaneGood F a b w := by
  rw [exact_decoded_query] at returned
  exact sourcePlaneQuery_sound F a b w (Option.some.inj returned)
theorem polynomial_complete {n : Nat} (F : Family n) (a b : Affine n)
    (existsWitness : ∃ w, PlaneGood F a b w) :
    ∃ w, (SourceAffineOutput.witnessCodec F.length n).decode
      (polynomial.output (codec.encode ⟨n, [a, b], F⟩)) = some (some w) := by
  obtain ⟨w, found⟩ := sourcePlaneQuery_complete F a b existsWitness
  exact ⟨w, by rw [exact_decoded_query, found]⟩
/-- Failure excludes only this exact plane activity. It is not a claim about
all contraction routes, satisfiability, global minimality or ZeroSlack. -/
theorem polynomial_none_iff {n : Nat} (F : Family n) (a b : Affine n) :
    (SourceAffineOutput.witnessCodec F.length n).decode
      (polynomial.output (codec.encode ⟨n, [a, b], F⟩)) = some none ↔ ¬ ∃ w, PlaneGood F a b w := by
  rw [exact_decoded_query]
  constructor
  · intro missing
    exact (sourcePlaneQuery_none_iff F a b).mp (Option.some.inj missing)
  · intro absent
    rw [(sourcePlaneQuery_none_iff F a b).mpr absent]

end PNP.Concrete.ResidualReduction.SourcePolynomialPlaneQuery
