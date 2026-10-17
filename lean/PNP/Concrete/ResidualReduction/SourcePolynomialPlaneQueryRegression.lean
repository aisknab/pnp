import Lean
import PNP.Concrete.ResidualReduction.SourcePolynomialPlaneQuery
import PNP.Concrete.ResidualReduction.SourcePlaneLiftRegression

namespace PNP.Concrete.ResidualReduction.SourcePolynomialPlaneQuery.Regression
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceDirectionEncoding
open PNP.Concrete.ResidualReduction.SourceDirectionInput
open PNP.Concrete.ResidualReduction.SourcePlaneInput
open PNP.Concrete.ResidualReduction.SourcePlane

private def linear : Row 2 := ⟨false, (true, (false, false)), (false, (false, true))⟩
private def diagonal : Affine 2 := (true, (true, false))
private def inactive : Row 2 := ⟨false, (false, (false, false)), (false, (false, true))⟩
private def alpha : Affine 2 := (true, (false, true))
private def beta : Affine 2 := (false, (true, true))
private def good : BitString := codec.encode ⟨2, [diagonal, diagonal], [linear]⟩
private def late : BitString := codec.encode ⟨2, [diagonal, diagonal], [inactive, linear]⟩
private def idle : BitString := codec.encode ⟨2, [diagonal, diagonal], [inactive]⟩
private def inconsistent : BitString := codec.encode ⟨2, [alpha, beta], ([] : Family 2)⟩
private def emptyPair : BitString := codec.encode ⟨0, [true, true], ([] : Family 0)⟩
private def shortNormals : BitString := [false, true, true, false, true]
private def missingFamily : BitString := [false, true, true, false, true, true]
private def shortFamily : BitString := [false, true, true, false, true, true, true, false, false, false]

example : answer good = [true, true, true, true] := rfl
example : answer late = [true, false, true, true, true] := rfl
example : answer idle = [false] := rfl
example : answer inconsistent = [false] := rfl
example : answer emptyPair = [false] := rfl
example : answer (codec.encode ⟨2, ([] : System 2), [linear]⟩) = [false] := rfl
example : answer (codec.encode ⟨2, [diagonal], [linear]⟩) = [false] := rfl
example : answer (codec.encode ⟨2, [diagonal, diagonal, diagonal], [linear]⟩) = [false] := rfl
example : codec.decode (codec.encode ⟨2, [diagonal], [linear]⟩) = some ⟨2, [diagonal], [linear]⟩ :=
  roundtrip 2 [linear] [diagonal]
example : normalSize shortNormals = 2 := rfl
example : (first shortNormals).payload.length = 1 := rfl
example : (header missingFamily).terminated = false := rfl
example : (header shortFamily).count = 1 := rfl
example : (header shortFamily).rest.length = 2 := rfl
example : answer [] = [false] := rfl
example : answer [true, true] = [false] := rfl
example : answer [false, true, true] = [false] := rfl
example : answer shortNormals = [false] := rfl
example : answer missingFamily = [false] := rfl
example : answer shortFamily = [false] := rfl
example : answer (emptyPair ++ [false]) = [false] := rfl
example : answer (emptyPair ++ [true]) = [false] := rfl

private def RawProduces (input word : BitString) : Prop :=
  ∃ used after, BitRegister.run program (used + 1) ⟨.running 0, SourcePlaneRaw.start input⟩ =
      ⟨.accepted, after⟩ ∧ after.get 8 = word ∧ used ≤ SourcePlaneRaw.sourceBudget input.length
private theorem raw_produces (input word : BitString) (expected : answer input = word) :
    RawProduces input word := by
  obtain ⟨used, after, checked, bound, output⟩ := SourcePlaneRaw.block_exec input
  exact ⟨used, after, checked.program_run 0 8, output.trans expected, bound⟩
example : RawProduces good [true, true, true, true] := raw_produces _ _ rfl
example : RawProduces late [true, false, true, true, true] := raw_produces _ _ rfl
example : RawProduces idle [false] := raw_produces _ _ rfl
example : RawProduces inconsistent [false] := raw_produces _ _ rfl
example : RawProduces emptyPair [false] := raw_produces _ _ rfl
example : RawProduces [] [false] := raw_produces _ _ rfl
example : RawProduces [true, true] [false] := raw_produces _ _ rfl
example : RawProduces [false, true, true] [false] := raw_produces _ _ rfl
example : RawProduces shortNormals [false] := raw_produces _ _ rfl
example : RawProduces missingFamily [false] := raw_produces _ _ rfl
example : RawProduces shortFamily [false] := raw_produces _ _ rfl
example : RawProduces (emptyPair ++ [false]) [false] := raw_produces _ _ rfl
example : RawProduces (emptyPair ++ [true]) [false] := raw_produces _ _ rfl
example : RawProduces (codec.encode ⟨2, ([] : System 2), [linear]⟩) [false] := raw_produces _ _ rfl
example : RawProduces (codec.encode ⟨2, [diagonal], [linear]⟩) [false] := raw_produces _ _ rfl
example : RawProduces (codec.encode ⟨2, [diagonal, diagonal, diagonal], [linear]⟩) [false] :=
  raw_produces _ _ rfl

example : polynomial.output good = [true, true, true, true] := (polynomial_output good).trans rfl
example : polynomial.output late = [true, false, true, true, true] := (polynomial_output late).trans rfl
example : polynomial.output [] = [false] := (polynomial_output []).trans rfl
example : polynomial.output (emptyPair ++ [true]) = [false] := (polynomial_output _).trans rfl
example : polynomial.output (codec.encode ⟨2, List.replicate 64 diagonal, [linear]⟩) = [false] :=
  polynomial_wrong_count 2 [linear] (List.replicate 64 diagonal) (by rw [List.length_replicate]; decide)
example (input : BitString) : (polynomial.output input).length ≤ 2 * input.length + 1 :=
  polynomial_output_bound input
example (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program) ((CompilerIO.runtimePolynomial 29 sourceFuel).eval input.length) input = .accept :=
  polynomial_machine_accepts input
example {n : Nat} (F : Family n) (a b : Affine n) :
    (SourceAffineOutput.witnessCodec F.length n).decode (polynomial.output (codec.encode ⟨n, [a, b], F⟩)) =
      some (sourcePlaneQuery F a b) := exact_decoded_query n F a b
example : (SourceAffineOutput.witnessCodec 1 2).decode (polynomial.output good) =
    some (some ((true, ()), (true, (true, ())))) :=
  (exact_decoded_query 2 [linear] diagonal diagonal).trans rfl
example : PlaneGood [linear] diagonal diagonal ((true, ()), (true, (true, ()))) :=
  polynomial_sound [linear] diagonal diagonal _ (by rw [exact_decoded_query]; rfl)
example {n : Nat} (F : Family n) (a b : Affine n) :
    (SourceAffineOutput.witnessCodec F.length n).decode (polynomial.output (codec.encode ⟨n, [a, b], F⟩)) =
      some none ↔ ¬ ∃ w, PlaneGood F a b w := polynomial_none_iff F a b

run_cmd do
  for name in [
    ``SourcePlaneInput.answer_canonical, ``SourcePlaneInput.answer_pair,
    ``SourcePlaneInput.answer_malformed, ``SourcePlaneInput.answerFor_wrong_count,
    ``SourcePlaneInput.answer_wrong_count, ``SourcePlaneInput.answer_length,
    ``SourcePlaneRaw.lift_exec, ``SourcePlaneRaw.framed_output, ``SourcePlaneRaw.failure_exec,
    ``SourcePlaneRaw.failed_output, ``SourcePlaneRaw.saveCount_exec, ``SourcePlaneRaw.popCount_exec,
    ``SourcePlaneRaw.countGate_two, ``SourcePlaneRaw.countGate_wrong, ``SourcePlaneRaw.captureRows_exec,
    ``SourcePlaneRaw.finish_exec, ``SourcePlaneRaw.construct_pair, ``SourcePlaneRaw.construct_wrong,
    ``SourcePlaneRaw.construct_exec, ``SourcePlaneRaw.complete_check, ``SourcePlaneRaw.short_check,
    ``SourcePlaneRaw.extra_check, ``SourcePlaneRaw.family_check_exec, ``SourcePlaneRaw.family_selection_exec,
    ``SourcePlaneRaw.normal_selection_exec, ``SourcePlaneRaw.selection_exec, ``SourcePlaneRaw.block_exec,
    ``sourceFuel_eval, ``source_result, ``acceptsWithin, ``source_output, ``polynomial_program,
    ``polynomial_output, ``polynomial_canonical, ``polynomial_malformed, ``polynomial_wrong_count,
    ``polynomial_machine_accepts, ``polynomial_output_bound, ``exact_decoded_query,
    ``polynomial_sound, ``polynomial_complete, ``polynomial_none_iff] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourcePlaneRaw.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourcePolynomialPlaneQuery.polynomial_output
#print axioms PNP.Concrete.ResidualReduction.SourcePolynomialPlaneQuery.polynomial_machine_accepts
#print axioms PNP.Concrete.ResidualReduction.SourcePolynomialPlaneQuery.polynomial_sound
#print axioms PNP.Concrete.ResidualReduction.SourcePolynomialPlaneQuery.polynomial_none_iff

end PNP.Concrete.ResidualReduction.SourcePolynomialPlaneQuery.Regression
