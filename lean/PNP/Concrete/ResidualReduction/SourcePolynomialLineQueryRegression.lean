import Lean
import PNP.Concrete.ResidualReduction.SourcePolynomialLineQuery
import PNP.Concrete.ResidualReduction.SourceLineOutputRegression

namespace PNP.Concrete.ResidualReduction.SourcePolynomialLineQuery.Regression
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceDirectionEncoding
open PNP.Concrete.ResidualReduction.SourceDirectionInput
open PNP.Concrete.ResidualReduction.SourceLineInput
open PNP.Concrete.ResidualReduction.SourceLine

private def alpha : Affine 2 := (true, (false, true))
private def diagonal : Affine 2 := (true, (true, false))
private def linear : Row 2 := ⟨true, aConst 2 true, (false, (true, false))⟩
private def sample : Row 2 := ⟨true, alpha, (false, (true, false))⟩
private def inactive : Row 2 := ⟨false, aConst 2 false, aConst 2 true⟩
private def good : BitString := codec.encode ⟨2, [alpha], [linear]⟩
private def changedBasis : BitString := codec.encode ⟨2, [diagonal], [linear]⟩
private def late : BitString := codec.encode ⟨2, [alpha], [inactive, linear]⟩
private def idle : BitString := codec.encode ⟨2, [alpha], [sample]⟩
private def emptySingle : BitString := codec.encode ⟨0, [true], ([] : Family 0)⟩
private def shortNormals : BitString := [false, true, false]
private def missingFamily : BitString := [false, true, false, true]
private def shortFamily : BitString := [false, true, false, true, true, false, false, false]

example : answer good = [true, true, false, false, false, true] := rfl
example : answer changedBasis = [true, true, false, false, true, true] := rfl
example : answer late = [true, false, true, false, false, false, true] := rfl
example : answer idle = [false] := rfl
example : answer emptySingle = [false] := rfl
example : answer (codec.encode ⟨2, ([] : System 2), [linear]⟩) = [false] := rfl
example : answer (codec.encode ⟨2, [alpha, alpha], [linear]⟩) = [false] := rfl
example : answer (codec.encode ⟨2, [alpha, alpha, alpha], [linear]⟩) = [false] := rfl
example : codec.decode good = some ⟨2, [alpha], [linear]⟩ := roundtrip 2 [linear] [alpha]
example : normalSize shortNormals = 1 := rfl
example : (first shortNormals).payload.length = 0 := rfl
example : (header missingFamily).terminated = false := rfl
example : (header shortFamily).count = 1 := rfl
example : (header shortFamily).rest.length = 2 := rfl
example : codec.decode shortNormals = none := rfl
example : codec.decode missingFamily = none := rfl
example : codec.decode shortFamily = none := rfl
example : answer [] = [false] := rfl
example : answer [true, true] = [false] := rfl
example : answer [false, true, true] = [false] := rfl
example : answer shortNormals = [false] := rfl
example : answer missingFamily = [false] := rfl
example : answer shortFamily = [false] := rfl
example : answer (emptySingle ++ [false]) = [false] := rfl
example : answer (emptySingle ++ [true]) = [false] := rfl

private def RawProduces (input word : BitString) : Prop :=
  ∃ used after, BitRegister.run program (used + 1) ⟨.running 0, SourceLineRaw.start input⟩ =
      ⟨.accepted, after⟩ ∧ after.get 8 = word ∧ used ≤ SourceLineRaw.sourceBudget input.length
private theorem raw_produces (input word : BitString) (expected : answer input = word) :
    RawProduces input word := by
  obtain ⟨used, after, checked, bound, output⟩ := SourceLineRaw.block_exec input
  exact ⟨used, after, checked.program_run 0 8, output.trans expected, bound⟩

-- Actual counted parser-to-query executions, including malformed boundaries.
example : RawProduces good [true, true, false, false, false, true] := raw_produces _ _ rfl
example : RawProduces changedBasis [true, true, false, false, true, true] := raw_produces _ _ rfl
example : RawProduces late [true, false, true, false, false, false, true] := raw_produces _ _ rfl
example : RawProduces idle [false] := raw_produces _ _ rfl
example : RawProduces emptySingle [false] := raw_produces _ _ rfl
example : RawProduces [] [false] := raw_produces _ _ rfl
example : RawProduces [true, true] [false] := raw_produces _ _ rfl
example : RawProduces [false, true, true] [false] := raw_produces _ _ rfl
example : RawProduces shortNormals [false] := raw_produces _ _ rfl
example : RawProduces missingFamily [false] := raw_produces _ _ rfl
example : RawProduces shortFamily [false] := raw_produces _ _ rfl
example : RawProduces (emptySingle ++ [false]) [false] := raw_produces _ _ rfl
example : RawProduces (emptySingle ++ [true]) [false] := raw_produces _ _ rfl
example : RawProduces (codec.encode ⟨2, ([] : System 2), [linear]⟩) [false] := raw_produces _ _ rfl
example : RawProduces (codec.encode ⟨2, [alpha, alpha], [linear]⟩) [false] := raw_produces _ _ rfl
example : RawProduces (codec.encode ⟨2, [alpha, alpha, alpha], [linear]⟩) [false] := raw_produces _ _ rfl

example : polynomial.output good = [true, true, false, false, false, true] := (polynomial_output good).trans rfl
example : polynomial.output changedBasis = [true, true, false, false, true, true] :=
  (polynomial_output changedBasis).trans rfl
example : polynomial.output late = [true, false, true, false, false, false, true] := (polynomial_output late).trans rfl
example : polynomial.output [] = [false] := polynomial_malformed [] rfl
example : polynomial.output shortNormals = [false] := polynomial_malformed shortNormals rfl
example : polynomial.output shortFamily = [false] := polynomial_malformed shortFamily rfl
example : polynomial.output (emptySingle ++ [true]) = [false] := (polynomial_output _).trans rfl
example : polynomial.output (codec.encode ⟨2, List.replicate 64 alpha, [linear]⟩) = [false] :=
  polynomial_wrong_count 2 [linear] (List.replicate 64 alpha) (by rw [List.length_replicate]; decide)

-- The type-level machine identity and runtime theorem retain the real compiler.
example : polynomial.program = .machine (CompilerIO.rawMachine program) (CompilerIO.runtimePolynomial 38 sourceFuel) :=
  polynomial_program
example (input : BitString) : (polynomial.output input).length ≤ 3 * input.length + 1 := polynomial_output_bound input
example (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program) ((CompilerIO.runtimePolynomial 38 sourceFuel).eval input.length) input = .accept :=
  polynomial_machine_accepts input
example {n : Nat} (F : Family n) (a : Affine n) :
    (SourceLineOutput.codec n F.length).decode (polynomial.output (codec.encode ⟨n, [a], F⟩)) =
      some (sourceLineQuery F a) := exact_decoded_query n F a
example : (SourceLineOutput.codec 2 1).decode (polynomial.output good) =
    some (some ⟨(true, ()), (false, (false, ())), (false, (true, ()))⟩) :=
  (exact_decoded_query 2 [linear] alpha).trans rfl
example : LineGood [linear] alpha ⟨(true, ()), (false, (false, ())), (false, (true, ()))⟩ :=
  polynomial_sound [linear] alpha _ (by rw [exact_decoded_query]; rfl)
example {n : Nat} (F : Family n) (a : Affine n) (existsWitness : ∃ w, LineGood F a w) :
    ∃ w, (SourceLineOutput.codec n F.length).decode (polynomial.output (codec.encode ⟨n, [a], F⟩)) = some (some w) :=
  polynomial_complete F a existsWitness
example {n : Nat} (F : Family n) (a : Affine n) :
    (SourceLineOutput.codec n F.length).decode (polynomial.output (codec.encode ⟨n, [a], F⟩)) =
      some none ↔ ¬ ∃ w, LineGood F a w := polynomial_none_iff F a

run_cmd do
  for name in [
    ``SourceLineInput.answer_canonical,
    ``SourceLineInput.answer_single,
    ``SourceLineInput.answer_malformed,
    ``SourceLineInput.answerFor_wrong_count,
    ``SourceLineInput.answer_wrong_count,
    ``SourceLineInput.answer_length,
    ``SourceLineRaw.lift_exec,
    ``SourceLineRaw.framed_output,
    ``SourceLineRaw.failure_exec,
    ``SourceLineRaw.failed_output,
    ``SourceLineRaw.saveCount_exec,
    ``SourceLineRaw.popCount_exec,
    ``SourceLineRaw.countGate_one,
    ``SourceLineRaw.countGate_wrong,
    ``SourceLineRaw.captureRows_exec,
    ``SourceLineRaw.finish_exec,
    ``SourceLineRaw.construct_single,
    ``SourceLineRaw.construct_wrong,
    ``SourceLineRaw.construct_exec,
    ``SourceLineRaw.complete_check,
    ``SourceLineRaw.short_check,
    ``SourceLineRaw.extra_check,
    ``SourceLineRaw.family_check_exec,
    ``SourceLineRaw.family_selection_exec,
    ``SourceLineRaw.normal_selection_exec,
    ``SourceLineRaw.selection_exec,
    ``SourceLineRaw.block_exec,
    ``SourcePolynomialLineQuery.sourceFuel_eval,
    ``SourcePolynomialLineQuery.source_result,
    ``SourcePolynomialLineQuery.acceptsWithin,
    ``SourcePolynomialLineQuery.source_output,
    ``SourcePolynomialLineQuery.polynomial_program,
    ``SourcePolynomialLineQuery.polynomial_output,
    ``SourcePolynomialLineQuery.polynomial_canonical,
    ``SourcePolynomialLineQuery.polynomial_malformed,
    ``SourcePolynomialLineQuery.polynomial_wrong_count,
    ``SourcePolynomialLineQuery.polynomial_machine_accepts,
    ``SourcePolynomialLineQuery.polynomial_output_bound,
    ``SourcePolynomialLineQuery.exact_decoded_query,
    ``SourcePolynomialLineQuery.polynomial_sound,
    ``SourcePolynomialLineQuery.polynomial_complete,
    ``SourcePolynomialLineQuery.polynomial_none_iff] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourceLineRaw.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourcePolynomialLineQuery.polynomial_output
#print axioms PNP.Concrete.ResidualReduction.SourcePolynomialLineQuery.polynomial_machine_accepts
#print axioms PNP.Concrete.ResidualReduction.SourcePolynomialLineQuery.polynomial_sound
#print axioms PNP.Concrete.ResidualReduction.SourcePolynomialLineQuery.polynomial_complete
#print axioms PNP.Concrete.ResidualReduction.SourcePolynomialLineQuery.polynomial_none_iff

end PNP.Concrete.ResidualReduction.SourcePolynomialLineQuery.Regression
