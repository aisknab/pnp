import Lean
import PNP.Concrete.ResidualReduction.SourcePolynomialAffineQuery
import PNP.Concrete.ResidualReduction.SourceAffineOutputRegression

namespace PNP.Concrete.ResidualReduction.SourcePolynomialAffineQuery.Regression
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding

private def row : Row 2 := ⟨false, (false, (true, false)), (false, (false, true))⟩
private def source : Family 2 := [row]
private def quadratic : Row 2 := ⟨false, (true, (false, false)), (false, (true, false))⟩
private def nonlinear : Family 2 := [quadratic]

-- The full machine rejects missing headers, missing terminators, truncated
-- payloads and trailing bytes. Tests use the actual source-family decoder.
example : polynomial.output [] = [false] := polynomial_malformed [] rfl
example : polynomial.output [false] = [false] := polynomial_malformed _ rfl
example : polynomial.output [true, true] = [false] := polynomial_malformed _ rfl
example : polynomial.output [false, true] = [false] := polynomial_malformed _ rfl
example : polynomial.output [false, true, false, false, true] = [false] := polynomial_malformed _ rfl
example : polynomial.output [false, false, false] = [false] := polynomial_malformed _ rfl
example : polynomial.output [false, false, true] = [false] := polynomial_malformed _ rfl
example : polynomial.output [false, true, false, true, true, true, false] = [false] := polynomial_malformed _ rfl
example : polynomial.output [false, true, false, true, true, true, true] = [false] := polynomial_malformed _ rfl

-- Valid empty instances retain both matrix headers and reach the solver path;
-- their correct no-witness result is not a malformed-input assumption.
example : codec.decode [false, false] = some ⟨0, ([] : Family 0)⟩ := rfl
example : (SourceAffineInput.matrixReady ([] : Family 0)).store.get 20 = [false] := rfl
example : polynomial.output [false, false] = [false] := by rw [polynomial_output]; rfl
example : polynomial.output [true, false, false] = [false] := by rw [polynomial_output]; rfl
example : polynomial.output (codec.encode ⟨3, ([] : Family 3)⟩) = [false] := by
  rw [polynomial_canonical]; rfl
example : polynomial.output (codec.encode ⟨0, ([⟨true, true, false⟩] : Family 0)⟩) = [false] := by
  rw [polynomial_canonical]; rfl

-- A late direction is found using the actual source-derived solution map,
-- without passing a candidate, map, success premise or prepared state.
example : polynomial.output (codec.encode ⟨2, source⟩) = [true, true, false, true] := by
  rw [polynomial_canonical]; rfl
example : (SourceAffineOutput.witnessCodec 1 2).decode
    (polynomial.output (codec.encode ⟨2, source⟩)) = some (some ((true, ()), (false, (true, ())))) :=
  exact_decoded_query 2 source
example : (SourceAffineOutput.witnessCodec 1 2).decode [true, true] = none := rfl
example : (SourceAffineOutput.witnessCodec 1 2).decode [false, true] = none := rfl

-- Failure can occur at positive dimension. It excludes affine-mask activity
-- only, and must not be relabelled as a global terminal or SAT result.
example : polynomial.output (codec.encode ⟨2, nonlinear⟩) = [false] := by
  rw [polynomial_canonical]; rfl
example : ¬ ∃ w, SourceClosure.AffineGood nonlinear w := by
  apply (polynomial_none_iff nonlinear).mp
  rw [exact_decoded_query]
  rfl

-- Small closed instruction runs also exercise the raw initial-store wiring.
set_option maxRecDepth 8192 in
example : (BitRegister.run program 128 (BitRegister.initial program [])).control = .accepted := rfl
set_option maxRecDepth 8192 in
example : (BitRegister.run program 128 (BitRegister.initial program [false, false, true])).store.get 8 = [false] := rfl

-- Universal contracts cover arbitrary bitstrings and arbitrary finite families.
example : CompilerIO.AcceptsWithin program sourceFuel := acceptsWithin
example (input : BitString) :
    ∃ after : Store 22, CompilerIO.sourceResult program (sourceFuel.eval input.length) input =
      ⟨.accepted, after⟩ ∧ after.get 8 = SourceAffineRawQuery.answer input := source_result input
example (input : BitString) : polynomial.output input = SourceAffineRawQuery.answer input := polynomial_output input
example (n : Nat) (F : Family n) :
    (SourceAffineOutput.witnessCodec F.length n).decode (polynomial.output (codec.encode ⟨n, F⟩)) =
      some (SourceClosure.sourceAffineQuery F) := exact_decoded_query n F
example (L : Nat) : sourceFuel.eval L = SourceAffineRawQuery.budget L + 1 := sourceFuel_eval L
example : polynomial.program = .machine (CompilerIO.rawMachine program) (CompilerIO.runtimePolynomial 22 sourceFuel) :=
  polynomial_program
example (input : BitString) : boundedDecide (CompilerIO.rawMachine program)
    ((CompilerIO.runtimePolynomial 22 sourceFuel).eval input.length) input = .accept := polynomial_machine_accepts input
example (input : BitString) : (polynomial.output input).length ≤ 2 * input.length + 1 := polynomial_output_bound input
example {n : Nat} (F : Family n) (h : ∃ w, SourceClosure.AffineGood F w) :
    ∃ w, (SourceAffineOutput.witnessCodec F.length n).decode
      (polynomial.output (codec.encode ⟨n, F⟩)) = some (some w) := polynomial_complete F h

-- The guard audits the new bridges, all-input branches, compiler contract,
-- semantic correctness and bounds; only the standard constructive boundary is allowed.
run_cmd do
  for name in [``PNP.Concrete.ResidualReduction.SourceAffineInput.source_exec,
    ``PNP.Concrete.ResidualReduction.SourceAffineInput.source_valid,
    ``PNP.Concrete.ResidualReduction.SourceAffineInput.inspectMatrix_exec,
    ``PNP.Concrete.ResidualReduction.SourceAffineInput.matrix_tail_nonempty,
    ``PNP.Concrete.ResidualReduction.SourceAffineInput.resetCore_exec,
    ``PNP.Concrete.ResidualReduction.SourceAffineInput.prepareSolver_exec,
    ``PNP.Concrete.ResidualReduction.SourceAffineInput.solver_exec,
    ``PNP.Concrete.ResidualReduction.SourceAffineInput.result_some,
    ``PNP.Concrete.ResidualReduction.SourceAffineInput.transferData_exec,
    ``PNP.Concrete.ResidualReduction.SourceAffineInput.transferCounters_exec,
    ``PNP.Concrete.ResidualReduction.SourceAffineInput.finishSearch_exec,
    ``PNP.Concrete.ResidualReduction.SourceAffineInput.prepareSearch_exec,
    ``PNP.Concrete.ResidualReduction.SourceAffineInput.search_exec,
    ``PNP.Concrete.ResidualReduction.SourceAffineInput.select_exec,
    ``PNP.Concrete.ResidualReduction.SourceAffineRawQuery.process_exec,
    ``PNP.Concrete.ResidualReduction.SourceAffineRawQuery.valid_exec,
    ``PNP.Concrete.ResidualReduction.SourceAffineRawQuery.malformed_exec,
    ``PNP.Concrete.ResidualReduction.SourceAffineRawQuery.block_exec,
    ``PNP.Concrete.ResidualReduction.SourceAffineRawQuery.answer_length,
    ``sourceFuel_eval, ``source_result, ``acceptsWithin, ``source_output,
    ``polynomial_program, ``polynomial_output, ``polynomial_canonical,
    ``polynomial_malformed, ``polynomial_machine_accepts, ``polynomial_output_bound,
    ``exact_decoded_query, ``polynomial_sound, ``polynomial_complete, ``polynomial_none_iff] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourceAffineRawQuery.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourcePolynomialAffineQuery.polynomial_output
#print axioms PNP.Concrete.ResidualReduction.SourcePolynomialAffineQuery.polynomial_machine_accepts
#print axioms PNP.Concrete.ResidualReduction.SourcePolynomialAffineQuery.polynomial_sound
#print axioms PNP.Concrete.ResidualReduction.SourcePolynomialAffineQuery.polynomial_none_iff

end PNP.Concrete.ResidualReduction.SourcePolynomialAffineQuery.Regression
