import Lean
import PNP.Concrete.ResidualReduction.SourceLineQueryMatrices
import PNP.Concrete.ResidualReduction.SourceLineSolverRegression

namespace PNP.Concrete.ResidualReduction.SourceLineQueryMatrices.Regression
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.SourceActivityMapAlgebra
open PNP.Concrete.ResidualReduction.SourceLineQueryMatrixAlgebra

private def alpha : Affine 2 := (true, (false, true))
private def sample : Row 2 := ⟨true, alpha, (false, (true, false))⟩
private def shifted : Space 2 := ⟨2, ((true, (false, true)), ((true, (true, true)), ()))⟩
private def pointOnly : Space 2 := ⟨0, (true, (false, ()))⟩

-- Affine origins must be discarded in the normal projection, but original
-- source constants must be retained for activity. The two rules differ.
example : mapBits shifted.forms = [true, false, true, true, true, true] := rfl
example : linearBits shifted.forms = [true, false, true, true] := rfl
example : coefficientMatrixBits (suffixMatrix 2 shifted.forms) =
    [false, false, false, false, true, false, true, true] := rfl
example : coefficientMatrixBits (prefixMatrix [sample] shifted) =
    [false, true, false, false, false, false] := rfl
-- Changing (x + 1)y to xy changes the basis values from (0,1) to
-- (1,0): the first direction is (1,1), and the second is (0,1).
example : coefficientMatrixBits (prefixMatrix (n := 2) [{sample with left := (true, (false, false))}] shifted) =
    [true, false, false, false, false, false] := rfl
example : coefficientMatrixBits (suffixMatrix 2 pointOnly.forms) = [] := rfl
example : coefficientMatrixBits (prefixMatrix [sample] pointOnly) = [] := rfl
example : linearBits (n := 0) (k := 3) () = [] := rfl

-- The source-weight rows precede all covector rows; column order is that
-- of the actually computed direction map, not a supplied basis.
example : (directionSpace [sample] [alpha]).parameters = 1 := rfl
example : normalBytes [sample] alpha = [false, false, true] := rfl
example : activityBytes [sample] alpha = [true, false, false] := rfl
example : coefficientMatrixBits (SourceLine.normalQueryMatrix [sample] alpha) =
    [false, false, true] := rfl
example : coefficientMatrixBits (SourceLine.activityQueryMatrix [sample] alpha) =
    [true, false, false] := rfl
example : normalBytes [sample, {sample with selected := false}] alpha =
    [false, false, false, true] := rfl
example : activityBytes [sample, {sample with selected := false}] alpha =
    [true, true, false, false] := rfl
example : normalBytes ([] : Family 2) alpha = [false, true] := rfl
example : activityBytes ([] : Family 2) alpha = [false, false] := rfl
example : normalBytes [sample] (aConst 2 false) = [] := rfl
example : activityBytes [sample] (aConst 2 false) = [] := rfl
example : normalBytes (n := 0) [⟨true, true, false⟩] true = [] := rfl
example : activityBytes (n := 0) [⟨true, true, false⟩] true = [] := rfl
example : normalBytes ([] : Family 0) true = [] := rfl
example : activityBytes ([] : Family 0) true = [] := rfl

-- Zero-width rows still consume their constants and row counters.
example : SourceLineQueryMatrixPadding.zeroFuel 3 0 = 13 := rfl
example : SourceLineQueryMatrixPadding.normalFuel 2 3 0 = 23 := rfl
example : SourceLineQueryMatrixPadding.appendFuel 2 1 3 = 53 := rfl
set_option maxRecDepth 16384 in
example : (BitRegister.run (SourceLineQueryMatrixPadding.normalBlock.program 0 8) 24
    ⟨.running 0, ({base 0 [] with input := mapBits pointOnly.forms, sign := [true, true, true]}).store⟩).control =
      .accepted := rfl
set_option maxRecDepth 16384 in
example : (BitRegister.run (SourceLineQueryMatrixPadding.appendBlock.program 0 8) 54
    ⟨.running 0, ({base 1 [] with sign := [true, true], output := [true, false, true]}).store⟩).store.get 8 =
      [true, false, true, false, false] := rfl
example : (BitRegister.run (SourceLineQueryMatrixProjection.block.program 0 8)
    (SourceLineQueryMatrixProjection.fuel 2 2 2 + 1)
    ⟨.running 0, ({base 2 [] with input := mapBits shifted.forms, excess := [false, true]}).store⟩).store.get 8 =
      [true, false, true, false, true, true] := by
  exact congrArg (fun c => c.store.get (8 : Fin 9))
    ((SourceLineQueryMatrixProjection.block_exec (base 2 []) shifted.forms [true, false]).program_run 0 8)

example : (BitRegister.run program (fuel [sample] alpha + 1)
    ⟨.running 0, (start [sample] alpha).store⟩).store.get 22 = [false, false, true] := by
  exact congrArg (fun c => c.store.get (22 : Fin 24)) (program_run [sample] alpha)
example : (BitRegister.run program (fuel [sample] alpha + 1)
    ⟨.running 0, (start [sample] alpha).store⟩).store.get 23 = [true, false, false] := by
  exact congrArg (fun c => c.store.get (23 : Fin 24)) (program_run [sample] alpha)
example : (BitRegister.run program (fuel ([] : Family 0) true + 1)
    ⟨.running 0, (start ([] : Family 0) true).store⟩).control = .accepted := by
  exact congrArg (fun c => c.control) (program_run ([] : Family 0) true)
example : (result [sample] alpha).store.get 15 = [false, false, true, false] := rfl
example : (result [sample] alpha).store.get 18 = [true, true] := rfl
example : (result [sample] alpha).store.get 19 = [true, false, true] := rfl
example : (result [sample] alpha).store.get 21 = [true] := rfl

-- The complete prepared construction is uniform over all finite dimensions
-- and families. No supplied direction map or output matrix is a premise.
example {n : Nat} (F : Family n) (a : Affine n) :
    Exec block (start F a).store (fuel F a) (result F a).store := block_exec F a
example {n : Nat} (F : Family n) (a : Affine n) :
    (result F a).store.get 22 = coefficientMatrixBits (SourceLine.normalQueryMatrix F a) := normal_output F a
example {n : Nat} (F : Family n) (a : Affine n) :
    (result F a).store.get 23 = coefficientMatrixBits (SourceLine.activityQueryMatrix F a) := activity_output F a
example {n : Nat} (F : Family n) (a : Affine n) :
    fuel F a ≤ costPolynomial.eval (SourceDirectionEncoding.codec.encode ⟨n, [a], F⟩).length :=
  original_input_bound F a
example {n : Nat} (F : Family n) (a : Affine n) :
    ((result F a).store.get 22).length ≤
      2 * ((SourceDirectionEncoding.codec.encode ⟨n, [a], F⟩).length *
        (SourceDirectionEncoding.codec.encode ⟨n, [a], F⟩).length) := normal_output_bound F a
example {n : Nat} (F : Family n) (a : Affine n) :
    ((result F a).store.get 23).length ≤
      2 * ((SourceDirectionEncoding.codec.encode ⟨n, [a], F⟩).length *
        (SourceDirectionEncoding.codec.encode ⟨n, [a], F⟩).length) := activity_output_bound F a
example {n : Nat} (F : Family n) (a : Affine n) :
    ∃ steps ≤ costPolynomial.eval (SourceDirectionEncoding.codec.encode ⟨n, [a], F⟩).length + 1,
      BitRegister.run program steps ⟨.running 0, (start F a).store⟩ =
        ⟨.accepted, (result F a).store⟩ := program_original_bound F a

run_cmd do
  for name in [``SourceLineQueryMatrixAlgebra.constant_bits,
    ``SourceLineQueryMatrixAlgebra.matrixBits_cons,
    ``SourceLineQueryMatrixAlgebra.replicate_join,
    ``SourceLineQueryMatrixAlgebra.zero_matrix_bits,
    ``SourceLineQueryMatrixAlgebra.coefficientMatrixBits_length,
    ``SourceLineQueryMatrixAlgebra.linearBits_length,
    ``SourceLineQueryMatrixAlgebra.normalWord_units,
    ``SourceLineQueryMatrixAlgebra.linearMapEval_cons,
    ``SourceLineQueryMatrixAlgebra.normal_matrix_bits,
    ``SourceLineQueryMatrixAlgebra.suffixMatrix_first,
    ``SourceLineQueryMatrixAlgebra.suffixMatrix_next,
    ``SourceLineQueryMatrixAlgebra.suffixMatrix_bits,
    ``SourceLineQueryMatrixAlgebra.prefixMatrix_first,
    ``SourceLineQueryMatrixAlgebra.prefixMatrix_next,
    ``SourceLineQueryMatrixAlgebra.prefixMatrix_bits,
    ``SourceLineQueryMatrixAlgebra.normal_query_bytes,
    ``SourceLineQueryMatrixAlgebra.activity_query_bytes,
    ``SourceLineQueryMatrixProjection.row_exec,
    ``SourceLineQueryMatrixProjection.loop_exec,
    ``SourceLineQueryMatrixProjection.block_exec,
    ``SourceLineQueryMatrixPadding.inner_exec,
    ``SourceLineQueryMatrixPadding.zeroStep_exec,
    ``SourceLineQueryMatrixPadding.zero_exec,
    ``SourceLineQueryMatrixPadding.reverse_output_exec,
    ``SourceLineQueryMatrixPadding.append_exec,
    ``SourceLineQueryMatrixPadding.normal_exec,
    ``SourceLineQueryMatrices.lifted_exec,
    ``SourceLineQueryMatrices.small_exec,
    ``SourceLineQueryMatrices.compute_exec,
    ``SourceLineQueryMatrices.prepareActivity_exec,
    ``SourceLineQueryMatrices.activity_exec,
    ``SourceLineQueryMatrices.saveActivity_exec,
    ``SourceLineQueryMatrices.prepareNormal_exec,
    ``SourceLineQueryMatrices.normal_exec,
    ``SourceLineQueryMatrices.saveNormal_exec,
    ``SourceLineQueryMatrices.block_exec,
    ``SourceLineQueryMatrices.normal_output,
    ``SourceLineQueryMatrices.activity_output,
    ``SourceLineQueryMatrices.retained_map,
    ``SourceLineQueryMatrices.retained_dimension,
    ``SourceLineQueryMatrices.retained_source_count,
    ``SourceLineQueryMatrices.retained_normal,
    ``SourceLineQueryMatrices.program_run,
    ``SourceLineQueryMatrices.normal_output_length,
    ``SourceLineQueryMatrices.activity_output_length,
    ``SourceLineQueryMatrices.parameter_bound,
    ``SourceLineQueryMatrices.normal_output_bound,
    ``SourceLineQueryMatrices.activity_output_bound,
    ``SourceLineQueryMatrices.append_original_bound,
    ``SourceLineQueryMatrices.normal_original_bound,
    ``SourceLineQueryMatrices.appendPolynomial_eval,
    ``SourceLineQueryMatrices.normalPolynomial_eval,
    ``SourceLineQueryMatrices.original_input_bound,
    ``SourceLineQueryMatrices.program_original_bound] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourceLineQueryMatrixAlgebra.normal_query_bytes
#print axioms PNP.Concrete.ResidualReduction.SourceLineQueryMatrixAlgebra.activity_query_bytes
#print axioms PNP.Concrete.ResidualReduction.SourceLineQueryMatrixProjection.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceLineQueryMatrixPadding.normal_exec
#print axioms PNP.Concrete.ResidualReduction.SourceLineQueryMatrices.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceLineQueryMatrices.original_input_bound
#print axioms PNP.Concrete.ResidualReduction.SourceLineQueryMatrices.program_original_bound

end PNP.Concrete.ResidualReduction.SourceLineQueryMatrices.Regression
