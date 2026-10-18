import Lean
import PNP.Concrete.ResidualReduction.SourceLineSolver
import PNP.Concrete.ResidualReduction.SourceLineMatrixRegression

namespace PNP.Concrete.ResidualReduction.SourceLineSolver.Regression
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.SourceLine
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.SourceLineMatrixAugmentation (start)

private def alpha : Affine 2 := (true, (false, true))
private def beta : Affine 2 := (false, (true, true))
private def sample : Row 2 := ⟨true, alpha, beta⟩
private def expected : BitString :=
  [true, true, true, false, false, true, false, true, false, false, false, true, false]

-- The joint space has three coordinates, not one source-weight coordinate.
-- The relation is weight = second covector coefficient; the first is free.
example : (ready [sample] alpha).store.get 1 = [true, true, true] := rfl
example : (ready [sample] alpha).store.get 9 = [true, true, true] := rfl
example : (ready [sample] alpha).store.get 10 = [] := rfl
example : (ready [sample] alpha).store.get 13 = [true, true] := rfl
example : (ready [sample] alpha).store.get 15 = [true] := rfl
example : (ready [sample] alpha).store.get 16 = [true, false, true] := rfl
example : (kernelSpace (rankOneRows [sample] alpha)).parameters = 2 := rfl
example : (solutionCodec 3).encode (solve 3 (rankOneRows [sample] alpha)) = expected := rfl
example : (solutionCodec 3).encode (solve 3 (rankOneRows [{sample with selected := false}] alpha)) = expected := rfl
example : (solutionCodec 3).encode (solve 3 (rankOneRows [sample] (true, (false, false)))) = expected := rfl
example : (solutionCodec 3).encode (solve 3 (rankOneRows [sample] (aConst 2 true))) =
    [true, true, true, false, false, false, false, true, false, false, false, true, false] := rfl
example : (solutionCodec 2).encode (solve 2 (rankOneRows ([] : Family 2) alpha)) =
    [true, true, false, true, false, false, false] := rfl
example : (kernelSpace (rankOneRows ([] : Family 2) alpha)).parameters = 1 := rfl
example : (kernelSpace (rankOneRows (n := 0) [⟨true, true, false⟩] true)).parameters = 1 := rfl
example : (solutionCodec 0).encode (solve 0 (rankOneRows ([] : Family 0) true)) = [true, false] := rfl
example : sourceLineQuery ([] : Family 0) true = none := rfl
example : prepareFuel 0 = 7 := rfl
example : prepareFuel 5 = 22 := rfl
example : solverPolynomial.eval 0 = 20 := rfl

-- Actual program handoff and output, using the all-input execution theorem.
example : (BitRegister.run (prepare.program 0 8) (prepareFuel 2 + 1)
    ⟨.running 0, (SourceLineMatrixConstruction.result [sample] alpha).store⟩).store.get 1 =
      [true, true, true] := by
  exact congrArg (fun c => c.store.get (1 : Fin 17)) ((prepare_exec [sample] alpha).program_run 0 8)
example : (BitRegister.run (countLoop.program 0 1) 11
    ⟨.running 0, (counterReady [sample] alpha 2 3).store⟩).store.get 1 =
      [true, true, true, true, true] := by
  exact congrArg (fun c => c.store.get (1 : Fin 17)) ((countLoop_exec [sample] alpha 2 3).program_run 0 1)
example : (BitRegister.run program (fuel [sample] alpha + 1)
    ⟨.running 0, (start [sample] alpha).store⟩).store.get 8 = expected := by
  have output := congrArg (fun c => c.store.get (8 : Fin 17)) (program_run [sample] alpha)
  exact output.trans (result_output [sample] alpha)
example : (BitRegister.run program (fuel ([] : Family 2) alpha + 1)
    ⟨.running 0, (start ([] : Family 2) alpha).store⟩).store.get 8 =
      [true, true, false, true, false, false, false] := by
  have output := congrArg (fun c => c.store.get (8 : Fin 17)) (program_run ([] : Family 2) alpha)
  exact output.trans (result_output ([] : Family 2) alpha)
example : (BitRegister.run program (fuel ([] : Family 0) true + 1)
    ⟨.running 0, (start ([] : Family 0) true).store⟩).store.get 8 = [true, false] := by
  have output := congrArg (fun c => c.store.get (8 : Fin 17)) (program_run ([] : Family 0) true)
  exact output.trans (result_output ([] : Family 0) true)
example : (result [sample] alpha).store.get 13 = [true, true] := rfl
example : (result [sample] alpha).store.get 15 = [true] := rfl
example : (result [sample] alpha).store.get 16 = [true, false, true] := rfl

example {n : Nat} (F : Family n) (a : Affine n) :
    homogeneous (rankOneRows F a) = rankOneRows F a := homogeneous_rows F a
example {n : Nat} (F : Family n) (a : Affine n) :
    Exec block (start F a).store (fuel F a) (result F a).store := block_exec F a
example {n : Nat} (F : Family n) (a : Affine n) :
    (solutionCodec (n + F.length)).decode ((result F a).store.get 8) =
      some (some (kernelSpace (rankOneRows F a))) := exact_decoded_kernel F a
example {n : Nat} (F : Family n) (a : Affine n) :
    fuel F a ≤ costPolynomial.eval (SourceDirectionEncoding.codec.encode ⟨n, [a], F⟩).length :=
  original_input_bound F a
example {n : Nat} (F : Family n) (a : Affine n) :
    ((result F a).store.get 8).length ≤
      (2 * (SourceDirectionEncoding.codec.encode ⟨n, [a], F⟩).length + 1) *
        (2 * (SourceDirectionEncoding.codec.encode ⟨n, [a], F⟩).length + 1) + 1 := original_output_bound F a
example {n : Nat} (F : Family n) (a : Affine n) (w : Point (n + F.length)) :
    (∀ x y, weightedPolar F (splitPoint F.length w).1 x y =
      wedge a (splitPoint F.length w).2 x y) ↔
      ∃ z, (kernelSpace (rankOneRows F a)).direction z = w := kernel_exact F a w

run_cmd do
  for name in [``countStep_exec, ``countLoop_exec, ``finish_exec, ``prepare_exec,
    ``ready_width, ``ready_matrix, ``ready_dimension, ``ready_source_count,
    ``constraint_homogeneous, ``homogeneous_rows, ``solve_kernel, ``solve_exec,
    ``block_exec, ``result_output, ``result_kernel_output, ``result_solver,
    ``retained_dimension, ``retained_normal, ``retained_source_count,
    ``exact_decoded_kernel, ``kernel_exact, ``program_run, ``solverPolynomial_eval,
    ``original_solver_bound, ``original_input_bound, ``original_output_bound] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourceLineSolver.prepare_exec
#print axioms PNP.Concrete.ResidualReduction.SourceLineSolver.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceLineSolver.exact_decoded_kernel
#print axioms PNP.Concrete.ResidualReduction.SourceLineSolver.kernel_exact
#print axioms PNP.Concrete.ResidualReduction.SourceLineSolver.original_input_bound

end PNP.Concrete.ResidualReduction.SourceLineSolver.Regression
