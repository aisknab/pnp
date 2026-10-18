import Lean
import PNP.Concrete.ResidualReduction.SourceLinePullbackBudget
import PNP.Concrete.ResidualReduction.SourceBilinearPullbackRegression

namespace PNP.Concrete.ResidualReduction.SourceLinePullback.Regression
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.SourceActivityMapAlgebra

private def alpha : Affine 2 := (true, (false, true))
private def sample : Row 2 := ⟨true, alpha, (false, (true, false))⟩
private def linear : Row 2 := ⟨true, aConst 2 true, (false, (true, false))⟩
private def dirty : MatrixReconstruction.State :=
  ⟨⟨[true], [false], [true, false], [false, true], [true], [false],
    [true, true], [false, false], [true, false, true]⟩, [false], [true], [false, true]⟩

-- The caller provides original data only, not either transformed matrix or map.
example : (start [sample] alpha).get 28 = [] :=
  (initial_no_derived_data [sample] alpha).1
example : (start [sample] alpha).get 30 = [] :=
  (initial_no_derived_data [sample] alpha).2.1
example : (start [sample] alpha).get 32 = [] :=
  (initial_no_derived_data [sample] alpha).2.2.2.1
example : (start [sample] alpha).get 34 = [] :=
  (initial_no_derived_data [sample] alpha).2.2.2.2.1
example : (start [sample] alpha).get 36 = [] :=
  (initial_no_derived_data [sample] alpha).2.2.2.2.2.1
example : (start [sample] alpha).get 37 = [] :=
  (initial_no_derived_data [sample] alpha).2.2.2.2.2.2

-- Kernel basis order is observable. The first pulled matrix is not its
-- original three-row input; the two free coordinates remain in solver order.
example : (leftSpace [sample] alpha).parameters = 2 := rfl
example : (rightSpace [sample] alpha).parameters = 1 := rfl
example : mapBits (leftSpace [sample] alpha).forms =
    [false, true, false, true, false, false, false, true, false] := rfl
example : mapBits (rightSpace [sample] alpha).forms = [true, false] := rfl
example : coefficientMatrixBits (normalPull [sample] alpha) = [false, true] := rfl
example : coefficientMatrixBits (activityPull [sample] alpha) = [false, true] := rfl
example : SourceLine.lineRawQuery [sample] alpha = none := rfl
example : coefficientMatrixBits (normalPull [linear] alpha) = [false, false] := rfl
example : coefficientMatrixBits (activityPull [linear] alpha) = [true, false] := rfl
example : (SourceLine.lineRawQuery [linear] alpha).isSome = true := rfl

-- Empty systems, zero dimensions and zero-width transforms are all real
-- executions, not omitted branches. Route failure does not mean unsatisfiability.
example : (leftSpace ([] : Family 2) alpha).parameters = 1 := rfl
example : coefficientMatrixBits (normalPull ([] : Family 2) alpha) = [false] := rfl
example : coefficientMatrixBits (activityPull ([] : Family 2) alpha) = [false] := rfl
example : coefficientMatrixBits (normalPull [sample] (aConst 2 false)) = [] := rfl
example : coefficientMatrixBits (activityPull [sample] (aConst 2 false)) = [] := rfl
example : (leftSpace (n := 0) [⟨true, true, false⟩] true).parameters = 1 := rfl
example : (rightSpace (n := 0) [⟨true, true, false⟩] true).parameters = 0 := rfl
example : coefficientMatrixBits (normalPull (n := 0) [⟨true, true, false⟩] true) = [] := rfl
example : coefficientMatrixBits (activityPull (n := 0) [⟨true, true, false⟩] true) = [] := rfl
example : coefficientMatrixBits (normalPull ([] : Family 0) true) = [] := rfl
example : coefficientMatrixBits (activityPull ([] : Family 0) true) = [] := rfl

set_option maxRecDepth 16384 in
example : BitRegister.run (clearSolver.program 0 8) 13 ⟨.running 0, dirty.store⟩ =
    ⟨.accepted, zeroSolver.store⟩ := rfl

-- Complete source-derived execution, rather than an independently supplied
-- pair of maps and matrices, reaches the checked row-major output.
example : (BitRegister.run program (fuel [sample] alpha + 1)
    ⟨.running 0, start [sample] alpha⟩).store.get 36 = [false, true] := by
  exact (congrArg (fun c => c.store.get (36 : Fin 38)) (program_run [sample] alpha)).trans
    (result_normal [sample] alpha)
example : (BitRegister.run program (fuel [linear] alpha + 1)
    ⟨.running 0, start [linear] alpha⟩).store.get 37 = [true, false] := by
  exact (congrArg (fun c => c.store.get (37 : Fin 38)) (program_run [linear] alpha)).trans
    (result_activity [linear] alpha)
example : (BitRegister.run program (fuel ([] : Family 0) true + 1)
    ⟨.running 0, start ([] : Family 0) true⟩).control = .accepted :=
  congrArg (fun c => c.control) (program_run ([] : Family 0) true)
example : (BitRegister.run program (fuel (n := 0) [⟨true, true, false⟩] true + 1)
    ⟨.running 0, start (n := 0) [⟨true, true, false⟩] true⟩).store.get 37 = [] := by
  exact (congrArg (fun c => c.store.get (37 : Fin 38))
    (program_run (n := 0) [⟨true, true, false⟩] true)).trans
    (result_activity (n := 0) [⟨true, true, false⟩] true)
example : (result [sample] alpha).get 28 = [false, false, true, false] :=
  retained_direction [sample] alpha
example : (result [sample] alpha).get 32 =
    [false, true, false, true, false, false, false, true, false] :=
  retained_left_map [sample] alpha
example : (result [sample] alpha).get 34 = [true, false] :=
  retained_right_map [sample] alpha

example {n : Nat} (F : Family n) (a : Affine n) :
    Exec kernels (start F a) (kernelsFuel F a) (kernelsDone F a) := kernels_exec F a
example {n : Nat} (F : Family n) (a : Affine n) :
    Exec block (start F a) (fuel F a) (result F a) := block_exec F a
example {n : Nat} (F : Family n) (a : Affine n) :
    (result F a).get 36 = coefficientMatrixBits (normalPull F a) := result_normal F a
example {n : Nat} (F : Family n) (a : Affine n) :
    (result F a).get 37 = coefficientMatrixBits (activityPull F a) := result_activity F a
example {n : Nat} (F : Family n) (a : Affine n) :
    fuel F a ≤ costPolynomial.eval (SourceDirectionEncoding.codec.encode ⟨n, [a], F⟩).length :=
  original_input_bound F a
example {n : Nat} (F : Family n) (a : Affine n) :
    ((result F a).get 36).length ≤
      2 * ((SourceDirectionEncoding.codec.encode ⟨n, [a], F⟩).length *
        (SourceDirectionEncoding.codec.encode ⟨n, [a], F⟩).length) :=
  normal_output_bound F a
example {n : Nat} (F : Family n) (a : Affine n) :
    ((result F a).get 37).length ≤
      2 * ((SourceDirectionEncoding.codec.encode ⟨n, [a], F⟩).length *
        (SourceDirectionEncoding.codec.encode ⟨n, [a], F⟩).length) :=
  activity_output_bound F a
example {n : Nat} (F : Family n) (a : Affine n) :
    ∃ steps ≤ costPolynomial.eval (SourceDirectionEncoding.codec.encode ⟨n, [a], F⟩).length + 1,
      BitRegister.run program steps ⟨.running 0, start F a⟩ = ⟨.accepted, result F a⟩ :=
  program_original_bound F a
example {n : Nat} (F : Family n) (a : Affine n) :
    SourceLine.lineRawQuery F a =
      (BilinearSelection.select (normalPull F a) (activityPull F a)).witness.map
        (fun w => ((leftSpace F a).direction (sumUnits w.1),
          (rightSpace F a).direction (sumUnits w.2))) := exact_query_interface F a

run_cmd do
  for name in [
    ``copy_to_saved,
    ``copy_from_saved,
    ``clear_core,
    ``pop_saved,
    ``transfers_exec,
    ``save_exec,
    ``matrices_exec,
    ``capture_exec,
    ``matrices_saved_get,
    ``initial_no_derived_data,
    ``captured_normal,
    ``captured_activity,
    ``prepareLeft_exec,
    ``left_exec,
    ``captureLeft_exec,
    ``clearSolver_exec,
    ``clearLeftSolver_exec,
    ``prepareRight_exec,
    ``empty_solver_result,
    ``right_exec,
    ``captureRight_exec,
    ``kernels_exec,
    ``resetForPull_exec,
    ``prepareNormal_exec,
    ``normal_exec,
    ``saveNormal_exec,
    ``prepareActivity_exec,
    ``activity_exec,
    ``saveActivity_exec,
    ``block_exec,
    ``program_run,
    ``result_normal,
    ``result_activity,
    ``retained_direction,
    ``retained_left_map,
    ``retained_right_map,
    ``exact_query_interface,
    ``solverCostPolynomial_eval,
    ``right_original_bound,
    ``pull_original_bound,
    ``original_input_bound,
    ``left_parameter_bound,
    ``right_parameter_bound,
    ``normal_output_bound,
    ``activity_output_bound,
    ``program_original_bound] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourceLinePullback.kernels_exec
#print axioms PNP.Concrete.ResidualReduction.SourceLinePullback.empty_solver_result
#print axioms PNP.Concrete.ResidualReduction.SourceLinePullback.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceLinePullback.original_input_bound
#print axioms PNP.Concrete.ResidualReduction.SourceLinePullback.exact_query_interface
#print axioms PNP.Concrete.ResidualReduction.SourceLinePullback.program_original_bound

end PNP.Concrete.ResidualReduction.SourceLinePullback.Regression
