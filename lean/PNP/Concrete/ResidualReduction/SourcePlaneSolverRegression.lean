import Lean
import PNP.Concrete.ResidualReduction.SourcePlaneSolver
import PNP.Concrete.ResidualReduction.SourcePlaneMatrixRegression

namespace PNP.Concrete.ResidualReduction.SourcePlaneSolver.Regression
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.SourcePlaneMatrixAugmentation (start)

private def alpha : Affine 2 := (true, (false, true))
private def beta : Affine 2 := (false, (true, true))
private def sample : Row 2 := ⟨true, alpha, beta⟩

example : solve 1 (SourcePlane.planeRows [sample] alpha beta) = some ⟨0, (true, ())⟩ := rfl
example : (result [sample] alpha beta).store.get 8 = [true, false, true] := rfl
example : (result [sample] alpha beta).store.get 0 = [true] := rfl
example : (result [sample] alpha beta).store.get 1 = [true] := rfl
example : (result [sample] alpha beta).store.get 13 = [true, true] := rfl
example : (result [sample] alpha beta).store.get 15 = [true] := rfl
example : (result [sample] alpha beta).store.get 16 = [true, false, true, false, true, true] := rfl
-- An inconsistent plane weight system is not an unsatisfiability verdict
-- for the original Boolean problem or for any other contraction route.
example : (result ([] : Family 2) alpha beta).store.get 8 = [false] := rfl
example : (result ([] : Family 2) (aConst 2 true) beta).store.get 8 = [true, false] := rfl
example : (result ([] : Family 0) true false).store.get 8 = [true, false] := rfl
example : (result (n := 0) [⟨false, true, false⟩] true false).store.get 1 = [true, true] := rfl
example : (solve 2 (SourcePlane.planeRows [sample, sample] alpha beta)).isSome = true := rfl
example : (BitRegister.run program (fuel [sample] alpha beta + 1)
    ⟨.running 0, (start [sample] alpha beta).store⟩).store.get 8 = [true, false, true] := by
  rw [program_run, result_output]
  rfl
example : (BitRegister.run program (fuel ([] : Family 2) alpha beta + 1)
    ⟨.running 0, (start ([] : Family 2) alpha beta).store⟩).store.get 8 = [false] := by
  rw [program_run, result_output]
  rfl
example : (BitRegister.run program (fuel (n := 0) [⟨false, true, false⟩] true false + 1)
    ⟨.running 0, (start (n := 0) [⟨false, true, false⟩] true false).store⟩).control = .accepted := by
  rw [program_run]

example {n : Nat} (F : Family n) (a b : Affine n) :
    Exec block (start F a b).store (fuel F a b) (result F a b).store := block_exec F a b
example {n : Nat} (F : Family n) (a b : Affine n) :
    (result F a b).store.get 8 = (solutionCodec F.length).encode (solve F.length (SourcePlane.planeRows F a b)) :=
  result_output F a b
example {n : Nat} (F : Family n) (a b : Affine n) :
    fuel F a b ≤ costPolynomial.eval (SourceDirectionEncoding.codec.encode ⟨n, [a, b], F⟩).length :=
  original_input_bound F a b

run_cmd do
  for name in [``lift12_exec, ``prepare_exec, ``solve_exec, ``block_exec,
    ``result_output, ``retained_dimension, ``retained_normals, ``retained_source_count,
    ``program_run, ``solverPolynomial_eval, ``original_solver_bound, ``original_input_bound] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourcePlaneSolver.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourcePlaneSolver.result_output
#print axioms PNP.Concrete.ResidualReduction.SourcePlaneSolver.original_input_bound

end PNP.Concrete.ResidualReduction.SourcePlaneSolver.Regression
