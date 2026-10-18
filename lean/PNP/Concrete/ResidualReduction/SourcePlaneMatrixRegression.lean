import Lean
import PNP.Concrete.ResidualReduction.SourcePlaneMatrixBudget
import PNP.Concrete.ResidualReduction.SourceActivityConstructionRegression

namespace PNP.Concrete.ResidualReduction.SourcePlaneMatrixConstruction.Regression
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourcePlaneMatrix
open PNP.Concrete.ResidualReduction.SourcePlaneMatrixAugmentation (start)

private def alpha : Affine 2 := (true, (false, true))
private def beta : Affine 2 := (false, (true, true))
private def sample : Row 2 := ⟨true, alpha, beta⟩
private def expected : BitString := [false, false, true, true, true, true, false, false]

-- The true affine right sides must survive. The extra false bits must not.
example : matrixBits (SourcePlane.planeRows [sample] alpha beta) = expected := rfl
example : paddedRows (SourcePlane.planeRows [sample] alpha beta) =
    [false, false, false, true, true, false, true, true, false, false, false, false] := rfl
example : matrixBits (SourceClosure.affineMaskRows (augmented [sample] alpha beta)) =
    [false, false, false, true, true, false, true, true, false, false, false, false] := rfl
example : SourceMatrixEncoding.familyBits (augmented [sample] alpha beta) =
    [true, true, false, true, false, true, true, false, true, false, true, false, true, true] := rfl
example : matrixBits (SourcePlane.planeRows [{sample with selected := false}] alpha beta) = expected := rfl
example : matrixBits (SourcePlane.planeRows [sample] beta alpha) = expected := rfl
example : matrixBits (SourcePlane.planeRows [sample] (true, (false, false)) (false, (true, false))) = expected := rfl
example : matrixBits (SourcePlane.planeRows [sample] (aConst 2 true) beta) =
    [false, false, true, false, true, false, false, false] := rfl

-- With no source rows, a nonzero wedge produces inconsistent constant rows.
-- Replacing these constants by padding zeros would incorrectly make it solvable.
example : matrixBits (SourcePlane.planeRows ([] : Family 2) alpha beta) = [false, true, true, false] := rfl
example : solve 0 (SourcePlane.planeRows ([] : Family 2) alpha beta) = none := rfl
example : solve 0 ([false, false, false, false] : System 0) = some ⟨0, ()⟩ := rfl
example : matrixBits (SourcePlane.planeRows (n := 0) [⟨true, true, false⟩] true false) = [] := rfl
example : (result ([] : Family 2) alpha beta).store.get 8 = [false, true, true, false] := rfl
example : (result [sample] alpha beta).store.get 8 = expected := rfl
example : (result [sample] alpha beta).store.get 15 = [true] := rfl
example : (result [sample] alpha beta).store.get 16 = [true, false, true, false, true, true] := rfl

set_option maxRecDepth 16384 in
example : (BitRegister.run (SourcePlaneMatrixProjection.block.program 0 8) 29
    ⟨.running 0, ({base 1 [] with input := [true, false, false, false]}).store⟩).store.get 8 = [true, false] := rfl
set_option maxRecDepth 16384 in
example : (BitRegister.run (SourcePlaneMatrixProjection.block.program 0 8) 29
    ⟨.running 0, ({base 1 [] with input := [true, false, false, false]}).store⟩).control = .accepted := rfl
set_option maxRecDepth 16384 in
example : (BitRegister.run (SourcePlaneMatrixProjection.block.program 0 8) 3
    ⟨.running 0, (base 8 []).store⟩).control = .accepted := rfl
example : (BitRegister.run (SourcePlaneMatrixAugmentation.block.program 0 0)
    (SourcePlaneMatrixAugmentation.fuel [sample] + 1) ⟨.running 0, (start [sample] alpha beta).store⟩).store.get 0 =
      SourceMatrixEncoding.familyBits (augmented [sample] alpha beta) := by
  exact congrArg (fun c => c.store.get (0 : Fin 17))
    ((SourcePlaneMatrixAugmentation.block_exec [sample] alpha beta).program_run 0 0)
example : (BitRegister.run program (fuel [sample] alpha beta + 1)
    ⟨.running 0, (start [sample] alpha beta).store⟩).store.get 8 = expected := by
  exact congrArg (fun c => c.store.get (8 : Fin 17)) (program_run [sample] alpha beta)
example : (BitRegister.run program (fuel ([] : Family 2) alpha beta + 1)
    ⟨.running 0, (start ([] : Family 2) alpha beta).store⟩).store.get 8 = [false, true, true, false] := by
  exact congrArg (fun c => c.store.get (8 : Fin 17)) (program_run ([] : Family 2) alpha beta)
set_option maxRecDepth 16384 in
example : (BitRegister.run program 23 ⟨.running 0, (start ([] : Family 0) true false).store⟩).control = .accepted := rfl
example : (BitRegister.run program (fuel (n := 0) [⟨false, true, false⟩] true false + 1)
    ⟨.running 0, (start (n := 0) [⟨false, true, false⟩] true false).store⟩).store.get 8 = [] := by
  exact congrArg (fun c => c.store.get (8 : Fin 17)) (program_run (n := 0) [⟨false, true, false⟩] true false)

example {n : Nat} (F : Family n) (a b : Affine n) :
    matrixBits (SourceClosure.affineMaskRows (augmented F a b)) = paddedRows (SourcePlane.planeRows F a b) :=
  augmented_matrix F a b
example {n : Nat} (F : Family n) (a b : Affine n) :
    Exec block (start F a b).store (fuel F a b) (result F a b).store := block_exec F a b
example {n : Nat} (F : Family n) (a b : Affine n) :
    ((result F a b).store.get 8).length = (F.length + 1) * (n * n) := output_length F a b
example {n : Nat} (F : Family n) (a b : Affine n) :
    fuel F a b ≤ SourcePlaneMatrixBudget.costPolynomial.eval (SourceDirectionEncoding.codec.encode ⟨n, [a, b], F⟩).length :=
  SourcePlaneMatrixBudget.original_input_bound F a b
example {n : Nat} (F : Family n) (a b : Affine n) :
    ((result F a b).store.get 8).length ≤
      ((SourceDirectionEncoding.codec.encode ⟨n, [a, b], F⟩).length + 1) *
        ((SourceDirectionEncoding.codec.encode ⟨n, [a, b], F⟩).length * (SourceDirectionEncoding.codec.encode ⟨n, [a, b], F⟩).length) :=
  SourcePlaneMatrixBudget.original_output_bound F a b

run_cmd do
  for name in [``SourcePlaneMatrix.coefficients_eval, ``SourcePlaneMatrix.coefficients_word,
    ``SourcePlaneMatrix.plane_coefficients, ``SourcePlaneMatrix.plane_word,
    ``SourcePlaneMatrix.synthetic_polar, ``SourcePlaneMatrix.augmented_length,
    ``SourcePlaneMatrix.familyBits_append, ``SourcePlaneMatrix.augmented_bits,
    ``SourcePlaneMatrix.paddedRows_append, ``SourcePlaneMatrix.paddedRows_map,
    ``SourcePlaneMatrix.paddedRows_flatMap, ``SourcePlaneMatrix.paddedRows_length,
    ``SourcePlaneMatrix.augmented_matrix,
    ``SourcePlaneMatrixProjection.row_exec, ``SourcePlaneMatrixProjection.loop_exec,
    ``SourcePlaneMatrixProjection.block_exec,
    ``SourcePlaneMatrixAugmentation.lift16_exec, ``SourcePlaneMatrixAugmentation.lift15_exec,
    ``SourcePlaneMatrixAugmentation.lift9_exec, ``SourcePlaneMatrixAugmentation.block_exec,
    ``payload_exec, ``prepareProjection_exec, ``projection_exec, ``block_exec,
    ``result_output, ``retained_normals, ``retained_source_count, ``output_length, ``program_run,
    ``SourcePlaneMatrixBudget.payloadBudget_mono, ``SourcePlaneMatrixBudget.matrixPolynomial_eval,
    ``SourcePlaneMatrixBudget.projectionPolynomial_eval, ``SourcePlaneMatrixBudget.costPolynomial_eval,
    ``SourcePlaneMatrixBudget.original_input_bound, ``SourcePlaneMatrixBudget.original_output_bound] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourcePlaneMatrix.augmented_matrix
#print axioms PNP.Concrete.ResidualReduction.SourcePlaneMatrixProjection.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourcePlaneMatrixAugmentation.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourcePlaneMatrixConstruction.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourcePlaneMatrixBudget.original_input_bound

end PNP.Concrete.ResidualReduction.SourcePlaneMatrixConstruction.Regression
