import Lean
import PNP.Concrete.ResidualReduction.SourceLineMatrixConstruction
import PNP.Concrete.ResidualReduction.SourcePolynomialPlaneQueryRegression

namespace PNP.Concrete.ResidualReduction.SourceLineMatrixConstruction.Regression
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceLineMatrix
open PNP.Concrete.ResidualReduction.SourceLineMatrixAugmentation (start)

private def alpha : Affine 2 := (true, (false, true))
private def beta : Affine 2 := (false, (true, true))
private def sample : Row 2 := ⟨true, alpha, beta⟩
private def constantRow : Row 2 := ⟨false, aConst 2 false, aConst 2 true⟩
private def expected : BitString :=
  [false, false, false, false, true, false, true, false,
   true, false, true, false, false, false, false, false]

-- The weight column comes before both covector columns, and every constant
-- is zero. These are not the inhomogeneous equations of the plane branch.
example : matrixBits (SourceLine.rankOneRows [sample] alpha) = expected := rfl
example : matrixBits (SourceClosure.affineMaskRows (augmented [sample] alpha)) = expected := rfl
example : affineWord (SourceLine.polarConstraint [sample] alpha
    (unitPoint 2 ⟨0, by decide⟩) (unitPoint 2 ⟨1, by decide⟩)) = [true, false, true, false] := rfl
example : affineWord (SourceLine.polarConstraint [sample, constantRow] alpha
    (unitPoint 2 ⟨0, by decide⟩) (unitPoint 2 ⟨1, by decide⟩)) = [true, false, false, true, false] := rfl
example : affineWord (SourceLine.polarConstraint [constantRow, sample] alpha
    (unitPoint 2 ⟨0, by decide⟩) (unitPoint 2 ⟨1, by decide⟩)) = [false, true, false, true, false] := rfl
example : matrixBits (SourceLine.rankOneRows [{sample with selected := false}] alpha) = expected := rfl
example : matrixBits (SourceLine.rankOneRows [sample] (true, (false, false))) = expected := rfl
example : matrixBits (SourceLine.rankOneRows [sample] (aConst 2 true)) =
    [false, false, false, false, true, false, false, false,
     true, false, false, false, false, false, false, false] := rfl
example : matrixBits (SourceLine.rankOneRows ([] : Family 2) alpha) =
    [false, false, false, false, true, false, false, true, false, false, false, false] := rfl
example : matrixBits (SourceLine.rankOneRows ([] : Family 1) (true, false)) = [false, false] := rfl
example : matrixBits (SourceLine.rankOneRows (n := 0) [⟨true, true, false⟩] true) = [] := rfl
example : SourceMatrixEncoding.familyBits (augmented [sample] alpha) =
    [true, true, false, true, false, true, true,
     false, true, false, true, true, false, false,
     false, true, false, true, false, true, false] := rfl
example : SourceMatrixEncoding.familyBits (syntheticFamily alpha) =
    [false, true, false, true, true, false, false,
     false, true, false, true, false, true, false] := rfl
example : (augmented [sample] alpha).length = 3 := rfl
example : (augmented (n := 0) [⟨true, true, false⟩] true).length = 1 := rfl
example : (augmented ([] : Family 1) (true, false)).length = 1 := rfl
example : (result [sample] alpha).store.get 8 = expected := rfl
example : (result [sample] alpha).store.get 15 = [true] := rfl
example : (result [sample] alpha).store.get 16 = [true, false, true] := rfl
example : (result [sample] alpha).store.get 9 = [true, true] := rfl
example : ((result [sample] alpha).store.get 8).length = 16 := rfl
example : SourceLineMatrixRows.rowFuel 5 2 = 48 := rfl
example : SourceLineMatrixRows.loopFuel 2 0 2 = 58 := rfl
example : fuel ([] : Family 0) true = 18 := rfl
example : costPolynomial.eval 0 = 18 := rfl

-- The concrete runs use the same general program, not a finite substitute
-- for the all-input execution theorem.
example : (BitRegister.run program (fuel [sample] alpha + 1)
    ⟨.running 0, (start [sample] alpha).store⟩).store.get 8 = expected := by
  exact congrArg (fun c => c.store.get (8 : Fin 17)) (program_run [sample] alpha)
example : (BitRegister.run program (fuel ([] : Family 1) (true, false) + 1)
    ⟨.running 0, (start ([] : Family 1) (true, false)).store⟩).store.get 8 = [false, false] := by
  exact congrArg (fun c => c.store.get (8 : Fin 17)) (program_run ([] : Family 1) (true, false))
example : (BitRegister.run program (fuel (n := 0) [⟨true, true, false⟩] true + 1)
    ⟨.running 0, (start (n := 0) [⟨true, true, false⟩] true).store⟩).store.get 8 = [] := by
  exact congrArg (fun c => c.store.get (8 : Fin 17)) (program_run (n := 0) [⟨true, true, false⟩] true)
set_option maxRecDepth 16384 in
example : (BitRegister.run program 19 ⟨.running 0, (start ([] : Family 0) true).store⟩).control = .accepted := rfl

example {n : Nat} (F : Family n) (a : Affine n) :
    matrixBits (SourceClosure.affineMaskRows (augmented F a)) = matrixBits (SourceLine.rankOneRows F a) :=
  augmented_matrix F a
example {n : Nat} (F : Family n) (a : Affine n) :
    Exec block (start F a).store (fuel F a) (result F a).store := block_exec F a
example {n : Nat} (F : Family n) (a : Affine n) :
    ((result F a).store.get 8).length = (n + F.length + 1) * (n * n) := output_length F a
example {n : Nat} (F : Family n) (a : Affine n) :
    fuel F a ≤ costPolynomial.eval (SourceDirectionEncoding.codec.encode ⟨n, [a], F⟩).length :=
  original_input_bound F a
example {n : Nat} (F : Family n) (a : Affine n) :
    ((result F a).store.get 8).length ≤
      (2 * (SourceDirectionEncoding.codec.encode ⟨n, [a], F⟩).length + 1) *
        ((SourceDirectionEncoding.codec.encode ⟨n, [a], F⟩).length *
         (SourceDirectionEncoding.codec.encode ⟨n, [a], F⟩).length) := original_output_bound F a
example {n : Nat} (F : Family n) (a : Affine n) :
    (augmented F a).length ≤ 2 * (SourceDirectionEncoding.codec.encode ⟨n, [a], F⟩).length :=
  augmented_rows_bound F a

run_cmd do
  for name in [``SourceLineMatrix.vectorForm_eval, ``SourceLineMatrix.betaNormal_eq,
    ``SourceLineMatrix.vectorForm_word, ``SourceLineMatrix.betaNormal_word,
    ``SourceLineMatrix.coefficients_eval, ``SourceLineMatrix.coefficients_word,
    ``SourceLineMatrix.covectorCoefficients_eval, ``SourceLineMatrix.constraint_coefficients,
    ``SourceLineMatrix.constraint_word, ``SourceLineMatrix.synthetic_polar,
    ``SourceLineMatrix.synthetic_polar_units, ``SourceLineMatrix.augmented_length,
    ``SourceLineMatrix.rowBytes_exact, ``SourceLineMatrix.rowsBytes_zero,
    ``SourceLineMatrix.rowsBytes_succ, ``SourceLineMatrix.familyBits_map,
    ``SourceLineMatrix.synthetic_bytes, ``SourceLineMatrix.augmented_bits,
    ``SourceLineMatrix.augmented_matrix,
    ``SourceLineMatrixRows.rowBlock_exec, ``SourceLineMatrixRows.rowFuel_bound,
    ``SourceLineMatrixRows.step_exec, ``SourceLineMatrixRows.loop_exec,
    ``SourceLineMatrixRows.loopFuel_bound,
    ``SourceLineMatrixAugmentation.seed_exec, ``SourceLineMatrixAugmentation.reorder_exec,
    ``SourceLineMatrixAugmentation.block_exec, ``SourceLineMatrixAugmentation.input_bytes,
    ``SourceLineMatrixAugmentation.retained_count, ``SourceLineMatrixAugmentation.retained_normal,
    ``payload_exec, ``block_exec, ``result_output, ``retained_normal,
    ``retained_source_count, ``retained_dimension, ``output_length, ``program_run,
    ``augmentedSizePolynomial_eval, ``augmentationPolynomial_eval,
    ``matrixPolynomial_eval, ``costPolynomial_eval, ``augmented_rows_bound,
    ``augmented_size_bound, ``augmentation_bound, ``original_input_bound,
    ``original_output_bound] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourceLineMatrix.augmented_matrix
#print axioms PNP.Concrete.ResidualReduction.SourceLineMatrixRows.loop_exec
#print axioms PNP.Concrete.ResidualReduction.SourceLineMatrixAugmentation.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceLineMatrixConstruction.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceLineMatrixConstruction.original_input_bound

end PNP.Concrete.ResidualReduction.SourceLineMatrixConstruction.Regression
