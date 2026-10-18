import Lean
import PNP.Concrete.ResidualReduction.SourceActivityConstruction
import PNP.Concrete.ResidualReduction.SourcePolynomialDirectionRegression

namespace PNP.Concrete.ResidualReduction.SourceActivityConstruction.Regression
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding (familyBits)
open PNP.Concrete.ResidualReduction.SourceActivityMapAlgebra

private def sample : Row 2 := ⟨true, (true, (false, true)), (false, (true, false))⟩
private def shifted : Space 2 := ⟨2, ((true, (false, true)), ((true, (true, true)), ()))⟩
private def pointOnly : Space 2 := ⟨0, (true, (false, ()))⟩
private def constrained : System 2 := [(true, (false, true))]
private def diagonal : Row 1 := ⟨true, (true, false), (true, false)⟩

-- The pullback constants are shifted: substituting them for the original
-- constants gives the wrong activity matrix. This fixture distinguishes them.
example : bits (aConstant sample.left) (aConstant sample.right)
    (pullback sample.left shifted.forms) (pullback sample.right shifted.forms) = [false, true] := rfl
example : bits (aConstant (pullback sample.left shifted.forms)) (aConstant (pullback sample.right shifted.forms))
    (pullback sample.left shifted.forms) (pullback sample.right shifted.forms) = [false, false] := rfl
example : sourceBits [sample] shifted = [false, true] := rfl
example : coefficientMatrixBits (activityMatrix shifted [sample]) = [false, true] := rfl
example : sourceBits [sample, {sample with selected := false}] shifted = [false, true, false, true] := rfl
example : sourceBits ([] : Family 2) shifted = [] := rfl
example : sourceBits [sample] pointOnly = [] := rfl
example : sourceBits (n := 0) [⟨true, true, false⟩] ⟨2, ()⟩ = [false, false] := rfl

-- Basis coefficients alone do not imply linearity on an arbitrary map.
-- The semantic extension requires the actually computed direction space.
example : bilinearEval (activityMatrix shifted [sample]) (true, ()) (true, (true, ())) = true := rfl
example : weightedActivity [sample] (true, ()) (shifted.direction (true, (true, ()))) = false := rfl
example : sourceBits [sample] (directionSpace [sample] constrained) = [true] := rfl
example : sourceBits [sample] (directionSpace [sample] []) = [] := rfl
example : sourceBits [diagonal] (directionSpace [diagonal] []) = [true] := rfl
example : (directionSpace [diagonal] []).parameters = 1 := rfl

set_option maxRecDepth 16384 in
example : (BitRegister.run (SourceActivityCoefficientInstructions.block.program 0 8) 12
    ⟨.running 0, (SourcePolarPairInstructions.working (n := 0) (k := 0)
      1 ⟨true, true, false⟩ true false [] [] []).store⟩).control = .accepted := rfl
set_option maxRecDepth 16384 in
example : (BitRegister.run (SourceActivityCoefficientInstructions.block.program 0 8) 38
    ⟨.running 0, (SourcePolarPairInstructions.working 3 sample
      (pullback sample.left shifted.forms) (pullback sample.right shifted.forms) [] [] []).store⟩).store.get 8 =
        [true, false] := rfl

example : (BitRegister.run SourceActivityFamilyInstructions.program
    (SourceActivityFamilyInstructions.fuel [sample] shifted + 1)
    ⟨.running 0, (SourcePolarFamilyInstructions.ready 2 2 (mapBits shifted.forms) (familyBits [sample]) []).store⟩).store.get 8 =
      [false, true] := by
  exact congrArg (fun c => c.store.get (8 : Fin 18)) (SourceActivityFamilyInstructions.program_run [sample] shifted)
example : (BitRegister.run program (fuel [sample] constrained + 1)
    ⟨.running 0, (start [sample] constrained).store⟩).store.get 8 = [true] := by
  exact congrArg (fun c => c.store.get (8 : Fin 21)) (program_run [sample] constrained)
example : (result [sample] constrained).store.get 15 = [false, false, true, false] := rfl
example : (result [sample] constrained).store.get 1 = [true, true] := rfl
example : (BitRegister.run program (fuel [diagonal] [] + 1)
    ⟨.running 0, (start [diagonal] []).store⟩).store.get 8 = [true] := by
  exact congrArg (fun c => c.store.get (8 : Fin 21)) (program_run [diagonal] [])

-- All source rows and coordinates, not a family of finite-prefix claims.
example {n : Nat} (F : Family n) (s : Space n) :
    sourceBits F s = coefficientMatrixBits (activityMatrix s F) := sourceBits_matrix F s
example {n : Nat} (F : Family n) (s : Space n) :
    (sourceBits F s).length = F.length * s.parameters := sourceBits_length F s
example {n : Nat} (F : Family n) (U : System n) :
    Exec block (start F U).store (fuel F U) (result F U).store := block_exec F U
example {n : Nat} (F : Family n) (U : System n) :
    (result F U).store.get 8 = coefficientMatrixBits (activityMatrix (directionSpace F U) F) := result_output F U
example {n : Nat} (F : Family n) (U : System n) :
    ((result F U).store.get 8).length = F.length * (directionSpace F U).parameters := output_length F U
example {n : Nat} (F : Family n) (U : System n) :
    ((result F U).store.get 8).length ≤
      (SourceDirectionEncoding.codec.encode ⟨n, U, F⟩).length *
        (SourceDirectionEncoding.codec.encode ⟨n, U, F⟩).length := original_output_bound F U
example {n : Nat} (F : Family n) (U : System n) :
    fuel F U ≤ costPolynomial.eval (SourceDirectionEncoding.codec.encode ⟨n, U, F⟩).length := original_input_bound F U
example {n : Nat} (F : Family n) (U : System n) (w : Point F.length)
    (z : Point (directionSpace F U).parameters) :
    bilinearEval (activityMatrix (directionSpace F U) F) w z =
      weightedActivity F w ((directionSpace F U).direction z) := computed_activity_matrix_eval F U w z

run_cmd do
  for name in [``SourceActivityMapAlgebra.eval_linear_constant,
    ``SourceActivityMapAlgebra.activity_value, ``SourceActivityMapAlgebra.coefficient_value,
    ``SourceActivityMapAlgebra.bits_length, ``SourceActivityMapAlgebra.bits_finRange,
    ``SourceActivityMapAlgebra.bits_pullback, ``SourceActivityMapAlgebra.sourceBits_length,
    ``SourceActivityMapAlgebra.sourceBits_matrix, ``SourceActivityMapAlgebra.constant_suffix,
    ``SourceActivityCoefficientInstructions.readInput_exec,
    ``SourceActivityCoefficientInstructions.readConstant_exec,
    ``SourceActivityCoefficientInstructions.body_exec, ``SourceActivityCoefficientInstructions.loop_exec,
    ``SourceActivityCoefficientInstructions.block_exec,
    ``SourceActivityRowInstructions.block_exec, ``SourceActivityRowInstructions.space_exec,
    ``SourceActivityRowInstructions.fuel_bound,
    ``SourceActivityFamilyInstructions.row_exec, ``SourceActivityFamilyInstructions.loop_exec,
    ``SourceActivityFamilyInstructions.rowFuel_bound, ``SourceActivityFamilyInstructions.loopFuel_bound,
    ``SourceActivityFamilyInstructions.block_exec, ``SourceActivityFamilyInstructions.matrix_exec,
    ``SourceActivityFamilyInstructions.fuel_bound, ``SourceActivityFamilyInstructions.program_run,
    ``lifted_exec, ``save_exec, ``direction_exec, ``prepare_exec, ``activity_exec,
    ``block_exec, ``result_output, ``output_length, ``original_output_bound, ``retained_map, ``retained_width, ``activity_bound,
    ``activityPolynomial_eval, ``original_input_bound, ``program_run,
    ``SourceDirections.computed_activity_matrix_eval] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourceActivityMapAlgebra.sourceBits_matrix
#print axioms PNP.Concrete.ResidualReduction.SourceActivityCoefficientInstructions.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceActivityFamilyInstructions.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceActivityConstruction.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceActivityConstruction.original_input_bound

end PNP.Concrete.ResidualReduction.SourceActivityConstruction.Regression
