import Lean
import PNP.Concrete.ResidualReduction.SourcePolarFamilyInstructions
import PNP.Concrete.ResidualReduction.MatrixKernelRegression

namespace PNP.Concrete.ResidualReduction.SourcePolarFamilyInstructions.Regression
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.SourcePolarRowAlgebra

private def sample : Row 2 := ⟨true, (true, (false, true)), (false, (true, false))⟩
private def shifted : Space 2 := ⟨2, ((true, (false, true)), ((true, (true, true)), ()))⟩
private def pointOnly : Space 2 := ⟨0, (true, (false, ()))⟩
private def redundantParameters : Space 0 := ⟨2, ()⟩
private def constrained : System 2 := [(true, (false, true))]

-- Affine evaluation is not linear direction evaluation when the origin is
-- nonzero. Both this distinction and nonzero pullback constants are exercised.
example : mapEval shifted.forms (unitPoint 2 ⟨0, by decide⟩) = (false, (false, ())) := rfl
example : shifted.direction (unitPoint 2 ⟨0, by decide⟩) = (true, (true, ())) := rfl
example : affineWord (pullback sample.left shifted.forms) = [true, false, false] := rfl
example : affineWord (pullback sample.right shifted.forms) = [true, true, true] := rfl
example : affineWord (combine false false sample.left sample.right) = [false, false, false] := rfl
example : affineWord (combine true false sample.left sample.right) = [true, false, false] := rfl
example : affineWord (combine false true sample.left sample.right) = [false, true, false] := rfl
example : affineWord (combine true true sample.left sample.right) = [true, true, false] := rfl

-- The exact source order and basis order matter, not just the equation span.
example : matrixBits (polarRows [sample] shifted) = [true, true, false, true, false, false] := rfl
example : matrixBits (sourceRows [sample] shifted) = [true, true, false, true, false, false] := rfl
example : matrixBits (sourceRows [sample, {sample with selected := false}] shifted) =
    [true, true, false, true, false, false, true, true, false, true, false, false] := rfl
example : matrixBits (sourceRows [sample] pointOnly) = [] := rfl
example : matrixBits (sourceRows ([] : Family 2) shifted) = [] := rfl
example : matrixBits (sourceRows (n := 0) [⟨true, true, false⟩] redundantParameters) = [false, false] := rfl
example : matrixBits (sourceRows [sample] (kernelSpace constrained)) = [true, false, false] := rfl
example : matrixBits (sourceRows [sample] (kernelSpace ([] : System 2))) =
    [false, true, false, true, false, false] := rfl

-- A direct small literal run is independent of the general output theorem.
set_option maxRecDepth 8192 in
example : (BitRegister.run program 16
    ⟨.running 0, (ready 2 2 (mapBits shifted.forms) [] []).store⟩).control = .accepted := rfl
set_option maxRecDepth 8192 in
example : (BitRegister.run program 16
    ⟨.running 0, (ready 2 2 (mapBits shifted.forms) [] []).store⟩).store.get 8 = [] := rfl
set_option maxRecDepth 8192 in
example : (BitRegister.run (MatrixLinearCombinationInstructions.block true true |>.program 0 8) 19
    ⟨.running 0, ({base 0 [] with input := affineWord sample.left, mode := affineWord sample.right, remaining := [true, true]}).store⟩).store.get 8 =
      [false, true, true] := rfl

example : (BitRegister.run program (fuel [sample] shifted + 1)
    ⟨.running 0, (ready 2 2 (mapBits shifted.forms) (familyBits [sample]) []).store⟩).store.get 8 =
      [true, true, false, true, false, false] := by
  exact congrArg (fun c => c.store.get (8 : Fin 18)) (program_run [sample] shifted)
example : (BitRegister.run program (fuel [sample] pointOnly + 1)
    ⟨.running 0, (ready 2 0 (mapBits pointOnly.forms) (familyBits [sample]) []).store⟩).store.get 8 = [] := by
  exact congrArg (fun c => c.store.get (8 : Fin 18)) (program_run [sample] pointOnly)

-- The universal theorem has no supplied row-correctness premise. Instantiating
-- the actual kernel is permitted, but connecting its machine output remains
-- a separate handoff; this is not an all-bitstring runtime theorem yet.
example {n : Nat} (F : Family n) (s : Space n) :
    Exec block (ready n s.parameters (mapBits s.forms) (familyBits F) []).store
      (fuel F s) (ready n s.parameters (mapBits s.forms) [] (matrixBits (polarRows F s))).store :=
  block_exec F s
example {n : Nat} (F : Family n) (U : System n) :
    Exec block
      (ready n (kernelSpace U).parameters (mapBits (kernelSpace U).forms) (familyBits F) []).store
      (fuel F (kernelSpace U))
      (ready n (kernelSpace U).parameters (mapBits (kernelSpace U).forms) []
        (matrixBits (polarRows F (kernelSpace U)))).store := block_exec F (kernelSpace U)
example {n : Nat} (F : Family n) (s : Space n) :
    fuel F s ≤ (130 * (s.parameters + 2) * (n + 1) + 1) * F.length + 1 +
      (4 * ((n + 1) * (F.length * s.parameters)) + 3) := fuel_bound F s

run_cmd do
  for name in [``SourcePolarRowAlgebra.linearEval_pullback,
    ``SourcePolarRowAlgebra.linearEval_pullback_unit,
    ``SourcePolarRowAlgebra.combine_eq,
    ``SourcePolarRowAlgebra.combine_constant,
    ``SourcePolarRowAlgebra.combine_word,
    ``SourcePolarRowAlgebra.pairRows_length,
    ``SourcePolarRowAlgebra.pairRows_finRange,
    ``SourcePolarRowAlgebra.combine_pullback_coefficient,
    ``SourcePolarRowAlgebra.pairRows_pullback,
    ``SourcePolarRowAlgebra.sourceRows_eq,
    ``SourcePolarRowAlgebra.sourceRows_bytes,
    ``MatrixLinearCombinationInstructions.readInput_exec,
    ``MatrixLinearCombinationInstructions.readMode_exec,
    ``MatrixLinearCombinationInstructions.emit_exec,
    ``MatrixLinearCombinationInstructions.body_exec,
    ``MatrixLinearCombinationInstructions.loop_exec,
    ``MatrixLinearCombinationInstructions.block_exec,
    ``SourcePolarPairInstructions.lift_exec,
    ``SourcePolarPairInstructions.readLeft_exec,
    ``SourcePolarPairInstructions.readRight_exec,
    ``SourcePolarPairInstructions.assemble_exec,
    ``SourcePolarPairInstructions.body_exec,
    ``SourcePolarPairInstructions.loop_exec,
    ``SourcePolarRowInstructions.finish_exec,
    ``SourcePolarRowInstructions.block_exec,
    ``SourcePolarRowInstructions.space_exec,
    ``SourcePolarRowInstructions.fuel_bound,
    ``SourcePolarRowInstructions.program_run,
    ``lift_exec, ``small_exec, ``extract_exec, ``load_exec, ``row_exec, ``loop_exec,
    ``rowFuel_bound, ``loopFuel_bound, ``reorder_exec, ``block_exec, ``fuel_bound, ``program_run] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourcePolarRowAlgebra.sourceRows_eq
#print axioms PNP.Concrete.ResidualReduction.SourcePolarRowInstructions.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourcePolarFamilyInstructions.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourcePolarFamilyInstructions.fuel_bound
#print axioms PNP.Concrete.ResidualReduction.SourcePolarFamilyInstructions.program_run

end PNP.Concrete.ResidualReduction.SourcePolarFamilyInstructions.Regression
