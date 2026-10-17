import Lean
import PNP.Concrete.ResidualReduction.SourcePlanePreparedSearch
import PNP.Concrete.ResidualReduction.SourcePlaneSolverRegression

namespace PNP.Concrete.ResidualReduction.SourceBilinearSearch.Regression
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.SourcePlane
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.SourceActivityMapAlgebra
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding

private def matrix : Matrix 1 2 := fun _ j => j == (1 : Fin 2)
private def later : Space 1 := ⟨2, ((false, (true, false)), ())⟩
private def constant : Space 1 := ⟨0, (true, ())⟩
private def missing : Space 1 := ⟨2, ((false, (false, false)), ())⟩
private def identity : Matrix 2 2 := fun i j => i == j
private def full : Space 2 := ⟨2, ((true, (false, false)), ((false, (true, false)), ()))⟩
private def shifted : Space 2 := ⟨1, ((true, true), ((true, false), ()))⟩
private def noColumns : Matrix 2 0 := fun _ j => Fin.elim0 j
private def noRows : Matrix 0 2 := fun i => Fin.elim0 i
private def emptyMap : Space 0 := ⟨0, ()⟩

example : familyBits (SourceBilinearFamily.family matrix) = [false, false, true, false, false, false, true] := rfl
example : coefficientMatrixBits matrix = [false, true] := rfl
example : (SourceBilinearFamily.family noColumns).length = 2 := rfl
example : coefficientMatrixBits noColumns = [] := rfl
example : familyBits (SourceBilinearFamily.family noColumns) = [false, false, true, false, false, true] := rfl
example : affineBilinearQuery later matrix = some ((true, ()), (false, (true, ()))) := rfl
example : affineBilinearQuery constant matrix = some ((true, ()), (false, (true, ()))) := rfl
example : affineBilinearQuery missing matrix = none := rfl
example : affineBilinearQuery full identity = some ((true, (false, ())), (true, (false, ()))) := rfl
-- The shifted base point is tested before the shifted generators.
example : affineBilinearQuery shifted identity = some ((true, (false, ())), (true, (false, ()))) := rfl
example : affineBilinearQuery full noColumns = none := rfl
example : affineBilinearQuery emptyMap noRows = none := rfl
example : (start matrix later).store.get 0 = [false, true] := rfl
example : (start matrix later).store.get 13 = [] := rfl
example : (start matrix later).store.get 16 = [false, true, false] := rfl
example : (start matrix later).store.get 17 = [true, true] := rfl

private def zeroColumnSeed : Registers :=
  {MatrixInstructions.base 0 [] with input := [], target := [], remaining := [], sign := [true, true], excess := [], output := []}
example : SourceBilinearMatrixInstructions.fuel 2 0 = 44 := rfl
-- An input-driven loop would drop both zero-column rows. The literal counted
-- loop instead constructs all six bytes.
example : (BitRegister.run (SourceBilinearMatrixInstructions.block.program 0 8) 45
    ⟨.running 0, zeroColumnSeed.store⟩).store.get 8 = [false, false, true, false, false, true] := rfl
example : (BitRegister.run (SourceBilinearMatrixInstructions.block.program 0 8) 45
    ⟨.running 0, zeroColumnSeed.store⟩).control = .accepted := rfl

set_option maxRecDepth 8192 in
example : ∃ used after, BitRegister.run program (used + 1) ⟨.running 0, (start matrix later).store⟩ = ⟨.accepted, after⟩ ∧
    after.get 8 = [true, true, false, true] ∧ used ≤ cost 1 2 2 := program_run matrix later
set_option maxRecDepth 8192 in
example : ∃ used after, BitRegister.run program (used + 1) ⟨.running 0, (start matrix constant).store⟩ = ⟨.accepted, after⟩ ∧
    after.get 8 = [true, true, false, true] ∧ used ≤ cost 1 2 0 := program_run matrix constant
set_option maxRecDepth 8192 in
example : ∃ used after, BitRegister.run program (used + 1) ⟨.running 0, (start matrix missing).store⟩ = ⟨.accepted, after⟩ ∧
    after.get 8 = [false] ∧ used ≤ cost 1 2 2 := program_run matrix missing
set_option maxRecDepth 8192 in
example : ∃ used after, BitRegister.run program (used + 1) ⟨.running 0, (start identity shifted).store⟩ = ⟨.accepted, after⟩ ∧
    after.get 8 = [true, true, false, true, false] ∧ used ≤ cost 2 2 1 := program_run identity shifted
set_option maxRecDepth 8192 in
example : ∃ used after, BitRegister.run program (used + 1) ⟨.running 0, (start noColumns full).store⟩ = ⟨.accepted, after⟩ ∧
    after.get 8 = [false] ∧ used ≤ cost 2 0 2 := program_run noColumns full
set_option maxRecDepth 8192 in
example : ∃ used after, BitRegister.run program (used + 1) ⟨.running 0, (start noRows emptyMap).store⟩ = ⟨.accepted, after⟩ ∧
    after.get 8 = [false] ∧ used ≤ cost 0 2 0 := program_run noRows emptyMap

-- Re-solving the synthetic family's affine-mask equations would replace the
-- actual weight constraints with a full space and can turn failure into success.
example : SourceClosure.affineSpaceQuery (SourceBilinearFamily.family matrix)
    (SourceBilinearFamily.space matrix missing) = none := rfl
example : (SourceClosure.sourceAffineQuery (SourceBilinearFamily.family matrix)).isSome = true := rfl

private def linear : Row 1 := ⟨false, (true, false), (false, true)⟩
private def unrestricted : Space 1 := ⟨1, ((true, false), ())⟩
example : solve 1 (SourcePlane.planeRows [linear] (aConst 1 false) (aConst 1 false)) = some unrestricted := rfl
example : planeRawQuery [linear] (aConst 1 false) (aConst 1 false) = some ((true, ()), (true, ())) := rfl
example : (SourcePlanePreparedSearch.start [linear] (aConst 1 false) (aConst 1 false) unrestricted).store.get 0 = [true] := rfl
example : (SourcePlanePreparedSearch.start [linear] (aConst 1 false) (aConst 1 false) unrestricted).store.get 16 = [true, false] := rfl

example {m n : Nat} (M : Matrix m n) (s : Space m) :
    ∃ used after, Exec block (start M s).store used after ∧
      after.get 8 = (SourceAffineOutput.witnessCodec m n).encode (affineBilinearQuery s M) ∧
      used ≤ cost m n s.parameters := block_exec M s
example {n : Nat} (F : Family n) (a b : Affine n) (s : Space F.length)
    (computed : solve F.length (SourcePlane.planeRows F a b) = some s) :
    ∃ used after, Exec block (SourcePlanePreparedSearch.start F a b s).store used after ∧
      after.get 8 = (SourceAffineOutput.witnessCodec F.length (directionSpace F [a, b]).parameters).encode
        (planeRawQuery F a b) ∧
      used ≤ costPolynomial.eval (SourceDirectionEncoding.codec.encode ⟨n, [a, b], F⟩).length :=
  SourcePlanePreparedSearch.original_input_bound F a b s computed
example {n : Nat} (F : Family n) (a b : Affine n) :
    ((SourceAffineOutput.witnessCodec F.length (directionSpace F [a, b]).parameters).encode
      (planeRawQuery F a b)).length ≤ 2 * (SourceDirectionEncoding.codec.encode ⟨n, [a, b], F⟩).length + 1 :=
  SourcePlanePreparedSearch.original_output_bound F a b

run_cmd do
  for name in [
    ``PNP.Concrete.ResidualReduction.SourceBilinearFamily.row_activity,
    ``PNP.Concrete.ResidualReduction.SourceBilinearFamily.family_length,
    ``PNP.Concrete.ResidualReduction.SourceBilinearFamily.weights_bits,
    ``PNP.Concrete.ResidualReduction.SourceBilinearFamily.forms_bits,
    ``PNP.Concrete.ResidualReduction.SourceBilinearFamily.forms_eval,
    ``PNP.Concrete.ResidualReduction.SourceBilinearFamily.weighted_activity,
    ``PNP.Concrete.ResidualReduction.SourceBilinearFamily.testPairs_exact,
    ``PNP.Concrete.ResidualReduction.SourceBilinearFamily.firstTrue_map,
    ``PNP.Concrete.ResidualReduction.SourceBilinearFamily.query_exact,
    ``PNP.Concrete.ResidualReduction.SourceBilinearFamily.witness_bits,
    ``PNP.Concrete.ResidualReduction.SourceBilinearFamily.search_output_exact,
    ``PNP.Concrete.ResidualReduction.SourceBilinearFamily.coefficient_word,
    ``PNP.Concrete.ResidualReduction.SourceBilinearFamily.constant_word,
    ``PNP.Concrete.ResidualReduction.SourceBilinearFamily.row_word,
    ``PNP.Concrete.ResidualReduction.SourceBilinearFamily.family_bits_length,
    ``PNP.Concrete.ResidualReduction.SourceBilinearFamily.query_exec,
    ``PNP.Concrete.ResidualReduction.SourceBilinearRowInstructions.zero_exec,
    ``PNP.Concrete.ResidualReduction.SourceBilinearRowInstructions.prefix_exec,
    ``PNP.Concrete.ResidualReduction.SourceBilinearRowInstructions.suffix_exec,
    ``PNP.Concrete.ResidualReduction.SourceBilinearRowInstructions.row_exec,
    ``PNP.Concrete.ResidualReduction.SourceBilinearRowInstructions.coefficient_row_exec,
    ``PNP.Concrete.ResidualReduction.SourceBilinearMatrixInstructions.coefficient_bits_succ,
    ``PNP.Concrete.ResidualReduction.SourceBilinearMatrixInstructions.loop_exec,
    ``PNP.Concrete.ResidualReduction.SourceBilinearMatrixInstructions.block_exec,
    ``PNP.Concrete.ResidualReduction.SourceBilinearMatrixInstructions.fuel_mono,
    ``start_matrix, ``start_has_no_family, ``start_map, ``start_rows, ``start_columns, ``start_parameters,
    ``conversion_exec, ``finish_exec, ``block_exec, ``cost_mono, ``costPolynomial_eval, ``bounded_exec, ``program_run,
    ``PNP.Concrete.ResidualReduction.SourcePlanePreparedSearch.matrix_from_source,
    ``PNP.Concrete.ResidualReduction.SourcePlanePreparedSearch.map_from_solver,
    ``PNP.Concrete.ResidualReduction.SourcePlanePreparedSearch.width_from_solver,
    ``PNP.Concrete.ResidualReduction.SourcePlanePreparedSearch.columns_from_direction,
    ``PNP.Concrete.ResidualReduction.SourcePlanePreparedSearch.original_input_bound,
    ``PNP.Concrete.ResidualReduction.SourcePlanePreparedSearch.original_output_bound] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourceBilinearSearch.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourcePlanePreparedSearch.original_input_bound

end PNP.Concrete.ResidualReduction.SourceBilinearSearch.Regression
