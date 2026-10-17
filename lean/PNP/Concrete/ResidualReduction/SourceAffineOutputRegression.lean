import Lean
import PNP.Concrete.ResidualReduction.SourceAffineEncodedSearch
import PNP.Concrete.ResidualReduction.SourceAffineSearchRegression

namespace PNP.Concrete.ResidualReduction.SourceAffineOutput.Regression
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear

private def row : Row 2 := ⟨false, (false, (true, false)), (false, (false, true))⟩
private def source : Family 2 := [row]
private def later : AffineMap 1 2 := ((false, (true, false)), ())
private def constant : AffineMap 1 0 := (true, ())
private def missing : AffineMap 1 2 := ((false, (false, false)), ())
private def pairForms : AffineMap 2 1 := ((false, true), ((true, false), ()))
private def solved : Space 1 := ⟨1, ((true, false), ())⟩

example : SourceUnitDirectionInstructions.word 3 0 = [true, false, false] := rfl
example : SourceUnitDirectionInstructions.word 3 1 = [false, true, false] := rfl
example : SourceUnitDirectionInstructions.word 3 2 = [false, false, true] := rfl
example : SourceUnitDirectionInstructions.fuel 7 0 = 22 := rfl
example : SourceUnitDirectionInstructions.fuel 7 6 = 28 := rfl

-- A small direct literal run checks the reverse accumulator and saved suffix.
private def seed : Registers := {MatrixInstructions.base 0 [] with target := [true], remaining := [true, true, true], output := [true, false]}
example : BitRegister.run (SourceUnitDirectionInstructions.block.program 0 8)
    (SourceUnitDirectionInstructions.fuel 3 1 + 1) ⟨.running 0, seed.store⟩ =
      ⟨.accepted, ({seed with target := [], remaining := [], output := [false, true, false, true, false]}).store⟩ := rfl

-- Pair order is weights then direction, preceded by one option tag.
example : pairBits ([row, row] : Family 2) pairForms none (1 : Fin 2) = [true, false, false, true] := rfl
example : (result ([row, row] : Family 2) pairForms none (1 : Fin 2)).store.get 8 =
    [true, true, false, false, true] := rfl
example : (witnessCodec 1 2).parse [true, true, false, true] =
    some (some ((true, ()), (false, (true, ()))), []) := rfl
example : (witnessCodec 1 2).parse [false, true] = some (none, [true]) := rfl
example : (witnessCodec 1 2).parse [true, true] = none := rfl
example : solve 1 (SourceClosure.affineMaskRows source) = some solved := rfl
example : SourceClosure.sourceAffineQuery source = some ((true, ()), (false, (true, ()))) := rfl

set_option maxRecDepth 8192 in
example : BitRegister.run (success.program 0 8) (successFuel 2 2 1 (some 1) 1 + 1)
    ⟨.running 0, (holder source later (some 1) 1).store⟩ =
      ⟨.accepted, (result source later (some 1) (1 : Fin 2)).store⟩ :=
  (success_exec source later (some 1) (1 : Fin 2)).program_run 0 8
set_option maxRecDepth 8192 in
example : BitRegister.run (success.program 0 8) (successFuel 2 0 1 none 1 + 1)
    ⟨.running 0, (holder source constant none 1).store⟩ =
      ⟨.accepted, (result source constant none (1 : Fin 2)).store⟩ :=
  (success_exec source constant none (1 : Fin 2)).program_run 0 8

private theorem query_run {n k : Nat} (F : Family n) (forms : AffineMap F.length k) :
    ∃ used after, BitRegister.run (query.program 0 8) (used + 1)
      ⟨.running 0, (SourceAffineSearch.ready F forms false 0 0 n 0 false).store⟩ = ⟨.accepted, after⟩ ∧
      after.get 8 = (witnessCodec F.length n).encode (SourceAffineSearch.decode F forms (SourceAffineSearch.outcome F forms)) ∧
      used ≤ SourceAffineSearch.fuel F forms + outputBudget n k F.length := by
  obtain ⟨used, after, execution, bytes, bound⟩ := query_exec F forms
  exact ⟨used, after, execution.program_run 0 8, bytes, bound⟩

-- Exact full-program outputs for late success, constant success and no result.
set_option maxRecDepth 8192 in
example : ∃ used after, BitRegister.run (query.program 0 8) (used + 1)
    ⟨.running 0, (SourceAffineSearch.ready source later false 0 0 2 0 false).store⟩ = ⟨.accepted, after⟩ ∧
    after.get 8 = [true, true, false, true] ∧ used ≤ SourceAffineSearch.fuel source later + outputBudget 2 2 1 :=
  query_run source later
set_option maxRecDepth 8192 in
example : ∃ used after, BitRegister.run (query.program 0 8) (used + 1)
    ⟨.running 0, (SourceAffineSearch.ready source constant false 0 0 2 0 false).store⟩ = ⟨.accepted, after⟩ ∧
    after.get 8 = [true, true, false, true] ∧ used ≤ SourceAffineSearch.fuel source constant + outputBudget 2 0 1 :=
  query_run source constant
set_option maxRecDepth 8192 in
example : ∃ used after, BitRegister.run (query.program 0 8) (used + 1)
    ⟨.running 0, (SourceAffineSearch.ready source missing false 0 0 2 0 false).store⟩ = ⟨.accepted, after⟩ ∧
    after.get 8 = [false] ∧ used ≤ SourceAffineSearch.fuel source missing + outputBudget 2 2 1 :=
  query_run source missing
set_option maxRecDepth 8192 in
example : ∃ used after, BitRegister.run (query.program 0 8) (used + 1)
    ⟨.running 0, (SourceAffineSearch.ready (k := 0) ([] : Family 0) (() : AffineMap 0 0) false 0 0 0 0 false).store⟩ = ⟨.accepted, after⟩ ∧
    after.get 8 = [false] ∧ used ≤ SourceAffineSearch.fuel (k := 0) ([] : Family 0) (() : AffineMap 0 0) + outputBudget 0 0 0 :=
  query_run (k := 0) ([] : Family 0) (() : AffineMap 0 0)

-- This instance uses the actual source-derived solve result, not a supplied map.
set_option maxRecDepth 8192 in
example : ∃ used after, BitRegister.run (query.program 0 8) (used + 1)
    ⟨.running 0, (SourceAffineSearch.ready source solved.forms false 0 0 2 0 false).store⟩ = ⟨.accepted, after⟩ ∧
    after.get 8 = [true, true, false, true] ∧
    used ≤ originalInputBudget (SourceMatrixEncoding.codec.encode ⟨2, source⟩).length := by
  obtain ⟨used, after, execution, bytes, bound⟩ := computed_query_exec source solved rfl
  exact ⟨used, after, execution.program_run 0 8, bytes, bound⟩

-- General execution and bounds, including all preparation-independent output work.
example (r : Registers) (n : Nat) (j : Fin n) :
    Exec SourceUnitDirectionInstructions.block
      ({r with target := List.replicate j.val true, remaining := List.replicate n true}).store
      (SourceUnitDirectionInstructions.fuel n j.val)
      ({r with target := [], remaining := [], output := ((SourceEncoding.pointCodec n).encode (unitPoint n j)).reverse ++ r.output}).store :=
  SourceUnitDirectionInstructions.block_exec r n j
example {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (q : Option (Fin k)) (j : Fin n) :
    Exec success (holder F forms q j.val).store (successFuel n k F.length q j.val) (result F forms q j).store :=
  success_exec F forms q j
example (rows n : Nat) (value : Option (Point rows × Point n)) :
    ((witnessCodec rows n).encode value).length ≤ rows + n + 1 := witness_bytes_bound rows n value

run_cmd do
  for name in [``PNP.Concrete.ResidualReduction.SourceUnitDirectionInstructions.unit_bytes,
    ``PNP.Concrete.ResidualReduction.SourceUnitDirectionInstructions.prefix_exec,
    ``PNP.Concrete.ResidualReduction.SourceUnitDirectionInstructions.suffix_exec,
    ``PNP.Concrete.ResidualReduction.SourceUnitDirectionInstructions.block_exec,
    ``PNP.Concrete.ResidualReduction.SourceUnitDirectionInstructions.fuel_bound,
    ``prepareMap_exec, ``map_exec, ``prepareDirection_exec, ``direction_exec,
    ``emitDirection_exec, ``reorder_exec, ``success_exec, ``successFuel_bound,
    ``unitSearch_mode, ``zero_parameter_index, ``successful_selection, ``decode_selected,
    ``emit_exec, ``query_exec, ``computed_query_exec, ``witness_bytes_bound] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourceUnitDirectionInstructions.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceAffineOutput.success_exec
#print axioms PNP.Concrete.ResidualReduction.SourceAffineOutput.successful_selection
#print axioms PNP.Concrete.ResidualReduction.SourceAffineOutput.computed_query_exec

end PNP.Concrete.ResidualReduction.SourceAffineOutput.Regression
