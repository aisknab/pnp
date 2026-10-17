import Lean
import PNP.Concrete.ResidualReduction.SourceOrderedSelectorPrelude
import PNP.Concrete.ResidualReduction.SourceLinePullbackRegression

namespace PNP.Concrete.ResidualReduction.SourceOrderedSelectorPrelude.Regression
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceActivityMapAlgebra

private def clean : Registers := ⟨[], [], [], [], [], [], [], [], []⟩
private def dirty : Registers :=
  ⟨[true], [false], [true, false], [true], [true], [false], [false, true], [true, false], [true, true]⟩
private def zero (m n : Nat) : Matrix m n := fun _ _ => false
private def normal : Matrix 2 3 := fun i j => decide (i.val = 0 ∧ j.val = 2)
private def activity : Matrix 2 3 := fun i j => decide ((i.val = 0 ∧ j.val = 2) ∨ (i.val = 1 ∧ j.val = 1))
private def lastOnly : Matrix 3 4 := fun i j => decide (i.val = 2 ∧ j.val = 3)
private def firstOnly : Matrix 1 1 := fun _ _ => true

-- Position counts rejected entries. Successful reads are separate.
example : SourceOrderedScan.search [] = (false, 0) := rfl
example : SourceOrderedScan.search [false, false, true, true] = (true, 2) := rfl
example : SourceOrderedScan.search [false, false] = (false, 2) := rfl
example : (BilinearSelection.scan id [false, false, true, true]).2 = 3 := rfl
example : (BilinearSelection.scan id [false, false]).2 = 2 := rfl

-- The two first-entry searches are distinct and must retain row-major order.
example : SourceOrderedScan.matrixSearch false normal activity = (true, 2) := by decide
example : SourceOrderedScan.matrixSearch true normal activity = (true, 4) := by decide
example : SourceOrderedMatrixScan.entry false normal activity = some (0, 2) := by decide
example : SourceOrderedMatrixScan.entry true normal activity = some (1, 1) := by decide
example : selectedSeeds normal activity = some ((0, 2), (1, 1)) := by decide
example : entryPair normal activity = some ((0, 2), (1, 1)) := by decide
example : (BilinearSelection.select normal activity).witness = some ([1], [1]) := by decide

-- No nonzero entry means the difference scan is skipped even when A differs.
example : entryPair normal (zero 2 3) = none := by decide
example : fuel normal (zero 2 3) = 48 := by decide
example : entryPair normal normal = none := by decide
example : fuel normal normal = 93 := by decide
example : fuel normal activity = 114 := by decide
example : (result dirty normal activity).get 12 = [] := by decide
example : (result dirty normal activity).get 13 = [true, true] := by decide
example : (result dirty normal activity).get 1 = [true] := by decide
example : (result dirty normal activity).get 3 = [true] := by decide
example : (result dirty normal activity).get 4 = [true] := by decide
example : (result dirty normal normal).get 4 = [] := by decide
example : (result dirty normal (zero 2 3)).get 4 = [] := by decide
example : (result dirty normal activity).get 6 = dirty.active := by decide
example : (result dirty normal activity).get 7 = dirty.reserved := by decide

-- Last entries, row boundaries, repeated coordinates and zero dimensions.
example : SourceOrderedScan.walk 4 0 0 3 = (0, 3) := rfl
example : SourceOrderedScan.walk 4 0 0 4 = (1, 0) := rfl
example : SourceOrderedScan.walk 4 0 0 11 = (2, 3) := rfl
example : SourceOrderedScan.walkFuel 4 0 11 = 60 := rfl
example : SourceOrderedMatrixScan.entry false (zero 3 4) lastOnly = some (2, 3) := by decide
example : SourceOrderedMatrixScan.fuel false (zero 3 4) lastOnly = 139 := by decide
example : fuel (zero 3 4) lastOnly = 296 := by decide
example : entryPair (zero 1 1) firstOnly = some ((0, 0), (0, 0)) := rfl
example : entryPair (zero 0 3) (zero 0 3) = none := rfl
example : entryPair (zero 3 0) (zero 3 0) = none := rfl
example : entryPair (zero 0 0) (zero 0 0) = none := rfl
example : fuel (zero 0 3) (zero 0 3) = 12 := rfl
example : fuel (zero 3 0) (zero 3 0) = 12 := rfl
example : (data normal activity).firstRow = [] := rfl
example : (data normal activity).firstColumn = [] := rfl

-- Direct machine executions supplement the all-input execution theorem.
set_option maxRecDepth 32768 in
example : BitRegister.run program 47 ⟨.running 0, store clean (data (zero 1 1) firstOnly)⟩ =
    ⟨.accepted, result clean (zero 1 1) firstOnly⟩ := rfl
set_option maxRecDepth 32768 in
example : BitRegister.run program 13 ⟨.running 0, store dirty (data (zero 3 0) (zero 3 0))⟩ =
    ⟨.accepted, result dirty (zero 3 0) (zero 3 0)⟩ := rfl

example {m n : Nat} (r : Registers) (A C : Matrix m n) :
    Exec block (store r (data A C)) (fuel A C) (result r A C) := block_exec r A C
example {m n : Nat} (r : Registers) (A C : Matrix m n) :
    BitRegister.run program (fuel A C + 1) ⟨.running 0, store r (data A C)⟩ =
      ⟨.accepted, result r A C⟩ := program_run r A C
example {m n : Nat} (A C : Matrix m n) :
    fuel A C ≤ 26 * (m * n) + 46 := fuel_bound A C
example {m n : Nat} (r : Registers) (A C : Matrix m n) :
    (result r A C).get 4 = SourceOrderedScan.flag (entryPair A C).isSome := result_flag r A C
example {m n : Nat} (r : Registers) (A C : Matrix m n) (e f : Nat × Nat)
    (h : entryPair A C = some (e, f)) :
    (result r A C).get 12 = List.replicate e.1 true ∧
      (result r A C).get 13 = List.replicate e.2 true ∧
      (result r A C).get 1 = List.replicate f.1 true ∧
      (result r A C).get 3 = List.replicate f.2 true := result_coordinates r A C e f h
example {m n : Nat} (r : Registers) (A C : Matrix m n) :
    (result r A C).get 9 = coefficientMatrixBits A := retained_normal r A C
example {m n : Nat} (r : Registers) (A C : Matrix m n) :
    (result r A C).get 10 = coefficientMatrixBits C := retained_activity r A C
example {m n : Nat} (A C : Matrix m n) :
    (BilinearSelection.select A C).witness =
      (selectedSeeds A C).bind fun p =>
        (BilinearSelection.scan (BilinearSelection.accepts A C)
          (BilinearSelection.candidates p.1.1 p.2.1 p.1.2 p.2.2)).1 := select_from_seeds A C
example {n : Nat} (F : Family n) (alpha : Affine n) :
    fuel (SourceLinePullback.normalPull F alpha) (SourceLinePullback.activityPull F alpha) ≤
      sourceCostPolynomial.eval (SourceDirectionEncoding.codec.encode ⟨n, [alpha], F⟩).length :=
  source_bound F alpha

private def alpha : Affine 2 := (true, (false, true))
private def sample : Row 2 := ⟨true, alpha, (false, (true, false))⟩
private def linear : Row 2 := ⟨true, aConst 2 true, (false, (true, false))⟩
example : entryPair (SourceLinePullback.normalPull [sample] alpha)
    (SourceLinePullback.activityPull [sample] alpha) = none := rfl
example : entryPair (SourceLinePullback.normalPull [linear] alpha)
    (SourceLinePullback.activityPull [linear] alpha) = some ((0, 0), (0, 0)) := rfl

run_cmd do
  for name in [
    ``PNP.Concrete.ResidualReduction.SourceOrderedScan.search_bound,
    ``PNP.Concrete.ResidualReduction.SourceOrderedScan.search_found_bound,
    ``PNP.Concrete.ResidualReduction.SourceOrderedScan.search_exhausted,
    ``PNP.Concrete.ResidualReduction.SourceOrderedScan.scan_exact,
    ``PNP.Concrete.ResidualReduction.SourceOrderedScan.scan_checks,
    ``PNP.Concrete.ResidualReduction.SourceOrderedScan.zip_map,
    ``PNP.Concrete.ResidualReduction.SourceOrderedScan.matrix_bits_entries,
    ``PNP.Concrete.ResidualReduction.SourceOrderedScan.matrix_search_entries,
    ``PNP.Concrete.ResidualReduction.SourceOrderedScan.matrix_scan_exact,
    ``PNP.Concrete.ResidualReduction.SourceOrderedScan.matrix_scan_checks,
    ``PNP.Concrete.ResidualReduction.SourceOrderedScan.matrix_search_bound,
    ``PNP.Concrete.ResidualReduction.SourceOrderedScan.matrix_found_bound,
    ``PNP.Concrete.ResidualReduction.SourceOrderedScan.nonzero_predicate,
    ``PNP.Concrete.ResidualReduction.SourceOrderedScan.difference_predicate,
    ``PNP.Concrete.ResidualReduction.SourceOrderedScan.step_miss,
    ``PNP.Concrete.ResidualReduction.SourceOrderedScan.step_hit,
    ``PNP.Concrete.ResidualReduction.SourceOrderedScan.block_exec,
    ``PNP.Concrete.ResidualReduction.SourceOrderedScan.fuel_bound,
    ``PNP.Concrete.ResidualReduction.SourceOrderedScan.matrix_exec,
    ``PNP.Concrete.ResidualReduction.SourceOrderedScan.matrix_fuel_bound,
    ``PNP.Concrete.ResidualReduction.SourceOrderedScan.program_run,
    ``PNP.Concrete.ResidualReduction.SourceOrderedScan.walkFuel_bound,
    ``PNP.Concrete.ResidualReduction.SourceOrderedScan.walk_invariant,
    ``PNP.Concrete.ResidualReduction.SourceOrderedScan.walk_row_bound,
    ``PNP.Concrete.ResidualReduction.SourceOrderedScan.coordinate_step_boundary,
    ``PNP.Concrete.ResidualReduction.SourceOrderedScan.coordinate_step_interior,
    ``PNP.Concrete.ResidualReduction.SourceOrderedScan.coordinate_loop_exec,
    ``PNP.Concrete.ResidualReduction.SourceOrderedScan.coordinate_prepare_exec,
    ``PNP.Concrete.ResidualReduction.SourceOrderedScan.coordinate_exec,
    ``PNP.Concrete.ResidualReduction.SourceOrderedScan.entries_succ,
    ``PNP.Concrete.ResidualReduction.SourceOrderedScan.finRange_get,
    ``PNP.Concrete.ResidualReduction.SourceOrderedScan.entries_get,
    ``PNP.Concrete.ResidualReduction.SourceOrderedScan.recovered_entry_exact,
    ``PNP.Concrete.ResidualReduction.SourceOrderedMatrixScan.positive_width,
    ``PNP.Concrete.ResidualReduction.SourceOrderedMatrixScan.finish_exec,
    ``PNP.Concrete.ResidualReduction.SourceOrderedMatrixScan.block_exec,
    ``PNP.Concrete.ResidualReduction.SourceOrderedMatrixScan.entry_exact,
    ``PNP.Concrete.ResidualReduction.SourceOrderedMatrixScan.result_flag,
    ``PNP.Concrete.ResidualReduction.SourceOrderedMatrixScan.result_coordinates,
    ``PNP.Concrete.ResidualReduction.SourceOrderedMatrixScan.fuel_bound,
    ``PNP.Concrete.ResidualReduction.SourceOrderedMatrixScan.costPolynomial_eval,
    ``PNP.Concrete.ResidualReduction.SourceOrderedMatrixScan.bounded_exec,
    ``PNP.Concrete.ResidualReduction.SourceOrderedMatrixScan.program_run,
    ``PNP.Concrete.ResidualReduction.SourceOrderedMatrixScan.source_bound,
    ``PNP.Concrete.ResidualReduction.SourceOrderedSelectorPrelude.prepare_exec,
    ``PNP.Concrete.ResidualReduction.SourceOrderedSelectorPrelude.capture_exec,
    ``PNP.Concrete.ResidualReduction.SourceOrderedSelectorPrelude.first_exec,
    ``PNP.Concrete.ResidualReduction.SourceOrderedSelectorPrelude.continuation_exec,
    ``PNP.Concrete.ResidualReduction.SourceOrderedSelectorPrelude.first_flag,
    ``PNP.Concrete.ResidualReduction.SourceOrderedSelectorPrelude.finish_exec,
    ``PNP.Concrete.ResidualReduction.SourceOrderedSelectorPrelude.block_exec,
    ``PNP.Concrete.ResidualReduction.SourceOrderedSelectorPrelude.entry_pair_exact,
    ``PNP.Concrete.ResidualReduction.SourceOrderedSelectorPrelude.pair_none_first,
    ``PNP.Concrete.ResidualReduction.SourceOrderedSelectorPrelude.result_flag,
    ``PNP.Concrete.ResidualReduction.SourceOrderedSelectorPrelude.result_coordinates,
    ``PNP.Concrete.ResidualReduction.SourceOrderedSelectorPrelude.retained_normal,
    ``PNP.Concrete.ResidualReduction.SourceOrderedSelectorPrelude.retained_activity,
    ``PNP.Concrete.ResidualReduction.SourceOrderedSelectorPrelude.selected_seeds_exact,
    ``PNP.Concrete.ResidualReduction.SourceOrderedSelectorPrelude.select_from_seeds,
    ``PNP.Concrete.ResidualReduction.SourceOrderedSelectorPrelude.fuel_bound,
    ``PNP.Concrete.ResidualReduction.SourceOrderedSelectorPrelude.source_bound,
    ``PNP.Concrete.ResidualReduction.SourceOrderedSelectorPrelude.costPolynomial_eval,
    ``PNP.Concrete.ResidualReduction.SourceOrderedSelectorPrelude.sourceCostPolynomial_eval,
    ``PNP.Concrete.ResidualReduction.SourceOrderedSelectorPrelude.program_run] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourceOrderedScan.scan_exact
#print axioms PNP.Concrete.ResidualReduction.SourceOrderedScan.coordinate_loop_exec
#print axioms PNP.Concrete.ResidualReduction.SourceOrderedSelectorPrelude.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceOrderedSelectorPrelude.result_coordinates
#print axioms PNP.Concrete.ResidualReduction.SourceOrderedSelectorPrelude.select_from_seeds
#print axioms PNP.Concrete.ResidualReduction.SourceOrderedSelectorPrelude.source_bound

end PNP.Concrete.ResidualReduction.SourceOrderedSelectorPrelude.Regression
