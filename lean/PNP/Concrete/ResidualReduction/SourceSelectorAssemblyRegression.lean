import Lean
import PNP.Concrete.ResidualReduction.SourceOrderedMatrixSelector
import PNP.Concrete.ResidualReduction.SourceCandidateSelectionRegression

namespace PNP.Concrete.ResidualReduction.SourceOrderedMatrixSelector.Regression
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.ConstrainedBilinear

private def dirty : Registers :=
  ⟨[false, true], [true], [true, false], [false], [true], [true, true], [false, true], [true, false], [false, true]⟩
private def zero (m n : Nat) : Matrix m n := fun _ _ => false
private def single : Matrix 1 1 := fun _ _ => true
private def normal : Matrix 2 3 := fun i j => decide (i.val = 0 ∧ j.val = 2)
private def activity : Matrix 2 3 := fun i j => decide ((i.val = 0 ∧ j.val = 2) ∨ (i.val = 1 ∧ j.val = 1))
private def identity : Matrix 2 2 := fun i j => decide (i.val = j.val)
private def upperLeft : Matrix 2 2 := fun i j => decide (i.val = 0 ∧ j.val = 0)

-- Neither failure path evaluates candidates or requires valid seed indices.
example : code normal (zero 2 3) = none := by decide
example : code normal normal = none := by decide
example : finishFuel normal (zero 2 3) = 3 := by decide
example : finishFuel normal normal = 3 := by decide
example : fuel normal (zero 2 3) = 51 := by decide
example : fuel normal normal = 96 := by decide
example : (result dirty normal (zero 2 3)).get 8 = [false] := by decide
example : (result dirty normal normal).get 8 = [false] := by decide
example : code (zero 0 3) (zero 0 3) = none := rfl
example : code (zero 3 0) (zero 3 0) = none := rfl
example : code (zero 0 0) (zero 0 0) = none := rfl
example : fuel (zero 0 3) (zero 0 3) = 15 := rfl
example : fuel (zero 3 0) (zero 3 0) = 15 := rfl

-- Derived seeds, including duplicates, retain the exact candidate order.
example : code (zero 1 1) single = some (.first, .first) := rfl
example : code normal activity = some (.second, .second) := by decide
example : code identity upperLeft = some (.both, .both) := by decide
example : fuel (zero 1 1) single = 181 := rfl
example : fuel normal activity = 373 := by decide
example : (result dirty normal activity).get 8 = [true, false, true, false, true] := by decide
example : (result dirty identity upperLeft).get 8 = [true, true, true, true, true] := by decide
-- These coordinates differ, so a mistaken overlapping handoff is observable.
example : (result dirty normal activity).get 12 = [] := by decide
example : (result dirty normal activity).get 13 = [true] := by decide
example : (result dirty normal activity).get 14 = [true, true] := by decide
example : (result dirty normal activity).get 15 = [true] := by decide
example : (result dirty normal activity).get 6 = dirty.active := by decide
example : (result dirty normal activity).get 7 = dirty.reserved := by decide

-- Direct execution of an early failure; the generic refinement covers success.
set_option maxRecDepth 32768 in
example : BitRegister.run program 16 ⟨.running 0, start dirty (zero 3 0) (zero 3 0)⟩ =
    ⟨.accepted, result dirty (zero 3 0) (zero 3 0)⟩ := rfl
example : BitRegister.run program 182 ⟨.running 0, start dirty (zero 1 1) single⟩ =
    ⟨.accepted, result dirty (zero 1 1) single⟩ := program_run dirty (zero 1 1) single
example : BitRegister.run program 374 ⟨.running 0, start dirty normal activity⟩ =
    ⟨.accepted, result dirty normal activity⟩ := program_run dirty normal activity

-- General contracts require neither caller-supplied seeds nor success evidence.
example {m n : Nat} (r : Registers) (A C : Matrix m n) :
    Exec block (start r A C) (fuel A C) (result r A C) := block_exec r A C
example {m n : Nat} (r : Registers) (A C : Matrix m n) :
    (result r A C).get 8 = SourceCandidateChoice.outputBits (code A C) := output_exact r A C
example {m n : Nat} (A C : Matrix m n) :
    (BilinearSelection.select A C).witness =
      (SourceOrderedSelectorPrelude.selectedSeeds A C).bind fun p =>
        (SourceCandidateSelection.choice A C p.1.1 p.2.1 p.1.2 p.2.2).map
          (SourceCandidateChoice.decode p.1.1 p.2.1 p.1.2 p.2.2) := witness_exact A C
example {m n : Nat} (A C : Matrix m n) :
    fuel A C ≤ 26 * (m * n) + (6 + SourceMatrixEntry.budget m n) * 8 + 77 := fuel_bound A C
example {n : Nat} (F : Family n) (alpha : Affine n) :
    fuel (SourceLinePullback.normalPull F alpha) (SourceLinePullback.activityPull F alpha) ≤
      sourceCostPolynomial.eval (SourceDirectionEncoding.codec.encode ⟨n, [alpha], F⟩).length := source_bound F alpha

run_cmd do
  for name in [
    ``PNP.Concrete.ResidualReduction.SourceOrderedMatrixSelector.handoff_exec,
    ``PNP.Concrete.ResidualReduction.SourceOrderedMatrixSelector.first_found,
    ``PNP.Concrete.ResidualReduction.SourceOrderedMatrixSelector.selected_handoff,
    ``PNP.Concrete.ResidualReduction.SourceOrderedMatrixSelector.prelude_flag,
    ``PNP.Concrete.ResidualReduction.SourceOrderedMatrixSelector.reject_exec,
    ``PNP.Concrete.ResidualReduction.SourceOrderedMatrixSelector.reject_output,
    ``PNP.Concrete.ResidualReduction.SourceOrderedMatrixSelector.finish_exec,
    ``PNP.Concrete.ResidualReduction.SourceOrderedMatrixSelector.block_exec,
    ``PNP.Concrete.ResidualReduction.SourceOrderedMatrixSelector.output_exact,
    ``PNP.Concrete.ResidualReduction.SourceOrderedMatrixSelector.witness_exact,
    ``PNP.Concrete.ResidualReduction.SourceOrderedMatrixSelector.result_coordinates,
    ``PNP.Concrete.ResidualReduction.SourceOrderedMatrixSelector.fuel_bound,
    ``PNP.Concrete.ResidualReduction.SourceOrderedMatrixSelector.source_bound,
    ``PNP.Concrete.ResidualReduction.SourceOrderedMatrixSelector.program_run] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourceOrderedMatrixSelector.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceOrderedMatrixSelector.witness_exact
#print axioms PNP.Concrete.ResidualReduction.SourceOrderedMatrixSelector.source_bound

end PNP.Concrete.ResidualReduction.SourceOrderedMatrixSelector.Regression
