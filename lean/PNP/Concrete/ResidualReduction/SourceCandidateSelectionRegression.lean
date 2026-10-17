import Lean
import PNP.Concrete.ResidualReduction.SourceCandidateSelection
import PNP.Concrete.ResidualReduction.SourceOrderedScanRegression

namespace PNP.Concrete.ResidualReduction.SourceCandidateSelection.Regression
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceCandidateCorners (data store)

private def clean : Registers := ⟨[], [], [], [], [], [], [], [], []⟩
private def dirty : Registers :=
  ⟨[false, true], [true], [true, false], [false], [true], [true, true], [false, true], [true, false], [false, true]⟩
private def zero (m n : Nat) : Matrix m n := fun _ _ => false
private def identity : Matrix 2 2 := fun i j => decide (i.val = j.val)
private def upperLeft : Matrix 2 2 := fun i j => decide (i.val = 0 ∧ j.val = 0)
private def single : Matrix 1 1 := fun _ _ => true
private def fifthA : Matrix 2 2 := fun i j => decide (i.val = 0 ∧ j.val = 0)
private def fifthC : Matrix 2 2 := fun i j => decide (i.val = j.val)

-- Arbitrary indexed access really constructs and consumes the address.
example : SourceMatrixEntry.fuel 2 0 0 = 7 := rfl
example : SourceMatrixEntry.fuel 2 1 1 = 26 := rfl
example : SourceMatrixEntry.budget 2 2 = 45 := rfl
set_option maxRecDepth 32768 in
example : BitRegister.run SourceMatrixEntry.program 27
    ⟨.running 0, (SourceMatrixEntry.start dirty (SourceActivityMapAlgebra.coefficientMatrixBits identity) 2 1 1).store⟩ =
      ⟨.accepted, (SourceMatrixEntry.result dirty 2 true).store⟩ := rfl
example {m n : Nat} (M : Matrix m n) (i : Fin m) (j : Fin n) :
    Exec SourceMatrixEntry.block
      (SourceMatrixEntry.start dirty (SourceActivityMapAlgebra.coefficientMatrixBits M) n i.val j.val).store
      (SourceMatrixEntry.fuel n i.val j.val) (SourceMatrixEntry.result dirty n (M i j)).store :=
  SourceMatrixEntry.matrix_exec dirty M i j

-- The ninth candidate is genuinely needed: the first eight all fail.
example : choice identity upperLeft 0 1 0 1 = some (.both, .both) := by decide
example : SourceCandidateChoice.candidateChecks
    (SourceCandidateChoice.corners identity 0 1 0 1) (SourceCandidateChoice.corners upperLeft 0 1 0 1) = 9 := by decide
example : (BilinearSelection.select identity upperLeft).witness = some ([0, 1], [0, 1]) := by decide
example : choice (zero 2 2) upperLeft 0 1 0 1 = some (.first, .first) := by decide
example : choice fifthA fifthC 0 1 0 1 = some (.second, .second) := by decide
example : SourceCandidateChoice.candidateChecks
    (SourceCandidateChoice.corners fifthA 0 1 0 1) (SourceCandidateChoice.corners fifthC 0 1 0 1) = 5 := by decide
example : choice identity identity 0 1 0 1 = none := by decide
example : SourceCandidateChoice.candidateChecks
    (SourceCandidateChoice.corners identity 0 1 0 1) (SourceCandidateChoice.corners identity 0 1 0 1) = 9 := by decide

-- Duplicate seed indices are allowed; both-support lists cancel by XOR.
example : choice (zero 1 1) single 0 0 0 0 = some (.first, .first) := rfl
example : SourceCandidateChoice.value (SourceCandidateChoice.corners single 0 0 0 0) (.both, .first) = false := rfl
example : SourceCandidateChoice.value (SourceCandidateChoice.corners single 0 0 0 0) (.first, .both) = false := rfl
example : SourceCandidateChoice.decode (0 : Fin 1) 0 (0 : Fin 1) 0 (.both, .both) = ([0, 0], [0, 0]) := rfl

-- All eight bits are read from the matrices in the required decision order.
example : (SourceCandidateCorners.result dirty identity upperLeft 0 1 0 1).output =
    [true, false, false, true, true, false, false, false] := by decide
example : SourceCandidateCorners.fuel (0 : Fin 2) 1 (0 : Fin 2) 1 = 182 := rfl
example : fuel identity upperLeft 0 1 0 1 = 206 := by decide
example : fuel identity identity 0 1 0 1 = 202 := by decide
example : (result dirty identity upperLeft 0 1 0 1).output = [true, true, true, true, true] := by decide
example : (result dirty fifthA fifthC 0 1 0 1).output = [true, false, true, false, true] := by decide
example : (result dirty (zero 2 2) upperLeft 0 1 0 1).output = [true, true, false, true, false] := by decide
example : (result dirty identity identity 0 1 0 1).output = [false] := by decide
example : (result dirty identity upperLeft 0 1 0 1).active = dirty.active := rfl
example : (result dirty identity upperLeft 0 1 0 1).reserved = dirty.reserved := rfl
example : (result dirty identity upperLeft 0 1 0 1).input = [] := rfl
example : (store (result dirty identity upperLeft 0 1 0 1) (data identity upperLeft 0 1 0 1)).get 12 = [] := rfl
example : (store (result dirty identity upperLeft 0 1 0 1) (data identity upperLeft 0 1 0 1)).get 13 = [true] := rfl
example : (store (result dirty identity upperLeft 0 1 0 1) (data identity upperLeft 0 1 0 1)).get 14 = [] := rfl
example : (store (result dirty identity upperLeft 0 1 0 1) (data identity upperLeft 0 1 0 1)).get 15 = [true] := rfl

set_option maxRecDepth 32768 in
example : BitRegister.run SourceCandidateChoice.program 23
    ⟨.running 0, ({clean with input := [true, false, false, true, true, false, false, false]}).store⟩ =
      ⟨.accepted, ({clean with output := [true, true, true, true, true]}).store⟩ := rfl
example : BitRegister.run program 131 ⟨.running 0, store dirty (data (zero 1 1) single 0 0 0 0)⟩ =
    ⟨.accepted, store (result dirty (zero 1 1) single 0 0 0 0) (data (zero 1 1) single 0 0 0 0)⟩ :=
  program_run dirty (zero 1 1) single 0 0 0 0

-- General exactness, not just the concrete fixtures above.
example {m n : Nat} (A C : Matrix m n) (i k : Fin m) (j l : Fin n) :
    (choice A C i k j l).map (SourceCandidateChoice.decode i k j l) =
      (BilinearSelection.scan (BilinearSelection.accepts A C) (BilinearSelection.candidates i k j l)).1 :=
  choice_exact A C i k j l
example {m n : Nat} (A C : Matrix m n) (i k : Fin m) (j l : Fin n) :
    Exec block (store dirty (data A C i k j l)) (fuel A C i k j l)
      (store (result dirty A C i k j l) (data A C i k j l)) := block_exec dirty A C i k j l
example {m n : Nat} (A C : Matrix m n) (i k : Fin m) (j l : Fin n) :
    (store (result dirty A C i k j l) (data A C i k j l)).get 8 =
      SourceCandidateChoice.outputBits (choice A C i k j l) := output_exact dirty A C i k j l
example {m n : Nat} (A C : Matrix m n) (i k : Fin m) (j l : Fin n) :
    fuel A C i k j l ≤ (6 + SourceMatrixEntry.budget m n) * 8 + 26 := fuel_bound A C i k j l
example {m n : Nat} (A C : Matrix m n) (i k : Fin m) (j l : Fin n)
    (L : Nat) (hm : m ≤ L) (hn : n ≤ L) :
    ∃ used ≤ costPolynomial.eval L, Exec block (store dirty (data A C i k j l)) used
      (store (result dirty A C i k j l) (data A C i k j l)) := bounded_exec dirty A C i k j l L hm hn
example {n : Nat} (F : Family n) (alpha : Affine n)
    (i k : Fin (SourceLinePullback.leftSpace F alpha).parameters)
    (j l : Fin (SourceLinePullback.rightSpace F alpha).parameters) :
    fuel (SourceLinePullback.normalPull F alpha) (SourceLinePullback.activityPull F alpha) i k j l ≤
      sourceCostPolynomial.eval (SourceDirectionEncoding.codec.encode ⟨n, [alpha], F⟩).length := source_bound F alpha i k j l

run_cmd do
  for name in [
    ``PNP.Concrete.ResidualReduction.SourceMatrixEntry.add_exec,
    ``PNP.Concrete.ResidualReduction.SourceMatrixEntry.row_step_exec,
    ``PNP.Concrete.ResidualReduction.SourceMatrixEntry.row_loop_exec,
    ``PNP.Concrete.ResidualReduction.SourceMatrixEntry.seek_exec,
    ``PNP.Concrete.ResidualReduction.SourceMatrixEntry.read_exec,
    ``PNP.Concrete.ResidualReduction.SourceMatrixEntry.block_exec,
    ``PNP.Concrete.ResidualReduction.SourceMatrixEntry.matrix_bit,
    ``PNP.Concrete.ResidualReduction.SourceMatrixEntry.matrix_exec,
    ``PNP.Concrete.ResidualReduction.SourceMatrixEntry.fuel_bound,
    ``PNP.Concrete.ResidualReduction.SourceMatrixEntry.program_run,
    ``PNP.Concrete.ResidualReduction.SourceCandidateChoice.value_exact,
    ``PNP.Concrete.ResidualReduction.SourceCandidateChoice.accepts_exact,
    ``PNP.Concrete.ResidualReduction.SourceCandidateChoice.candidates_decode,
    ``PNP.Concrete.ResidualReduction.SourceCandidateChoice.scan_map,
    ``PNP.Concrete.ResidualReduction.SourceCandidateChoice.candidate_scan_exact,
    ``PNP.Concrete.ResidualReduction.SourceCandidateChoice.choose_exact,
    ``PNP.Concrete.ResidualReduction.SourceCandidateChoice.checks_bound,
    ``PNP.Concrete.ResidualReduction.SourceCandidateChoice.axisBits_length,
    ``PNP.Concrete.ResidualReduction.SourceCandidateChoice.output_length,
    ``PNP.Concrete.ResidualReduction.SourceCandidateChoice.output_length_bound,
    ``PNP.Concrete.ResidualReduction.SourceCandidateChoice.emit_exec,
    ``PNP.Concrete.ResidualReduction.SourceCandidateChoice.readEight_exec,
    ``PNP.Concrete.ResidualReduction.SourceCandidateChoice.block_exec,
    ``PNP.Concrete.ResidualReduction.SourceCandidateChoice.fuel_bound,
    ``PNP.Concrete.ResidualReduction.SourceCandidateChoice.program_run,
    ``PNP.Concrete.ResidualReduction.SourceCandidateCorners.prepare_exec,
    ``PNP.Concrete.ResidualReduction.SourceCandidateCorners.read_exec,
    ``PNP.Concrete.ResidualReduction.SourceCandidateCorners.requests_exec,
    ``PNP.Concrete.ResidualReduction.SourceCandidateCorners.block_exec,
    ``PNP.Concrete.ResidualReduction.SourceCandidateCorners.requests_bound,
    ``PNP.Concrete.ResidualReduction.SourceCandidateCorners.fuel_bound,
    ``PNP.Concrete.ResidualReduction.SourceCandidateCorners.output_exact,
    ``PNP.Concrete.ResidualReduction.SourceCandidateSelection.handoff_exec,
    ``PNP.Concrete.ResidualReduction.SourceCandidateSelection.block_exec,
    ``PNP.Concrete.ResidualReduction.SourceCandidateSelection.output_exact,
    ``PNP.Concrete.ResidualReduction.SourceCandidateSelection.choice_exact,
    ``PNP.Concrete.ResidualReduction.SourceCandidateSelection.fuel_bound,
    ``PNP.Concrete.ResidualReduction.SourceCandidateSelection.entry_budget_mono,
    ``PNP.Concrete.ResidualReduction.SourceCandidateSelection.costPolynomial_eval,
    ``PNP.Concrete.ResidualReduction.SourceCandidateSelection.bounded_exec,
    ``PNP.Concrete.ResidualReduction.SourceCandidateSelection.sourceCostPolynomial_eval,
    ``PNP.Concrete.ResidualReduction.SourceCandidateSelection.source_bound,
    ``PNP.Concrete.ResidualReduction.SourceCandidateSelection.program_run] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourceMatrixEntry.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceCandidateChoice.candidate_scan_exact
#print axioms PNP.Concrete.ResidualReduction.SourceCandidateChoice.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceCandidateCorners.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceCandidateSelection.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceCandidateSelection.source_bound

end PNP.Concrete.ResidualReduction.SourceCandidateSelection.Regression
