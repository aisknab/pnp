import Lean
import PNP.Concrete.ResidualReduction.SourceMatrixWitnessInstructions
import PNP.Concrete.ResidualReduction.SourceSelectorAssemblyRegression

namespace PNP.Concrete.ResidualReduction.SourceMatrixWitness.Regression
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear

private def dirty : Registers :=
  ⟨[false, true, true], [true], [true, false], [false], [true], [true, true], [false, true], [true, false], [false, true]⟩
private def zero (m n : Nat) : Matrix m n := fun _ _ => false
private def single : Matrix 1 1 := fun _ _ => true
private def normal : Matrix 2 3 := fun i j => decide (i.val = 0 ∧ j.val = 2)
private def activity : Matrix 2 3 := fun i j => decide ((i.val = 0 ∧ j.val = 2) ∨ (i.val = 1 ∧ j.val = 1))
private def identity : Matrix 2 2 := fun i j => decide (i.val = j.val)
private def upperLeft : Matrix 2 2 := fun i j => decide (i.val = 0 ∧ j.val = 0)

-- Unit and XOR construction preserve support multiplicity, not set union.
example : (SourceAxisWitness.result dirty (0 : Fin 3) 2 .first).get 8 = [true, false, false] := rfl
example : (SourceAxisWitness.result dirty (0 : Fin 3) 2 .second).get 8 = [false, false, true] := rfl
example : (SourceAxisWitness.result dirty (0 : Fin 3) 2 .both).get 8 = [true, false, true] := rfl
example : (SourceAxisWitness.result dirty (1 : Fin 3) 1 .both).get 8 = [false, false, false] := rfl
example {n : Nat} (i : Fin n) :
    (SourceEncoding.pointCodec n).encode (SourceAxisWitness.point i i .both) = List.replicate n false :=
  SourceAxisWitness.repeated_both_bytes i
example : (SourceAxisWitness.result dirty (0 : Fin 3) 2 .both).get 0 = [false, true, true] := rfl
example : (SourceAxisWitness.result dirty (0 : Fin 3) 2 .both).get 4 = dirty.sign := rfl
example : (SourceAxisWitness.result dirty (0 : Fin 3) 2 .both).get 6 = dirty.active := rfl
example : (SourceAxisWitness.result dirty (0 : Fin 3) 2 .both).get 7 = dirty.reserved := rfl
example : (SourceAxisWitness.result dirty (0 : Fin 3) 2 .both).get 12 = [] := rfl
example : (SourceAxisWitness.result dirty (0 : Fin 3) 2 .both).get 13 = [] := rfl
example : SourceAxisWitness.fuel (0 : Fin 1) 0 .first = 21 := rfl
example : SourceAxisWitness.fuel (0 : Fin 1) 0 .both = 45 := rfl
example : SourceAxisWitness.fuel (0 : Fin 3) 2 .both = 73 := rfl
set_option maxRecDepth 32768 in
example : BitRegister.run SourceAxisWitness.program 46
    ⟨.running 0, SourceAxisWitness.start dirty (0 : Fin 1) 0 .both⟩ =
      ⟨.accepted, SourceAxisWitness.result dirty (0 : Fin 1) 0 .both⟩ := rfl

-- The second vector must not overwrite the first or consume the caller's suffix.
example : (SourceWitnessPair.result dirty (0 : Fin 2) 1 (0 : Fin 3) 2 (.both, .second)).get 17 =
    [true, true] := rfl
example : (SourceWitnessPair.result dirty (0 : Fin 2) 1 (0 : Fin 3) 2 (.both, .second)).get 8 =
    [false, false, true] := rfl
example : (SourceWitnessPair.result dirty (0 : Fin 2) 1 (0 : Fin 3) 2 (.both, .second)).get 0 =
    dirty.input := rfl
example : (SourceWitnessPair.result dirty (0 : Fin 1) 0 (0 : Fin 1) 0 (.both, .both)).get 17 = [false] := rfl
example : (SourceWitnessPair.result dirty (0 : Fin 1) 0 (0 : Fin 1) 0 (.both, .both)).get 8 = [false] := rfl
example : SourceWitnessPair.fuel (0 : Fin 1) 0 (0 : Fin 1) 0 (.first, .first) = 47 := rfl

-- The full search takes no supplied indices. It clears stale success flags.
example : observed (result dirty normal (zero 2 3)) = none := by decide
example : observed (result dirty normal normal) = none := by decide
example : observed (result dirty (zero 0 3) (zero 0 3)) = none := rfl
example : observed (result dirty (zero 3 0) (zero 3 0)) = none := rfl
example : observed (result dirty (zero 0 0) (zero 0 0)) = none := rfl
example : (result dirty normal (zero 2 3)).get 4 = [] := by decide
example : (result dirty normal normal).get 4 = [] := by decide
example : fuel normal (zero 2 3) = 53 := by decide
example : fuel normal normal = 98 := by decide
example : fuel (zero 3 0) (zero 3 0) = 17 := rfl

-- A successful vector may start with false; presence is not its first bit.
example : observed (result dirty normal activity) = some ([false, true], [false, true, false]) := by decide
example : (result dirty normal activity).get 4 = [true] := by decide
example : observed (result dirty identity upperLeft) = some ([true, true], [true, true]) := by decide
example : observed (result dirty (zero 1 1) single) = some ([true], [true]) := rfl
example : fuel (zero 1 1) single = 243 := rfl
example : fuel normal activity = 458 := by decide
example : fuel identity upperLeft = 430 := by decide
example : (result dirty normal activity).get 6 = dirty.active := by decide
example : (result dirty normal activity).get 7 = dirty.reserved := by decide
example : BitRegister.run program 244 ⟨.running 0, start dirty (zero 1 1) single⟩ =
    ⟨.accepted, result dirty (zero 1 1) single⟩ := program_run dirty (zero 1 1) single
example : BitRegister.run program 459 ⟨.running 0, start dirty normal activity⟩ =
    ⟨.accepted, result dirty normal activity⟩ := program_run dirty normal activity

-- All dimensions and every selected axis, not just regression instances.
example {n : Nat} (i k : Fin n) (a : SourceCandidateChoice.Axis) :
    (SourceAxisWitness.result dirty i k a).get 8 =
      (SourceEncoding.pointCodec n).encode (sumUnits (SourceCandidateChoice.support i k a)) :=
  SourceAxisWitness.output_exact dirty i k a
example {n : Nat} (i k : Fin n) (a : SourceCandidateChoice.Axis) (L : Nat) (h : n ≤ L) :
    ∃ used ≤ SourceAxisWitness.costPolynomial.eval L,
      Exec SourceAxisWitness.block (SourceAxisWitness.start dirty i k a) used (SourceAxisWitness.result dirty i k a) :=
  SourceAxisWitness.bounded_exec dirty i k a L h
example {m n : Nat} (r : Registers) (A C : Matrix m n) :
    Exec block (start r A C) (fuel A C) (result r A C) := block_exec r A C
example {m n : Nat} (r : Registers) (A C : Matrix m n) :
    observed (result r A C) =
      (BilinearSelection.select A C).witness.map (fun w =>
        ((SourceEncoding.pointCodec m).encode (sumUnits w.1),
          (SourceEncoding.pointCodec n).encode (sumUnits w.2))) := result_exact r A C
example {n : Nat} (F : Family n) (alpha : Affine n) :
    fuel (SourceLinePullback.normalPull F alpha) (SourceLinePullback.activityPull F alpha) ≤
      sourceCostPolynomial.eval (SourceDirectionEncoding.codec.encode ⟨n, [alpha], F⟩).length := source_bound F alpha

run_cmd do
  for name in [
    ``PNP.Concrete.ResidualReduction.SourceAxisWitness.point_exact,
    ``PNP.Concrete.ResidualReduction.SourceAxisWitness.point_xor_bytes,
    ``PNP.Concrete.ResidualReduction.SourceAxisWitness.xor_reversed_bytes,
    ``PNP.Concrete.ResidualReduction.SourceAxisWitness.repeated_both,
    ``PNP.Concrete.ResidualReduction.SourceAxisWitness.repeated_both_bytes,
    ``PNP.Concrete.ResidualReduction.SourceAxisWitness.prepare_exec,
    ``PNP.Concrete.ResidualReduction.SourceAxisWitness.unit_exec,
    ``PNP.Concrete.ResidualReduction.SourceAxisWitness.single_exec,
    ``PNP.Concrete.ResidualReduction.SourceAxisWitness.both_exec,
    ``PNP.Concrete.ResidualReduction.SourceAxisWitness.block_exec,
    ``PNP.Concrete.ResidualReduction.SourceAxisWitness.output_exact,
    ``PNP.Concrete.ResidualReduction.SourceAxisWitness.tail_preserved,
    ``PNP.Concrete.ResidualReduction.SourceAxisWitness.fuel_bound,
    ``PNP.Concrete.ResidualReduction.SourceAxisWitness.bounded_exec,
    ``PNP.Concrete.ResidualReduction.SourceAxisWitness.program_run,
    ``PNP.Concrete.ResidualReduction.SourceWitnessPair.handoff_exec,
    ``PNP.Concrete.ResidualReduction.SourceWitnessPair.block_exec,
    ``PNP.Concrete.ResidualReduction.SourceWitnessPair.left_exact,
    ``PNP.Concrete.ResidualReduction.SourceWitnessPair.right_exact,
    ``PNP.Concrete.ResidualReduction.SourceWitnessPair.tail_preserved,
    ``PNP.Concrete.ResidualReduction.SourceWitnessPair.fuel_bound,
    ``PNP.Concrete.ResidualReduction.SourceWitnessPair.program_run,
    ``PNP.Concrete.ResidualReduction.SourceMatrixWitness.relocate_exec,
    ``PNP.Concrete.ResidualReduction.SourceMatrixWitness.prepare_choice_exec,
    ``PNP.Concrete.ResidualReduction.SourceMatrixWitness.handoff_exec,
    ``PNP.Concrete.ResidualReduction.SourceMatrixWitness.selected_handoff,
    ``PNP.Concrete.ResidualReduction.SourceMatrixWitness.after_code,
    ``PNP.Concrete.ResidualReduction.SourceMatrixWitness.finish_exec,
    ``PNP.Concrete.ResidualReduction.SourceMatrixWitness.block_exec,
    ``PNP.Concrete.ResidualReduction.SourceMatrixWitness.selected_witness,
    ``PNP.Concrete.ResidualReduction.SourceMatrixWitness.reject_observed,
    ``PNP.Concrete.ResidualReduction.SourceMatrixWitness.successful_observed,
    ``PNP.Concrete.ResidualReduction.SourceMatrixWitness.result_exact,
    ``PNP.Concrete.ResidualReduction.SourceMatrixWitness.finish_bound,
    ``PNP.Concrete.ResidualReduction.SourceMatrixWitness.fuel_bound,
    ``PNP.Concrete.ResidualReduction.SourceMatrixWitness.source_bound,
    ``PNP.Concrete.ResidualReduction.SourceMatrixWitness.program_run] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourceAxisWitness.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceAxisWitness.both_exec
#print axioms PNP.Concrete.ResidualReduction.SourceWitnessPair.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceMatrixWitness.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceMatrixWitness.result_exact
#print axioms PNP.Concrete.ResidualReduction.SourceMatrixWitness.source_bound

end PNP.Concrete.ResidualReduction.SourceMatrixWitness.Regression
