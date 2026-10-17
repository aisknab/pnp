import PNP.Concrete.ResidualReduction.SourceMenuInsertion
import PNP.Concrete.ResidualReduction.SourceMenuFamilyRegression
import PNP.Concrete.ResidualReduction.CoefficientComparisonRegression
import Lean

/-! Exact reference ordering, equality, prefix/suffix preservation and compiled
axiom guards for general insertion. Finite fixtures test the implementation;
they do not turn this component into a complete selector or solver. -/

namespace PNP.Concrete.ResidualReduction.SourceMenuInsertion.Regression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.CoefficientComparison
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceChain
open PNP.Concrete.ResidualReduction.SourceMenuOrder
open PNP.Concrete.ResidualReduction.SourceMenuCompare
open PNP.Concrete.ResidualReduction.SourceMenuInsertStep

private def z : Affine 2 := (false, (false, false))
private def a : Affine 2 := (true, (false, false))
private def b : Affine 2 := (false, (true, false))
private def c : Affine 2 := (true, (true, false))
private def withConstant : Affine 2 := (true, (false, true))
private def dirty : Saved := ⟨[true, false], [false, true], [false, false]⟩
private def abc : BitString := [true, false, false, false, true, false, true, true, false]

example : lower a b = true := rfl
example : lower b a = false := rfl
example : lower b b = true := rfl
example : lower z a = true := rfl
example : aEq a b = false := rfl
example : normalCode withConstant = normalCode a := rfl
example : wordLower (affineWord withConstant) (affineWord a) = false := rfl
example : ¬Homogeneous withConstant := by change ¬(aConstant withConstant = false); decide

example : insertNormal a [] = [a] := rfl
example : insertNormal a [b, c] = [a, b, c] := rfl
example : insertNormal b [a, c] = [a, b, c] := rfl
example : insertNormal c [a, b] = [a, b, c] := rfl
example : insertNormal b [a, b, c] = [a, b, c] := rfl
example : insertNormal z [a, b, c] = [z, a, b, c] := rfl
-- The reference does not search past an earlier insertion point to repair an
-- already-unsorted/duplicated input. The machine must preserve that behavior.
example : insertNormal b [c, b] = [b, c, b] := rfl
example : insertNormal c [b, a] = [b, a, c] := rfl
example : insertNormal c [c, c] = [c, c] := rfl
example : insertNormal (n := 0) false [false] = [false] := rfl

private theorem homogeneous_list {n : Nat} (us : List (Affine n))
    (h : us.all (fun x => decide (aConstant x = false)) = true) :
    ∀ x ∈ us, Homogeneous x := by
  intro x hx
  change aConstant x = false
  exact of_decide_eq_true ((List.all_eq_true.mp h) x hx)

private def Produces {n : Nat} (a : Affine n) (us : List (Affine n)) (prior output : BitString) : Prop :=
  ∃ used after last, Exec block (full (ready a us prior) dirty) used (full after last) ∧
    after.active = [] ∧ after.output = output ∧ used ≤ bound n us.length prior.length
private theorem produces {n : Nat} (a : Affine n) (us : List (Affine n)) (prior output : BitString)
    (ha : Homogeneous a) (hu : us.all (fun x => decide (aConstant x = false)) = true)
    (expected : prior.reverse ++ matrixBits (insertNormal a us) = output) :
    Produces a us prior output := by
  obtain ⟨used, after, last, checked, halted, value, budget⟩ :=
    block_exec a ha us prior dirty (homogeneous_list us hu)
  exact ⟨used, after, last, checked, halted, value.trans expected, budget⟩

example : Produces a [] [] [true, false, false] := produces _ _ _ _ rfl rfl rfl
example : Produces a [b, c] [] abc := produces _ _ _ _ rfl rfl rfl
example : Produces b [a, c] [] abc := produces _ _ _ _ rfl rfl rfl
example : Produces c [a, b] [] abc := produces _ _ _ _ rfl rfl rfl
example : Produces b [a, b, c] [] abc := produces _ _ _ _ rfl rfl rfl
example : Produces z [a, b, c] [] ([false, false, false] ++ abc) := produces _ _ _ _ rfl rfl rfl
example : Produces b [c, b] [] [false, true, false, true, true, false, false, true, false] :=
  produces _ _ _ _ rfl rfl rfl
example : Produces c [b, a] [] [false, true, false, true, false, false, true, true, false] :=
  produces _ _ _ _ rfl rfl rfl
example : Produces c [c, c] [] [true, true, false, true, true, false] :=
  produces _ _ _ _ rfl rfl rfl
example : Produces b [a, c] [false, true] ([true, false] ++ abc) :=
  produces _ _ _ _ rfl rfl rfl
example : Produces a [] [true, false] [false, true, true, false, false] :=
  produces _ _ _ _ rfl rfl rfl
example : Produces (n := 0) false [] [] [false] := produces _ _ _ _ rfl rfl rfl
example : Produces (n := 0) false [false] [] [false] := produces _ _ _ _ rfl rfl rfl
example : Produces (n := 0) false [false, false] [true] [true, false, false] :=
  produces _ _ _ _ rfl rfl rfl

private def ProgramProduces {n : Nat} (a : Affine n) (us : List (Affine n)) (prior output : BitString) : Prop :=
  ∃ used after last, BitRegister.run program (used + 1)
      ⟨.running 0, full (ready a us prior) dirty⟩ = ⟨.accepted, full after last⟩ ∧
    (full after last).get 8 = output ∧ used + 1 ≤ bound n us.length prior.length + 1
private theorem program_produces {n : Nat} (a : Affine n) (us : List (Affine n)) (prior output : BitString)
    (ha : Homogeneous a) (hu : us.all (fun x => decide (aConstant x = false)) = true)
    (expected : prior.reverse ++ matrixBits (insertNormal a us) = output) :
    ProgramProduces a us prior output := by
  obtain ⟨used, after, last, checked, value, budget⟩ :=
    program_run a ha us (homogeneous_list us hu) prior dirty
  exact ⟨used, after, last, checked, value.trans expected, budget⟩
example : ProgramProduces a [b, c] [] abc := program_produces _ _ _ _ rfl rfl rfl
example : ProgramProduces b [a, c] [false, true] ([true, false] ++ abc) :=
  program_produces _ _ _ _ rfl rfl rfl
example : ProgramProduces c [a, b] [] abc := program_produces _ _ _ _ rfl rfl rfl
example : ProgramProduces b [a, b, c] [] abc := program_produces _ _ _ _ rfl rfl rfl
example : (BitRegister.run program 21
    ⟨.running 0, full (ready (n := 0) false [] []) dirty⟩).store.get 8 = [false] := rfl

example {n : Nat} (a : Affine n) (ha : Homogeneous a) (us : List (Affine n))
    (hu : ∀ x ∈ us, Homogeneous x) (prior : BitString) (s : Saved) :
    ∃ used after last, Exec block (full (ready a us prior) s) used (full after last) ∧
      after.active = [] ∧ after.output = prior.reverse ++ matrixBits (insertNormal a us) ∧
      used ≤ bound n us.length prior.length := block_exec a ha us prior s hu
example {n : Nat} (a : Affine n) (us : List (Affine n)) (prior : BitString) :
    (prior.reverse ++ matrixBits (insertNormal a us)).length ≤
      prior.length + (n + 1) * (us.length + 1) := output_bound a us prior
example {n : Nat} (F : Family n) : ∀ x ∈ sourceMenu F, Homogeneous x := source_menu_homogeneous F
example {n : Nat} (a : Affine n) (us : List (Affine n))
    (ha : Homogeneous a) (hu : ∀ x ∈ us, Homogeneous x) :
    ∀ x ∈ insertNormal a us, Homogeneous x := insert_homogeneous a us ha hu

run_cmd do
  for name in [
    ``CoefficientComparison.rightResult_correct,
    ``CoefficientComparison.carry_correct,
    ``CoefficientComparison.compare_correct,
    ``CoefficientComparison.comparison_exec,
    ``CoefficientComparison.normal_comparison_exec,
    ``SourceMenuOrder.binaryValue_append_false,
    ``SourceMenuOrder.homogeneous_value,
    ``SourceMenuOrder.lower_exact,
    ``SourceMenuOrder.equality_flags,
    ``SourceMenuOrder.insert_by_flags,
    ``SourceMenuOrder.row_homogeneous,
    ``SourceMenuOrder.family_homogeneous,
    ``SourceMenuOrder.insert_homogeneous,
    ``SourceMenuOrder.source_menu_homogeneous,
    ``SourceMenuCompare.comparison_exec,
    ``SourceMenuCompare.capture_exec,
    ``SourceMenuCompare.prepare_exec,
    ``SourceMenuCompare.second_exec,
    ``SourceMenuCompare.restore_exec,
    ``SourceMenuCompare.block_exec,
    ``SourceMenuCompare.cost_bound,
    ``SourceMenuCompare.result_first,
    ``SourceMenuCompare.result_second,
    ``SourceMenuCompare.result_cursor,
    ``SourceMenuCompare.result_width,
    ``SourceMenuInsertOutput.append_exec,
    ``SourceMenuInsertOutput.finish_exec,
    ``SourceMenuInsertOutput.end_exec,
    ``SourceMenuInsertOutput.equal_exec,
    ``SourceMenuInsertOutput.before_exec,
    ``SourceMenuInsertOutput.advance_exec,
    ``SourceMenuInsertOutput.end_output,
    ``SourceMenuInsertOutput.equal_output,
    ``SourceMenuInsertOutput.before_output,
    ``SourceMenuInsertStep.loadHead_exec,
    ``SourceMenuInsertStep.gate_exec,
    ``SourceMenuInsertStep.step_exec,
    ``SourceMenuInsertStep.compareCost_bound,
    ``SourceMenuInsertStep.advance_cost_bound,
    ``SourceMenuInsertStep.stop_cost_bound,
    ``SourceMenuInsertStep.advance_state,
    ``SourceMenuInsertStep.end_output,
    ``SourceMenuInsertStep.equal_output,
    ``SourceMenuInsertStep.before_output,
    ``SourceMenuInsertion.body_exec,
    ``SourceMenuInsertion.advance_budget,
    ``SourceMenuInsertion.stop_budget,
    ``SourceMenuInsertion.block_exec,
    ``SourceMenuInsertion.output_bound,
    ``SourceMenuInsertion.program_run] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourceMenuOrder.insert_by_flags
#print axioms PNP.Concrete.ResidualReduction.SourceMenuCompare.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceMenuInsertStep.step_exec
#print axioms PNP.Concrete.ResidualReduction.SourceMenuInsertion.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceMenuInsertion.output_bound
#print axioms PNP.Concrete.ResidualReduction.SourceMenuInsertion.program_run

end PNP.Concrete.ResidualReduction.SourceMenuInsertion.Regression
