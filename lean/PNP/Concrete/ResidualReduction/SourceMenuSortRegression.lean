import PNP.Concrete.ResidualReduction.SourceMenuBudget
import PNP.Concrete.ResidualReduction.SourceMenuInsertionRegression
import Lean

/-! Source-to-sorted-menu regressions. Independent expected bytes cover
reordering, duplicates, degenerate rows, constants, zero dimension and dirty
scratch words. General statements and compiled axiom guards remain the proof
authority; these fixtures do not establish a complete selector or solver. -/

namespace PNP.Concrete.ResidualReduction.SourceMenuSort.Regression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceChain
open PNP.Concrete.ResidualReduction.SourceMenuOrder

private def z : Affine 2 := (false, (false, false))
private def a : Affine 2 := (true, (false, false))
private def b : Affine 2 := (false, (true, false))
private def c : Affine 2 := (true, (true, false))
private def ac : Affine 2 := (true, (false, true))
private def bc : Affine 2 := (false, (true, true))
private def zc : Affine 2 := (false, (false, true))
private def ab : Row 2 := ⟨true, a, b⟩
private def cb : Row 2 := ⟨false, c, b⟩
private def constants : Row 2 := ⟨false, ac, bc⟩
private def repeated : Row 2 := ⟨true, a, ac⟩
private def zeroLeft : Row 2 := ⟨false, zc, b⟩
private def zeroRight : Row 2 := ⟨true, a, zc⟩
private def dirty : SourceMenuCompare.Saved := ⟨[true, false], [false, true], [false, false]⟩
private def held : SourceMenuSortStep.Held := ⟨[true, true, false], [false, false, true]⟩
private def abc : BitString := [true, false, false, false, true, false, true, true, false]

example : fold [c, b, a] [] = [a, b, c] := rfl
example : fold [a, b, c] [] = [a, b, c] := rfl
example : fold [b, a, c, a, b, c] [] = [a, b, c] := rfl
example : fold [a, a, a] [] = [a] := rfl
example : fold [z, c, z, a, b] [] = [z, a, b, c] := rfl
example : fold [] [c, b, b] = [c, b, b] := rfl
example : fold [b] [c, b] = [b, c, b] := rfl
example : fold (n := 0) [false, false] [] = [false] := rfl
example : SourceMenuFromFamily.candidates [ab] = [c, b, a] := rfl
example : SourceMenuFromFamily.candidates [cb] = [a, b, c] := rfl
example : sourceMenu [ab, cb, constants] = [a, b, c] := rfl
example : sourceMenu [repeated, zeroLeft, zeroRight] = [] := rfl

private theorem homogeneous_list {n : Nat} (us : List (Affine n))
    (h : us.all (fun x => decide (aConstant x = false)) = true) :
    ∀ x ∈ us, Homogeneous x := by
  intro x hx
  change aConstant x = false
  exact of_decide_eq_true ((List.all_eq_true.mp h) x hx)

private def SortProduces {n : Nat} (xs us : List (Affine n)) (word : BitString) : Prop :=
  ∃ used after, Exec block (SourceMenuSortStep.full (SourceMenuSortStep.initial xs us) dirty held)
    used after ∧ after.get 7 = word ∧ used ≤ bound n (xs.length + us.length) xs.length

private theorem sort_produces {n : Nat} (xs us : List (Affine n)) (word : BitString)
    (hx : xs.all (fun x => decide (aConstant x = false)) = true)
    (hu : us.all (fun x => decide (aConstant x = false)) = true)
    (expected : matrixBits (fold xs us) = word) : SortProduces xs us word := by
  obtain ⟨used, last, saved, checked, budget⟩ :=
    block_exec xs us dirty held (xs.length + us.length)
      (homogeneous_list xs hx) (homogeneous_list us hu) (Nat.le_refl _)
  exact ⟨used, SourceMenuSortStep.full (SourceMenuSortStep.initial [] (fold xs us)) last saved,
    checked, expected, budget⟩

example : SortProduces ([] : List (Affine 2)) [] [] := sort_produces _ _ _ rfl rfl rfl
example : SortProduces [c, b, a] [] abc := sort_produces _ _ _ rfl rfl rfl
example : SortProduces [a, b, c] [] abc := sort_produces _ _ _ rfl rfl rfl
example : SortProduces [b, a, c, a, b, c] [] abc := sort_produces _ _ _ rfl rfl rfl
example : SortProduces [a, a, a] [] [true, false, false] := sort_produces _ _ _ rfl rfl rfl
example : SortProduces [z, c, z, a, b] [] ([false, false, false] ++ abc) :=
  sort_produces _ _ _ rfl rfl rfl
example : SortProduces [b] [c, b]
    [false, true, false, true, true, false, false, true, false] := sort_produces _ _ _ rfl rfl rfl
example : SortProduces [] [c, b, b]
    [true, true, false, false, true, false, false, true, false] := sort_produces _ _ _ rfl rfl rfl
example : SortProduces (n := 0) [false, false] [] [false] := sort_produces _ _ _ rfl rfl rfl

private def FamilyProduces {n : Nat} (F : Family n) (word : BitString) : Prop :=
  ∃ used after, BitRegister.run SourceMenuFromFamily.program (used + 1)
      ⟨.running 0, SourceMenuFromFamily.initial F dirty held⟩ = ⟨.accepted, after⟩ ∧
    after.get 7 = word ∧ used + 1 ≤ SourceMenuFromFamily.bound n F.length + 1

private theorem family_produces {n : Nat} (F : Family n) (word : BitString)
    (expected : matrixBits (sourceMenu F) = word) : FamilyProduces F word := by
  obtain ⟨used, last, saved, checked, output, budget⟩ := SourceMenuFromFamily.program_run F dirty held
  exact ⟨used, SourceMenuFromFamily.terminal F last saved, checked, output.trans expected, budget⟩

example : FamilyProduces ([] : Family 0) [] := family_produces _ _ rfl
example : FamilyProduces ([] : Family 2) [] := family_produces _ _ rfl
example : FamilyProduces (n := 0) [⟨true, false, true⟩, ⟨false, true, true⟩] [] :=
  family_produces _ _ rfl
example : FamilyProduces (n := 1) [⟨true, (true, true), (true, false)⟩] [] := family_produces _ _ rfl
example : FamilyProduces [ab] abc := family_produces _ _ rfl
example : FamilyProduces [cb] abc := family_produces _ _ rfl
example : FamilyProduces [constants] abc := family_produces _ _ rfl
example : FamilyProduces [ab, ab] abc := family_produces _ _ rfl
example : FamilyProduces [ab, cb, constants] abc := family_produces _ _ rfl
example : FamilyProduces [cb, ab, repeated] abc := family_produces _ _ rfl
example : FamilyProduces [zeroLeft, zeroRight, repeated] [] := family_produces _ _ rfl
example : FamilyProduces [zeroLeft, constants, repeated, zeroRight] abc := family_produces _ _ rfl

-- Small literal instruction reductions complement the general execution theorem.
example : (BitRegister.run program 2
    ⟨.running 0, SourceMenuSortStep.full (SourceMenuSortStep.initial ([] : List (Affine 2)) []) dirty held⟩).control =
    .accepted := rfl
example : (BitRegister.run SourceMenuFromFamily.program 12
    ⟨.running 0, SourceMenuFromFamily.initial ([] : Family 2) dirty held⟩).store.get 7 = [] :=
  congrArg (fun r : BitRegister.Configuration 14 => r.store.get 7)
    ((SourceMenuFromFamily.empty_exec 2 dirty held).program_run 0 7)

example {n : Nat} (xs us : List (Affine n)) : (fold xs us).length ≤ xs.length + us.length :=
  fold_length xs us
example {n : Nat} (xs us : List (Affine n)) :
    (matrixBits (fold xs us)).length ≤ (n + 1) * (xs.length + us.length) := output_bound xs us
example {n : Nat} (F : Family n) :
    SourceMenuSort.fold (SourceMenuFromFamily.candidates F) [] = sourceMenu F :=
  SourceMenuFromFamily.fold_exact F
example {n : Nat} (F : Family n) (s : SourceMenuCompare.Saved) (t : SourceMenuSortStep.Held) :
    ∃ used last saved, Exec SourceMenuFromFamily.block (SourceMenuFromFamily.initial F s t) used
      (SourceMenuFromFamily.terminal F last saved) ∧ used ≤ SourceMenuFromFamily.bound n F.length :=
  SourceMenuFromFamily.block_exec F s t
example {n : Nat} (F : Family n) :
    (matrixBits (sourceMenu F)).length ≤ (n + 1) * (3 * F.length) := SourceMenuFromFamily.output_bound F

example {n : Nat} (F : Family n) :
    SourceMenuFromFamily.bound n F.length ≤ SourceMenuBudget.costPolynomial.eval
      (SourceMatrixEncoding.codec.encode ⟨n, F⟩).length := SourceMenuBudget.original_input_bound F
example {n : Nat} (F : Family n) :
    (matrixBits (sourceMenu F)).length ≤ 3 * (SourceMatrixEncoding.codec.encode ⟨n, F⟩).length :=
  SourceMenuBudget.output_original_bound F

run_cmd do
  for name in [
    ``SourceMenuSortStep.load_exec,
    ``SourceMenuSortStep.capture_exec,
    ``SourceMenuSortStep.prepare_exec,
    ``SourceMenuSortStep.enter_exec,
    ``SourceMenuSortStep.reload_exec,
    ``SourceMenuSortStep.restore_exec,
    ``SourceMenuSortStep.block_exec,
    ``SourceMenuSortStep.bound_mono,
    ``SourceMenuSort.fold_length,
    ``SourceMenuSort.fold_homogeneous,
    ``SourceMenuSort.input_present,
    ``SourceMenuSort.advance_budget,
    ``SourceMenuSort.block_exec,
    ``SourceMenuSort.output_bound,
    ``SourceMenuSort.program_run,
    ``SourceMenuFromFamily.candidates_homogeneous,
    ``SourceMenuFromFamily.candidates_length,
    ``SourceMenuFromFamily.fold_exact,
    ``SourceMenuFromFamily.prepare_exec,
    ``SourceMenuFromFamily.block_exec,
    ``SourceMenuFromFamily.empty_exec,
    ``SourceMenuFromFamily.output_bound,
    ``SourceMenuFromFamily.program_run,
    ``SourceMenuBudget.costPolynomial_eval,
    ``SourceMenuBudget.bounded_cost,
    ``SourceMenuBudget.original_input_bound,
    ``SourceMenuBudget.output_original_bound,
    ``SourceMenuBudget.block_original_bound,
    ``SourceMenuBudget.program_original_bound] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourceMenuSortStep.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceMenuSort.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceMenuSort.program_run
#print axioms PNP.Concrete.ResidualReduction.SourceMenuFromFamily.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceMenuFromFamily.output_bound
#print axioms PNP.Concrete.ResidualReduction.SourceMenuFromFamily.program_run

end PNP.Concrete.ResidualReduction.SourceMenuSort.Regression
