/-
Copyright (c) 2026 PNP Labs.

Source-specialized selection in the canonical variable-width paired rows.
Each row width is derived as tapeWidth + length. The arithmetic cursor
increments that width and subtracts it from the residual coordinate; it does
not receive a width table or materialize the family. These are specification
and loop-invariant results, not a raw-machine runtime theorem.
-/

import PNP.Concrete.CookLevinBuilderInitialCellCoordinates

namespace PNP.Concrete.CookLevin.BuilderInitialLengthSelection

open VerifierTableauProblem

/-- Exact total width of consecutive blocks with widths width, width+1, ... . -/
def rowSpan : Nat → Nat → Nat
  | 0, _ => 0
  | count + 1, width => width + rowSpan count (width + 1)

/-- One arithmetic cursor; no externally supplied row family or width table. -/
def locate : (count : Nat) → Nat → Nat → Option (Fin count × Nat)
  | 0, _, _ => none
  | count + 1, width, coordinate =>
      if coordinate < width then some (⟨0, Nat.zero_lt_succ count⟩, coordinate)
      else (locate count (width + 1) (coordinate - width)).map
        (fun found => (found.1.succ, found.2))

/-- Number of row comparisons in the arithmetic specification, not machine steps. -/
def iterations : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | count + 1, width, coordinate =>
      if coordinate < width then 1 else 1 + iterations count (width + 1) (coordinate - width)

private theorem shifted_widths (count width : Nat) :
    (fun position : Fin count => width + position.succ.val) =
      (fun position : Fin count => (width + 1) + position.val) := by
  funext position
  change width + (position.val + 1) = (width + 1) + position.val
  omega

theorem rowSpan_eq_totalWidth (count width : Nat) :
    rowSpan count width = DirectSlot.totalWidth count (fun position => width + position.val) := by
  induction count generalizing width with
  | zero => rfl
  | succ count ih =>
      rw [rowSpan, DirectSlot.totalWidth, shifted_widths]
      simp only [Nat.add_zero]
      rw [ih]

/-- A derived cursor result includes the exact prefix offset and both bounds. -/
theorem locate_spec (count width coordinate : Nat) :
    match locate count width coordinate with
    | none => rowSpan count width ≤ coordinate
    | some (position, offset) =>
        offset < width + position.val ∧
        coordinate = rowSpan position.val width + offset ∧
        coordinate < rowSpan count width := by
  induction count generalizing width coordinate with
  | zero => exact Nat.zero_le coordinate
  | succ count ih =>
      by_cases hFirst : coordinate < width
      · simp only [locate, if_pos hFirst, rowSpan, Nat.add_zero, Nat.zero_add]
        refine ⟨hFirst, True.intro, ?_⟩
        omega
      · have hTail := ih (width + 1) (coordinate - width)
        cases hFound : locate count (width + 1) (coordinate - width) with
        | none =>
            simp only [hFound] at hTail
            simp only [locate, if_neg hFirst, hFound, Option.map_none, rowSpan]
            omega
        | some found =>
            rcases found with ⟨position, offset⟩
            simp only [hFound] at hTail
            simp only [locate, if_neg hFirst, hFound, Option.map_some]
            change offset < width + (position.val + 1) ∧
              coordinate = rowSpan (position.val + 1) width + offset ∧
              coordinate < rowSpan (count + 1) width
            rw [rowSpan, rowSpan]
            refine ⟨?_, ?_, ?_⟩ <;> omega

theorem locate_none_iff (count width coordinate : Nat) :
    locate count width coordinate = none ↔ rowSpan count width ≤ coordinate := by
  have hSpec := locate_spec count width coordinate
  cases hFound : locate count width coordinate with
  | none =>
      simp only [hFound] at hSpec
      constructor
      · intro _
        exact hSpec
      · intro _
        rfl
  | some found =>
      rcases found with ⟨position, offset⟩
      simp only [hFound] at hSpec
      constructor
      · intro impossible
        cases impossible
      · intro hOutside
        have hInside := hSpec.2.2
        omega

theorem locate_some_bounds (count width coordinate : Nat) (position : Fin count) (offset : Nat)
    (hFound : locate count width coordinate = some (position, offset)) :
    offset < width + position.val ∧ coordinate = rowSpan position.val width + offset ∧
      coordinate < rowSpan count width := by
  have h := locate_spec count width coordinate
  simpa only [hFound] using h

theorem iterations_le (count width coordinate : Nat) : iterations count width coordinate ≤ count := by
  induction count generalizing width coordinate with
  | zero => exact Nat.le_refl 0
  | succ count ih =>
      by_cases hFirst : coordinate < width
      · simp only [iterations, if_pos hFirst]
        omega
      · have hTail := ih (width + 1) (coordinate - width)
        simp only [iterations, if_neg hFirst]
        omega

private theorem totalWidth_le (count bound : Nat) (widths : Fin count → Nat)
    (hWidths : ∀ position, widths position ≤ bound) :
    DirectSlot.totalWidth count widths ≤ count * bound := by
  induction count with
  | zero => simp only [DirectSlot.totalWidth, Nat.zero_mul]; exact Nat.le_refl 0
  | succ count ih =>
      have hFirst := hWidths ⟨0, Nat.zero_lt_succ count⟩
      have hTail := ih (fun position => widths position.succ) (fun position => hWidths position.succ)
      rw [DirectSlot.totalWidth, Nat.succ_mul]
      omega

theorem rowSpan_le (count width : Nat) : rowSpan count width ≤ count * (width + count) := by
  rw [rowSpan_eq_totalWidth]
  apply totalWidth_le
  intro position
  have h := position.isLt
  omega

/-- Preserve the exact canonical flattened slot order, including zero-width blocks. -/
theorem locate_flatFinite (count width coordinate : Nat) (slots : Fin count → Nat → Option α) :
    DirectSlot.flatFinite count slots (fun position => width + position.val) coordinate =
      (locate count width coordinate).bind (fun found => slots found.1 found.2) := by
  induction count generalizing width coordinate with
  | zero => rfl
  | succ count ih =>
      rw [DirectSlot.flatFinite, locate]
      simp only [Nat.add_zero]
      by_cases hFirst : coordinate < width
      · simp only [if_pos hFirst, Option.bind_some]
      · simp only [if_neg hFirst]
        rw [shifted_widths, ih]
        cases locate count (width + 1) (coordinate - width) with
        | none => rfl
        | some found => cases found; rfl

def selectedLength {language : Language} (problem : VerifierTableauProblem language) (coordinate : Nat) :
    Option (Fin (problem.certificateLimit + 1) × Nat) :=
  locate (problem.certificateLimit + 1) (problem.dimensions.tapeWidth problem.tableauInputMode) coordinate

theorem paired_total_width {language : Language} (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired) :
    problem.pairedCellsWidthDirect =
      rowSpan (problem.certificateLimit + 1) (problem.dimensions.tapeWidth problem.tableauInputMode) := by
  unfold pairedCellsWidthDirect
  have hWidths : problem.pairedCellsForLengthWidthDirect =
      (fun length => problem.dimensions.tapeWidth problem.tableauInputMode + length.val) := by
    funext length
    exact BuilderInitialCellCoordinates.paired_row_width problem hMode length
  rw [hWidths, rowSpan_eq_totalWidth]

theorem selectedLength_canonical {language : Language} (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired) (coordinate : Nat) :
    problem.pairedCellsSlotDirect hMode coordinate =
      (selectedLength problem coordinate).bind
        (fun found => problem.pairedCellsForLengthSlotDirect hMode found.1 found.2) := by
  unfold pairedCellsSlotDirect selectedLength
  have hWidths : problem.pairedCellsForLengthWidthDirect =
      (fun length => problem.dimensions.tapeWidth problem.tableauInputMode + length.val) := by
    funext length
    exact BuilderInitialCellCoordinates.paired_row_width problem hMode length
  rw [hWidths, locate_flatFinite]

theorem selectedLength_none_iff {language : Language} (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired) (coordinate : Nat) :
    selectedLength problem coordinate = none ↔ problem.pairedCellsWidthDirect ≤ coordinate := by
  rw [paired_total_width problem hMode]
  exact locate_none_iff _ _ _

theorem selectedLength_bounds {language : Language} (problem : VerifierTableauProblem language) (coordinate : Nat)
    (length : Fin (problem.certificateLimit + 1)) (offset : Nat)
    (hFound : selectedLength problem coordinate = some (length, offset)) :
    offset < problem.dimensions.tapeWidth problem.tableauInputMode + length.val ∧
      coordinate = rowSpan length.val (problem.dimensions.tapeWidth problem.tableauInputMode) + offset ∧
      coordinate < rowSpan (problem.certificateLimit + 1) (problem.dimensions.tapeWidth problem.tableauInputMode) :=
  locate_some_bounds _ _ _ length offset hFound

theorem selectedLength_iterations_le {language : Language} (problem : VerifierTableauProblem language) (coordinate : Nat) :
    iterations (problem.certificateLimit + 1) (problem.dimensions.tapeWidth problem.tableauInputMode) coordinate ≤
      problem.certificateLimit + 1 :=
  iterations_le _ _ _

theorem paired_total_width_le {language : Language} (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired) :
    problem.pairedCellsWidthDirect ≤ (problem.certificateLimit + 1) *
      (problem.dimensions.tapeWidth problem.tableauInputMode + (problem.certificateLimit + 1)) := by
  rw [paired_total_width problem hMode]
  exact rowSpan_le _ _

end PNP.Concrete.CookLevin.BuilderInitialLengthSelection
