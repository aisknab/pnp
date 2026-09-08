/-
Copyright (c) 2026 PNP Labs.

Decode the compressed one- and two-slot initial-cell order, then compose with
the source-specialized certificate-length cursor. The arithmetic formulas
do not materialize the cell family or accept a selection certificate.
This is a specification interface, not a physical machine or runtime claim.
-/

import PNP.Concrete.CookLevinBuilderInitialLengthSelection

namespace PNP.Concrete.CookLevin.BuilderInitialCellSelection

open VerifierTableauProblem
open BuilderInitialCellCoordinates

/-- Invert the prefix widths of one contiguous interval of two-slot cells. -/
def cellCoordinate (start length coordinate : Nat) : Nat × Nat :=
  if coordinate < start then (coordinate, 0)
  else if coordinate < start + 2 * length then
    (start + (coordinate - start) / 2, (coordinate - start) % 2)
  else (coordinate - length, 0)

/-- The exact original coordinate and both bounds, not merely membership. -/
theorem cellCoordinate_spec (width start length coordinate : Nat)
    (hInterval : start + length ≤ width) (hInside : coordinate < width + length) :
    (cellCoordinate start length coordinate).1 < width ∧
      (cellCoordinate start length coordinate).2 <
        intervalWidth start length (cellCoordinate start length coordinate).1 ∧
      coordinate = (cellCoordinate start length coordinate).1 +
        min length ((cellCoordinate start length coordinate).1 - start) +
        (cellCoordinate start length coordinate).2 := by
  by_cases hBefore : coordinate < start
  · have hOutside : ¬ (start ≤ coordinate ∧ coordinate < start + length) := by
      intro h
      omega
    have hPrefix : min length (coordinate - start) = 0 := by omega
    simp only [cellCoordinate, if_pos hBefore, intervalWidth, if_neg hOutside, hPrefix]
    refine ⟨?_, ?_, ?_⟩ <;> omega
  · by_cases hDouble : coordinate < start + 2 * length
    · have hCell : start ≤ start + (coordinate - start) / 2 ∧
          start + (coordinate - start) / 2 < start + length := by
        constructor <;> omega
      have hPrefix : min length (start + (coordinate - start) / 2 - start) =
          (coordinate - start) / 2 := by omega
      simp only [cellCoordinate, if_neg hBefore, if_pos hDouble,
        intervalWidth, if_pos hCell, hPrefix]
      refine ⟨?_, ?_, ?_⟩ <;> omega
    · have hOutside : ¬ (start ≤ coordinate - length ∧
          coordinate - length < start + length) := by
        intro h
        omega
      have hPrefix : min length (coordinate - length - start) = length := by omega
      simp only [cellCoordinate, if_neg hBefore, if_neg hDouble,
        intervalWidth, if_neg hOutside, hPrefix]
      refine ⟨?_, ?_, ?_⟩ <;> omega

/-- A generic prefix coordinate selects the corresponding variable-width block. -/
theorem flatFinite_at_prefix (count : Nat) (widths : Nat → Nat)
    (slots : Fin count → Nat → Option α) (position : Fin count) (offset : Nat)
    (hOffset : offset < widths position.val) :
    DirectSlot.flatFinite count slots (fun cell => widths cell.val)
      (DirectSlot.totalWidth position.val (fun cell => widths cell.val) + offset) =
      slots position offset := by
  induction count generalizing widths with
  | zero => exact Fin.elim0 position
  | succ count ih =>
      cases position using Fin.cases with
      | zero =>
          change offset < widths 0 at hOffset
          simp only [Fin.val_zero, DirectSlot.totalWidth, Nat.zero_add, DirectSlot.flatFinite]
          exact if_pos hOffset
      | succ position =>
          have hPrefix :
              DirectSlot.totalWidth position.succ.val (fun cell => widths cell.val) =
                widths 0 + DirectSlot.totalWidth position.val (fun cell => widths (cell.val + 1)) := rfl
          rw [DirectSlot.flatFinite, hPrefix]
          have hAfter : ¬ (widths 0 +
              DirectSlot.totalWidth position.val (fun cell => widths (cell.val + 1)) + offset <
              widths 0) := by omega
          rw [if_neg hAfter]
          have hSubtract : widths 0 +
              DirectSlot.totalWidth position.val (fun cell => widths (cell.val + 1)) + offset -
              widths 0 =
              DirectSlot.totalWidth position.val (fun cell => widths (cell.val + 1)) + offset := by omega
          rw [hSubtract]
          exact ih (fun cell => widths (cell + 1)) (fun cell => slots cell.succ)
            position hOffset

/-- Exhausting a variable-width family returns none, even with empty blocks. -/
theorem flatFinite_none_of_le (count : Nat) (widths : Nat → Nat)
    (slots : Fin count → Nat → Option α) (coordinate : Nat)
    (hOutside : DirectSlot.totalWidth count (fun cell => widths cell.val) ≤ coordinate) :
    DirectSlot.flatFinite count slots (fun cell => widths cell.val) coordinate = none := by
  induction count generalizing widths coordinate with
  | zero => rfl
  | succ count ih =>
      have hSpan : widths 0 +
          DirectSlot.totalWidth count (fun cell => widths (cell.val + 1)) ≤ coordinate := hOutside
      have hFirst : ¬ coordinate < widths 0 := by omega
      rw [DirectSlot.flatFinite, if_neg hFirst]
      apply ih (fun cell => widths (cell + 1)) (fun cell => slots cell.succ)
      change DirectSlot.totalWidth count (fun cell => widths (cell.val + 1)) ≤ coordinate - widths 0
      omega

/-- Derive a bounded cell and offset; the structural premise is erased. -/
def locate (width start length : Nat) (hInterval : start + length ≤ width)
    (coordinate : Nat) : Option (Fin width × Nat) :=
  if hInside : coordinate < width + length then
    some (⟨(cellCoordinate start length coordinate).1,
      (cellCoordinate_spec width start length coordinate hInterval hInside).1⟩,
      (cellCoordinate start length coordinate).2)
  else none

theorem locate_none_iff (width start length : Nat) (hInterval : start + length ≤ width)
    (coordinate : Nat) :
    locate width start length hInterval coordinate = none ↔ width + length ≤ coordinate := by
  by_cases hInside : coordinate < width + length
  · simp only [locate, dif_pos hInside]
    constructor
    · intro h
      cases h
    · intro h
      omega
  · simp only [locate, dif_neg hInside]
    constructor
    · intro _
      omega
    · intro _
      exact True.intro

theorem locate_some_bounds (width start length : Nat) (hInterval : start + length ≤ width)
    (coordinate : Nat) (position : Fin width) (offset : Nat)
    (hFound : locate width start length hInterval coordinate = some (position, offset)) :
    offset < intervalWidth start length position.val ∧
      coordinate = position.val + min length (position.val - start) + offset ∧
      coordinate < width + length := by
  by_cases hInside : coordinate < width + length
  · simp only [locate, dif_pos hInside, Option.some.injEq, Prod.mk.injEq] at hFound
    rcases hFound with ⟨hPosition, hOffset⟩
    cases hPosition
    cases hOffset
    have h := cellCoordinate_spec width start length coordinate hInterval hInside
    exact ⟨h.2.1, h.2.2, hInside⟩
  · simp only [locate, dif_neg hInside] at hFound
    cases hFound

/-- Preserve the existing compressed flattening, including the exhausted tail. -/
theorem locate_flatFinite (width start length : Nat) (hInterval : start + length ≤ width)
    (coordinate : Nat) (slots : Fin width → Nat → Option α) :
    DirectSlot.flatFinite width slots (fun cell => intervalWidth start length cell.val) coordinate =
      (locate width start length hInterval coordinate).bind (fun found => slots found.1 found.2) := by
  by_cases hInside : coordinate < width + length
  · simp only [locate, dif_pos hInside, Option.bind_some]
    have h := cellCoordinate_spec width start length coordinate hInterval hInside
    have hPrefix :
        DirectSlot.totalWidth (cellCoordinate start length coordinate).1
          (fun cell => intervalWidth start length cell.val) +
          (cellCoordinate start length coordinate).2 = coordinate := by
      rw [interval_totalWidth]
      exact h.2.2.symm
    calc
      DirectSlot.flatFinite width slots (fun cell => intervalWidth start length cell.val) coordinate =
          DirectSlot.flatFinite width slots (fun cell => intervalWidth start length cell.val)
            (DirectSlot.totalWidth (cellCoordinate start length coordinate).1
              (fun cell => intervalWidth start length cell.val) +
              (cellCoordinate start length coordinate).2) := congrArg
                (DirectSlot.flatFinite width slots (fun cell => intervalWidth start length cell.val))
                hPrefix.symm
      _ = _ := flatFinite_at_prefix width (intervalWidth start length) slots
        ⟨(cellCoordinate start length coordinate).1, h.1⟩
        (cellCoordinate start length coordinate).2 h.2.1
  · simp only [locate, dif_neg hInside, Option.bind_none]
    apply flatFinite_none_of_le
    rw [interval_totalWidth]
    omega

/-- Source-facing selection derives containment from the actual paired model. -/
def selectedCell {language : Language} (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (length : Fin (problem.certificateLimit + 1)) (coordinate : Nat) :
    Option (Fin (problem.dimensions.tapeWidth problem.tableauInputMode) × Nat) :=
  locate (problem.dimensions.tapeWidth problem.tableauInputMode)
    (certificateStart problem.input.length length.val problem.uniformFuel) length.val
    (certificate_interval_within_tape problem hMode length) coordinate

theorem selectedCell_canonical {language : Language} (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (length : Fin (problem.certificateLimit + 1)) (coordinate : Nat) :
    problem.pairedCellsForLengthSlotDirect hMode length coordinate =
      (selectedCell problem hMode length coordinate).bind
        (fun found => problem.pairedCellConstraintSlotDirect hMode length found.1 found.2) := by
  unfold pairedCellsForLengthSlotDirect selectedCell
  have hWidths :
      (fun position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode) =>
        problem.pairedCellConstraintWidthDirect length position) =
      (fun position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode) =>
        intervalWidth (certificateStart problem.input.length length.val problem.uniformFuel)
          length.val position.val) := by
    funext position
    exact pairedCellConstraintWidthDirect_eq_interval problem length position
  rw [hWidths, locate_flatFinite]

theorem selectedCell_none_iff {language : Language} (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (length : Fin (problem.certificateLimit + 1)) (coordinate : Nat) :
    selectedCell problem hMode length coordinate = none ↔
      problem.pairedCellsForLengthWidthDirect length ≤ coordinate := by
  rw [paired_row_width problem hMode length]
  exact locate_none_iff _ _ _ _ coordinate

theorem selectedCell_bounds {language : Language} (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (length : Fin (problem.certificateLimit + 1)) (coordinate : Nat)
    (position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) (offset : Nat)
    (hFound : selectedCell problem hMode length coordinate = some (position, offset)) :
    offset < problem.pairedCellConstraintWidthDirect length position ∧
      coordinate = position.val +
        min length.val (position.val - certificateStart problem.input.length length.val problem.uniformFuel) +
        offset ∧ coordinate < problem.pairedCellsForLengthWidthDirect length := by
  rw [pairedCellConstraintWidthDirect_eq_interval, paired_row_width problem hMode length]
  exact locate_some_bounds _ _ _ _ coordinate position offset hFound

/-- Derive length, cell and within-cell offset from one complete paired-cell coordinate. -/
def selectedInitialCell {language : Language} (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired) (coordinate : Nat) :
    Option (Fin (problem.certificateLimit + 1) ×
      Fin (problem.dimensions.tapeWidth problem.tableauInputMode) × Nat) :=
  (BuilderInitialLengthSelection.selectedLength problem coordinate).bind (fun row =>
    (selectedCell problem hMode row.1 row.2).map (fun cell => (row.1, cell.1, cell.2)))

theorem selectedInitialCell_canonical {language : Language} (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired) (coordinate : Nat) :
    problem.pairedCellsSlotDirect hMode coordinate =
      (selectedInitialCell problem hMode coordinate).bind
        (fun found => problem.pairedCellConstraintSlotDirect hMode found.1 found.2.1 found.2.2) := by
  rw [BuilderInitialLengthSelection.selectedLength_canonical]
  unfold selectedInitialCell
  cases hRow : BuilderInitialLengthSelection.selectedLength problem coordinate with
  | none => rfl
  | some row =>
      rcases row with ⟨length, offset⟩
      simp only [Option.bind_some]
      rw [selectedCell_canonical]
      cases selectedCell problem hMode length offset with
      | none => rfl
      | some cell => cases cell; rfl

theorem selectedInitialCell_none_iff {language : Language} (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired) (coordinate : Nat) :
    selectedInitialCell problem hMode coordinate = none ↔ problem.pairedCellsWidthDirect ≤ coordinate := by
  rw [← BuilderInitialLengthSelection.selectedLength_none_iff problem hMode coordinate]
  unfold selectedInitialCell
  cases hRow : BuilderInitialLengthSelection.selectedLength problem coordinate with
  | none =>
      simp only [Option.bind_none]
  | some row =>
      rcases row with ⟨length, offset⟩
      have hBounds := BuilderInitialLengthSelection.selectedLength_bounds problem coordinate length offset hRow
      have hCellInside : offset < problem.pairedCellsForLengthWidthDirect length := by
        rw [paired_row_width problem hMode length]
        exact hBounds.1
      cases hCell : selectedCell problem hMode length offset with
      | none =>
          have hOutside := (selectedCell_none_iff problem hMode length offset).mp hCell
          omega
      | some cell =>
          simp only [Option.bind_some, hCell, Option.map_some]
          constructor <;> intro impossible <;> cases impossible

end PNP.Concrete.CookLevin.BuilderInitialCellSelection
