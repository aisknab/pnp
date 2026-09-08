import PNP.Concrete.CookLevinBuilderInitialCellSelection

namespace PNP.Concrete.CookLevin.BuilderInitialCellSelectionRegression

open VerifierTableauProblem BuilderInitialCellCoordinates BuilderInitialCellSelection

example : cellCoordinate 3 2 0 = (0, 0) := by decide
example : cellCoordinate 3 2 2 = (2, 0) := by decide
example : cellCoordinate 3 2 3 = (3, 0) := by decide
example : cellCoordinate 3 2 4 = (3, 1) := by decide
example : cellCoordinate 3 2 5 = (4, 0) := by decide
example : cellCoordinate 3 2 6 = (4, 1) := by decide
example : cellCoordinate 3 2 7 = (5, 0) := by decide
example : cellCoordinate 3 2 9 = (7, 0) := by decide
example : cellCoordinate 0 3 0 = (0, 0) := by decide
example : cellCoordinate 0 3 5 = (2, 1) := by decide
example : cellCoordinate 0 3 6 = (3, 0) := by decide
example : cellCoordinate 3 0 3 = (3, 0) := by decide
example : cellCoordinate 0 0 19 = (19, 0) := by decide

example : locate 8 3 2 (by decide) 0 = some (⟨0, by decide⟩, 0) := by decide
example : locate 8 3 2 (by decide) 2 = some (⟨2, by decide⟩, 0) := by decide
example : locate 8 3 2 (by decide) 3 = some (⟨3, by decide⟩, 0) := by decide
example : locate 8 3 2 (by decide) 4 = some (⟨3, by decide⟩, 1) := by decide
example : locate 8 3 2 (by decide) 6 = some (⟨4, by decide⟩, 1) := by decide
example : locate 8 3 2 (by decide) 7 = some (⟨5, by decide⟩, 0) := by decide
example : locate 8 3 2 (by decide) 9 = some (⟨7, by decide⟩, 0) := by decide
example : locate 8 3 2 (by decide) 10 = none := by decide
example : locate 8 3 2 (by decide) 11 = none := by decide
example : locate 0 0 0 (by decide) 0 = none := by decide
example : locate 5 5 0 (by decide) 4 = some (⟨4, by decide⟩, 0) := by decide
example : locate 5 5 0 (by decide) 5 = none := by decide
example : locate 5 3 0 (by decide) 3 = some (⟨3, by decide⟩, 0) := by decide
example : locate 3 0 3 (by decide) 5 = some (⟨2, by decide⟩, 1) := by decide
example : locate 3 0 3 (by decide) 6 = none := by decide
example : locate 5 3 2 (by decide) 6 = some (⟨4, by decide⟩, 1) := by decide
example : locate 5 3 2 (by decide) 7 = none := by decide
example : locate 8 3 2 (by decide) 4 ≠ some (⟨4, by decide⟩, 0) := by decide
example : locate 8 3 2 (by decide) 7 ≠ some (⟨4, by decide⟩, 1) := by decide

example : DirectSlot.flatFinite 8 (fun cell offset => some (cell.val, offset))
    (fun cell => intervalWidth 3 2 cell.val) 6 = some (4, 1) := by decide
example : DirectSlot.flatFinite 8 (fun cell offset => some (cell.val, offset))
    (fun cell => intervalWidth 3 2 cell.val) 7 = some (5, 0) := by decide
example : DirectSlot.flatFinite 8 (fun cell offset => some (cell.val, offset))
    (fun cell => intervalWidth 3 2 cell.val) 10 = none := by decide

example (width start length coordinate : Nat) (hInterval : start + length ≤ width)
    (hInside : coordinate < width + length) :
    (cellCoordinate start length coordinate).1 < width ∧
      (cellCoordinate start length coordinate).2 <
        intervalWidth start length (cellCoordinate start length coordinate).1 ∧
      coordinate = (cellCoordinate start length coordinate).1 +
        min length ((cellCoordinate start length coordinate).1 - start) +
        (cellCoordinate start length coordinate).2 :=
  cellCoordinate_spec width start length coordinate hInterval hInside

example (width start length coordinate : Nat) (hInterval : start + length ≤ width)
    (slots : Fin width → Nat → Option α) :
    DirectSlot.flatFinite width slots (fun cell => intervalWidth start length cell.val) coordinate =
      (locate width start length hInterval coordinate).bind (fun found => slots found.1 found.2) :=
  locate_flatFinite width start length hInterval coordinate slots

example (count : Nat) (widths : Nat → Nat) (slots : Fin count → Nat → Option α)
    (position : Fin count) (offset : Nat) (hOffset : offset < widths position.val) :
    DirectSlot.flatFinite count slots (fun cell => widths cell.val)
      (DirectSlot.totalWidth position.val (fun cell => widths cell.val) + offset) = slots position offset :=
  flatFinite_at_prefix count widths slots position offset hOffset

example (count : Nat) (widths : Nat → Nat) (slots : Fin count → Nat → Option α) (coordinate : Nat)
    (hOutside : DirectSlot.totalWidth count (fun cell => widths cell.val) ≤ coordinate) :
    DirectSlot.flatFinite count slots (fun cell => widths cell.val) coordinate = none :=
  flatFinite_none_of_le count widths slots coordinate hOutside

variable {language : Language} (problem : VerifierTableauProblem language)
  (hMode : problem.tableauInputMode = .paired)

example (length : Fin (problem.certificateLimit + 1)) (coordinate : Nat) :
    problem.pairedCellsForLengthSlotDirect hMode length coordinate =
      (selectedCell problem hMode length coordinate).bind
        (fun found => problem.pairedCellConstraintSlotDirect hMode length found.1 found.2) :=
  selectedCell_canonical problem hMode length coordinate

example (length : Fin (problem.certificateLimit + 1)) (coordinate : Nat) :
    selectedCell problem hMode length coordinate = none ↔
      problem.pairedCellsForLengthWidthDirect length ≤ coordinate :=
  selectedCell_none_iff problem hMode length coordinate

example (length : Fin (problem.certificateLimit + 1)) (coordinate : Nat)
    (position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) (offset : Nat)
    (hFound : selectedCell problem hMode length coordinate = some (position, offset)) :
    offset < problem.pairedCellConstraintWidthDirect length position ∧
      coordinate = position.val +
        min length.val (position.val - certificateStart problem.input.length length.val problem.uniformFuel) +
        offset ∧ coordinate < problem.pairedCellsForLengthWidthDirect length :=
  selectedCell_bounds problem hMode length coordinate position offset hFound

example (coordinate : Nat) :
    problem.pairedCellsSlotDirect hMode coordinate =
      (selectedInitialCell problem hMode coordinate).bind
        (fun found => problem.pairedCellConstraintSlotDirect hMode found.1 found.2.1 found.2.2) :=
  selectedInitialCell_canonical problem hMode coordinate

example (coordinate : Nat) :
    selectedInitialCell problem hMode coordinate = none ↔ problem.pairedCellsWidthDirect ≤ coordinate :=
  selectedInitialCell_none_iff problem hMode coordinate

end PNP.Concrete.CookLevin.BuilderInitialCellSelectionRegression
