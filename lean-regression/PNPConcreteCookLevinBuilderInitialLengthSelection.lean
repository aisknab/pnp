import PNP.Concrete.CookLevinBuilderInitialLengthSelection

open PNP.Concrete PNP.Concrete.CookLevin
open BuilderInitialLengthSelection

example : rowSpan 3 2 = 9 := rfl
example : locate 0 7 0 = none := rfl
example : locate 3 2 0 = some (⟨0, by decide⟩, 0) := rfl
example : locate 3 2 1 = some (⟨0, by decide⟩, 1) := rfl
example : locate 3 2 2 = some (⟨1, by decide⟩, 0) := rfl
example : locate 3 2 4 = some (⟨1, by decide⟩, 2) := rfl
example : locate 3 2 5 = some (⟨2, by decide⟩, 0) := rfl
example : locate 3 2 8 = some (⟨2, by decide⟩, 3) := rfl
example : locate 3 2 9 = none := rfl
example : locate 4 0 0 = some (⟨1, by decide⟩, 0) := rfl
example : locate 4 0 1 = some (⟨2, by decide⟩, 0) := rfl
example : locate 4 0 5 = some (⟨3, by decide⟩, 2) := rfl
example : locate 4 0 6 = none := rfl
example : iterations 3 2 0 = 1 := rfl
example : iterations 3 2 2 = 2 := rfl
example : iterations 3 2 8 = 3 := rfl
example : iterations 3 2 99 = 3 := rfl
example : iterations 0 2 99 = 0 := rfl

section Universal
variable (count width coordinate : Nat)

example : rowSpan count width = DirectSlot.totalWidth count (fun position => width + position.val) :=
  rowSpan_eq_totalWidth count width
example : (match locate count width coordinate with
    | none => rowSpan count width ≤ coordinate
    | some (position, offset) =>
        offset < width + position.val ∧ coordinate = rowSpan position.val width + offset ∧
          coordinate < rowSpan count width) :=
  locate_spec count width coordinate
example : locate count width coordinate = none ↔ rowSpan count width ≤ coordinate :=
  locate_none_iff count width coordinate
example (position : Fin count) (offset : Nat)
    (hFound : locate count width coordinate = some (position, offset)) :
    offset < width + position.val ∧ coordinate = rowSpan position.val width + offset ∧
      coordinate < rowSpan count width :=
  locate_some_bounds count width coordinate position offset hFound
example : iterations count width coordinate ≤ count := iterations_le count width coordinate
example : rowSpan count width ≤ count * (width + count) := rowSpan_le count width
example (slots : Fin count → Nat → Option α) :
    DirectSlot.flatFinite count slots (fun position => width + position.val) coordinate =
      (locate count width coordinate).bind (fun found => slots found.1 found.2) :=
  locate_flatFinite count width coordinate slots
end Universal

section Source
variable {language : Language} (problem : VerifierTableauProblem language)
variable (hMode : problem.tableauInputMode = .paired) (coordinate : Nat)

example : problem.pairedCellsWidthDirect =
    rowSpan (problem.certificateLimit + 1) (problem.dimensions.tapeWidth problem.tableauInputMode) :=
  paired_total_width problem hMode
example : problem.pairedCellsSlotDirect hMode coordinate =
    (selectedLength problem coordinate).bind
      (fun found => problem.pairedCellsForLengthSlotDirect hMode found.1 found.2) :=
  selectedLength_canonical problem hMode coordinate
example : selectedLength problem coordinate = none ↔ problem.pairedCellsWidthDirect ≤ coordinate :=
  selectedLength_none_iff problem hMode coordinate
example (length : Fin (problem.certificateLimit + 1)) (offset : Nat)
    (hFound : selectedLength problem coordinate = some (length, offset)) :
    offset < problem.dimensions.tapeWidth problem.tableauInputMode + length.val ∧
      coordinate = rowSpan length.val (problem.dimensions.tapeWidth problem.tableauInputMode) + offset ∧
      coordinate < rowSpan (problem.certificateLimit + 1) (problem.dimensions.tapeWidth problem.tableauInputMode) :=
  selectedLength_bounds problem coordinate length offset hFound
example : iterations (problem.certificateLimit + 1) (problem.dimensions.tapeWidth problem.tableauInputMode) coordinate ≤
    problem.certificateLimit + 1 :=
  selectedLength_iterations_le problem coordinate
example : problem.pairedCellsWidthDirect ≤ (problem.certificateLimit + 1) *
    (problem.dimensions.tapeWidth problem.tableauInputMode + (problem.certificateLimit + 1)) :=
  paired_total_width_le problem hMode
end Source
