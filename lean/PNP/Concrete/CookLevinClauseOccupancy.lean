/-
Copyright (c) 2026 PNP Labs.

Clause-occupancy projection for the complete canonical Cook-Levin schedule.
The existing exact local clause counts are reused; this selector does not emit
the selected clause or materialize the clause schedule. These are specification
functions for the physical selector, not a raw machine or a runtime theorem.
This component does not earn the complete-builder checkpoint by itself.
-/

import PNP.Concrete.CookLevinFormulaCursor

namespace PNP.Concrete.CookLevin.ClauseOccupancy

/-- Decide local occupancy from the previously proved exact clause count. -/
def localSlot {width : Nat} (constraint : LocalConstraint width)
    (index : Nat) : Bool :=
  decide (index < constraint.clauseCount)

theorem localSlot_eq {width : Nat} (constraint : LocalConstraint width)
    (index : Nat) :
    localSlot constraint index =
      (constraint.clauseSlotDirect index).isSome := by
  unfold localSlot
  rw [LocalConstraint.clauseSlotDirect_eq_emit_getElem?,
    ← LocalConstraint.emit_length]
  by_cases hIndex : index < constraint.emit.length
  · rw [List.getElem?_eq_getElem hIndex]
    simp only [hIndex, decide_true, Option.isSome_some]
  · rw [List.getElem?_eq_none (Nat.le_of_not_gt hIndex)]
    simp only [hIndex, decide_false, Option.isSome_none]

/-- An in-range empty opportunity is `some false`; outside is `none`. -/
def paddedSlot {width : Nat} (bound : Nat)
    (constraint : Option (LocalConstraint width)) (index : Nat) :
    Option Bool :=
  if index < bound then
    some (match constraint with
      | none => false
      | some item => localSlot item index)
  else none

theorem paddedSlot_eq {width : Nat} (bound : Nat)
    (constraint : Option (LocalConstraint width)) (index : Nat) :
    paddedSlot bound constraint index =
      (DirectSlot.pad bound
        (fun next => constraint.bind
          (fun item => item.clauseSlotDirect next)) index).map
            Option.isSome := by
  unfold paddedSlot DirectSlot.pad
  by_cases hIndex : index < bound
  · rw [if_pos hIndex, if_pos hIndex]
    cases constraint with
    | none => rfl
    | some item => exact congrArg some (localSlot_eq item index)
  · rw [if_neg hIndex, if_neg hIndex]
    rfl

private theorem flatFinite_map (f : α → β) (count : Nat)
    (blockSlot : Fin count → Nat → Option α)
    (blockLength : Fin count → Nat) (index : Nat) :
    DirectSlot.flatFinite count
        (fun coordinate next => (blockSlot coordinate next).map f)
        blockLength index =
      (DirectSlot.flatFinite count blockSlot blockLength index).map f := by
  induction count generalizing index with
  | zero => rfl
  | succ count ih =>
      by_cases hIndex : index < blockLength ⟨0, Nat.zero_lt_succ count⟩
      · simp only [DirectSlot.flatFinite, if_pos hIndex]
      · simpa only [DirectSlot.flatFinite, if_neg hIndex] using
          (ih (fun coordinate next => blockSlot coordinate.succ next)
            (fun coordinate => blockLength coordinate.succ)
            (index - blockLength ⟨0, Nat.zero_lt_succ count⟩))

/-- Obtain the constraint from the source-derived decoder before testing its
local clause coordinate. No constraint is supplied to this interface. -/
def blockSlot {language : Language}
    (problem : VerifierTableauProblem language)
    (coordinate : Fin problem.formulaConstraintSlotCount) (index : Nat) :
    Option Bool :=
  match problem.formulaConstraintSlotDirect coordinate.val with
  | none => none
  | some constraint =>
      paddedSlot problem.formulaClauseSlotsPerConstraint constraint index

theorem blockSlot_eq {language : Language}
    (problem : VerifierTableauProblem language)
    (coordinate : Fin problem.formulaConstraintSlotCount) (index : Nat) :
    blockSlot problem coordinate index =
      (problem.constraintClauseBlockSlotDirect coordinate index).map
        Option.isSome := by
  unfold blockSlot VerifierTableauProblem.constraintClauseBlockSlotDirect
  cases problem.formulaConstraintSlotDirect coordinate.val with
  | none => rfl
  | some constraint =>
      cases constraint with
      | none => exact paddedSlot_eq _ none index
      | some item => exact paddedSlot_eq _ (some item) index

/-- Occupancy at any coordinate of the complete clause rectangle. -/
def formulaSlot {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) : Option Bool :=
  DirectSlot.rectangle problem.formulaConstraintSlotCount
    problem.formulaClauseSlotsPerConstraint (blockSlot problem) index

theorem formulaSlot_eq {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    formulaSlot problem index =
      (problem.formulaClauseSlotDirect index).map Option.isSome := by
  unfold formulaSlot VerifierTableauProblem.formulaClauseSlotDirect
  have hBlocks : blockSlot problem =
      (fun coordinate next =>
        (problem.constraintClauseBlockSlotDirect coordinate next).map
          Option.isSome) := by
    funext coordinate next
    exact blockSlot_eq problem coordinate next
  rw [hBlocks]
  exact flatFinite_map Option.isSome problem.formulaConstraintSlotCount
    problem.constraintClauseBlockSlotDirect
    (fun _ => problem.formulaClauseSlotsPerConstraint) index

theorem formulaSlot_eq_schedule {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    formulaSlot problem index =
      (problem.formulaClauseSchedule[index]?).map Option.isSome := by
  rw [formulaSlot_eq, problem.formulaClauseSlotDirect_eq]

theorem formulaSlot_outOfRange {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat)
    (hIndex : problem.formulaClauseSlotCount ≤ index) :
    formulaSlot problem index = none := by
  have hLength : problem.formulaClauseSchedule.length ≤ index := by
    rw [problem.formulaClauseSchedule_length]
    exact hIndex
  rw [formulaSlot_eq_schedule, List.getElem?_eq_none hLength]
  rfl

end PNP.Concrete.CookLevin.ClauseOccupancy
