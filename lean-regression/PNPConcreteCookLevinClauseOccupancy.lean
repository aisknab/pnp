import PNP.Concrete.CookLevinClauseOccupancy

namespace PNP.Concrete.CookLevinClauseOccupancyRegression

open CookLevin CookLevin.ClauseOccupancy

private def positive : BoundedLiteral 3 := ⟨true, ⟨0, by decide⟩⟩
private def negative : BoundedLiteral 3 := ⟨false, ⟨1, by decide⟩⟩
private def variables : List (Fin 3) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩]

-- An empty clause is still a populated clause slot.
example : localSlot (.exactlyOne ([] : List (Fin 0))) 0 = true := rfl
example : localSlot (.exactlyOne ([] : List (Fin 0))) 1 = false := rfl

example : localSlot (.require positive) 0 = true := rfl
example : localSlot (.require positive) 1 = false := rfl
example : localSlot (.implication [negative, positive] positive) 0 = true := rfl
example : localSlot (.implication [negative, positive] positive) 1 = false := rfl
example : localSlot (.exactlyOne variables) 3 = true := rfl
example : localSlot (.exactlyOne variables) 4 = false := rfl

-- No distinctness premise is silently imposed on a local variable list.
example : localSlot
    (.exactlyOne ([⟨0, by decide⟩, ⟨0, by decide⟩] : List (Fin 1))) 1 = true := rfl

example : paddedSlot (width := 0) 2 none 0 = some false := rfl
example : paddedSlot (width := 0) 2 none 1 = some false := rfl
example : paddedSlot (width := 0) 2 none 2 = none := rfl
example : paddedSlot (width := 0) 0 (some (.exactlyOne [])) 0 = none := rfl
example : paddedSlot (width := 0) 3 (some (.exactlyOne [])) 0 = some true := rfl
example : paddedSlot (width := 0) 3 (some (.exactlyOne [])) 1 = some false := rfl
example : paddedSlot (width := 0) 3 (some (.exactlyOne [])) 3 = none := rfl

example {width : Nat} (constraint : LocalConstraint width) (index : Nat) :
    localSlot constraint index = (constraint.clauseSlotDirect index).isSome :=
  localSlot_eq constraint index

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) :
    formulaSlot problem index =
      (problem.formulaClauseSchedule[index]?).map Option.isSome :=
  formulaSlot_eq_schedule problem index

example {language : Language} (problem : VerifierTableauProblem language) :
    formulaSlot problem problem.formulaClauseSlotCount = none :=
  formulaSlot_outOfRange problem _ (Nat.le_refl _)

end PNP.Concrete.CookLevinClauseOccupancyRegression
