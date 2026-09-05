import PNP.Concrete.CookLevinClauseOccupancyDivision

namespace PNP.Concrete.CookLevinClauseOccupancyDivisionRegression

open CookLevin CookLevin.ClauseOccupancy

example : rectanglePair? 0 7 0 = none := rfl
example : rectanglePair? 4 0 0 = none := rfl
example : rectanglePair? 0 0 3 = none := rfl
example : rectanglePair? 3 4 0 = some (0, 0) := rfl
example : rectanglePair? 3 4 3 = some (0, 3) := rfl
example : rectanglePair? 3 4 4 = some (1, 0) := rfl
example : rectanglePair? 3 4 11 = some (2, 3) := rfl
example : rectanglePair? 3 4 12 = none := rfl
example : rectanglePair? 3 4 13 = none := rfl
example : rectanglePair? 5 1 4 = some (4, 0) := rfl
example : rectanglePair? 5 1 5 = none := rfl

-- The finite fixtures exercise one definition whose theorem covers every size.
example (count width index : Nat) :
    rectanglePair? count width index =
      (BuilderArbitrarySlotPostHeaderDecoder.rectangleCoordinate?
        count width index).map (fun pair => (pair.1.val, pair.2.val)) :=
  rectanglePair?_eq count width index

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) :
    dividedSlot problem index =
      (problem.formulaClauseSchedule[index]?).map Option.isSome :=
  dividedSlot_eq_schedule problem index

example {language : Language} (problem : VerifierTableauProblem language) :
    dividedSlot problem problem.formulaClauseSlotCount = none := by
  rw [dividedSlot_eq]
  exact formulaSlot_outOfRange problem _ (Nat.le_refl _)

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin problem.formulaClauseSlotCount) :
    constraintSlot problem
        (index.val / problem.formulaClauseSlotsPerConstraint)
        (index.val % problem.formulaClauseSlotsPerConstraint) =
      formulaSlot problem index.val :=
  constraintSlot_div_mod problem index

-- An exterior containing divider symbols must not contaminate decoded values.
open BuilderPostHeaderRawTapeBridge

example : BuilderPostHeaderRawDivider.terminalQuotientRemainder
    (shieldedDividerFinalConfiguration 0 1
      [BuilderPostHeaderRawDivider.unitSymbol]) = (0, 1) := rfl

example : shieldedTerminalQuotientRemainder
    (shieldedDividerFinalConfiguration 0 1
      [BuilderPostHeaderRawDivider.unitSymbol])
    [BuilderPostHeaderRawDivider.unitSymbol] = (0, 0) := rfl

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin problem.formulaClauseSlotCount) :
    6 * BuilderPostHeaderRawDivider.workSteps index.val
        problem.formulaClauseSlotsPerConstraint ≤
      (dividerRawTimeBound problem.verifier).eval problem.input.length :=
  dividerCompiledSteps_le problem index

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Fin problem.formulaClauseSlotCount) (exterior : List WorkSymbol) :
    let width := problem.formulaClauseSlotsPerConstraint
    let steps := BuilderPostHeaderRawDivider.workSteps index.val width
    let initial := shieldedDividerStartConfiguration index.val width exterior
    let final := shieldedDividerFinalConfiguration index.val width exterior
    workRunExact? dividerMachine steps initial = some final ∧
    run (compileWorkMachine dividerMachine) (6 * steps)
        (encodeWorkConfiguration initial) = encodeWorkConfiguration final := by
  exact ⟨(shielded_divider_execution problem index exterior).1,
    (shielded_divider_execution problem index exterior).2.1⟩

end PNP.Concrete.CookLevinClauseOccupancyDivisionRegression
