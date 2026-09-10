/-
Copyright (c) 2026 PNP Labs.

Quotient/remainder interface for complete-schedule clause occupancy. Reuse the
existing rectangle decoder and fixed raw divider rather than materializing a
clause schedule. The physical divider starts from its specified unary input
tape; constructing that tape from the preceding builder endpoint and executing
the remaining occupancy test are still separate obligations.
-/

import PNP.Concrete.CookLevinClauseOccupancy
import PNP.Concrete.CookLevinBuilderPostHeaderRawLaunch
import PNP.Concrete.CookLevinBuilderPostHeaderRawTapeBridge

namespace PNP.Concrete.CookLevin.ClauseOccupancy

open BuilderArbitrarySlotPostHeaderDecoder

/-- Natural quotient and remainder, guarded by the complete rectangle bound. -/
def rectanglePair? (count width index : Nat) : Option (Nat × Nat) :=
  if index < count * width then some (index / width, index % width) else none

theorem rectanglePair?_eq (count width index : Nat) :
    rectanglePair? count width index =
      (rectangleCoordinate? count width index).map
        (fun coordinate => (coordinate.1.val, coordinate.2.val)) := by
  cases hCoordinate : rectangleCoordinate? count width index with
  | none =>
      have hOutside := (rectangleCoordinate?_eq_none_iff count width index).1
        hCoordinate
      simp only [rectanglePair?, Nat.not_lt_of_ge hOutside, if_false,
        Option.map_none]
  | some coordinate =>
      have hInside : index < count * width := by
        apply Nat.lt_of_not_ge
        intro hOutside
        have hNone := (rectangleCoordinate?_eq_none_iff count width index).2
          hOutside
        rw [hCoordinate] at hNone
        contradiction
      have hReconstruct := rectangleCoordinate?_reconstruct hCoordinate
      have hLower : coordinate.1.val * width ≤ index := by omega
      have hUpper : index < (coordinate.1.val + 1) * width := by
        rw [Nat.succ_mul]
        have hRemainder := coordinate.2.isLt
        omega
      have hQuotient : index / width = coordinate.1.val :=
        Nat.div_eq_of_lt_le hLower hUpper
      have hNatural := BuilderPostHeaderRawDivider.quotient_remainder_reconstruct
        index width
      have hRemainder : index % width = coordinate.2.val := by
        rw [hQuotient] at hNatural
        omega
      simp only [rectanglePair?, hInside, if_true, hQuotient, hRemainder,
        Option.map_some]

/-- Decode only the selected source-derived constraint and its local occupancy. -/
def constraintSlot {language : Language}
    (problem : VerifierTableauProblem language)
    (constraintIndex clauseIndex : Nat) : Option Bool :=
  match problem.formulaConstraintSlotDirect constraintIndex with
  | none => none
  | some constraint =>
      paddedSlot problem.formulaClauseSlotsPerConstraint constraint clauseIndex

/-- Complete occupancy selection using quotient and remainder coordinates. -/
def dividedSlot {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) : Option Bool :=
  (rectanglePair? problem.formulaConstraintSlotCount
    problem.formulaClauseSlotsPerConstraint index).bind
      (fun coordinate => constraintSlot problem coordinate.1 coordinate.2)

theorem dividedSlot_eq {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    dividedSlot problem index = formulaSlot problem index := by
  unfold dividedSlot formulaSlot
  rw [rectanglePair?_eq, rectangle_eq_coordinate?]
  cases hCoordinate : rectangleCoordinate? problem.formulaConstraintSlotCount
      problem.formulaClauseSlotsPerConstraint index with
  | none => rfl
  | some coordinate => rfl

theorem dividedSlot_eq_schedule {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    dividedSlot problem index =
      (problem.formulaClauseSchedule[index]?).map Option.isSome := by
  rw [dividedSlot_eq, formulaSlot_eq_schedule]

theorem constraintSlot_div_mod {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin problem.formulaClauseSlotCount) :
    constraintSlot problem
        (index.val / problem.formulaClauseSlotsPerConstraint)
        (index.val % problem.formulaClauseSlotsPerConstraint) =
      formulaSlot problem index.val := by
  have hInside : index.val < problem.formulaConstraintSlotCount *
      problem.formulaClauseSlotsPerConstraint := index.isLt
  have hSelected := dividedSlot_eq problem index.val
  simpa only [dividedSlot, rectanglePair?, hInside, if_true,
    Option.bind_some] using hSelected

theorem clauseWidth_pos {language : Language}
    (problem : VerifierTableauProblem language) :
    0 < problem.formulaClauseSlotsPerConstraint := by
  change 0 < 1 + problem.formulaVariableSlotBound * problem.formulaVariableSlotBound
  omega

/-- The actual fixed divider execution supplies the exact occupancy coordinates.
This does not assert that the remaining constraint decoder is a raw machine. -/
theorem divider_run_occupancy {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin problem.formulaClauseSlotCount) :
    let width := problem.formulaClauseSlotsPerConstraint
    let final := workRun BuilderPostHeaderRawDivider.machine
      (BuilderPostHeaderRawDivider.workSteps index.val width)
      (workStartConfiguration BuilderPostHeaderRawDivider.machine
        (BuilderPostHeaderRawDivider.inputTape index.val width))
    let coordinate := BuilderPostHeaderRawDivider.terminalQuotientRemainder final
    constraintSlot problem coordinate.1 coordinate.2 =
      (problem.formulaClauseSchedule[index.val]?).map Option.isSome := by
  dsimp only
  rw [workRun_eq_of_workRunExact _ _ _ _
    (BuilderPostHeaderRawDivider.workRunExact index.val
      problem.formulaClauseSlotsPerConstraint (clauseWidth_pos problem))]
  rw [BuilderPostHeaderRawDivider.final_quotient_remainder]
  exact (constraintSlot_div_mod problem index).trans
    (formulaSlot_eq_schedule problem index.val)

/-! ## Preserved exterior and source-size bounds for the physical division -/

open BuilderPostHeaderRawTapeBridge

/-- Uniform unary size bound for every clause coordinate of this input. -/
def dividerSizePolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  let variables := formulaVariableCountPolynomial verifier
  .add
    (.add (formulaClauseCountPolynomial verifier)
      (.add (.constant 1) (.mul variables variables)))
    (.constant 1)

/-- Only the divider's compiled execution is charged here, not the whole builder. -/
def dividerRawTimeBound {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .mul (.constant 120)
    (.mul (dividerSizePolynomial verifier) (dividerSizePolynomial verifier))

theorem dividerSizePolynomial_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (dividerSizePolynomial problem.verifier).eval problem.input.length =
      problem.formulaClauseSlotCount + problem.formulaClauseSlotsPerConstraint + 1 := by
  rfl

theorem dividerRawTimeBound_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (dividerRawTimeBound problem.verifier).eval problem.input.length =
      120 * ((problem.formulaClauseSlotCount +
        problem.formulaClauseSlotsPerConstraint + 1) *
        (problem.formulaClauseSlotCount +
          problem.formulaClauseSlotsPerConstraint + 1)) := by
  rfl

theorem dividerCompiledSteps_le {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin problem.formulaClauseSlotCount) :
    6 * BuilderPostHeaderRawDivider.workSteps index.val
        problem.formulaClauseSlotsPerConstraint ≤
      (dividerRawTimeBound problem.verifier).eval problem.input.length := by
  let localSize := index.val + problem.formulaClauseSlotsPerConstraint + 1
  let size := problem.formulaClauseSlotCount +
    problem.formulaClauseSlotsPerConstraint + 1
  have hSize : localSize ≤ size := by
    have hIndex := index.isLt
    dsimp only [localSize, size]
    omega
  have hLocal := BuilderPostHeaderRawDivider.workSteps_le_quadratic index.val
    problem.formulaClauseSlotsPerConstraint (clauseWidth_pos problem)
  rw [dividerRawTimeBound_eval]
  change 6 * BuilderPostHeaderRawDivider.workSteps index.val
      problem.formulaClauseSlotsPerConstraint ≤ 120 * (size * size)
  calc
    _ ≤ 6 * (20 * localSize * localSize) := Nat.mul_le_mul_left 6 hLocal
    _ = (6 * 20) * (localSize * localSize) := by
      rw [Nat.mul_assoc 20 localSize localSize,
        ← Nat.mul_assoc 6 20 (localSize * localSize)]
    _ = 120 * (localSize * localSize) := rfl
    _ ≤ 120 * (size * size) :=
      Nat.mul_le_mul_left 120 (Nat.mul_le_mul hSize hSize)

/-- Actual shielded execution preserves the exterior and exposes the canonical
occupancy coordinates within the charged source-size bound. The endpoint tape
construction and the rest of the physical selector remain to be connected. -/
theorem shielded_divider_execution {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin problem.formulaClauseSlotCount) (exterior : List WorkSymbol) :
    let width := problem.formulaClauseSlotsPerConstraint
    let steps := BuilderPostHeaderRawDivider.workSteps index.val width
    let initial := shieldedDividerStartConfiguration index.val width exterior
    let final := shieldedDividerFinalConfiguration index.val width exterior
    let coordinate := shieldedTerminalQuotientRemainder final exterior
    workRunExact? dividerMachine steps initial = some final ∧
    run (compileWorkMachine dividerMachine) (6 * steps)
        (encodeWorkConfiguration initial) = encodeWorkConfiguration final ∧
    final.tape.left =
      (BuilderPostHeaderRawDivider.finalConfiguration index.val width).tape.left ++
        exterior ∧
    constraintSlot problem coordinate.1 coordinate.2 =
      (problem.formulaClauseSchedule[index.val]?).map Option.isSome ∧
    6 * steps ≤
      (dividerRawTimeBound problem.verifier).eval problem.input.length := by
  dsimp only
  refine ⟨shielded_divider_workRunExact _ _ exterior (clauseWidth_pos problem),
    run_compile_shielded_divider_exact _ _ exterior (clauseWidth_pos problem),
    shieldedDividerFinal_exterior_preserved _ _ exterior, ?_,
    dividerCompiledSteps_le problem index⟩
  rw [shielded_final_quotient_remainder]
  exact (constraintSlot_div_mod problem index).trans
    (formulaSlot_eq_schedule problem index.val)

end PNP.Concrete.CookLevin.ClauseOccupancy
