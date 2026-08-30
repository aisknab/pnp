/-
Copyright (c) 2026 PNP Labs.

All-coordinate executable orchestration from the exact raw header-router
result into the fixed post-header quotient/remainder machine.

This module reads the shifted remainder exposed by M209's literal raw result,
launches M211's fixed divider on that recovered natural and the exact
problem-derived clause width, and classifies every M210 body, finish, and
out-of-range result. It does not implement a literal tape-to-tape bridge,
preserve a complete builder workspace through such a bridge, emit a body token,
or construct the complete formula builder, RawRefinement, reduction, CNFSAT
decider, root theorem, or P = NP.
-/

import PNP.Concrete.CookLevinBuilderPostHeaderRawDivider

namespace PNP.Concrete

namespace CookLevin

namespace BuilderPostHeaderRawLaunch

open BuilderArbitrarySlotHeaderRouter
  BuilderArbitrarySlotPostHeaderDecoder

abbrev routerMachine : WorkMachine :=
  BuilderArbitrarySlotHeaderRouter.RawRouter.machine

abbrev dividerMachine : WorkMachine :=
  BuilderPostHeaderRawDivider.machine

/-- The literal M209 endpoint's checked post-header remainder. -/
def recoveredRemainder? {language : Language}
    (problem : VerifierTableauProblem language)
    (coordinate : Nat) : Option Nat :=
  BuilderArbitrarySlotPostHeaderDecoder.RawRemainder.configurationPostHeaderRemainder?
      (BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration coordinate
        (BuilderFullScheduleCursorController.firstBodySlot problem))

/-- Execute the fixed M211 divider exactly when M209's endpoint is on the
post-header branch. This executable Lean orchestration constructs the
divider's canonical input tape; it is not itself a raw tape-rewrite machine. -/
def launch? {language : Language}
    (problem : VerifierTableauProblem language)
    (coordinate : Nat) : Option WorkConfiguration :=
  match recoveredRemainder? problem coordinate with
  | none => none
  | some remainder =>
      BuilderPostHeaderRawDivider.divide? remainder
        problem.formulaTokensPerClause

/-- Exact quotient/remainder visible at M211's endpoint for one shifted
post-header index. -/
def decodedPair {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Nat) : Nat × Nat :=
  BuilderPostHeaderRawDivider.terminalQuotientRemainder
    (BuilderPostHeaderRawDivider.finalConfiguration index
      problem.formulaTokensPerClause)

theorem formulaTokensPerClause_pos {language : Language}
    (problem : VerifierTableauProblem language) :
    0 < problem.formulaTokensPerClause := by
  unfold VerifierTableauProblem.formulaTokensPerClause
  omega

theorem recoveredRemainder?_eq {language : Language}
    (problem : VerifierTableauProblem language)
    (coordinate : Nat) :
    recoveredRemainder? problem coordinate =
      if coordinate <
          BuilderFullScheduleCursorController.firstBodySlot problem then
        none
      else
        some (coordinate -
          BuilderFullScheduleCursorController.firstBodySlot problem) := by
  exact BuilderArbitrarySlotPostHeaderDecoder.RawRemainder.finalConfiguration_postHeaderRemainder?
    coordinate
      (BuilderFullScheduleCursorController.firstBodySlot problem)

theorem launch?_eq {language : Language}
    (problem : VerifierTableauProblem language)
    (coordinate : Nat) :
    launch? problem coordinate =
      if coordinate <
          BuilderFullScheduleCursorController.firstBodySlot problem then
        none
      else
        some (BuilderPostHeaderRawDivider.finalConfiguration
          (coordinate -
            BuilderFullScheduleCursorController.firstBodySlot problem)
          problem.formulaTokensPerClause) := by
  unfold launch?
  rw [recoveredRemainder?_eq]
  by_cases hHeader : coordinate <
      BuilderFullScheduleCursorController.firstBodySlot problem
  · simp [hHeader]
  · simp [hHeader, BuilderPostHeaderRawDivider.divide?,
      formulaTokensPerClause_pos problem]

theorem launch?_eq_none_iff_header {language : Language}
    (problem : VerifierTableauProblem language)
    (coordinate : Nat) :
    launch? problem coordinate = none ↔
      outerRoute problem coordinate = .header coordinate := by
  rw [launch?_eq]
  by_cases hHeader : coordinate <
      BuilderFullScheduleCursorController.firstBodySlot problem
  · rw [if_pos hHeader]
    exact iff_of_true rfl
      ((outerRoute_eq_header_iff problem coordinate coordinate).2
        ⟨hHeader, rfl⟩)
  · rw [if_neg hHeader]
    constructor
    · intro hImpossible
      contradiction
    · intro hRoute
      exact False.elim (hHeader
        ((outerRoute_eq_header_iff problem coordinate coordinate).1 hRoute).1)

theorem launch?_postHeader {language : Language}
    (problem : VerifierTableauProblem language)
    (coordinate remainder : Nat)
    (hRoute : outerRoute problem coordinate = .postHeader remainder) :
    launch? problem coordinate =
      some (BuilderPostHeaderRawDivider.finalConfiguration remainder
        problem.formulaTokensPerClause) := by
  have hPost := (outerRoute_eq_postHeader_iff
    problem coordinate remainder).1 hRoute
  rw [launch?_eq, if_neg (Nat.not_lt_of_ge hPost.1), hPost.2]

theorem router_workRunExact {language : Language}
    (problem : VerifierTableauProblem language)
    (coordinate : Nat) :
    workRunExact? routerMachine
        (BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps coordinate
          (BuilderFullScheduleCursorController.firstBodySlot problem))
        (workStartConfiguration routerMachine
          (BuilderArbitrarySlotHeaderRouter.RawRouter.inputTape coordinate
            (BuilderFullScheduleCursorController.firstBodySlot problem))) =
      some (BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration
        coordinate
        (BuilderFullScheduleCursorController.firstBodySlot problem)) := by
  exact BuilderArbitrarySlotHeaderRouter.RawRouter.workRunExact coordinate
    (BuilderFullScheduleCursorController.firstBodySlot problem)

theorem divider_workRunExact {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Nat) :
    workRunExact? dividerMachine
        (BuilderPostHeaderRawDivider.workSteps index
          problem.formulaTokensPerClause)
        (workStartConfiguration dividerMachine
          (BuilderPostHeaderRawDivider.inputTape index
            problem.formulaTokensPerClause)) =
      some (BuilderPostHeaderRawDivider.finalConfiguration index
        problem.formulaTokensPerClause) := by
  exact BuilderPostHeaderRawDivider.workRunExact index
    problem.formulaTokensPerClause (formulaTokensPerClause_pos problem)

theorem decodedPair_eq_div_mod {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Nat) :
    decodedPair problem index =
      (index / problem.formulaTokensPerClause,
        index % problem.formulaTokensPerClause) := by
  exact BuilderPostHeaderRawDivider.final_quotient_remainder index
    problem.formulaTokensPerClause

/-- Route-indexed correctness proposition used below to keep the exact M210
branch visible without supplying a branch certificate to the public theorem. -/
def RouteDecodeHolds {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Nat) : Prop :=
  match postHeaderRoute problem index with
  | .body clauseCoordinate tokenCoordinate =>
      decodedPair problem index =
        (clauseCoordinate.val, tokenCoordinate.val)
  | .finish =>
      decodedPair problem index =
        (problem.formulaClauseSlotCount, 0)
  | .outOfRange =>
      (decodedPair problem index).1 * problem.formulaTokensPerClause +
          (decodedPair problem index).2 = index ∧
        (decodedPair problem index).2 < problem.formulaTokensPerClause ∧
        problem.formulaClauseSlotCount *
            problem.formulaTokensPerClause < index

theorem decodedPair_finish {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Nat)
    (hRoute : postHeaderRoute problem index = .finish) :
    decodedPair problem index =
      (problem.formulaClauseSlotCount, 0) := by
  have hIndex := (postHeaderRoute_eq_finish_iff problem index).1 hRoute
  have hWidth := formulaTokensPerClause_pos problem
  have hLower :
      problem.formulaClauseSlotCount * problem.formulaTokensPerClause ≤
        index := by omega
  have hUpper :
      index < (problem.formulaClauseSlotCount + 1) *
        problem.formulaTokensPerClause := by
    rw [Nat.succ_mul]
    omega
  have hQuotient :
      index / problem.formulaTokensPerClause =
        problem.formulaClauseSlotCount :=
    Nat.div_eq_of_lt_le hLower hUpper
  have hNatural := BuilderPostHeaderRawDivider.quotient_remainder_reconstruct
    index problem.formulaTokensPerClause
  have hRemainder : index % problem.formulaTokensPerClause = 0 := by
    rw [hQuotient] at hNatural
    omega
  rw [decodedPair_eq_div_mod, hQuotient, hRemainder]

theorem decodedPair_outOfRange {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Nat)
    (hRoute : postHeaderRoute problem index = .outOfRange) :
    (decodedPair problem index).1 * problem.formulaTokensPerClause +
          (decodedPair problem index).2 = index ∧
      (decodedPair problem index).2 < problem.formulaTokensPerClause ∧
      problem.formulaClauseSlotCount *
          problem.formulaTokensPerClause < index := by
  have hPair := decodedPair_eq_div_mod problem index
  have hReconstruct := BuilderPostHeaderRawDivider.quotient_remainder_reconstruct
    index problem.formulaTokensPerClause
  have hRemainder := BuilderPostHeaderRawDivider.remainder_lt_width index
    problem.formulaTokensPerClause (formulaTokensPerClause_pos problem)
  have hOut := (postHeaderRoute_eq_outOfRange_iff problem index).1 hRoute
  rw [hPair]
  exact ⟨hReconstruct, hRemainder, hOut⟩

theorem routeDecodeHolds {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Nat) :
    RouteDecodeHolds problem index := by
  unfold RouteDecodeHolds
  cases hRoute : postHeaderRoute problem index with
  | body clauseCoordinate tokenCoordinate =>
      exact BuilderPostHeaderRawDivider.final_quotient_remainder_eq_body_coordinates
        problem index
          clauseCoordinate tokenCoordinate hRoute
  | finish => exact decodedPair_finish problem index hRoute
  | outOfRange => exact decodedPair_outOfRange problem index hRoute

/-- Every coordinate in the complete schedule either remains in the header
branch or launches the exact raw divider on an in-range M210 post-header
route. No route witness is supplied to this theorem. -/
theorem inRange_launch {language : Language}
    (problem : VerifierTableauProblem language)
    (coordinate :
      Fin (BuilderFullScheduleCursorController.terminalSlot problem)) :
    match outerRoute problem coordinate.val with
    | .header _ => launch? problem coordinate.val = none
    | .postHeader remainder =>
        launch? problem coordinate.val =
            some (BuilderPostHeaderRawDivider.finalConfiguration remainder
              problem.formulaTokensPerClause) ∧
          RouteDecodeHolds problem remainder ∧
          postHeaderRoute problem remainder ≠ .outOfRange := by
  cases hOuter : outerRoute problem coordinate.val with
  | header headerCoordinate =>
      have hHeader := (outerRoute_eq_header_iff problem coordinate.val
        headerCoordinate).1 hOuter
      rw [launch?_eq, if_pos hHeader.1]
  | postHeader remainder =>
      exact ⟨launch?_postHeader problem coordinate.val remainder hOuter,
        routeDecodeHolds problem remainder,
        postHeaderRoute_in_range problem coordinate remainder hOuter⟩

/-- Total compiled raw-transition count of the two exact machines selected by
the executable orchestration. The header branch runs only M209; a post-header
branch additionally runs the fixed M211 divider. -/
def stagedCompiledSteps {language : Language}
    (problem : VerifierTableauProblem language)
    (coordinate : Nat) : Nat :=
  6 * BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps coordinate
      (BuilderFullScheduleCursorController.firstBodySlot problem) +
    (match recoveredRemainder? problem coordinate with
    | none => 0
    | some remainder =>
        6 * BuilderPostHeaderRawDivider.workSteps remainder
          problem.formulaTokensPerClause)

/-- Source-size polynomial used for the complete staged M209/M211 bound. -/
def stagedSizePolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add
    (.add
      (BuilderFullScheduleCursorController.terminalSlotPolynomial verifier)
      (formulaClauseTokenPolynomial verifier))
    (.constant 1)

/-- One source-size polynomial dominating both compiled raw traces at every
coordinate inside the complete formula-token schedule. -/
def rawTimeBound {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add
    (BuilderArbitrarySlotHeaderRouter.RawRouter.rawTimeBound verifier)
    (.mul (.constant 120)
      (.mul (stagedSizePolynomial verifier)
        (stagedSizePolynomial verifier)))

theorem rawTimeBound_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (rawTimeBound problem.verifier).eval problem.input.length =
      (BuilderArbitrarySlotHeaderRouter.RawRouter.rawTimeBound
          problem.verifier).eval problem.input.length +
        120 *
          ((BuilderFullScheduleCursorController.terminalSlot problem +
              problem.formulaTokensPerClause + 1) *
            (BuilderFullScheduleCursorController.terminalSlot problem +
              problem.formulaTokensPerClause + 1)) := by
  rfl

theorem stagedCompiledSteps_le_rawTimeBound {language : Language}
    (problem : VerifierTableauProblem language)
    (coordinate : Nat)
    (hCoordinate :
      coordinate < BuilderFullScheduleCursorController.terminalSlot problem) :
    stagedCompiledSteps problem coordinate ≤
      (rawTimeBound problem.verifier).eval problem.input.length := by
  have hRouter :=
    BuilderArbitrarySlotHeaderRouter.RawRouter.rawTimeBound_le problem
      coordinate hCoordinate
  unfold stagedCompiledSteps
  rw [recoveredRemainder?_eq]
  by_cases hHeader : coordinate <
      BuilderFullScheduleCursorController.firstBodySlot problem
  · simp only [if_pos hHeader, Nat.add_zero]
    rw [rawTimeBound_eval]
    omega
  · simp only [if_neg hHeader]
    let remainder := coordinate -
      BuilderFullScheduleCursorController.firstBodySlot problem
    let width := problem.formulaTokensPerClause
    have hWidth : 0 < width := by
      exact formulaTokensPerClause_pos problem
    have hDividerWork :=
      BuilderPostHeaderRawDivider.workSteps_le_quadratic remainder width hWidth
    have hDividerCompiled :
        6 * BuilderPostHeaderRawDivider.workSteps remainder width ≤
          120 * ((remainder + width + 1) *
            (remainder + width + 1)) := by
      have hScaled := Nat.mul_le_mul_left 6 hDividerWork
      calc
        6 * BuilderPostHeaderRawDivider.workSteps remainder width ≤
            6 * (20 * (remainder + width + 1) *
              (remainder + width + 1)) := hScaled
        _ = (6 * 20) * ((remainder + width + 1) *
              (remainder + width + 1)) := by
            simp only [Nat.mul_assoc]
        _ = 120 * ((remainder + width + 1) *
              (remainder + width + 1)) := by rfl
    have hSize : remainder + width + 1 ≤
        BuilderFullScheduleCursorController.terminalSlot problem +
          width + 1 := by
      dsimp [remainder]
      omega
    have hDividerTotal :
        6 * BuilderPostHeaderRawDivider.workSteps remainder width ≤
          120 *
            ((BuilderFullScheduleCursorController.terminalSlot problem +
                width + 1) *
              (BuilderFullScheduleCursorController.terminalSlot problem +
                width + 1)) := by
      apply Nat.le_trans hDividerCompiled
      have hSquare := Nat.mul_le_mul hSize hSize
      exact Nat.mul_le_mul_left 120 hSquare
    change
      6 * BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps coordinate
          (BuilderFullScheduleCursorController.firstBodySlot problem) +
          6 * BuilderPostHeaderRawDivider.workSteps remainder width ≤
        (rawTimeBound problem.verifier).eval problem.input.length
    rw [rawTimeBound_eval]
    exact Nat.add_le_add hRouter hDividerTotal

/-- M212 closes the executable post-header handoff boundary for every natural
coordinate: M209's exact raw result launches M211's exact fixed divider, M210's
three semantic route classes are recovered without supplied route data, and
the combined compiled work is bounded by one source-size polynomial for every
in-range coordinate. This remains an orchestration of two machines, not a
literal tape-to-tape bridge or body-token emitter. -/
theorem cook_levin_builder_post_header_raw_launch_checked_complete
    {language : Language} (problem : VerifierTableauProblem language) :
    (∀ coordinate,
      workRunExact? routerMachine
          (BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps coordinate
            (BuilderFullScheduleCursorController.firstBodySlot problem))
          (workStartConfiguration routerMachine
            (BuilderArbitrarySlotHeaderRouter.RawRouter.inputTape coordinate
              (BuilderFullScheduleCursorController.firstBodySlot problem))) =
        some (BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration
          coordinate
          (BuilderFullScheduleCursorController.firstBodySlot problem))) ∧
    (∀ coordinate,
      recoveredRemainder? problem coordinate =
        match outerRoute problem coordinate with
        | .header _ => none
        | .postHeader remainder => some remainder) ∧
    (∀ index,
      workRunExact? dividerMachine
          (BuilderPostHeaderRawDivider.workSteps index
            problem.formulaTokensPerClause)
          (workStartConfiguration dividerMachine
            (BuilderPostHeaderRawDivider.inputTape index
              problem.formulaTokensPerClause)) =
        some (BuilderPostHeaderRawDivider.finalConfiguration index
          problem.formulaTokensPerClause)) ∧
    (∀ index, RouteDecodeHolds problem index) ∧
    (∀ coordinate :
        Fin (BuilderFullScheduleCursorController.terminalSlot problem),
      match outerRoute problem coordinate.val with
      | .header _ => launch? problem coordinate.val = none
      | .postHeader remainder =>
          launch? problem coordinate.val =
              some (BuilderPostHeaderRawDivider.finalConfiguration remainder
                problem.formulaTokensPerClause) ∧
            RouteDecodeHolds problem remainder ∧
            postHeaderRoute problem remainder ≠ .outOfRange) ∧
    (∀ coordinate,
      coordinate < BuilderFullScheduleCursorController.terminalSlot problem →
        stagedCompiledSteps problem coordinate ≤
          (rawTimeBound problem.verifier).eval problem.input.length) := by
  exact ⟨router_workRunExact problem,
    BuilderArbitrarySlotPostHeaderDecoder.RawRemainder.finalConfiguration_postHeaderRemainder?_eq_outerRoute
      problem,
    divider_workRunExact problem,
    routeDecodeHolds problem,
    inRange_launch problem,
    stagedCompiledSteps_le_rawTimeBound problem⟩

end BuilderPostHeaderRawLaunch

end CookLevin

end PNP.Concrete
