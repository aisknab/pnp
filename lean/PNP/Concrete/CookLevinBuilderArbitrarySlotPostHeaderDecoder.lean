/-
Copyright (c) 2026 PNP Labs.

An all-coordinate post-header decoder for the concrete Cook--Levin token
schedule.

The decoder exposes the exact clause-rectangle and within-clause coordinate
for every body slot, preserves the direct token value, and isolates the unique
final `Finish` coordinate.  It also reads the exact shifted remainder from the
already checked M209 raw-router result.  This module does not implement raw
division or raw body-token emission.
-/

import PNP.Concrete.CookLevinBuilderArbitrarySlotHeaderRouter

namespace PNP.Concrete

namespace CookLevin

namespace BuilderArbitrarySlotPostHeaderDecoder

open BuilderArbitrarySlotHeaderRouter

/-! ## Generic fixed-rectangle coordinate decoding -/

/-- Structurally decode a natural coordinate in a fixed-width finite
rectangle.  The outer coordinate is consumed recursively; no coordinate list
or flattened block list is materialized. -/
def rectangleCoordinate? : (count width index : Nat) →
    Option (Fin count × Fin width)
  | 0, _, _ => none
  | count + 1, width, index =>
      if hIndex : index < width then
        some (⟨0, Nat.zero_lt_succ count⟩, ⟨index, hIndex⟩)
      else
        (rectangleCoordinate? count width (index - width)).map
          (fun coordinate => (coordinate.1.succ, coordinate.2))

/-- The decoder returns no coordinate exactly outside the rectangle. -/
theorem rectangleCoordinate?_eq_none_iff
    (count width index : Nat) :
    rectangleCoordinate? count width index = none ↔
      count * width ≤ index := by
  induction count generalizing index with
  | zero => simp [rectangleCoordinate?]
  | succ count ih =>
      by_cases hIndex : index < width
      · rw [rectangleCoordinate?, dif_pos hIndex]
        simp [Nat.succ_mul]
        omega
      · rw [rectangleCoordinate?, dif_neg hIndex]
        cases hPrevious : rectangleCoordinate? count width (index - width) with
        | none =>
            have hPreviousBound := (ih (index - width)).1 hPrevious
            have hLe : width ≤ index := Nat.le_of_not_gt hIndex
            have hSplit : width + (index - width) = index :=
              Nat.add_sub_of_le hLe
            change (none = none ↔ (count + 1) * width ≤ index)
            constructor
            · intro _
              rw [Nat.succ_mul]
              omega
            · intro _
              rfl
        | some previous =>
            have hPreviousInside : ¬count * width ≤ index - width := by
              intro hBound
              have hNone := (ih (index - width)).2 hBound
              rw [hPrevious] at hNone
              contradiction
            have hLe : width ≤ index := Nat.le_of_not_gt hIndex
            have hSplit : width + (index - width) = index :=
              Nat.add_sub_of_le hLe
            change
              (some (previous.1.succ, previous.2) = none ↔
                (count + 1) * width ≤ index)
            constructor
            · intro impossible
              contradiction
            · intro hWhole
              exfalso
              rw [Nat.succ_mul] at hWhole
              have hSub : count * width ≤ index - width := by omega
              exact hPreviousInside hSub

/-- Every decoded pair reconstructs the original natural coordinate. -/
theorem rectangleCoordinate?_reconstruct
    {count width index : Nat} {coordinate : Fin count × Fin width}
    (hCoordinate :
      rectangleCoordinate? count width index = some coordinate) :
    coordinate.1.val * width + coordinate.2.val = index := by
  induction count generalizing index with
  | zero => simp [rectangleCoordinate?] at hCoordinate
  | succ count ih =>
      by_cases hIndex : index < width
      · rw [rectangleCoordinate?, dif_pos hIndex] at hCoordinate
        cases hCoordinate
        simp
      · rw [rectangleCoordinate?, dif_neg hIndex] at hCoordinate
        cases hPrevious : rectangleCoordinate? count width (index - width) with
        | none => simp [hPrevious] at hCoordinate
        | some previous =>
            simp only [hPrevious, Option.map_some, Option.some.injEq] at hCoordinate
            cases hCoordinate
            have hReconstruct := ih hPrevious
            simp only [Fin.val_succ]
            rw [Nat.succ_mul]
            omega

/-- Direct fixed-rectangle lookup agrees with the decoded finite pair. -/
theorem rectangle_eq_coordinate?
    (count width : Nat) (blockSlot : Fin count → Nat → Option α)
    (index : Nat) :
    DirectSlot.rectangle count width blockSlot index =
      match rectangleCoordinate? count width index with
      | none => none
      | some coordinate => blockSlot coordinate.1 coordinate.2.val := by
  induction count generalizing index with
  | zero => rfl
  | succ count ih =>
      by_cases hIndex : index < width
      · rw [DirectSlot.rectangle, DirectSlot.flatFinite,
          rectangleCoordinate?, dif_pos hIndex, if_pos hIndex]
      · rw [DirectSlot.rectangle, DirectSlot.flatFinite,
          rectangleCoordinate?, dif_neg hIndex, if_neg hIndex]
        change DirectSlot.rectangle count width
            (fun coordinate => blockSlot coordinate.succ) (index - width) = _
        rw [ih (fun coordinate => blockSlot coordinate.succ)
          (index - width)]
        cases hCoordinate : rectangleCoordinate? count width (index - width) <;>
          simp

/-! ## Exact post-header route -/

/-- The complete three-way route after the formula header. -/
inductive PostHeaderRoute {language : Language}
    (problem : VerifierTableauProblem language) where
  | body
      (clauseCoordinate : Fin problem.formulaClauseSlotCount)
      (tokenCoordinate : Fin problem.formulaTokensPerClause)
  | finish
  | outOfRange
  deriving DecidableEq, Repr

/-- Decode a post-header coordinate into its fixed clause-token rectangle, the
unique final token, or the out-of-range suffix. -/
def postHeaderRoute {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    PostHeaderRoute problem :=
  match rectangleCoordinate? problem.formulaClauseSlotCount
      problem.formulaTokensPerClause index with
  | some coordinate => .body coordinate.1 coordinate.2
  | none =>
      if index =
          problem.formulaClauseSlotCount * problem.formulaTokensPerClause then
        .finish
      else
        .outOfRange

theorem postHeaderRoute_eq_body_iff {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat)
    (clauseCoordinate : Fin problem.formulaClauseSlotCount)
    (tokenCoordinate : Fin problem.formulaTokensPerClause) :
    postHeaderRoute problem index =
        .body clauseCoordinate tokenCoordinate ↔
      rectangleCoordinate? problem.formulaClauseSlotCount
          problem.formulaTokensPerClause index =
        some (clauseCoordinate, tokenCoordinate) := by
  unfold postHeaderRoute
  cases hCoordinate : rectangleCoordinate? problem.formulaClauseSlotCount
      problem.formulaTokensPerClause index with
  | none =>
      by_cases hFinish : index =
          problem.formulaClauseSlotCount * problem.formulaTokensPerClause
      · simp [hFinish]
      · simp [hFinish]
  | some coordinate =>
      rcases coordinate with ⟨outer, inner⟩
      simp

theorem postHeaderRoute_eq_finish_iff {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    postHeaderRoute problem index = .finish ↔
      index =
        problem.formulaClauseSlotCount * problem.formulaTokensPerClause := by
  unfold postHeaderRoute
  cases hCoordinate : rectangleCoordinate? problem.formulaClauseSlotCount
      problem.formulaTokensPerClause index with
  | some coordinate =>
      have hNotBound : ¬problem.formulaClauseSlotCount *
          problem.formulaTokensPerClause ≤ index := by
        intro hBound
        have hNone := (rectangleCoordinate?_eq_none_iff _ _ _).2 hBound
        rw [hCoordinate] at hNone
        contradiction
      have hNe : index ≠ problem.formulaClauseSlotCount *
          problem.formulaTokensPerClause := by omega
      simp [hNe]
  | none =>
      have hBound :=
        (rectangleCoordinate?_eq_none_iff _ _ _).1 hCoordinate
      by_cases hFinish : index =
          problem.formulaClauseSlotCount * problem.formulaTokensPerClause
      · simp [hFinish]
      · have hGreater : problem.formulaClauseSlotCount *
            problem.formulaTokensPerClause < index := by omega
        simp [hFinish]

theorem postHeaderRoute_eq_outOfRange_iff {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    postHeaderRoute problem index = .outOfRange ↔
      problem.formulaClauseSlotCount * problem.formulaTokensPerClause <
        index := by
  unfold postHeaderRoute
  cases hCoordinate : rectangleCoordinate? problem.formulaClauseSlotCount
      problem.formulaTokensPerClause index with
  | some coordinate =>
      have hNotBound : ¬problem.formulaClauseSlotCount *
          problem.formulaTokensPerClause ≤ index := by
        intro hBound
        have hNone := (rectangleCoordinate?_eq_none_iff _ _ _).2 hBound
        rw [hCoordinate] at hNone
        contradiction
      have hNotGreater : ¬problem.formulaClauseSlotCount *
          problem.formulaTokensPerClause < index := by omega
      simp [hNotGreater]
  | none =>
      have hBound :=
        (rectangleCoordinate?_eq_none_iff _ _ _).1 hCoordinate
      by_cases hFinish : index =
          problem.formulaClauseSlotCount * problem.formulaTokensPerClause
      · subst index
        simp
      · have hGreater : problem.formulaClauseSlotCount *
            problem.formulaTokensPerClause < index := by omega
        simp [hFinish, hGreater]

/-- Every body result is the exact quotient/remainder reconstruction of its
post-header coordinate. -/
theorem postHeaderRoute_body_reconstruct {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat)
    (clauseCoordinate : Fin problem.formulaClauseSlotCount)
    (tokenCoordinate : Fin problem.formulaTokensPerClause)
    (hRoute : postHeaderRoute problem index =
      .body clauseCoordinate tokenCoordinate) :
    clauseCoordinate.val * problem.formulaTokensPerClause +
        tokenCoordinate.val = index := by
  have hCoordinate : rectangleCoordinate? problem.formulaClauseSlotCount
      problem.formulaTokensPerClause index =
      some (clauseCoordinate, tokenCoordinate) :=
    (postHeaderRoute_eq_body_iff problem index
      clauseCoordinate tokenCoordinate).1 hRoute
  exact rectangleCoordinate?_reconstruct
    (coordinate := (clauseCoordinate, tokenCoordinate)) hCoordinate

/-- Interpret one decoded post-header route without materializing the full
token schedule. -/
def PostHeaderRoute.token? {language : Language}
    {problem : VerifierTableauProblem language} :
    PostHeaderRoute problem → Option (Option CNFToken)
  | .body clauseCoordinate tokenCoordinate =>
      problem.clauseTokenBlockSlotDirect clauseCoordinate tokenCoordinate.val
  | .finish => some (some .finish)
  | .outOfRange => none

/-- The existing direct post-header lookup is exactly the typed route
interpreter. -/
theorem postHeaderSlotDirect_route {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    BuilderArbitrarySlotHeaderRouter.postHeaderSlotDirect problem index =
      (postHeaderRoute problem index).token? := by
  unfold BuilderArbitrarySlotHeaderRouter.postHeaderSlotDirect
    DirectSlot.append
  by_cases hBody : index <
      problem.formulaClauseSlotCount * problem.formulaTokensPerClause
  · rw [if_pos hBody]
    unfold VerifierTableauProblem.formulaClauseTokenSlotDirect
    rw [rectangle_eq_coordinate?]
    cases hCoordinate : rectangleCoordinate? problem.formulaClauseSlotCount
        problem.formulaTokensPerClause index with
    | none =>
        have hOutside :=
          (rectangleCoordinate?_eq_none_iff _ _ _).1 hCoordinate
        omega
    | some coordinate =>
        rcases coordinate with ⟨outer, inner⟩
        simp [postHeaderRoute, hCoordinate, PostHeaderRoute.token?]
  · rw [if_neg hBody]
    have hLe : problem.formulaClauseSlotCount *
        problem.formulaTokensPerClause ≤ index := Nat.le_of_not_gt hBody
    have hNone : rectangleCoordinate? problem.formulaClauseSlotCount
        problem.formulaTokensPerClause index = none :=
      (rectangleCoordinate?_eq_none_iff _ _ _).2 hLe
    by_cases hFinish : index = problem.formulaClauseSlotCount *
        problem.formulaTokensPerClause
    · subst index
      simp [postHeaderRoute, hNone, DirectSlot.singleton,
        PostHeaderRoute.token?]
    · have hPositive : 0 < index -
          problem.formulaClauseSlotCount * problem.formulaTokensPerClause := by
        omega
      cases hDifference : index -
          problem.formulaClauseSlotCount * problem.formulaTokensPerClause with
      | zero => omega
      | succ difference =>
          simp [postHeaderRoute, hNone, hFinish, DirectSlot.singleton,
            PostHeaderRoute.token?]

/-! ## Full direct-token route -/

/-- Interpret M209's outer route through the complete post-header decoder. -/
def decodedTokenSlotDirect {language : Language}
    (problem : VerifierTableauProblem language) (coordinate : Nat) :
    Option (Option CNFToken) :=
  match outerRoute problem coordinate with
  | .header headerCoordinate =>
      problem.formulaHeaderTokenSlotDirect headerCoordinate
  | .postHeader remainder => (postHeaderRoute problem remainder).token?

theorem formulaTokenSlotDirect_decoded {language : Language}
    (problem : VerifierTableauProblem language) (coordinate : Nat) :
    problem.formulaTokenSlotDirect coordinate =
      decodedTokenSlotDirect problem coordinate := by
  rw [BuilderArbitrarySlotHeaderRouter.formulaTokenSlotDirect_route]
  unfold decodedTokenSlotDirect
  cases hOuter : outerRoute problem coordinate with
  | header headerCoordinate => rfl
  | postHeader remainder =>
      exact postHeaderSlotDirect_route problem remainder

/-! ## Exact remainder exposed by the M209 raw result -/

namespace RawRemainder

open BuilderArbitrarySlotHeaderRouter.RawRouter

/-- Read the shifted post-header remainder encoded by a canonical raw-router
result configuration.  Accepting header results deliberately decode to
`none`. -/
def configurationPostHeaderRemainder?
    (configuration : WorkConfiguration) : Option Nat :=
  if configuration.state = machine.rejectState then
    some ((configuration.tape.left.count unitSymbol +
      configuration.tape.left.count coordinateMark) -
      configuration.tape.left.count boundaryMark)
  else
    none

/-- Semantic remainder corresponding to each exact M209 comparison result. -/
def comparisonResultPostHeaderRemainder? : ComparisonResult → Option Nat
  | .less _ _ => none
  | .equal _ => some 0
  | .greater _ remainingCoordinate => some (remainingCoordinate + 1)

theorem configurationPostHeaderRemainder?_resultConfiguration
    (result : ComparisonResult) :
    configurationPostHeaderRemainder? (resultConfiguration result) =
      comparisonResultPostHeaderRemainder? result := by
  cases result <;>
    simp [configurationPostHeaderRemainder?,
      comparisonResultPostHeaderRemainder?, resultConfiguration, machine,
      List.count_append, List.count_replicate, unitSymbol,
      coordinateMark, boundaryMark,
      separatorSymbol, leftBoundary, BuilderUnaryPolynomial.unitSymbol,
      BuilderUnaryPolynomial.separatorSymbol,
      BuilderUnaryPolynomial.registerMarkSymbol, PipelineTape.leftMarker,
      WorkSymbol.oneOne, WorkSymbol.oneZero, WorkSymbol.zeroOne,
      WorkSymbol.zeroZero] <;>
    omega

theorem compareResult_postHeaderRemainder?
    (processed coordinate boundary : Nat) :
    comparisonResultPostHeaderRemainder?
        (compareResult processed coordinate boundary) =
      if coordinate < boundary then none
      else some (coordinate - boundary) := by
  induction coordinate generalizing processed boundary with
  | zero =>
      cases boundary <;>
        simp [compareResult, comparisonResultPostHeaderRemainder?]
  | succ coordinate ih =>
      cases boundary with
      | zero => simp [compareResult, comparisonResultPostHeaderRemainder?]
      | succ boundary =>
          simpa [compareResult] using ih (processed + 1) boundary

theorem finalConfiguration_postHeaderRemainder? (coordinate boundary : Nat) :
    configurationPostHeaderRemainder? (finalConfiguration coordinate boundary) =
      if coordinate < boundary then none
      else some (coordinate - boundary) := by
  rw [finalConfiguration,
    configurationPostHeaderRemainder?_resultConfiguration,
    compareResult_postHeaderRemainder?]

theorem finalConfiguration_postHeaderRemainder?_eq_outerRoute
    {language : Language} (problem : VerifierTableauProblem language)
    (coordinate : Nat) :
    configurationPostHeaderRemainder?
        (finalConfiguration coordinate
          (BuilderFullScheduleCursorController.firstBodySlot problem)) =
      match outerRoute problem coordinate with
      | .header _ => none
      | .postHeader remainder => some remainder := by
  rw [finalConfiguration_postHeaderRemainder?]
  unfold outerRoute
  split <;> rfl

end RawRemainder

/-! ## In-range endpoint -/

theorem postHeaderRoute_in_range {language : Language}
    (problem : VerifierTableauProblem language)
    (coordinate :
      Fin (BuilderFullScheduleCursorController.terminalSlot problem))
    (remainder : Nat)
    (hOuter : outerRoute problem coordinate.val = .postHeader remainder) :
    postHeaderRoute problem remainder ≠ .outOfRange := by
  intro hOut
  have hRoute :=
    (BuilderArbitrarySlotHeaderRouter.outerRoute_eq_postHeader_iff
      problem coordinate.val remainder).1 hOuter
  have hTooLarge :=
    (postHeaderRoute_eq_outOfRange_iff problem remainder).1 hOut
  have hCoordinate := coordinate.isLt
  have hCoordinateBound : coordinate.val <
      BuilderFullScheduleCursorController.firstBodySlot problem +
        (problem.formulaClauseSlotCount *
          problem.formulaTokensPerClause + 1) := by
    calc
      coordinate.val <
          BuilderFullScheduleCursorController.terminalSlot problem :=
        hCoordinate
      _ = BuilderFullScheduleCursorController.firstBodySlot problem +
          BuilderFullScheduleCursorController.bodySlotCount problem :=
        BuilderFullScheduleCursorController.terminalSlot_eq problem
      _ = BuilderFullScheduleCursorController.firstBodySlot problem +
          (problem.formulaClauseSlotCount *
            problem.formulaTokensPerClause + 1) := by
        rw [BuilderFullScheduleCursorController.bodySlotCount_eq]
  omega

/-- M210 closes the non-repeatable semantic decoder boundary after M209: every
in-range direct token coordinate routes through an exact clause/within-clause
pair or the unique final token, and the checked M209 raw result exposes the
exact shifted post-header remainder.  Raw division, raw body-token emission,
the complete formula builder and its refinement remain open. -/
theorem cook_levin_arbitrary_slot_post_header_decoder_checked_complete
    {language : Language} (problem : VerifierTableauProblem language)
    (coordinate :
      Fin (BuilderFullScheduleCursorController.terminalSlot problem)) :
    problem.formulaTokenSlotDirect coordinate.val =
        decodedTokenSlotDirect problem coordinate.val ∧
    (∀ remainder,
      outerRoute problem coordinate.val = .postHeader remainder →
        postHeaderRoute problem remainder ≠ .outOfRange) ∧
    (∀ remainder clauseCoordinate tokenCoordinate,
      outerRoute problem coordinate.val = .postHeader remainder →
      postHeaderRoute problem remainder =
          .body clauseCoordinate tokenCoordinate →
        clauseCoordinate.val * problem.formulaTokensPerClause +
          tokenCoordinate.val = remainder) ∧
    RawRemainder.configurationPostHeaderRemainder?
        (RawRouter.finalConfiguration coordinate.val
          (BuilderFullScheduleCursorController.firstBodySlot problem)) =
      (match outerRoute problem coordinate.val with
      | .header _ => none
      | .postHeader remainder => some remainder) ∧
    workRunExact? RawRouter.machine
        (RawRouter.workSteps coordinate.val
          (BuilderFullScheduleCursorController.firstBodySlot problem))
        (workStartConfiguration RawRouter.machine
          (RawRouter.inputTape coordinate.val
            (BuilderFullScheduleCursorController.firstBodySlot problem))) =
      some
        (RawRouter.finalConfiguration coordinate.val
          (BuilderFullScheduleCursorController.firstBodySlot problem)) := by
  refine ⟨formulaTokenSlotDirect_decoded problem coordinate.val,
    ?_, ?_, RawRemainder.finalConfiguration_postHeaderRemainder?_eq_outerRoute
      problem coordinate.val,
    RawRouter.workRunExact coordinate.val
      (BuilderFullScheduleCursorController.firstBodySlot problem)⟩
  · intro remainder hOuter
    exact postHeaderRoute_in_range problem coordinate remainder hOuter
  · intro remainder clauseCoordinate tokenCoordinate _hOuter hBody
    exact postHeaderRoute_body_reconstruct problem remainder
      clauseCoordinate tokenCoordinate hBody

end BuilderArbitrarySlotPostHeaderDecoder

end CookLevin

end PNP.Concrete
