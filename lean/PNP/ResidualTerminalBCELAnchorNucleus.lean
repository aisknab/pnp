/-
Copyright (c) 2026 PNP Labs.

Computed terminal BCEL anchor nuclei and their proper-cut square boundary.  An
input problem starts from one proof-bearing governed proper-positive terminal
support, one explicit forgetful projection, and one executable ambient
observer.  The anchor universe, every subfamily, its saturation, its projection
defect, and every cut square are computed from those inputs.

This is the finite terminal reconstruction of the anchor-nucleus and
constant-cut boundary used by the pinned manuscript's BCEL argument.  It does
not derive a positive whole-support projection defect, identify manuscript
activation or charge equivalence classes absent from the terminal model,
connect a local obstruction to the complete global route system, prove
SaturatePositive, BCELReady, ZeroSlack, PCCMin, polynomial runtime, SAT in P,
remove a project assumption, or prove P = NP.
-/

import PNP.ResidualTerminalBN2SquareLegitimacy

namespace PNP
namespace DirectWire

/-! ## Canonical anchor problem and subfamilies -/

/-- Source data for the finite computed anchor problem.  The governed support
    is an output of the existing exhaustive proper-positive search; callers do
    not provide an anchor list or any algebra/coherence certificate. -/
structure TerminalBCELAnchorProblem
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (system : TerminalSaturationSystem inputs gates outputs profileWidth) where
  support : TerminalProperPositiveSupport candidate system
  projection : TerminalProfileProjection profileWidth
  observe : Implementation (inputs + gates) gates ->
    TerminalProfile profileWidth

/-- Canonical primitive-record order restricted to the computed saturated
    support.  This removes work-list visitation order from all anchor choices. -/
def TerminalBCELAnchorProblem.anchorRecords
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system) :
    List (TerminalPrimitiveRecord inputs gates outputs profileWidth) :=
  (allTerminalPrimitiveRecords inputs gates outputs profileWidth).filter
    (fun record => decide (record ∈ problem.support.saturatedRecords))

/-- Exact membership in the canonical anchor universe. -/
theorem TerminalBCELAnchorProblem.mem_anchorRecords_iff
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (record : TerminalPrimitiveRecord inputs gates outputs profileWidth) :
    record ∈ problem.anchorRecords ↔
      record ∈ problem.support.saturatedRecords := by
  unfold TerminalBCELAnchorProblem.anchorRecords
  constructor
  · intro member
    exact of_decide_eq_true (List.mem_filter.mp member).2
  · intro member
    exact List.mem_filter.mpr
      ⟨mem_allTerminalPrimitiveRecords record, decide_eq_true member⟩

/-- Canonical anchor records are duplicate-free. -/
theorem TerminalBCELAnchorProblem.anchorRecords_nodup
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system) :
    problem.anchorRecords.Nodup :=
  (allTerminalPrimitiveRecords_nodup
    inputs gates outputs profileWidth).sublist List.filter_sublist

/-- Every order-preserving anchor subfamily in canonical order. -/
def TerminalBCELAnchorProblem.allAnchorSubfamilies
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system) :
    List (List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :=
  terminalListSubsets problem.anchorRecords

/-- The complete anchor family occurs in its own exhaustive subfamily list. -/
theorem TerminalBCELAnchorProblem.anchorRecords_mem_allAnchorSubfamilies
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system) :
    problem.anchorRecords ∈ problem.allAnchorSubfamilies := by
  unfold TerminalBCELAnchorProblem.allAnchorSubfamilies
  have filtered : problem.anchorRecords.filter (fun _record => true) =
      problem.anchorRecords := by
    induction problem.anchorRecords with
    | nil => rfl
    | cons head tail ih =>
        change head :: tail.filter (fun _record => true) = head :: tail
        rw [ih]
  have member := filter_mem_terminalListSubsets problem.anchorRecords
    (fun _record => true)
  rw [filtered] at member
  exact member

/-- The computed four-corner carrier associated with two anchor seeds. -/
def TerminalBCELAnchorProblem.carrier
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (leftSeed rightSeed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    TerminalFourCornerCarrier system :=
  (terminalSaturatedSupportSquare system leftSeed rightSeed).fourCornerCarrier
    candidate problem.projection

/-- The exact projection defect of one anchor subfamily.  The family occupies
    the left corner of a canonical carrier with an empty opposite seed. -/
def TerminalBCELAnchorProblem.familyDefect
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (family : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) : Nat :=
  let corners := (problem.carrier family []).optimizationCorners
    problem.observe
  terminalProjectionDefect corners.system corners.projection corners.left

/-! ## Deterministic minimum-cardinality positive nucleus -/

private structure TerminalMinimumPositiveAnchorFamily
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (families : List (List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))) where
  family : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)
  member : family ∈ families
  positive : 0 < problem.familyDefect family
  minimumCardinality : ∀ smaller,
    smaller ∈ families -> smaller.length < family.length ->
      problem.familyDefect smaller = 0

private inductive TerminalMinimumPositiveAnchorOutcome
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system) :
    (families : List (List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))) -> Type
  | none
      (allZero : ∀ family, family ∈ families ->
        problem.familyDefect family = 0) :
      TerminalMinimumPositiveAnchorOutcome problem families
  | found (result : TerminalMinimumPositiveAnchorFamily problem families) :
      TerminalMinimumPositiveAnchorOutcome problem families

private def minimumPositiveAnchorOutcome
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system) :
    (families : List (List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))) ->
      TerminalMinimumPositiveAnchorOutcome problem families
  | [] => .none (by intro family member; cases member)
  | head :: tail =>
      match minimumPositiveAnchorOutcome problem tail with
      | .none tailZero =>
          if headPositive : 0 < problem.familyDefect head then
            .found
              { family := head
                member := List.Mem.head tail
                positive := headPositive
                minimumCardinality := by
                  intro smaller member smallerLength
                  cases List.mem_cons.mp member with
                  | inl equal =>
                      subst smaller
                      exact False.elim (Nat.lt_irrefl _ smallerLength)
                  | inr tailMember =>
                      exact tailZero smaller tailMember }
          else
            .none (by
              intro family member
              cases List.mem_cons.mp member with
              | inl equal =>
                  subst family
                  exact Nat.eq_zero_of_not_pos headPositive
              | inr tailMember => exact tailZero family tailMember)
      | .found found =>
          if headPositive : 0 < problem.familyDefect head then
            if headNoLarger : head.length <= found.family.length then
              .found
                { family := head
                  member := List.Mem.head tail
                  positive := headPositive
                  minimumCardinality := by
                    intro smaller member smallerLength
                    cases List.mem_cons.mp member with
                    | inl equal =>
                        subst smaller
                        exact False.elim (Nat.lt_irrefl _ smallerLength)
                    | inr tailMember =>
                        exact found.minimumCardinality smaller tailMember
                          (Nat.lt_of_lt_of_le smallerLength headNoLarger) }
            else
              .found
                { family := found.family
                  member := List.Mem.tail head found.member
                  positive := found.positive
                  minimumCardinality := by
                    intro smaller member smallerLength
                    cases List.mem_cons.mp member with
                    | inl equal =>
                        subst smaller
                        have foundBeforeHead :
                            found.family.length < head.length :=
                          Nat.lt_of_not_ge headNoLarger
                        exact False.elim
                          ((Nat.not_lt_of_ge (Nat.le_of_lt foundBeforeHead))
                            smallerLength)
                    | inr tailMember =>
                        exact found.minimumCardinality smaller tailMember
                          smallerLength }
          else
            .found
              { family := found.family
                member := List.Mem.tail head found.member
                positive := found.positive
                minimumCardinality := by
                  intro smaller member smallerLength
                  cases List.mem_cons.mp member with
                  | inl equal =>
                      subst smaller
                      exact Nat.eq_zero_of_not_pos headPositive
                  | inr tailMember =>
                      exact found.minimumCardinality smaller tailMember
                        smallerLength }

/-- Proof-bearing result of the exhaustive positive anchor-nucleus search. -/
structure TerminalMinimalPositiveAnchorNucleus
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system) where
  anchors : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)
  governed : anchors ∈ problem.allAnchorSubfamilies
  positive : 0 < problem.familyDefect anchors
  minimumCardinality : ∀ smaller,
    smaller ∈ problem.allAnchorSubfamilies ->
      smaller.length < anchors.length -> problem.familyDefect smaller = 0

/-- Exhaustively compute the canonical first minimum-cardinality positive
    anchor subfamily.  Equal-cardinality ties retain subset-enumeration order. -/
def findTerminalPositiveAnchorNucleus
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system) :
    Option (TerminalMinimalPositiveAnchorNucleus problem) :=
  match minimumPositiveAnchorOutcome problem problem.allAnchorSubfamilies with
  | .none _allZero => none
  | .found result =>
      some
        { anchors := result.family
          governed := result.member
          positive := result.positive
          minimumCardinality := result.minimumCardinality }

/-- Search success exposes governance, positivity, and global
    minimum-cardinality evidence. -/
theorem findTerminalPositiveAnchorNucleus_sound
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (found : TerminalMinimalPositiveAnchorNucleus problem)
    (_foundAt : findTerminalPositiveAnchorNucleus problem = some found) :
    found.anchors ∈ problem.allAnchorSubfamilies ∧
      0 < problem.familyDefect found.anchors ∧
      ∀ smaller, smaller ∈ problem.allAnchorSubfamilies ->
        smaller.length < found.anchors.length ->
          problem.familyDefect smaller = 0 :=
  ⟨found.governed, found.positive, found.minimumCardinality⟩

/-- Search failure is exactly zero defect for every computed anchor subfamily. -/
theorem findTerminalPositiveAnchorNucleus_eq_none_iff
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system) :
    findTerminalPositiveAnchorNucleus problem = none ↔
      ∀ family, family ∈ problem.allAnchorSubfamilies ->
        problem.familyDefect family = 0 := by
  unfold findTerminalPositiveAnchorNucleus
  cases outcome : minimumPositiveAnchorOutcome problem
      problem.allAnchorSubfamilies with
  | none allZero =>
      constructor
      · intro _ family member
        exact allZero family member
      · intro _
        rfl
  | found result =>
      constructor
      · intro impossible
        cases impossible
      · intro allZero
        have zero := allZero result.family result.member
        have positive := result.positive
        rw [zero] at positive
        exact False.elim (Nat.not_lt_zero 0 positive)

/-- A positive defect on the complete saturated anchor support forces the
    exhaustive search to return a proof-bearing minimum nucleus. -/
theorem findTerminalPositiveAnchorNucleus_exists_of_whole_positive
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (wholePositive : 0 < problem.familyDefect problem.anchorRecords) :
    ∃ found, findTerminalPositiveAnchorNucleus problem = some found := by
  cases foundAt : findTerminalPositiveAnchorNucleus problem with
  | some found => exact ⟨found, rfl⟩
  | none =>
      have allZero :=
        (findTerminalPositiveAnchorNucleus_eq_none_iff problem).1 foundAt
      have zero := allZero problem.anchorRecords
        problem.anchorRecords_mem_allAnchorSubfamilies
      rw [zero] at wholePositive
      exact False.elim (Nat.not_lt_zero 0 wholePositive)

/-- The deterministic nucleus search has at most one returned proof object. -/
theorem findTerminalPositiveAnchorNucleus_unique
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    {left right : TerminalMinimalPositiveAnchorNucleus problem}
    (leftAt : findTerminalPositiveAnchorNucleus problem = some left)
    (rightAt : findTerminalPositiveAnchorNucleus problem = some right) :
    left = right :=
  Option.some.inj (leftAt.symm.trans rightAt)

/-! ## Exact Boolean anchor algebra or first mismatch -/

/-- Canonical intersection of two subfamilies, retaining nucleus order. -/
def terminalBCELAnchorIntersection
    {inputs gates outputs profileWidth : Nat}
    (nucleus left right : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    List (TerminalPrimitiveRecord inputs gates outputs profileWidth) :=
  nucleus.filter (fun record => decide (record ∈ left ∧ record ∈ right))

/-- Canonical union of two subfamilies, retaining nucleus order. -/
def terminalBCELAnchorUnion
    {inputs gates outputs profileWidth : Nat}
    (nucleus left right : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    List (TerminalPrimitiveRecord inputs gates outputs profileWidth) :=
  nucleus.filter (fun record => decide (record ∈ left ∨ record ∈ right))

/-- The two exact lattice laws checked for each anchor-subfamily pair. -/
inductive TerminalBCELAnchorAlgebraLaw where
  | meet
  | join
  deriving Repr, DecidableEq

/-- One concrete Boolean anchor-algebra query. -/
structure TerminalBCELAnchorAlgebraCheck
    (inputs gates outputs profileWidth : Nat) where
  left : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)
  right : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)
  record : TerminalPrimitiveRecord inputs gates outputs profileWidth
  law : TerminalBCELAnchorAlgebraLaw

/-- Exact proposition represented by one concrete anchor-algebra query. -/
def TerminalBCELAnchorAlgebraCheck.Holds
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (_problem : TerminalBCELAnchorProblem candidate system)
    (nucleus : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (check : TerminalBCELAnchorAlgebraCheck
      inputs gates outputs profileWidth) : Prop :=
  match check.law with
  | .meet =>
      check.record ∈ terminalSaturateRecords system
          (terminalBCELAnchorIntersection nucleus check.left check.right) ↔
        check.record ∈ terminalSaturateRecords system check.left ∧
          check.record ∈ terminalSaturateRecords system check.right
  | .join =>
      check.record ∈ terminalSaturateRecords system
          (terminalBCELAnchorUnion nucleus check.left check.right) ↔
        check.record ∈ terminalSaturateRecords system check.left ∨
          check.record ∈ terminalSaturateRecords system check.right

private def terminalBCELAnchorAlgebraHoldsDecidable
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (nucleus : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (check : TerminalBCELAnchorAlgebraCheck
      inputs gates outputs profileWidth) :
    Decidable (check.Holds problem nucleus) := by
  unfold TerminalBCELAnchorAlgebraCheck.Holds
  cases check.law <;> infer_instance

/-- Executable mismatch predicate for one exact algebra query. -/
def TerminalBCELAnchorAlgebraCheck.disagrees
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (nucleus : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (check : TerminalBCELAnchorAlgebraCheck
      inputs gates outputs profileWidth) : Bool := by
  letI := terminalBCELAnchorAlgebraHoldsDecidable problem nucleus check
  exact decide (¬check.Holds problem nucleus)

/-- The executable mismatch predicate has exactly the intended meaning. -/
theorem TerminalBCELAnchorAlgebraCheck.disagrees_eq_true_iff
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (nucleus : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (check : TerminalBCELAnchorAlgebraCheck
      inputs gates outputs profileWidth) :
    check.disagrees problem nucleus = true ↔
      ¬check.Holds problem nucleus := by
  unfold TerminalBCELAnchorAlgebraCheck.disagrees
  letI := terminalBCELAnchorAlgebraHoldsDecidable problem nucleus check
  constructor
  · exact fun checked => of_decide_eq_true checked
  · exact fun mismatch => decide_eq_true mismatch

/-- Every pair, primitive record, and meet-before-join law query in one
    deterministic finite list. -/
def allTerminalBCELAnchorAlgebraChecks
    {inputs gates outputs profileWidth : Nat}
    (nucleus : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    List (TerminalBCELAnchorAlgebraCheck
      inputs gates outputs profileWidth) :=
  (terminalListSubsets nucleus).flatMap fun left =>
    (terminalListSubsets nucleus).flatMap fun right =>
      (allTerminalPrimitiveRecords inputs gates outputs profileWidth).flatMap
        fun record =>
          [{ left := left, right := right, record := record, law := .meet },
           { left := left, right := right, record := record, law := .join }]

/-- A named query with governed subfamilies occurs in the complete algebra
    scan at its deterministic law position. -/
theorem terminalBCELAnchorAlgebraCheck_mem
    {inputs gates outputs profileWidth : Nat}
    (nucleus left right : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (leftMember : left ∈ terminalListSubsets nucleus)
    (rightMember : right ∈ terminalListSubsets nucleus)
    (record : TerminalPrimitiveRecord inputs gates outputs profileWidth)
    (law : TerminalBCELAnchorAlgebraLaw) :
    ({ left := left, right := right, record := record, law := law } :
        TerminalBCELAnchorAlgebraCheck inputs gates outputs profileWidth) ∈
      allTerminalBCELAnchorAlgebraChecks nucleus := by
  apply List.mem_flatMap.mpr
  refine ⟨left, leftMember, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨right, rightMember, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨record, mem_allTerminalPrimitiveRecords record, ?_⟩
  cases law with
  | meet => exact List.Mem.head _
  | join => exact List.Mem.tail _ (List.Mem.head _)

/-- Every query in the complete scan names two governed subfamilies. -/
theorem mem_allTerminalBCELAnchorAlgebraChecks_governed
    {inputs gates outputs profileWidth : Nat}
    (nucleus : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (check : TerminalBCELAnchorAlgebraCheck
      inputs gates outputs profileWidth)
    (member : check ∈ allTerminalBCELAnchorAlgebraChecks nucleus) :
    check.left ∈ terminalListSubsets nucleus ∧
      check.right ∈ terminalListSubsets nucleus := by
  obtain ⟨left, leftMember, remaining⟩ := List.mem_flatMap.mp member
  obtain ⟨right, rightMember, remaining⟩ := List.mem_flatMap.mp remaining
  obtain ⟨record, _recordMember, lawMember⟩ :=
    List.mem_flatMap.mp remaining
  cases List.mem_cons.mp lawMember with
  | inl equal => cases equal; exact ⟨leftMember, rightMember⟩
  | inr tailMember =>
      cases List.mem_cons.mp tailMember with
      | inl equal => cases equal; exact ⟨leftMember, rightMember⟩
      | inr impossible => cases impossible

/-- Exact Boolean algebra of computed saturations over all nucleus
    subfamilies. -/
structure TerminalBCELAnchorAlgebra
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (nucleus : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) : Prop where
  meet : ∀ left, left ∈ terminalListSubsets nucleus ->
    ∀ right, right ∈ terminalListSubsets nucleus ->
    ∀ record,
      ({ left := left, right := right, record := record, law := .meet } :
        TerminalBCELAnchorAlgebraCheck inputs gates outputs profileWidth).Holds
          problem nucleus
  join : ∀ left, left ∈ terminalListSubsets nucleus ->
    ∀ right, right ∈ terminalListSubsets nucleus ->
    ∀ record,
      ({ left := left, right := right, record := record, law := .join } :
        TerminalBCELAnchorAlgebraCheck inputs gates outputs profileWidth).Holds
          problem nucleus

/-- Deterministic first Boolean anchor-algebra mismatch. -/
def firstTerminalBCELAnchorAlgebraMismatch?
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (nucleus : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    Option (TerminalBCELAnchorAlgebraCheck
      inputs gates outputs profileWidth) :=
  (allTerminalBCELAnchorAlgebraChecks nucleus).find?
    (fun check => check.disagrees problem nucleus)

/-- Every returned algebra mismatch is governed and propositionally exact. -/
theorem firstTerminalBCELAnchorAlgebraMismatch?_sound
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (nucleus : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (check : TerminalBCELAnchorAlgebraCheck
      inputs gates outputs profileWidth)
    (found : firstTerminalBCELAnchorAlgebraMismatch? problem nucleus =
      some check) :
    check.left ∈ terminalListSubsets nucleus ∧
      check.right ∈ terminalListSubsets nucleus ∧
        ¬check.Holds problem nucleus := by
  have member : check ∈ allTerminalBCELAnchorAlgebraChecks nucleus :=
    List.mem_of_find?_eq_some found
  have mismatchCheck : check.disagrees problem nucleus = true :=
    List.find?_some found
  have governed :=
    mem_allTerminalBCELAnchorAlgebraChecks_governed nucleus check member
  exact ⟨governed.1, governed.2,
    (check.disagrees_eq_true_iff problem nucleus).1 mismatchCheck⟩

/-- No mismatch is equivalent to the complete exact Boolean anchor algebra. -/
theorem firstTerminalBCELAnchorAlgebraMismatch?_eq_none_iff
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (nucleus : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    firstTerminalBCELAnchorAlgebraMismatch? problem nucleus = none ↔
      TerminalBCELAnchorAlgebra problem nucleus := by
  constructor
  · intro noneFound
    have everyCheckHolds : ∀ check,
        check ∈ allTerminalBCELAnchorAlgebraChecks nucleus ->
          check.Holds problem nucleus := by
      intro check member
      letI := terminalBCELAnchorAlgebraHoldsDecidable problem nucleus check
      by_cases holds : check.Holds problem nucleus
      · exact holds
      · have mismatchCheck : check.disagrees problem nucleus = true :=
          (check.disagrees_eq_true_iff problem nucleus).2 holds
        have someCheck :
            (firstTerminalBCELAnchorAlgebraMismatch?
              problem nucleus).isSome = true :=
          (List.find?_isSome).mpr ⟨check, member, mismatchCheck⟩
        rw [noneFound] at someCheck
        exact Bool.noConfusion someCheck
    exact
      { meet := by
          intro left leftMember right rightMember record
          exact everyCheckHolds _
            (terminalBCELAnchorAlgebraCheck_mem nucleus left right
              leftMember rightMember record .meet)
        join := by
          intro left leftMember right rightMember record
          exact everyCheckHolds _
            (terminalBCELAnchorAlgebraCheck_mem nucleus left right
              leftMember rightMember record .join) }
  · intro algebra
    cases found : firstTerminalBCELAnchorAlgebraMismatch? problem nucleus with
    | none => rfl
    | some check =>
        have sound := firstTerminalBCELAnchorAlgebraMismatch?_sound
          problem nucleus check found
        rcases check with ⟨left, right, record, law⟩
        cases law with
        | meet =>
            exfalso
            exact sound.2.2 (algebra.meet left sound.1
              right sound.2.1 record)
        | join =>
            exfalso
            exact sound.2.2 (algebra.join left sound.1
              right sound.2.1 record)

/-- Proof-bearing exact first algebra failure. -/
structure TerminalBCELAnchorAlgebraFailure
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (nucleus : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) where
  check : TerminalBCELAnchorAlgebraCheck inputs gates outputs profileWidth
  first : firstTerminalBCELAnchorAlgebraMismatch? problem nucleus = some check
  governedLeft : check.left ∈ terminalListSubsets nucleus
  governedRight : check.right ∈ terminalListSubsets nucleus
  mismatch : ¬check.Holds problem nucleus

/-- Total executable algebra classifier. -/
inductive TerminalBCELAnchorAlgebraClassification
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (nucleus : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) where
  | algebra (proof : TerminalBCELAnchorAlgebra problem nucleus)
  | failure (reason : TerminalBCELAnchorAlgebraFailure problem nucleus)

/-- Execute the exact Boolean-algebra-or-first-mismatch dichotomy. -/
def classifyTerminalBCELAnchorAlgebra
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (nucleus : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    TerminalBCELAnchorAlgebraClassification problem nucleus :=
  match found : firstTerminalBCELAnchorAlgebraMismatch? problem nucleus with
  | none => .algebra
      ((firstTerminalBCELAnchorAlgebraMismatch?_eq_none_iff
        problem nucleus).1 found)
  | some check =>
      let sound := firstTerminalBCELAnchorAlgebraMismatch?_sound
        problem nucleus check found
      .failure
        { check := check
          first := found
          governedLeft := sound.1
          governedRight := sound.2.1
          mismatch := sound.2.2 }

/-! ## Proper cuts and exact defect checks -/

/-- Exact finite predicate for an oriented nonempty proper nucleus cut. -/
def TerminalBCELProperCutSeed
    {inputs gates outputs profileWidth : Nat}
    (nucleus left : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) : Prop :=
  left ∈ terminalListSubsets nucleus ∧ left ≠ [] ∧
    left.length < nucleus.length

private def terminalBCELProperCutSeedDecidable
    {inputs gates outputs profileWidth : Nat}
    (nucleus left : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    Decidable (TerminalBCELProperCutSeed nucleus left) := by
  unfold TerminalBCELProperCutSeed
  infer_instance

/-- Executable proper-cut predicate. -/
def terminalBCELProperCutSeedBool
    {inputs gates outputs profileWidth : Nat}
    (nucleus left : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) : Bool :=
  @decide (TerminalBCELProperCutSeed nucleus left)
    (terminalBCELProperCutSeedDecidable nucleus left)

/-- The executable proper-cut predicate has exactly the intended meaning. -/
theorem terminalBCELProperCutSeedBool_eq_true_iff
    {inputs gates outputs profileWidth : Nat}
    (nucleus left : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    terminalBCELProperCutSeedBool nucleus left = true ↔
      TerminalBCELProperCutSeed nucleus left := by
  letI := terminalBCELProperCutSeedDecidable nucleus left
  unfold terminalBCELProperCutSeedBool
  constructor
  · exact fun checked => of_decide_eq_true checked
  · exact fun proper => decide_eq_true proper

/-- Every oriented nonempty proper cut in canonical subset order. -/
def allTerminalBCELProperCutSeeds
    {inputs gates outputs profileWidth : Nat}
    (nucleus : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    List (List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :=
  (terminalListSubsets nucleus).filter
    (terminalBCELProperCutSeedBool nucleus)

/-- Exact membership in the complete proper-cut enumeration. -/
theorem mem_allTerminalBCELProperCutSeeds_iff
    {inputs gates outputs profileWidth : Nat}
    (nucleus left : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    left ∈ allTerminalBCELProperCutSeeds nucleus ↔
      TerminalBCELProperCutSeed nucleus left := by
  unfold allTerminalBCELProperCutSeeds
  constructor
  · intro member
    exact (terminalBCELProperCutSeedBool_eq_true_iff nucleus left).1
      (List.mem_filter.mp member).2
  · intro proper
    exact List.mem_filter.mpr
      ⟨proper.1,
        (terminalBCELProperCutSeedBool_eq_true_iff nucleus left).2 proper⟩

/-- Canonical complementary side of an oriented anchor cut. -/
def terminalBCELAnchorComplement
    {inputs gates outputs profileWidth : Nat}
    (nucleus left : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    List (TerminalPrimitiveRecord inputs gates outputs profileWidth) :=
  nucleus.filter (fun record => decide (record ∉ left))

/-- The computed carrier of one oriented proper cut. -/
def TerminalBCELAnchorProblem.cutCarrier
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (nucleus left : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    TerminalFourCornerCarrier system :=
  problem.carrier left (terminalBCELAnchorComplement nucleus left)

/-- Projection defect at one exact corner of a computed cut carrier. -/
def TerminalBCELAnchorProblem.cutDefect
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (nucleus left : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (corner : TerminalSupportSquareCorner) : Nat :=
  let corners := (problem.cutCarrier nucleus left).optimizationCorners
    problem.observe
  terminalProjectionDefect corners.system corners.projection (corners.at corner)

/-- The four constant-cut defect identities, checked in this exact order. -/
inductive TerminalBCELCutDefectKind where
  | meetZero
  | leftZero
  | rightZero
  | joinNucleus
  deriving Repr, DecidableEq

/-- One exact corner-defect query for one oriented cut. -/
structure TerminalBCELCutDefectCheck
    (inputs gates outputs profileWidth : Nat) where
  cut : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)
  kind : TerminalBCELCutDefectKind

/-- Exact proposition represented by one corner-defect query. -/
def TerminalBCELCutDefectCheck.Holds
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (nucleus : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (defect : Nat)
    (check : TerminalBCELCutDefectCheck
      inputs gates outputs profileWidth) : Prop :=
  match check.kind with
  | .meetZero => problem.cutDefect nucleus check.cut .meet = 0
  | .leftZero => problem.cutDefect nucleus check.cut .left = 0
  | .rightZero => problem.cutDefect nucleus check.cut .right = 0
  | .joinNucleus => problem.cutDefect nucleus check.cut .join = defect

private def terminalBCELCutDefectHoldsDecidable
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (nucleus : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (defect : Nat)
    (check : TerminalBCELCutDefectCheck
      inputs gates outputs profileWidth) :
    Decidable (check.Holds problem nucleus defect) := by
  unfold TerminalBCELCutDefectCheck.Holds
  cases check.kind <;> infer_instance

/-- Executable mismatch predicate for one corner-defect query. -/
def TerminalBCELCutDefectCheck.disagrees
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (nucleus : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (defect : Nat)
    (check : TerminalBCELCutDefectCheck
      inputs gates outputs profileWidth) : Bool := by
  letI := terminalBCELCutDefectHoldsDecidable problem nucleus defect check
  exact decide (¬check.Holds problem nucleus defect)

/-- The executable corner mismatch predicate is exact. -/
theorem TerminalBCELCutDefectCheck.disagrees_eq_true_iff
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (nucleus : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (defect : Nat)
    (check : TerminalBCELCutDefectCheck
      inputs gates outputs profileWidth) :
    check.disagrees problem nucleus defect = true ↔
      ¬check.Holds problem nucleus defect := by
  unfold TerminalBCELCutDefectCheck.disagrees
  letI := terminalBCELCutDefectHoldsDecidable problem nucleus defect check
  constructor
  · exact fun checked => of_decide_eq_true checked
  · exact fun mismatch => decide_eq_true mismatch

/-- All proper-cut corner queries in meet-left-right-join order. -/
def allTerminalBCELCutDefectChecks
    {inputs gates outputs profileWidth : Nat}
    (nucleus : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    List (TerminalBCELCutDefectCheck inputs gates outputs profileWidth) :=
  (allTerminalBCELProperCutSeeds nucleus).flatMap fun cut =>
    [{ cut := cut, kind := .meetZero },
     { cut := cut, kind := .leftZero },
     { cut := cut, kind := .rightZero },
     { cut := cut, kind := .joinNucleus }]

/-- Each named query on a proper cut occurs in the complete defect scan. -/
theorem terminalBCELCutDefectCheck_mem
    {inputs gates outputs profileWidth : Nat}
    (nucleus cut : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (proper : TerminalBCELProperCutSeed nucleus cut)
    (kind : TerminalBCELCutDefectKind) :
    ({ cut := cut, kind := kind } :
        TerminalBCELCutDefectCheck inputs gates outputs profileWidth) ∈
      allTerminalBCELCutDefectChecks nucleus := by
  apply List.mem_flatMap.mpr
  refine ⟨cut, (mem_allTerminalBCELProperCutSeeds_iff nucleus cut).2 proper, ?_⟩
  cases kind with
  | meetZero => exact List.Mem.head _
  | leftZero => exact List.Mem.tail _ (List.Mem.head _)
  | rightZero =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  | joinNucleus =>
      exact List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

/-- Every query in the complete defect scan names a genuine proper cut. -/
theorem mem_allTerminalBCELCutDefectChecks_proper
    {inputs gates outputs profileWidth : Nat}
    (nucleus : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (check : TerminalBCELCutDefectCheck inputs gates outputs profileWidth)
    (member : check ∈ allTerminalBCELCutDefectChecks nucleus) :
    TerminalBCELProperCutSeed nucleus check.cut := by
  obtain ⟨cut, cutMember, localMember⟩ := List.mem_flatMap.mp member
  have proper := (mem_allTerminalBCELProperCutSeeds_iff nucleus cut).1 cutMember
  rcases check with ⟨checkedCut, kind⟩
  cases List.mem_cons.mp localMember with
  | inl equal => cases equal; exact proper
  | inr remainingOne =>
      cases List.mem_cons.mp remainingOne with
      | inl equal => cases equal; exact proper
      | inr remainingTwo =>
          cases List.mem_cons.mp remainingTwo with
          | inl equal => cases equal; exact proper
          | inr remainingThree =>
              cases List.mem_cons.mp remainingThree with
              | inl equal => cases equal; exact proper
              | inr impossible => cases impossible

/-- Deterministic first proper-cut corner-defect mismatch. -/
def firstTerminalBCELCutDefectMismatch?
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (nucleus : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (defect : Nat) :
    Option (TerminalBCELCutDefectCheck
      inputs gates outputs profileWidth) :=
  (allTerminalBCELCutDefectChecks nucleus).find?
    (fun check => check.disagrees problem nucleus defect)

/-- Every returned corner-defect mismatch is a proof-bearing exact failure on
    a governed proper cut. -/
theorem firstTerminalBCELCutDefectMismatch?_sound
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (nucleus : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (defect : Nat)
    (check : TerminalBCELCutDefectCheck
      inputs gates outputs profileWidth)
    (found : firstTerminalBCELCutDefectMismatch?
      problem nucleus defect = some check) :
    TerminalBCELProperCutSeed nucleus check.cut ∧
      ¬check.Holds problem nucleus defect := by
  have member : check ∈ allTerminalBCELCutDefectChecks nucleus :=
    List.mem_of_find?_eq_some found
  have mismatchCheck : check.disagrees problem nucleus defect = true :=
    List.find?_some found
  exact ⟨mem_allTerminalBCELCutDefectChecks_proper nucleus check member,
    (check.disagrees_eq_true_iff problem nucleus defect).1 mismatchCheck⟩

/-- Absence of a corner mismatch exposes all four exact defect identities for
    every proper cut. -/
theorem firstTerminalBCELCutDefectMismatch?_eq_none_all
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (nucleus : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (defect : Nat)
    (noneFound : firstTerminalBCELCutDefectMismatch?
      problem nucleus defect = none)
    (cut : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (proper : TerminalBCELProperCutSeed nucleus cut) :
    problem.cutDefect nucleus cut .meet = 0 ∧
      problem.cutDefect nucleus cut .left = 0 ∧
      problem.cutDefect nucleus cut .right = 0 ∧
      problem.cutDefect nucleus cut .join = defect := by
  have everyCheckHolds : ∀ check,
      check ∈ allTerminalBCELCutDefectChecks nucleus ->
        check.Holds problem nucleus defect := by
    intro check member
    letI := terminalBCELCutDefectHoldsDecidable problem nucleus defect check
    by_cases holds : check.Holds problem nucleus defect
    · exact holds
    · have mismatchCheck : check.disagrees problem nucleus defect = true :=
        (check.disagrees_eq_true_iff problem nucleus defect).2 holds
      have someCheck :
          (firstTerminalBCELCutDefectMismatch?
            problem nucleus defect).isSome = true :=
        (List.find?_isSome).mpr ⟨check, member, mismatchCheck⟩
      rw [noneFound] at someCheck
      exact Bool.noConfusion someCheck
  exact ⟨
    everyCheckHolds _
      (terminalBCELCutDefectCheck_mem nucleus cut proper .meetZero),
    everyCheckHolds _
      (terminalBCELCutDefectCheck_mem nucleus cut proper .leftZero),
    everyCheckHolds _
      (terminalBCELCutDefectCheck_mem nucleus cut proper .rightZero),
    everyCheckHolds _
      (terminalBCELCutDefectCheck_mem nucleus cut proper .joinNucleus)⟩

/-- Proof-bearing exact first proper-cut defect failure. -/
structure TerminalBCELCutDefectFailure
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (nucleus : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (defect : Nat) where
  check : TerminalBCELCutDefectCheck inputs gates outputs profileWidth
  first : firstTerminalBCELCutDefectMismatch? problem nucleus defect = some check
  proper : TerminalBCELProperCutSeed nucleus check.cut
  mismatch : ¬check.Holds problem nucleus defect

/-! ## Deterministic cut-route scan -/

/-- One selected local route coordinate, tied to an oriented cut and
    comparison mode.  Its exact query proof is reconstructed by the soundness
    theorem for the outer deterministic scan. -/
structure TerminalBCELCutRoute
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (nucleus : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) where
  cut : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)
  mode : TerminalOptimumCoherenceMode
  failure : TerminalFourCornerOptimumFailure
    (inputs + gates) gates profileWidth

/-- Exact local query selected by one cut-route coordinate. -/
def TerminalBCELCutRoute.Selected
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {problem : TerminalBCELAnchorProblem candidate system}
    {nucleus : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)}
    (route : TerminalBCELCutRoute problem nucleus) : Prop :=
  (problem.cutCarrier nucleus route.cut).firstOptimumRoute?
    problem.observe (.coherence route.mode) = some route.failure

private def firstTerminalBCELCutRouteIn?
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (nucleus : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    List (List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) ->
      Option (TerminalBCELCutRoute problem nucleus)
  | [] => none
  | cut :: tail =>
      let carrier := problem.cutCarrier nucleus cut
      match carrier.firstOptimumRoute?
          problem.observe (.coherence .full) with
      | some failure =>
          some
            { cut := cut
              mode := .full
              failure := failure }
      | none =>
          match carrier.firstOptimumRoute?
              problem.observe (.coherence .quotient) with
          | some failure =>
              some
                { cut := cut
                  mode := .quotient
                  failure := failure }
          | none => firstTerminalBCELCutRouteIn? problem nucleus tail

/-- Deterministic proper-cut, then full-before-quotient, first local route. -/
def firstTerminalBCELCutRoute?
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (nucleus : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    Option (TerminalBCELCutRoute problem nucleus) :=
  firstTerminalBCELCutRouteIn? problem nucleus
    (allTerminalBCELProperCutSeeds nucleus)

private theorem firstTerminalBCELCutRouteIn?_sound
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (nucleus : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (cuts : List (List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)))
    (route : TerminalBCELCutRoute problem nucleus)
    (found : firstTerminalBCELCutRouteIn? problem nucleus cuts = some route) :
    route.cut ∈ cuts ∧ route.Selected := by
  induction cuts with
  | nil => cases found
  | cons cut tail ih =>
      simp only [firstTerminalBCELCutRouteIn?] at found
      cases fullFound : (problem.cutCarrier nucleus cut).firstOptimumRoute?
          problem.observe (.coherence .full) with
      | some failure =>
          simp only [fullFound] at found
          cases found
          exact ⟨List.Mem.head tail, fullFound⟩
      | none =>
          simp only [fullFound] at found
          cases quotientFound :
              (problem.cutCarrier nucleus cut).firstOptimumRoute?
              problem.observe (.coherence .quotient) with
          | some failure =>
              simp only [quotientFound] at found
              cases found
              exact ⟨List.Mem.head tail, quotientFound⟩
          | none =>
              simp only [quotientFound] at found
              have tailSound := ih found
              exact ⟨List.Mem.tail cut tailSound.1, tailSound.2⟩

/-- Every selected cut route belongs to the governed proper-cut list and its
    embedded failure is sound. -/
theorem firstTerminalBCELCutRoute?_sound
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (nucleus : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (route : TerminalBCELCutRoute problem nucleus)
    (found : firstTerminalBCELCutRoute? problem nucleus = some route) :
    TerminalBCELProperCutSeed nucleus route.cut ∧
      route.Selected ∧ route.failure.Sound := by
  have selected := firstTerminalBCELCutRouteIn?_sound
    problem nucleus (allTerminalBCELProperCutSeeds nucleus) route found
  have sound : route.failure.Sound :=
    (problem.cutCarrier nucleus route.cut).firstOptimumRoute?_sound
      problem.observe (.coherence route.mode) route.failure selected.2
  exact ⟨
    (mem_allTerminalBCELProperCutSeeds_iff nucleus route.cut).1 selected.1,
    selected.2, sound⟩

private theorem firstTerminalBCELCutRouteIn?_eq_none_noRoutes
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (nucleus : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (cuts : List (List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)))
    (noneFound : firstTerminalBCELCutRouteIn?
      problem nucleus cuts = none)
    (cut : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (member : cut ∈ cuts) :
    (problem.cutCarrier nucleus cut).NoOptimumCoherenceRoutes
      problem.observe := by
  induction cuts with
  | nil => cases member
  | cons head tail ih =>
      simp only [firstTerminalBCELCutRouteIn?] at noneFound
      cases fullFound : (problem.cutCarrier nucleus head).firstOptimumRoute?
          problem.observe (.coherence .full) with
      | some failure =>
          simp only [fullFound] at noneFound
          cases noneFound
      | none =>
          simp only [fullFound] at noneFound
          cases quotientFound :
              (problem.cutCarrier nucleus head).firstOptimumRoute?
              problem.observe (.coherence .quotient) with
          | some failure =>
              simp only [quotientFound] at noneFound
              cases noneFound
          | none =>
              simp only [quotientFound] at noneFound
              cases List.mem_cons.mp member with
              | inl equal =>
                  subst cut
                  exact ⟨fullFound, quotientFound⟩
              | inr tailMember =>
                  exact ih noneFound tailMember

/-- Absence of any selected route supplies exact local route silence for every
    governed proper cut. -/
theorem firstTerminalBCELCutRoute?_eq_none_noRoutes
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (nucleus : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (noneFound : firstTerminalBCELCutRoute? problem nucleus = none)
    (cut : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (proper : TerminalBCELProperCutSeed nucleus cut) :
    (problem.cutCarrier nucleus cut).NoOptimumCoherenceRoutes
      problem.observe :=
  firstTerminalBCELCutRouteIn?_eq_none_noRoutes problem nucleus
    (allTerminalBCELProperCutSeeds nucleus) noneFound cut
    ((mem_allTerminalBCELProperCutSeeds_iff nucleus cut).2 proper)

/-- Exact selected first local cut route, including the top-level cut order. -/
structure TerminalBCELCutRouteFailure
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (nucleus : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) where
  selected : TerminalBCELCutRoute problem nucleus
  first : firstTerminalBCELCutRoute? problem nucleus = some selected
  proper : TerminalBCELProperCutSeed nucleus selected.cut
  selectedQuery : selected.Selected
  sound : selected.failure.Sound

/-! ## Successful proper-cut conclusion -/

/-- Complete constant-cut and local BN2 conclusion for one oriented proper
    cut of a computed positive nucleus. -/
structure TerminalComputedBCELCutConclusion
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (nucleus : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (defect : Nat)
    (cut : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) : Prop where
  proper : TerminalBCELProperCutSeed nucleus cut
  legitimate : TerminalComputedBN2SquareLegitimate
    (problem.cutCarrier nucleus cut)
  meetDefect : problem.cutDefect nucleus cut .meet = 0
  leftDefect : problem.cutDefect nucleus cut .left = 0
  rightDefect : problem.cutDefect nucleus cut .right = 0
  joinDefect : problem.cutDefect nucleus cut .join = defect
  constantCutEquation :
    ((problem.cutCarrier nucleus cut).optimizationCorners
      problem.observe).projectionExcess = Int.ofNat defect
  positiveExcess : 0 <
    ((problem.cutCarrier nucleus cut).optimizationCorners
      problem.observe).projectionExcess
  localConclusion : TerminalComputedBN2LocalConclusion
    (problem.cutCarrier nucleus cut) problem.observe

/-- Assemble the exact constant-cut equation and local BN2 result from the two
    exhaustive no-failure scans. -/
theorem computedBCELCutConclusionOfNoFailures
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (nucleus : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (defect : Nat)
    (positive : 0 < defect)
    (defectNone : firstTerminalBCELCutDefectMismatch?
      problem nucleus defect = none)
    (routeNone : firstTerminalBCELCutRoute? problem nucleus = none)
    (cut : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (proper : TerminalBCELProperCutSeed nucleus cut) :
    TerminalComputedBCELCutConclusion problem nucleus defect cut := by
  let carrier := problem.cutCarrier nucleus cut
  have defects := firstTerminalBCELCutDefectMismatch?_eq_none_all
    problem nucleus defect defectNone cut proper
  have noRoutes := firstTerminalBCELCutRoute?_eq_none_noRoutes
    problem nucleus routeNone cut proper
  have meetZero : terminalProjectionDefect
      (carrier.optimizationCorners problem.observe).system
      (carrier.optimizationCorners problem.observe).projection
      (carrier.optimizationCorners problem.observe).meet = 0 := by
    exact defects.1
  have leftZero : terminalProjectionDefect
      (carrier.optimizationCorners problem.observe).system
      (carrier.optimizationCorners problem.observe).projection
      (carrier.optimizationCorners problem.observe).left = 0 := by
    exact defects.2.1
  have rightZero : terminalProjectionDefect
      (carrier.optimizationCorners problem.observe).system
      (carrier.optimizationCorners problem.observe).projection
      (carrier.optimizationCorners problem.observe).right = 0 := by
    exact defects.2.2.1
  have joinDefect : terminalProjectionDefect
      (carrier.optimizationCorners problem.observe).system
      (carrier.optimizationCorners problem.observe).projection
      (carrier.optimizationCorners problem.observe).join = defect := by
    exact defects.2.2.2
  exact
    { proper := proper
      legitimate := carrier.computedBN2SquareLegitimate
      meetDefect := defects.1
      leftDefect := defects.2.1
      rightDefect := defects.2.2.1
      joinDefect := defects.2.2.2
      constantCutEquation :=
        (carrier.optimizationCorners problem.observe).constantCutEquation_of_defects
          defect meetZero leftZero rightZero joinDefect
      positiveExcess :=
        (carrier.optimizationCorners problem.observe).projectionExcess_pos_of_constantCut
          defect positive meetZero leftZero rightZero joinDefect
      localConclusion := carrier.computedBN2LocalConclusion
        problem.observe noRoutes }

/-! ## Total BCEL anchor-nucleus outcome -/

/-- Successful computed finite BCEL anchor nucleus.  The global scans are
    retained alongside the pointwise cut conclusions, so no caller can replace
    the executable algebra, defect, or route queries with a certificate. -/
structure TerminalComputedBCELAnchorNucleus
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system) where
  nucleus : TerminalMinimalPositiveAnchorNucleus problem
  atLeastTwo : 2 <= nucleus.anchors.length
  algebra : TerminalBCELAnchorAlgebra problem nucleus.anchors
  defectChecksSilent : firstTerminalBCELCutDefectMismatch? problem
    nucleus.anchors (problem.familyDefect nucleus.anchors) = none
  routeChecksSilent : firstTerminalBCELCutRoute?
    problem nucleus.anchors = none
  properCuts : ∀ cut, TerminalBCELProperCutSeed nucleus.anchors cut ->
    TerminalComputedBCELCutConclusion problem nucleus.anchors
      (problem.familyDefect nucleus.anchors) cut

/-- A minimum positive nucleus too small to admit a nontrivial BCEL cut. -/
structure TerminalBCELInsufficientNucleusFailure
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system) where
  nucleus : TerminalMinimalPositiveAnchorNucleus problem
  first : findTerminalPositiveAnchorNucleus problem = some nucleus
  fewerThanTwo : nucleus.anchors.length < 2

/-- Total fail-closed classification of the finite computed anchor boundary. -/
inductive TerminalBCELAnchorNucleusOutcome
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system) where
  | insufficient
      (failure : TerminalBCELInsufficientNucleusFailure problem)
  | algebraFailure
      (nucleus : TerminalMinimalPositiveAnchorNucleus problem)
      (first : findTerminalPositiveAnchorNucleus problem = some nucleus)
      (failure : TerminalBCELAnchorAlgebraFailure problem nucleus.anchors)
  | cutDefectFailure
      (nucleus : TerminalMinimalPositiveAnchorNucleus problem)
      (first : findTerminalPositiveAnchorNucleus problem = some nucleus)
      (failure : TerminalBCELCutDefectFailure problem nucleus.anchors
        (problem.familyDefect nucleus.anchors))
  | cutRouteFailure
      (nucleus : TerminalMinimalPositiveAnchorNucleus problem)
      (first : findTerminalPositiveAnchorNucleus problem = some nucleus)
      (failure : TerminalBCELCutRouteFailure problem nucleus.anchors)
  | ready (result : TerminalComputedBCELAnchorNucleus problem)

/-- Compute the minimum positive nucleus and then fail closed in the exact
    order: insufficient size, Boolean algebra, cut defects, cut coherence
    (full before quotient), or the complete finite BCEL nucleus. -/
def classifyTerminalBCELAnchorNucleus
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (wholePositive : 0 < problem.familyDefect problem.anchorRecords) :
    TerminalBCELAnchorNucleusOutcome problem :=
  match foundAt : findTerminalPositiveAnchorNucleus problem with
  | none =>
      False.elim (by
        have allZero :=
          (findTerminalPositiveAnchorNucleus_eq_none_iff problem).1 foundAt
        have zero := allZero problem.anchorRecords
          problem.anchorRecords_mem_allAnchorSubfamilies
        rw [zero] at wholePositive
        exact Nat.not_lt_zero 0 wholePositive)
  | some nucleus =>
      if atLeastTwo : 2 <= nucleus.anchors.length then
        match classifyTerminalBCELAnchorAlgebra
            problem nucleus.anchors with
        | .failure failure => .algebraFailure nucleus foundAt failure
        | .algebra algebra =>
            match defectFound : firstTerminalBCELCutDefectMismatch? problem
                nucleus.anchors (problem.familyDefect nucleus.anchors) with
            | some check =>
                let sound := firstTerminalBCELCutDefectMismatch?_sound problem
                  nucleus.anchors (problem.familyDefect nucleus.anchors)
                  check defectFound
                .cutDefectFailure nucleus foundAt
                  { check := check
                    first := defectFound
                    proper := sound.1
                    mismatch := sound.2 }
            | none =>
                match routeFound : firstTerminalBCELCutRoute?
                    problem nucleus.anchors with
                | some selected =>
                    let sound := firstTerminalBCELCutRoute?_sound problem
                      nucleus.anchors selected routeFound
                    .cutRouteFailure nucleus foundAt
                      { selected := selected
                        first := routeFound
                        proper := sound.1
                        selectedQuery := sound.2.1
                        sound := sound.2.2 }
                | none =>
                    .ready
                      { nucleus := nucleus
                        atLeastTwo := atLeastTwo
                        algebra := algebra
                        defectChecksSilent := defectFound
                        routeChecksSilent := routeFound
                        properCuts := by
                          intro cut proper
                          exact computedBCELCutConclusionOfNoFailures problem
                            nucleus.anchors
                            (problem.familyDefect nucleus.anchors)
                            nucleus.positive defectFound routeFound cut proper }
      else
        .insufficient
          { nucleus := nucleus
            first := foundAt
            fewerThanTwo := Nat.lt_of_not_ge atLeastTwo }

/-- Every successful computed nucleus retains the minimum-cardinality
    projection-defect fact for all strict anchor subfamilies. -/
theorem TerminalComputedBCELAnchorNucleus.strictSubfamily_defect_zero
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {problem : TerminalBCELAnchorProblem candidate system}
    (result : TerminalComputedBCELAnchorNucleus problem)
    (smaller : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (governed : smaller ∈ problem.allAnchorSubfamilies)
    (strict : smaller.length < result.nucleus.anchors.length) :
    problem.familyDefect smaller = 0 :=
  result.nucleus.minimumCardinality smaller governed strict

/-- Every successful nucleus has at least two anchors. -/
theorem TerminalComputedBCELAnchorNucleus.anchorSizeAtLeastTwo
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {problem : TerminalBCELAnchorProblem candidate system}
    (result : TerminalComputedBCELAnchorNucleus problem) :
    2 <= result.nucleus.anchors.length :=
  result.atLeastTwo

/-- Every oriented nonempty proper cut has the exact constant-cut equation. -/
theorem TerminalComputedBCELAnchorNucleus.properCutConstantEquation
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {problem : TerminalBCELAnchorProblem candidate system}
    (result : TerminalComputedBCELAnchorNucleus problem)
    (cut : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (proper : TerminalBCELProperCutSeed result.nucleus.anchors cut) :
    ((problem.cutCarrier result.nucleus.anchors cut).optimizationCorners
      problem.observe).projectionExcess =
        Int.ofNat (problem.familyDefect result.nucleus.anchors) :=
  (result.properCuts cut proper).constantCutEquation

/-- Every oriented nonempty proper cut has the complete local full and
    quotient BN2 conclusion. -/
theorem TerminalComputedBCELAnchorNucleus.properCutLocalConclusion
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {problem : TerminalBCELAnchorProblem candidate system}
    (result : TerminalComputedBCELAnchorNucleus problem)
    (cut : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (proper : TerminalBCELProperCutSeed result.nucleus.anchors cut) :
    TerminalComputedBN2LocalConclusion
      (problem.cutCarrier result.nucleus.anchors cut) problem.observe :=
  (result.properCuts cut proper).localConclusion

/-- The complete classifier is inhabited for every finite positive
    whole-support anchor problem; no fifth unclassified case remains. -/
theorem classifyTerminalBCELAnchorNucleus_exhaustive
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (problem : TerminalBCELAnchorProblem candidate system)
    (wholePositive : 0 < problem.familyDefect problem.anchorRecords) :
    Nonempty (TerminalBCELAnchorNucleusOutcome problem) :=
  ⟨classifyTerminalBCELAnchorNucleus problem wholePositive⟩

end DirectWire
end PNP
