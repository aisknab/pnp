/-
Copyright (c) 2026 PNP Labs.

All-size ordered exclusion-pair coordinates, with exact canonical clause order.
Reversing the clause ordinal permits reuse of the existing increasing-row
selector. Invalid ordinals map to its exhausted boundary, never a clamped hit.

These are source-independent arithmetic and canonical-observation contracts.
Physical preparation of the reversed ordinal and field reads remain separate.
-/

import PNP.Concrete.CookLevinBuilderInitialLengthSelection
import PNP.Concrete.CookLevinFormulaCursor

namespace PNP.Concrete.CookLevin.BuilderExclusionPairSelection

open LocalConstraint (pairCount)
open BuilderInitialLengthSelection (rowSpan)

def successorPair (pair : Nat × Nat) : Nat × Nat := (pair.1 + 1, pair.2 + 1)

/-- The canonical descending-row order, without materializing any pair list. -/
def pairSlot : Nat → Nat → Option (Nat × Nat)
  | 0, _ => none
  | count + 1, coordinate =>
      if coordinate < count then some (0, coordinate + 1)
      else (pairSlot count (coordinate - count)).map successorPair

def ordinal (count first second : Nat) : Nat :=
  pairCount count - pairCount (count - first) + (second - first - 1)

private theorem pairCount_mono (first second : Nat) (h : first ≤ second) :
    pairCount first ≤ pairCount second := by
  induction second with
  | zero =>
      have hFirst : first = 0 := by omega
      subst first
      exact Nat.le_refl _
  | succ second ih =>
      by_cases hEqual : first = second + 1
      · subst first
        exact Nat.le_refl _
      · have hPrevious := ih (by omega)
        simp only [pairCount]
        omega

theorem rowSpan_succ_right (count width : Nat) :
    rowSpan (count + 1) width = rowSpan count width + width + count := by
  induction count generalizing width with
  | zero => simp only [rowSpan, Nat.add_zero, Nat.zero_add]
  | succ count ih =>
      calc
        rowSpan (count + 1 + 1) width = width + rowSpan (count + 1) (width + 1) := rfl
        _ = width + (rowSpan count (width + 1) + (width + 1) + count) := by rw [ih]
        _ = rowSpan (count + 1) width + width + (count + 1) := by rw [rowSpan]; omega

theorem rowSpan_pairCount (count : Nat) : rowSpan count 1 = pairCount (count + 1) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [rowSpan_succ_right, ih]
      change pairCount (count + 1) + 1 + count = (count + 1) + pairCount (count + 1)
      omega

theorem rowSpan_count (count : Nat) : rowSpan (count - 1) 1 = pairCount count := by
  cases count with
  | zero => rfl
  | succ count => simpa only [Nat.add_sub_cancel] using rowSpan_pairCount count

theorem pairSlot_ordinal (count first second : Nat)
    (hOrder : first < second) (hSecond : second < count) :
    pairSlot count (ordinal count first second) = some (first, second) := by
  induction count generalizing first second with
  | zero => omega
  | succ count ih =>
      cases first with
      | zero =>
          have hIndex : second - 1 < count := by omega
          have hSecondValue : second - 1 + 1 = second := by omega
          simp only [ordinal, Nat.sub_zero, Nat.sub_self, Nat.zero_add,
            pairSlot, if_pos hIndex, hSecondValue]
      | succ first =>
          cases second with
          | zero => omega
          | succ second =>
              have hCount := pairCount_mono (count - first) count (by omega)
              have hRank : ordinal (count + 1) (first + 1) (second + 1) =
                  count + ordinal count first second := by
                simp only [ordinal, pairCount, Nat.add_sub_add_right]
                omega
              have hTail := ih first second (by omega) (by omega)
              have hOutside : ¬ count + ordinal count first second < count := by omega
              simp only [hRank, pairSlot, if_neg hOutside, Nat.add_sub_cancel_left,
                hTail, Option.map_some, successorPair]

theorem pairSlot_none_iff (count coordinate : Nat) :
    pairSlot count coordinate = none ↔ pairCount count ≤ coordinate := by
  induction count generalizing coordinate with
  | zero => exact ⟨fun _ => Nat.zero_le _, fun _ => rfl⟩
  | succ count ih =>
      by_cases hLess : coordinate < count
      · simp only [pairSlot, if_pos hLess, pairCount]
        constructor
        · intro impossible
          cases impossible
        · intro hOutside
          omega
      · have hTail := ih (coordinate - count)
        cases hFound : pairSlot count (coordinate - count) with
        | none =>
            simp only [hFound] at hTail
            have hOutside := hTail.mp True.intro
            simp only [pairSlot, if_neg hLess, hFound, Option.map_none, pairCount]
            exact ⟨fun _ => by omega, fun _ => True.intro⟩
        | some found =>
            simp only [pairSlot, if_neg hLess, hFound, Option.map_some, pairCount]
            constructor
            · intro impossible
              cases impossible
            · intro hOutside
              have hNone := hTail.mpr (by omega)
              rw [hFound] at hNone
              cases hNone

/-- Invalid slots are sent to the first exhausted row coordinate. -/
def reverseCoordinate (count coordinate : Nat) : Nat :=
  if coordinate < pairCount count then pairCount count - 1 - coordinate else pairCount count

def rowSelection (count coordinate : Nat) : Option (Fin (count - 1) × Nat) :=
  BuilderInitialLengthSelection.locate (count - 1) 1 (reverseCoordinate count coordinate)

def reversePair (count : Nat) (found : Fin (count - 1) × Nat) : Nat × Nat :=
  (count - 2 - found.1.val, count - 1 - found.2)

def selectedPair (count coordinate : Nat) : Option (Nat × Nat) :=
  (rowSelection count coordinate).map (reversePair count)

theorem rowSelection_none_iff (count coordinate : Nat) :
    rowSelection count coordinate = none ↔ pairCount count ≤ coordinate := by
  rw [rowSelection, BuilderInitialLengthSelection.locate_none_iff, rowSpan_count]
  unfold reverseCoordinate
  split <;> constructor <;> intro h <;> omega

theorem rowSelection_pair_spec (count coordinate : Nat) (position : Fin (count - 1)) (offset : Nat)
    (hFound : rowSelection count coordinate = some (position, offset)) :
    let pair := reversePair count (position, offset)
    pair.1 < pair.2 ∧ pair.2 < count ∧ ordinal count pair.1 pair.2 = coordinate := by
  have hValid : coordinate < pairCount count := by
    by_cases hValid : coordinate < pairCount count
    · exact hValid
    · have hNone := (rowSelection_none_iff count coordinate).mpr (by omega)
      rw [hFound] at hNone
      cases hNone
  have hSpec := BuilderInitialLengthSelection.locate_some_bounds
    (count - 1) 1 (reverseCoordinate count coordinate) position offset hFound
  simp only [reverseCoordinate, if_pos hValid, rowSpan_pairCount] at hSpec
  have hPosition := position.isLt
  have hCount : count - (count - 2 - position.val) = position.val + 2 := by omega
  dsimp only [reversePair]
  refine ⟨by omega, by omega, ?_⟩
  unfold ordinal
  rw [hCount]
  have hPairCount : pairCount (position.val + 2) = position.val + 1 + pairCount (position.val + 1) := rfl
  have hBound := pairCount_mono (position.val + 2) count (by omega)
  omega

theorem selectedPair_eq_pairSlot (count coordinate : Nat) :
    selectedPair count coordinate = pairSlot count coordinate := by
  cases hFound : rowSelection count coordinate with
  | none =>
      have hNone := (pairSlot_none_iff count coordinate).mpr
        ((rowSelection_none_iff count coordinate).mp hFound)
      simp only [selectedPair, hFound, Option.map_none, hNone]
  | some found =>
      rcases found with ⟨position, offset⟩
      have hSpec := rowSelection_pair_spec count coordinate position offset hFound
      have hSlot := pairSlot_ordinal count
        (reversePair count (position, offset)).1 (reversePair count (position, offset)).2
        hSpec.1 hSpec.2.1
      rw [hSpec.2.2] at hSlot
      simp only [selectedPair, hFound, Option.map_some]
      exact hSlot.symm

theorem selectedPair_none_iff (count coordinate : Nat) :
    selectedPair count coordinate = none ↔ pairCount count ≤ coordinate := by
  rw [selectedPair_eq_pairSlot, pairSlot_none_iff]

def observePair {width : Nat} (variables : List (Fin width)) :
    Option (Nat × Nat) → Option (BoundedClause width)
  | none => none
  | some (first, second) =>
      variables[first]?.bind (fun left =>
        variables[second]?.map (excludeBoundedPairClause left))

private theorem observe_successor {width : Nat} (first : Fin width) (rest : List (Fin width))
    (found : Option (Nat × Nat)) :
    observePair (first :: rest) (found.map successorPair) = observePair rest found := by
  cases found with
  | none => rfl
  | some found => rcases found with ⟨left, right⟩; rfl

private theorem excludeWith_eq_lookup {width : Nat} (first : Fin width)
    (rest : List (Fin width)) (coordinate : Nat) :
    rest[coordinate]?.map (excludeBoundedPairClause first) =
      LocalConstraint.excludeWithClauseSlotDirect first rest coordinate := by
  induction rest generalizing coordinate with
  | nil => rfl
  | cons next rest ih => cases coordinate with
    | zero => rfl
    | succ coordinate => exact ih coordinate

theorem pairSlot_observes_canonical {width : Nat} (variables : List (Fin width)) (coordinate : Nat) :
    observePair variables (pairSlot variables.length coordinate) =
      LocalConstraint.atMostOneClauseSlotDirect variables coordinate := by
  induction variables generalizing coordinate with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.length_cons, pairSlot, LocalConstraint.atMostOneClauseSlotDirect, DirectSlot.append]
      by_cases hLess : coordinate < rest.length
      · simp only [if_pos hLess]
        exact excludeWith_eq_lookup first rest coordinate
      · simp only [if_neg hLess, observe_successor, ih]

/-- Exact clause equality, not permutation or merely equisatisfiability. -/
theorem selectedPair_observes_canonical {width : Nat} (variables : List (Fin width)) (coordinate : Nat) :
    observePair variables (selectedPair variables.length coordinate) =
      (atMostOneBoundedClauses variables)[coordinate]? := by
  rw [selectedPair_eq_pairSlot, pairSlot_observes_canonical, LocalConstraint.atMostOneClauseSlotDirect_eq]

theorem selectedPair_observes_exactlyOne {width : Nat} (variables : List (Fin width)) (coordinate : Nat) :
    observePair variables (selectedPair variables.length coordinate) =
      LocalConstraint.clauseSlotDirect (.exactlyOne variables) (coordinate + 1) :=
by
  rw [selectedPair_eq_pairSlot]
  exact pairSlot_observes_canonical variables coordinate

end PNP.Concrete.CookLevin.BuilderExclusionPairSelection
