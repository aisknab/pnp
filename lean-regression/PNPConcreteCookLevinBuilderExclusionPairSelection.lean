import PNP.Concrete.CookLevinBuilderExclusionPairSelection

open PNP.Concrete PNP.Concrete.CookLevin
open BuilderExclusionPairSelection
open LocalConstraint (pairCount)
open BuilderInitialLengthSelection (rowSpan)

example (count width : Nat) :
    rowSpan (count + 1) width = rowSpan count width + width + count :=
  rowSpan_succ_right count width

example (count : Nat) : rowSpan count 1 = pairCount (count + 1) :=
  rowSpan_pairCount count

example (count : Nat) : rowSpan (count - 1) 1 = pairCount count :=
  rowSpan_count count

example (count first second : Nat)
    (hOrder : first < second) (hSecond : second < count) :
    pairSlot count (ordinal count first second) = some (first, second) :=
  pairSlot_ordinal count first second hOrder hSecond

example (count coordinate : Nat) :
    pairSlot count coordinate = none ↔ pairCount count ≤ coordinate :=
  pairSlot_none_iff count coordinate

example (count coordinate : Nat) :
    rowSelection count coordinate = none ↔ pairCount count ≤ coordinate :=
  rowSelection_none_iff count coordinate

example (count coordinate : Nat) (position : Fin (count - 1)) (offset : Nat)
    (hFound : rowSelection count coordinate = some (position, offset)) :
    let pair := reversePair count (position, offset)
    pair.1 < pair.2 ∧ pair.2 < count ∧ ordinal count pair.1 pair.2 = coordinate :=
  rowSelection_pair_spec count coordinate position offset hFound

example (count coordinate : Nat) :
    selectedPair count coordinate = pairSlot count coordinate :=
  selectedPair_eq_pairSlot count coordinate

example (count coordinate : Nat) :
    selectedPair count coordinate = none ↔ pairCount count ≤ coordinate :=
  selectedPair_none_iff count coordinate

example {width : Nat} (variables : List (Fin width)) (coordinate : Nat) :
    observePair variables (pairSlot variables.length coordinate) =
      LocalConstraint.atMostOneClauseSlotDirect variables coordinate :=
  pairSlot_observes_canonical variables coordinate

example {width : Nat} (variables : List (Fin width)) (coordinate : Nat) :
    observePair variables (selectedPair variables.length coordinate) =
      (atMostOneBoundedClauses variables)[coordinate]? :=
  selectedPair_observes_canonical variables coordinate

example {width : Nat} (variables : List (Fin width)) (coordinate : Nat) :
    observePair variables (selectedPair variables.length coordinate) =
      LocalConstraint.clauseSlotDirect (.exactlyOne variables) (coordinate + 1) :=
  selectedPair_observes_exactlyOne variables coordinate

example : selectedPair 0 0 = none := by decide
example : selectedPair 1 0 = none := by decide
example : selectedPair 1 10 = none := by decide
example : selectedPair 2 0 = some (0, 1) := by decide
example : selectedPair 2 1 = none := by decide
example : selectedPair 4 0 = some (0, 1) := by decide
example : selectedPair 4 1 = some (0, 2) := by decide
example : selectedPair 4 2 = some (0, 3) := by decide
example : selectedPair 4 3 = some (1, 2) := by decide
example : selectedPair 4 4 = some (1, 3) := by decide
example : selectedPair 4 5 = some (2, 3) := by decide
example : selectedPair 4 6 = none := by decide
example : selectedPair 4 100 = none := by decide
example : reverseCoordinate 4 6 = 6 := by decide
example : reverseCoordinate 4 100 = 6 := by decide
example : selectedPair 10 44 = some (8, 9) := by decide
example : selectedPair 10 45 = none := by decide
example : observePair ([2, 2, 1] : List (Fin 5)) (selectedPair 3 1) =
    some (excludeBoundedPairClause (2 : Fin 5) 1) := by decide
example : observePair ([] : List (Fin 0)) (selectedPair 0 0) = none := rfl
example : observePair ([0] : List (Fin 1)) (selectedPair 1 0) = none := rfl
