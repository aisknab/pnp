/-
Copyright (c) 2026 PNP Labs.

Fail-closed side-tight arithmetic for four independently attained terminal
profile minima.  A typed full or quotient basis supplies one realization at
each of the meet, left, right, and join corners.  Its signed incidence value is
the corresponding four-corner minimum delta plus the signed combination of
its four nonnegative slacks.  The optional extractor returns a value only when
all four slacks are zero.

This reconstructs the arithmetic and no-overclaim part of
`BN2-CoherentOptimum` in Section 11.1 of the pinned manuscript, including
`tightBasisValueEqualsDelta` and the numerical core of
`sideTightOnlyNoOverclaim`.  It does not construct a coherent four-corner
basis, prove BN2 square legitimacy, maximize over a tight family, or establish
SaturatePositive, BCELReady, ZeroSlack, polynomial runtime, or P = NP.
-/

import PNP.ResidualTerminalProjectionSquare

namespace PNP
namespace DirectWire

/-- Four natural gate counts in the manuscript's meet, left, right, and join
    order. -/
structure TerminalFourCornerSizes where
  meet : Nat
  left : Nat
  right : Nat
  join : Nat
deriving DecidableEq

/-- Signed incidence value `left + right - meet - join`. -/
def TerminalFourCornerSizes.incidenceValue
    (sizes : TerminalFourCornerSizes) : Int :=
  Int.ofNat sizes.left + Int.ofNat sizes.right - Int.ofNat sizes.meet -
    Int.ofNat sizes.join

/-- Componentwise comparison of all four named corners. -/
def TerminalFourCornerSizes.ComponentwiseLE
    (minimum sizes : TerminalFourCornerSizes) : Prop :=
  minimum.meet ≤ sizes.meet ∧
    minimum.left ≤ sizes.left ∧
    minimum.right ≤ sizes.right ∧
    minimum.join ≤ sizes.join

/-- The four nonnegative natural slacks above a proposed minimum vector. -/
def TerminalFourCornerSizes.slack
    (sizes minimum : TerminalFourCornerSizes) : TerminalFourCornerSizes :=
  { meet := sizes.meet - minimum.meet
    left := sizes.left - minimum.left
    right := sizes.right - minimum.right
    join := sizes.join - minimum.join }

/-- Numerical side-tightness means exact attainment at every named corner. -/
def TerminalFourCornerSizes.NumericallySideTight
    (sizes minimum : TerminalFourCornerSizes) : Prop :=
  sizes.meet = minimum.meet ∧
    sizes.left = minimum.left ∧
    sizes.right = minimum.right ∧
    sizes.join = minimum.join

/-- Executable recognizer for exact four-corner numerical side-tightness. -/
def TerminalFourCornerSizes.sideTightBool
    (sizes minimum : TerminalFourCornerSizes) : Bool :=
  sizes.meet == minimum.meet &&
    sizes.left == minimum.left &&
    sizes.right == minimum.right &&
    sizes.join == minimum.join

/-- Fail-closed value extraction.  No signed value is returned unless all four
    corner sizes exactly attain their named minima. -/
def TerminalFourCornerSizes.tightValue?
    (sizes minimum : TerminalFourCornerSizes) : Option Int :=
  if sizes.sideTightBool minimum then
    some sizes.incidenceValue
  else
    none

/-- Every four-corner vector componentwise bounds itself. -/
theorem TerminalFourCornerSizes.componentwiseLE_refl
    (sizes : TerminalFourCornerSizes) : sizes.ComponentwiseLE sizes :=
  ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

/-- Exact numerical side-tightness is equality of the complete named vector. -/
theorem TerminalFourCornerSizes.numericallySideTight_iff_eq
    (sizes minimum : TerminalFourCornerSizes) :
    sizes.NumericallySideTight minimum ↔ sizes = minimum := by
  constructor
  · rintro ⟨meetEqual, leftEqual, rightEqual, joinEqual⟩
    cases sizes
    cases minimum
    simp only at meetEqual leftEqual rightEqual joinEqual
    cases meetEqual
    cases leftEqual
    cases rightEqual
    cases joinEqual
    rfl
  · intro equal
    cases equal
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- The executable recognizer is true exactly for numerical side-tightness. -/
theorem TerminalFourCornerSizes.sideTightBool_eq_true_iff
    (sizes minimum : TerminalFourCornerSizes) :
    sizes.sideTightBool minimum = true ↔
      sizes.NumericallySideTight minimum := by
  unfold TerminalFourCornerSizes.sideTightBool
    TerminalFourCornerSizes.NumericallySideTight
  simp only [Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨⟨meetEqual, leftEqual⟩, rightEqual⟩, joinEqual⟩
    exact ⟨meetEqual, leftEqual, rightEqual, joinEqual⟩
  · rintro ⟨meetEqual, leftEqual, rightEqual, joinEqual⟩
    exact ⟨⟨⟨meetEqual, leftEqual⟩, rightEqual⟩, joinEqual⟩

/-- Exact characterization of successful fail-closed extraction. -/
theorem TerminalFourCornerSizes.tightValue?_eq_some_iff
    (sizes minimum : TerminalFourCornerSizes) (value : Int) :
    sizes.tightValue? minimum = some value ↔
      sizes.NumericallySideTight minimum ∧
        value = minimum.incidenceValue := by
  unfold TerminalFourCornerSizes.tightValue?
  by_cases tight : sizes.sideTightBool minimum = true
  · rw [if_pos tight]
    have numerical :=
      (TerminalFourCornerSizes.sideTightBool_eq_true_iff sizes minimum).1 tight
    have sizesEqual :=
      (TerminalFourCornerSizes.numericallySideTight_iff_eq sizes minimum).1
        numerical
    cases sizesEqual
    simp only [Option.some.injEq]
    exact ⟨fun valueEqual => ⟨numerical, valueEqual.symm⟩,
      fun result => result.2.symm⟩
  · rw [if_neg tight]
    constructor
    · intro impossible
      cases impossible
    · intro result
      have recognized :=
        (TerminalFourCornerSizes.sideTightBool_eq_true_iff sizes minimum).2
          result.1
      exact False.elim (tight recognized)

/-- Any returned value certifies all four equalities and is the minimum
    incidence delta. -/
theorem TerminalFourCornerSizes.tightValue?_sound
    {sizes minimum : TerminalFourCornerSizes} {value : Int}
    (returned : sizes.tightValue? minimum = some value) :
    sizes.NumericallySideTight minimum ∧
      value = minimum.incidenceValue :=
  (TerminalFourCornerSizes.tightValue?_eq_some_iff sizes minimum value).1 returned

/-- Exact four-corner attainment always passes the fail-closed extractor. -/
theorem TerminalFourCornerSizes.tightValue?_complete
    {sizes minimum : TerminalFourCornerSizes}
    (tight : sizes.NumericallySideTight minimum) :
    sizes.tightValue? minimum = some minimum.incidenceValue :=
  (TerminalFourCornerSizes.tightValue?_eq_some_iff
    sizes minimum minimum.incidenceValue).2 ⟨tight, rfl⟩

private theorem intOfNat_eq_minimum_add_slack
    (minimum size : Nat) (within : minimum ≤ size) :
    Int.ofNat size = Int.ofNat minimum + Int.ofNat (size - minimum) := by
  calc
    Int.ofNat size = Int.ofNat (minimum + (size - minimum)) := by
      rw [Nat.add_sub_of_le within]
    _ = Int.ofNat minimum + Int.ofNat (size - minimum) := by
      simp

/-- Generic signed slack identity.  The negative meet and join slacks are
    retained rather than hidden by natural subtraction. -/
theorem TerminalFourCornerSizes.incidenceValue_eq_minimum_add_slacks
    (sizes minimum : TerminalFourCornerSizes)
    (within : minimum.ComponentwiseLE sizes) :
    sizes.incidenceValue =
      minimum.incidenceValue + Int.ofNat (sizes.slack minimum).left +
        Int.ofNat (sizes.slack minimum).right -
        Int.ofNat (sizes.slack minimum).meet -
        Int.ofNat (sizes.slack minimum).join := by
  rcases within with ⟨meetWithin, leftWithin, rightWithin, joinWithin⟩
  unfold TerminalFourCornerSizes.incidenceValue
    TerminalFourCornerSizes.slack
  rw [intOfNat_eq_minimum_add_slack minimum.meet sizes.meet meetWithin,
    intOfNat_eq_minimum_add_slack minimum.left sizes.left leftWithin,
    intOfNat_eq_minimum_add_slack minimum.right sizes.right rightWithin,
    intOfNat_eq_minimum_add_slack minimum.join sizes.join joinWithin]
  simp only [Int.sub_eq_add_neg, Int.neg_add, Int.add_assoc, Int.add_comm,
    Int.add_left_comm]

/-- One independently attained full-carrier realization at every named
    four-corner position.  No cross-corner coherence is asserted. -/
structure TerminalFullFourCornerBasis
    {inputs outputs profileWidth : Nat}
    (corners : TerminalProjectionFourCorners inputs outputs profileWidth) where
  meet : TerminalFullCarrierRealization corners.system corners.meet
  left : TerminalFullCarrierRealization corners.system corners.left
  right : TerminalFullCarrierRealization corners.system corners.right
  join : TerminalFullCarrierRealization corners.system corners.join

/-- Gate-count vector represented by a typed full-carrier basis. -/
def TerminalFullFourCornerBasis.sizes
    {inputs outputs profileWidth : Nat}
    {corners : TerminalProjectionFourCorners inputs outputs profileWidth}
    (basis : TerminalFullFourCornerBasis corners) : TerminalFourCornerSizes :=
  { meet := basis.meet.realization.implementation.gateCount
    left := basis.left.realization.implementation.gateCount
    right := basis.right.realization.implementation.gateCount
    join := basis.join.realization.implementation.gateCount }

/-- Exact full-profile minimum at each named corner. -/
def TerminalProjectionFourCorners.fullMinimumSizes
    {inputs outputs profileWidth : Nat}
    (corners : TerminalProjectionFourCorners inputs outputs profileWidth) :
    TerminalFourCornerSizes :=
  { meet := terminalFullProfileMinimum corners.system corners.meet
    left := terminalFullProfileMinimum corners.system corners.left
    right := terminalFullProfileMinimum corners.system corners.right
    join := terminalFullProfileMinimum corners.system corners.join }

/-- The full minimum vector has the previously defined full delta as its
    signed incidence value. -/
theorem TerminalProjectionFourCorners.fullMinimumSizes_incidenceValue
    {inputs outputs profileWidth : Nat}
    (corners : TerminalProjectionFourCorners inputs outputs profileWidth) :
    corners.fullMinimumSizes.incidenceValue = corners.fullDelta :=
  rfl

/-- Every typed full basis lies componentwise above the exhaustive full
    minima. -/
theorem TerminalFullFourCornerBasis.minimum_componentwiseLE_sizes
    {inputs outputs profileWidth : Nat}
    {corners : TerminalProjectionFourCorners inputs outputs profileWidth}
    (basis : TerminalFullFourCornerBasis corners) :
    corners.fullMinimumSizes.ComponentwiseLE basis.sizes :=
  ⟨terminalFullProfileMinimum_le basis.meet,
    terminalFullProfileMinimum_le basis.left,
    terminalFullProfileMinimum_le basis.right,
    terminalFullProfileMinimum_le basis.join⟩

/-- A typed full basis value is the full delta plus its four signed slacks. -/
theorem TerminalFullFourCornerBasis.incidenceValue_eq_fullDelta_add_slacks
    {inputs outputs profileWidth : Nat}
    {corners : TerminalProjectionFourCorners inputs outputs profileWidth}
    (basis : TerminalFullFourCornerBasis corners) :
    basis.sizes.incidenceValue =
      corners.fullDelta +
        Int.ofNat (basis.sizes.slack corners.fullMinimumSizes).left +
        Int.ofNat (basis.sizes.slack corners.fullMinimumSizes).right -
        Int.ofNat (basis.sizes.slack corners.fullMinimumSizes).meet -
        Int.ofNat (basis.sizes.slack corners.fullMinimumSizes).join := by
  rw [← corners.fullMinimumSizes_incidenceValue]
  exact TerminalFourCornerSizes.incidenceValue_eq_minimum_add_slacks
    basis.sizes corners.fullMinimumSizes basis.minimum_componentwiseLE_sizes

/-- Canonical independently attained full minimum at all four corners. -/
def TerminalProjectionFourCorners.canonicalFullBasis
    {inputs outputs profileWidth : Nat}
    (corners : TerminalProjectionFourCorners inputs outputs profileWidth) :
    TerminalFullFourCornerBasis corners :=
  { meet := terminalFullProfileMinimumRealization corners.system corners.meet
    left := terminalFullProfileMinimumRealization corners.system corners.left
    right := terminalFullProfileMinimumRealization corners.system corners.right
    join := terminalFullProfileMinimumRealization corners.system corners.join }

/-- The canonical full basis attains the entire full minimum vector exactly. -/
theorem TerminalProjectionFourCorners.canonicalFullBasis_sizes
    {inputs outputs profileWidth : Nat}
    (corners : TerminalProjectionFourCorners inputs outputs profileWidth) :
    corners.canonicalFullBasis.sizes = corners.fullMinimumSizes :=
  rfl

/-- The canonical full basis is numerically side-tight. -/
theorem TerminalProjectionFourCorners.canonicalFullBasis_numericallySideTight
    {inputs outputs profileWidth : Nat}
    (corners : TerminalProjectionFourCorners inputs outputs profileWidth) :
    corners.canonicalFullBasis.sizes.NumericallySideTight
      corners.fullMinimumSizes :=
  (TerminalFourCornerSizes.numericallySideTight_iff_eq _ _).2
    corners.canonicalFullBasis_sizes

/-- The full fail-closed extractor returns exactly the full delta on the
    canonical independently attained basis. -/
theorem TerminalProjectionFourCorners.canonicalFullBasis_tightValue?
    {inputs outputs profileWidth : Nat}
    (corners : TerminalProjectionFourCorners inputs outputs profileWidth) :
    corners.canonicalFullBasis.sizes.tightValue? corners.fullMinimumSizes =
      some corners.fullDelta := by
  rw [← corners.fullMinimumSizes_incidenceValue]
  exact TerminalFourCornerSizes.tightValue?_complete
    corners.canonicalFullBasis_numericallySideTight

/-- One independently attained quotient comparison at every named four-corner
    position.  It carries no cross-corner coherence certificate. -/
structure TerminalQuotientFourCornerBasis
    {inputs outputs profileWidth : Nat}
    (corners : TerminalProjectionFourCorners inputs outputs profileWidth) where
  meet : TerminalQuotientComparison corners.system corners.projection corners.meet
  left : TerminalQuotientComparison corners.system corners.projection corners.left
  right : TerminalQuotientComparison corners.system corners.projection corners.right
  join : TerminalQuotientComparison corners.system corners.projection corners.join

/-- Gate-count vector represented by a typed quotient basis. -/
def TerminalQuotientFourCornerBasis.sizes
    {inputs outputs profileWidth : Nat}
    {corners : TerminalProjectionFourCorners inputs outputs profileWidth}
    (basis : TerminalQuotientFourCornerBasis corners) : TerminalFourCornerSizes :=
  { meet := basis.meet.realization.implementation.gateCount
    left := basis.left.realization.implementation.gateCount
    right := basis.right.realization.implementation.gateCount
    join := basis.join.realization.implementation.gateCount }

/-- Exact quotient-profile minimum at each named corner. -/
def TerminalProjectionFourCorners.quotientMinimumSizes
    {inputs outputs profileWidth : Nat}
    (corners : TerminalProjectionFourCorners inputs outputs profileWidth) :
    TerminalFourCornerSizes :=
  { meet := terminalQuotientProfileMinimum corners.system corners.projection
      corners.meet
    left := terminalQuotientProfileMinimum corners.system corners.projection
      corners.left
    right := terminalQuotientProfileMinimum corners.system corners.projection
      corners.right
    join := terminalQuotientProfileMinimum corners.system corners.projection
      corners.join }

/-- The quotient minimum vector has the previously defined quotient delta as
    its signed incidence value. -/
theorem TerminalProjectionFourCorners.quotientMinimumSizes_incidenceValue
    {inputs outputs profileWidth : Nat}
    (corners : TerminalProjectionFourCorners inputs outputs profileWidth) :
    corners.quotientMinimumSizes.incidenceValue = corners.quotientDelta :=
  rfl

/-- Every typed quotient basis lies componentwise above the exhaustive
    quotient minima. -/
theorem TerminalQuotientFourCornerBasis.minimum_componentwiseLE_sizes
    {inputs outputs profileWidth : Nat}
    {corners : TerminalProjectionFourCorners inputs outputs profileWidth}
    (basis : TerminalQuotientFourCornerBasis corners) :
    corners.quotientMinimumSizes.ComponentwiseLE basis.sizes :=
  ⟨terminalQuotientProfileMinimum_le basis.meet,
    terminalQuotientProfileMinimum_le basis.left,
    terminalQuotientProfileMinimum_le basis.right,
    terminalQuotientProfileMinimum_le basis.join⟩

/-- A typed quotient basis value is the quotient delta plus its four signed
    slacks. -/
theorem TerminalQuotientFourCornerBasis.incidenceValue_eq_quotientDelta_add_slacks
    {inputs outputs profileWidth : Nat}
    {corners : TerminalProjectionFourCorners inputs outputs profileWidth}
    (basis : TerminalQuotientFourCornerBasis corners) :
    basis.sizes.incidenceValue =
      corners.quotientDelta +
        Int.ofNat (basis.sizes.slack corners.quotientMinimumSizes).left +
        Int.ofNat (basis.sizes.slack corners.quotientMinimumSizes).right -
        Int.ofNat (basis.sizes.slack corners.quotientMinimumSizes).meet -
        Int.ofNat (basis.sizes.slack corners.quotientMinimumSizes).join := by
  rw [← corners.quotientMinimumSizes_incidenceValue]
  exact TerminalFourCornerSizes.incidenceValue_eq_minimum_add_slacks
    basis.sizes corners.quotientMinimumSizes basis.minimum_componentwiseLE_sizes

/-- Canonical independently attained quotient minimum at all four corners. -/
def TerminalProjectionFourCorners.canonicalQuotientBasis
    {inputs outputs profileWidth : Nat}
    (corners : TerminalProjectionFourCorners inputs outputs profileWidth) :
    TerminalQuotientFourCornerBasis corners :=
  { meet := terminalQuotientProfileMinimumComparison corners.system
      corners.projection corners.meet
    left := terminalQuotientProfileMinimumComparison corners.system
      corners.projection corners.left
    right := terminalQuotientProfileMinimumComparison corners.system
      corners.projection corners.right
    join := terminalQuotientProfileMinimumComparison corners.system
      corners.projection corners.join }

/-- The canonical quotient basis attains the entire quotient minimum vector. -/
theorem TerminalProjectionFourCorners.canonicalQuotientBasis_sizes
    {inputs outputs profileWidth : Nat}
    (corners : TerminalProjectionFourCorners inputs outputs profileWidth) :
    corners.canonicalQuotientBasis.sizes = corners.quotientMinimumSizes :=
  rfl

/-- The canonical quotient basis is numerically side-tight. -/
theorem TerminalProjectionFourCorners.canonicalQuotientBasis_numericallySideTight
    {inputs outputs profileWidth : Nat}
    (corners : TerminalProjectionFourCorners inputs outputs profileWidth) :
    corners.canonicalQuotientBasis.sizes.NumericallySideTight
      corners.quotientMinimumSizes :=
  (TerminalFourCornerSizes.numericallySideTight_iff_eq _ _).2
    corners.canonicalQuotientBasis_sizes

/-- The quotient fail-closed extractor returns exactly the quotient delta on
    the canonical independently attained basis. -/
theorem TerminalProjectionFourCorners.canonicalQuotientBasis_tightValue?
    {inputs outputs profileWidth : Nat}
    (corners : TerminalProjectionFourCorners inputs outputs profileWidth) :
    corners.canonicalQuotientBasis.sizes.tightValue?
        corners.quotientMinimumSizes =
      some corners.quotientDelta := by
  rw [← corners.quotientMinimumSizes_incidenceValue]
  exact TerminalFourCornerSizes.tightValue?_complete
    corners.canonicalQuotientBasis_numericallySideTight

/-- The canonical independently attained full and quotient bases are both
    numerically side-tight, and their fail-closed values are exactly the two
    pre-existing four-corner deltas.  This is numerical arithmetic only: it
    does not identify these independent realizations as one coherent basis. -/
theorem TerminalProjectionFourCorners.canonical_numericallySideTight_values
    {inputs outputs profileWidth : Nat}
    (corners : TerminalProjectionFourCorners inputs outputs profileWidth) :
    (corners.canonicalFullBasis.sizes.NumericallySideTight
          corners.fullMinimumSizes ∧
        corners.canonicalFullBasis.sizes.tightValue? corners.fullMinimumSizes =
          some corners.fullDelta) ∧
      (corners.canonicalQuotientBasis.sizes.NumericallySideTight
          corners.quotientMinimumSizes ∧
        corners.canonicalQuotientBasis.sizes.tightValue?
            corners.quotientMinimumSizes =
          some corners.quotientDelta) :=
  ⟨⟨corners.canonicalFullBasis_numericallySideTight,
      corners.canonicalFullBasis_tightValue?⟩,
    ⟨corners.canonicalQuotientBasis_numericallySideTight,
      corners.canonicalQuotientBasis_tightValue?⟩⟩

end DirectWire
end PNP
