/-
Copyright (c) 2026 PNP Labs.

Signed four-corner transfer arithmetic for terminal full/quotient profile
minima.  One computed profile system and one explicit projection are shared by
all four corners.  The structure carries no assertion that those corners were
constructed as a legitimate saturated support square; that construction is a
separate downstream obligation.

This is the direct-wire reconstruction of the pinned manuscript's Section 5.2
transfer identity.  Signed integers are essential because either four-corner
minimum delta may be negative.  No proper-support construction, saturation,
Package E route, BCELReady object, ZeroSlack result, or polynomial algorithm is
claimed.
-/

import PNP.ResidualTerminalProjectionMinimum

namespace PNP
namespace DirectWire

/-- Four terminal comparison corners sharing one computed profile observer and
    one quotient projection.  The names match the later support-square roles,
    but this record contains data rather than a support-legitimacy certificate. -/
structure TerminalProjectionFourCorners
    (inputs outputs profileWidth : Nat) where
  system : TerminalProfileSystem inputs outputs profileWidth
  projection : TerminalProfileProjection profileWidth
  meet : Implementation inputs outputs
  left : Implementation inputs outputs
  right : Implementation inputs outputs
  join : Implementation inputs outputs

/-- Signed four-corner delta of the full-profile minima. -/
def TerminalProjectionFourCorners.fullDelta
    {inputs outputs profileWidth : Nat}
    (corners : TerminalProjectionFourCorners inputs outputs profileWidth) : Int :=
  Int.ofNat (terminalFullProfileMinimum corners.system corners.left) +
      Int.ofNat (terminalFullProfileMinimum corners.system corners.right) -
    Int.ofNat (terminalFullProfileMinimum corners.system corners.meet) -
    Int.ofNat (terminalFullProfileMinimum corners.system corners.join)

/-- Signed four-corner delta of the quotient-profile minima. -/
def TerminalProjectionFourCorners.quotientDelta
    {inputs outputs profileWidth : Nat}
    (corners : TerminalProjectionFourCorners inputs outputs profileWidth) : Int :=
  Int.ofNat (terminalQuotientProfileMinimum corners.system corners.projection
      corners.left) +
      Int.ofNat (terminalQuotientProfileMinimum corners.system corners.projection
        corners.right) -
    Int.ofNat (terminalQuotientProfileMinimum corners.system corners.projection
      corners.meet) -
    Int.ofNat (terminalQuotientProfileMinimum corners.system corners.projection
      corners.join)

/-- The manuscript's signed projection excess `Omega = delta_0 - delta_1`. -/
def TerminalProjectionFourCorners.projectionExcess
    {inputs outputs profileWidth : Nat}
    (corners : TerminalProjectionFourCorners inputs outputs profileWidth) : Int :=
  corners.quotientDelta - corners.fullDelta

private theorem intOfNat_natSub_of_le (larger smaller : Nat)
    (within : smaller ≤ larger) :
    Int.ofNat (larger - smaller) =
      Int.ofNat larger - Int.ofNat smaller := by
  exact Int.ofNat_sub within

/-- The existing natural projection defect is exactly the corresponding
    signed difference of full and quotient minima. -/
theorem terminalProjectionDefect_int
    {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (projection : TerminalProfileProjection profileWidth)
    (current : Implementation inputs outputs) :
    Int.ofNat (terminalProjectionDefect system projection current) =
      Int.ofNat (terminalFullProfileMinimum system current) -
        Int.ofNat (terminalQuotientProfileMinimum system projection current) := by
  unfold terminalProjectionDefect
  exact intOfNat_natSub_of_le _ _
    (terminalProjectionMinimum_mono system projection current)

/-- Legacy Section 5.2 transfer identity.  It is valid for every four-corner
    family sharing one full observer and projection, hence in particular for a
    later-constructed legitimate saturated projection-compatible square. -/
theorem TerminalProjectionFourCorners.transferIdentity
    {inputs outputs profileWidth : Nat}
    (corners : TerminalProjectionFourCorners inputs outputs profileWidth) :
    Int.ofNat (terminalProjectionDefect corners.system corners.projection
        corners.join) +
        Int.ofNat (terminalProjectionDefect corners.system corners.projection
          corners.meet) =
      Int.ofNat (terminalProjectionDefect corners.system corners.projection
          corners.left) +
        Int.ofNat (terminalProjectionDefect corners.system corners.projection
          corners.right) +
        corners.projectionExcess := by
  rw [terminalProjectionDefect_int, terminalProjectionDefect_int,
    terminalProjectionDefect_int, terminalProjectionDefect_int]
  unfold TerminalProjectionFourCorners.projectionExcess
    TerminalProjectionFourCorners.quotientDelta
    TerminalProjectionFourCorners.fullDelta
  omega

/-- Constant-cut arithmetic used by the later BCEL nucleus: if the meet and
    both proper sides have zero defect while the join has defect `D`, then the
    signed projection excess is exactly `D`. -/
theorem TerminalProjectionFourCorners.constantCutEquation_of_defects
    {inputs outputs profileWidth : Nat}
    (corners : TerminalProjectionFourCorners inputs outputs profileWidth)
    (defect : Nat)
    (meetZero : terminalProjectionDefect corners.system corners.projection
      corners.meet = 0)
    (leftZero : terminalProjectionDefect corners.system corners.projection
      corners.left = 0)
    (rightZero : terminalProjectionDefect corners.system corners.projection
      corners.right = 0)
    (joinDefect : terminalProjectionDefect corners.system corners.projection
      corners.join = defect) :
    corners.projectionExcess = Int.ofNat defect := by
  have transfer := corners.transferIdentity
  rw [meetZero, leftZero, rightZero, joinDefect] at transfer
  have zeroOfNat : Int.ofNat 0 = 0 := rfl
  simp only [zeroOfNat, Int.add_zero, Int.zero_add] at transfer
  exact transfer.symm

/-- A strictly positive join defect in the constant-cut situation gives a
    strictly positive signed projection excess. -/
theorem TerminalProjectionFourCorners.projectionExcess_pos_of_constantCut
    {inputs outputs profileWidth : Nat}
    (corners : TerminalProjectionFourCorners inputs outputs profileWidth)
    (defect : Nat)
    (positive : 0 < defect)
    (meetZero : terminalProjectionDefect corners.system corners.projection
      corners.meet = 0)
    (leftZero : terminalProjectionDefect corners.system corners.projection
      corners.left = 0)
    (rightZero : terminalProjectionDefect corners.system corners.projection
      corners.right = 0)
    (joinDefect : terminalProjectionDefect corners.system corners.projection
      corners.join = defect) :
    0 < corners.projectionExcess := by
  rw [corners.constantCutEquation_of_defects defect meetZero leftZero rightZero
    joinDefect]
  exact Int.ofNat_lt.2 positive

end DirectWire
end PNP
