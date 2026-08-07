import PNP.ResidualTerminalSideTightMinimum

namespace PNP
namespace DirectWire

def sideTightIdentityImplementation : Implementation 1 1 :=
  ⟨0, Candidate.ofDirectWireWord identityProgram identityWord⟩

def sideTightGatePresenceSystem : TerminalProfileSystem 1 1 1 :=
  { role := fun _coordinate => .kernel
    observe := fun implementation _coordinate =>
      match implementation.gateCount with
      | 0 => false
      | _ + 1 => true }

def sideTightForgetAll : TerminalProfileProjection 1 :=
  { keep := fun _coordinate => false }

def sideTightKeepAll : TerminalProfileProjection 1 :=
  { keep := fun _coordinate => true }

def sideTightConstantCut : TerminalProjectionFourCorners 1 1 1 :=
  { system := sideTightGatePresenceSystem
    projection := sideTightForgetAll
    meet := sideTightIdentityImplementation
    left := sideTightIdentityImplementation
    right := sideTightIdentityImplementation
    join := redundantIdentityImplementation }

def sideTightAllZero : TerminalProjectionFourCorners 1 1 1 :=
  { system := sideTightGatePresenceSystem
    projection := sideTightForgetAll
    meet := sideTightIdentityImplementation
    left := sideTightIdentityImplementation
    right := sideTightIdentityImplementation
    join := sideTightIdentityImplementation }

def sideTightKeepAllCorners : TerminalProjectionFourCorners 1 1 1 :=
  { system := sideTightGatePresenceSystem
    projection := sideTightKeepAll
    meet := sideTightIdentityImplementation
    left := sideTightIdentityImplementation
    right := sideTightIdentityImplementation
    join := redundantIdentityImplementation }

def sideTightUnequalSides : TerminalProjectionFourCorners 1 1 1 :=
  { system := sideTightGatePresenceSystem
    projection := sideTightForgetAll
    meet := sideTightIdentityImplementation
    left := sideTightIdentityImplementation
    right := redundantIdentityImplementation
    join := redundantIdentityImplementation }

def sideTightUnequalSidesSwapped : TerminalProjectionFourCorners 1 1 1 :=
  { system := sideTightGatePresenceSystem
    projection := sideTightForgetAll
    meet := sideTightIdentityImplementation
    left := redundantIdentityImplementation
    right := sideTightIdentityImplementation
    join := redundantIdentityImplementation }

def sideTightZeroSizes : TerminalFourCornerSizes :=
  { meet := 0, left := 0, right := 0, join := 0 }

def sideTightNegativeSizes : TerminalFourCornerSizes :=
  { meet := 0, left := 0, right := 0, join := 1 }

def sideTightSlackMinimum : TerminalFourCornerSizes :=
  { meet := 1, left := 2, right := 3, join := 4 }

def sideTightSlackSizes : TerminalFourCornerSizes :=
  { meet := 2, left := 4, right := 6, join := 8 }

def sideTightLeftLoose : TerminalFourCornerSizes :=
  { meet := 0, left := 1, right := 0, join := 0 }

def sideTightMeetLoose : TerminalFourCornerSizes :=
  { meet := 1, left := 0, right := 0, join := 0 }

def sideTightJoinLoose : TerminalFourCornerSizes :=
  { meet := 0, left := 0, right := 0, join := 1 }

/-- Equal positive left and meet slacks cancel in the raw signed value, but
    the fail-closed extractor still rejects the non-tight vector. -/
def sideTightCancelingLoose : TerminalFourCornerSizes :=
  { meet := 1, left := 1, right := 0, join := 0 }

example : sideTightZeroSizes.incidenceValue = 0 := by rfl
example : sideTightNegativeSizes.incidenceValue = (-1 : Int) := by rfl

example : sideTightSlackMinimum.ComponentwiseLE sideTightSlackSizes :=
  ⟨by decide, by decide, by decide, by decide⟩

example :
    sideTightSlackSizes.incidenceValue =
      sideTightSlackMinimum.incidenceValue +
        Int.ofNat (sideTightSlackSizes.slack sideTightSlackMinimum).left +
        Int.ofNat (sideTightSlackSizes.slack sideTightSlackMinimum).right -
        Int.ofNat (sideTightSlackSizes.slack sideTightSlackMinimum).meet -
        Int.ofNat (sideTightSlackSizes.slack sideTightSlackMinimum).join :=
  TerminalFourCornerSizes.incidenceValue_eq_minimum_add_slacks
    sideTightSlackSizes sideTightSlackMinimum
      ⟨by decide, by decide, by decide, by decide⟩

example : sideTightZeroSizes.tightValue? sideTightZeroSizes = some 0 := by rfl
example : sideTightLeftLoose.tightValue? sideTightZeroSizes = none := by rfl
example : sideTightMeetLoose.tightValue? sideTightZeroSizes = none := by rfl
example : sideTightJoinLoose.tightValue? sideTightZeroSizes = none := by rfl

example : sideTightCancelingLoose.incidenceValue =
    sideTightZeroSizes.incidenceValue := by rfl

example : sideTightCancelingLoose.tightValue? sideTightZeroSizes = none := by
  rfl

example {sizes minimum : TerminalFourCornerSizes} {value : Int}
    (returned : sizes.tightValue? minimum = some value) :
    sizes.NumericallySideTight minimum ∧
      value = minimum.incidenceValue :=
  TerminalFourCornerSizes.tightValue?_sound returned

example : sideTightConstantCut.fullDelta = (-1 : Int) := by rfl
example : sideTightConstantCut.quotientDelta = 0 := by rfl

example :
    sideTightConstantCut.canonicalFullBasis.sizes.tightValue?
        sideTightConstantCut.fullMinimumSizes =
      some (-1 : Int) :=
  sideTightConstantCut.canonicalFullBasis_tightValue?

example :
    sideTightConstantCut.canonicalQuotientBasis.sizes.tightValue?
        sideTightConstantCut.quotientMinimumSizes =
      some 0 :=
  sideTightConstantCut.canonicalQuotientBasis_tightValue?

example :
    sideTightAllZero.canonicalFullBasis.sizes.NumericallySideTight
      sideTightAllZero.fullMinimumSizes :=
  sideTightAllZero.canonicalFullBasis_numericallySideTight

example :
    sideTightAllZero.canonicalQuotientBasis.sizes.NumericallySideTight
      sideTightAllZero.quotientMinimumSizes :=
  sideTightAllZero.canonicalQuotientBasis_numericallySideTight

example :
    sideTightConstantCut.fullMinimumSizes.ComponentwiseLE
      sideTightConstantCut.canonicalFullBasis.sizes :=
  sideTightConstantCut.canonicalFullBasis.minimum_componentwiseLE_sizes

example :
    sideTightConstantCut.quotientMinimumSizes.ComponentwiseLE
      sideTightConstantCut.canonicalQuotientBasis.sizes :=
  sideTightConstantCut.canonicalQuotientBasis.minimum_componentwiseLE_sizes

example :=
  sideTightConstantCut.canonicalFullBasis.incidenceValue_eq_fullDelta_add_slacks

example :=
  sideTightConstantCut.canonicalQuotientBasis.incidenceValue_eq_quotientDelta_add_slacks

example := sideTightConstantCut.canonical_numericallySideTight_values
example := sideTightAllZero.canonical_numericallySideTight_values
example := sideTightKeepAllCorners.canonical_numericallySideTight_values

example : sideTightUnequalSides.fullDelta =
    sideTightUnequalSidesSwapped.fullDelta := by rfl

example : sideTightUnequalSides.quotientDelta =
    sideTightUnequalSidesSwapped.quotientDelta := by rfl

end DirectWire
end PNP
