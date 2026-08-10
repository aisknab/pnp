import PNP.ResidualTerminalRankWF

namespace PNP
namespace DirectWire

def rankZero : TerminalResidualRank :=
  TerminalResidualRank.mk 0 0 0 0 0 0 0 0 0 0

def rankWitnessBefore : TerminalResidualRank :=
  TerminalResidualRank.mk 1 0 0 0 0 0 0 0 0 0

def rankSpanBefore : TerminalResidualRank :=
  TerminalResidualRank.mk 0 1 0 0 0 0 0 0 0 0

def rankModeBefore : TerminalResidualRank :=
  TerminalResidualRank.mk 0 0 1 0 0 0 0 0 0 0

def rankFrontierBefore : TerminalResidualRank :=
  TerminalResidualRank.mk 0 0 0 1 0 0 0 0 0 0

def rankProjectionBefore : TerminalResidualRank :=
  TerminalResidualRank.mk 0 0 0 0 1 0 0 0 0 0

def rankSaturationBefore : TerminalResidualRank :=
  TerminalResidualRank.mk 0 0 0 0 0 1 0 0 0 0

def rankAnchorBefore : TerminalResidualRank :=
  TerminalResidualRank.mk 0 0 0 0 0 0 1 0 0 0

def rankChargeBefore : TerminalResidualRank :=
  TerminalResidualRank.mk 0 0 0 0 0 0 0 1 0 0

def rankProfileBefore : TerminalResidualRank :=
  TerminalResidualRank.mk 0 0 0 0 0 0 0 0 1 0

def rankCodeBefore : TerminalResidualRank :=
  TerminalResidualRank.mk 0 0 0 0 0 0 0 0 0 1

example : rankZero.coordinates = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rfl

example : rankCodeBefore.coordinates = [0, 0, 0, 0, 0, 0, 0, 0, 0, 1] := by
  rfl

example : rankZero.coordinates.length = 10 := by
  exact TerminalResidualRank.coordinates_length rankZero

example : terminalResidualRankLTBool rankZero rankZero = false := by
  decide

example : terminalResidualRankLTBool rankZero rankWitnessBefore = true := by
  decide

example : terminalResidualRankLTBool rankWitnessBefore rankZero = false := by
  decide

example : rankZero.LexLT rankWitnessBefore := by
  apply terminalResidualRank_witnessType_lt
  decide

example : rankZero.LexLT rankSpanBefore := by
  apply terminalResidualRank_spanType_lt
  decide

example : rankZero.LexLT rankModeBefore := by
  apply terminalResidualRank_mode_lt
  decide

example : rankZero.LexLT rankFrontierBefore := by
  apply terminalResidualRank_frontierDefect_lt
  decide

example : rankZero.LexLT rankProjectionBefore := by
  apply terminalResidualRank_projectionDefect_lt
  decide

example : rankZero.LexLT rankSaturationBefore := by
  apply terminalResidualRank_saturationDefect_lt
  decide

example : rankZero.LexLT rankAnchorBefore := by
  apply terminalResidualRank_anchorCount_lt
  decide

example : rankZero.LexLT rankChargeBefore := by
  apply terminalResidualRank_chargeSize_lt
  decide

example : rankZero.LexLT rankProfileBefore := by
  apply terminalResidualRank_profileSize_lt
  decide

example : rankZero.LexLT rankCodeBefore := by
  apply terminalResidualRank_canonicalCode_lt
  decide

/-! A later decrease cannot override an earlier increase. -/

def rankEarlierLargerLaterSmallerAfter : TerminalResidualRank :=
  TerminalResidualRank.mk 1 0 0 0 0 0 0 0 0 0

def rankEarlierLargerLaterSmallerBefore : TerminalResidualRank :=
  TerminalResidualRank.mk 0 1 0 0 0 0 0 0 0 0

example : terminalResidualRankLTBool rankEarlierLargerLaterSmallerAfter
    rankEarlierLargerLaterSmallerBefore = false := by
  decide

def rankCodeDescent : TerminalResidualRankDescent :=
  { before := rankCodeBefore
    after := rankZero
    decreasing := by
      apply terminalResidualRank_canonicalCode_lt
      decide }

example : rankCodeDescent.Sound :=
  rankCodeDescent.sound

example
    {motive : TerminalResidualRank → Prop}
    (step : ∀ rank,
      (∀ smaller, smaller.LexLT rank → motive smaller) → motive rank) :
    ∀ rank, motive rank :=
  terminalResidualRank_induction step

end DirectWire
end PNP
