import PNP.ResidualTerminalProjectionTransfer

namespace PNP
namespace DirectWire

def terminalProjectionTransferIdentityImplementation : Implementation 1 1 :=
  ⟨0, Candidate.ofDirectWireWord identityProgram identityWord⟩

def terminalProjectionTransferGatePresenceSystem : TerminalProfileSystem 1 1 1 :=
  { role := fun _coordinate => .kernel
    observe := fun implementation _coordinate =>
      match implementation.gateCount with
      | 0 => false
      | _ + 1 => true }

def terminalProjectionTransferForgetAll : TerminalProfileProjection 1 :=
  { keep := fun _coordinate => false }

def terminalProjectionTransferKeepAll : TerminalProfileProjection 1 :=
  { keep := fun _coordinate => true }

/-- Three zero-gate corners and the redundant one-gate join give the exact
    signed constant-cut example: full delta -1, quotient delta 0, excess 1. -/
def terminalProjectionTransferConstantCut :
    TerminalProjectionFourCorners 1 1 1 :=
  { system := terminalProjectionTransferGatePresenceSystem
    projection := terminalProjectionTransferForgetAll
    meet := terminalProjectionTransferIdentityImplementation
    left := terminalProjectionTransferIdentityImplementation
    right := terminalProjectionTransferIdentityImplementation
    join := redundantIdentityImplementation }

theorem terminalProjectionTransfer_fullDelta_eq_neg_one :
    terminalProjectionTransferConstantCut.fullDelta = (-1 : Int) := by
  rfl

theorem terminalProjectionTransfer_quotientDelta_eq_zero :
    terminalProjectionTransferConstantCut.quotientDelta = 0 := by
  rfl

theorem terminalProjectionTransfer_projectionExcess_eq_one :
    terminalProjectionTransferConstantCut.projectionExcess = 1 := by
  rfl

example :
    Int.ofNat (terminalProjectionDefect
        terminalProjectionTransferGatePresenceSystem
        terminalProjectionTransferForgetAll redundantIdentityImplementation) =
      Int.ofNat (terminalFullProfileMinimum
        terminalProjectionTransferGatePresenceSystem
        redundantIdentityImplementation) -
      Int.ofNat (terminalQuotientProfileMinimum
        terminalProjectionTransferGatePresenceSystem
        terminalProjectionTransferForgetAll redundantIdentityImplementation) :=
  terminalProjectionDefect_int terminalProjectionTransferGatePresenceSystem
    terminalProjectionTransferForgetAll redundantIdentityImplementation

example :
    Int.ofNat (terminalProjectionDefect
        terminalProjectionTransferConstantCut.system
        terminalProjectionTransferConstantCut.projection
        terminalProjectionTransferConstantCut.join) +
      Int.ofNat (terminalProjectionDefect
        terminalProjectionTransferConstantCut.system
        terminalProjectionTransferConstantCut.projection
        terminalProjectionTransferConstantCut.meet) =
    Int.ofNat (terminalProjectionDefect
        terminalProjectionTransferConstantCut.system
        terminalProjectionTransferConstantCut.projection
        terminalProjectionTransferConstantCut.left) +
      Int.ofNat (terminalProjectionDefect
        terminalProjectionTransferConstantCut.system
        terminalProjectionTransferConstantCut.projection
        terminalProjectionTransferConstantCut.right) +
      terminalProjectionTransferConstantCut.projectionExcess :=
  terminalProjectionTransferConstantCut.transferIdentity

example : terminalProjectionTransferConstantCut.projectionExcess = 1 :=
  terminalProjectionTransferConstantCut.constantCutEquation_of_defects 1
    (by rfl) (by rfl) (by rfl) (by rfl)

example : 0 < terminalProjectionTransferConstantCut.projectionExcess :=
  terminalProjectionTransferConstantCut.projectionExcess_pos_of_constantCut 1
    (Nat.zero_lt_succ 0) (by rfl) (by rfl) (by rfl) (by rfl)

/-- An all-zero corner family makes every signed quantity definitionally zero. -/
def terminalProjectionTransferAllZero : TerminalProjectionFourCorners 1 1 1 :=
  { system := terminalProjectionTransferGatePresenceSystem
    projection := terminalProjectionTransferForgetAll
    meet := terminalProjectionTransferIdentityImplementation
    left := terminalProjectionTransferIdentityImplementation
    right := terminalProjectionTransferIdentityImplementation
    join := terminalProjectionTransferIdentityImplementation }

example : terminalProjectionTransferAllZero.fullDelta = 0 := by rfl
example : terminalProjectionTransferAllZero.quotientDelta = 0 := by rfl
example : terminalProjectionTransferAllZero.projectionExcess = 0 := by rfl
example := terminalProjectionTransferAllZero.transferIdentity

/-- Keeping every coordinate is lossless even when the full four-corner delta
    is negative. -/
def terminalProjectionTransferLossless : TerminalProjectionFourCorners 1 1 1 :=
  { system := terminalProjectionTransferGatePresenceSystem
    projection := terminalProjectionTransferKeepAll
    meet := terminalProjectionTransferIdentityImplementation
    left := terminalProjectionTransferIdentityImplementation
    right := terminalProjectionTransferIdentityImplementation
    join := redundantIdentityImplementation }

example : terminalProjectionTransferLossless.fullDelta = (-1 : Int) := by rfl
example : terminalProjectionTransferLossless.quotientDelta = (-1 : Int) := by rfl
example : terminalProjectionTransferLossless.projectionExcess = 0 := by rfl

/-- Concrete unequal side corners exercise left/right symmetry. -/
def terminalProjectionTransferUnequalSides : TerminalProjectionFourCorners 1 1 1 :=
  { system := terminalProjectionTransferGatePresenceSystem
    projection := terminalProjectionTransferForgetAll
    meet := terminalProjectionTransferIdentityImplementation
    left := terminalProjectionTransferIdentityImplementation
    right := redundantIdentityImplementation
    join := redundantIdentityImplementation }

def terminalProjectionTransferUnequalSidesSwapped :
    TerminalProjectionFourCorners 1 1 1 :=
  { system := terminalProjectionTransferGatePresenceSystem
    projection := terminalProjectionTransferForgetAll
    meet := terminalProjectionTransferIdentityImplementation
    left := redundantIdentityImplementation
    right := terminalProjectionTransferIdentityImplementation
    join := redundantIdentityImplementation }

example : terminalProjectionTransferUnequalSides.fullDelta =
    terminalProjectionTransferUnequalSidesSwapped.fullDelta := by rfl

example : terminalProjectionTransferUnequalSides.quotientDelta =
    terminalProjectionTransferUnequalSidesSwapped.quotientDelta := by rfl

example : terminalProjectionTransferUnequalSides.projectionExcess =
    terminalProjectionTransferUnequalSidesSwapped.projectionExcess := by rfl

end DirectWire
end PNP
