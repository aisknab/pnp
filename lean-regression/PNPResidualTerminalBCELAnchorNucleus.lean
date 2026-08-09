import PNP.ResidualTerminalBCELAnchorNucleus

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace PNP
namespace DirectWire

def bcelAnchorGate0 : Fin 3 := ⟨0, by decide⟩
def bcelAnchorGate1 : Fin 3 := ⟨1, by decide⟩
def bcelAnchorGate2 : Fin 3 := ⟨2, by decide⟩
def bcelAnchorEarlierGate0 : Fin 2 := ⟨0, by decide⟩
def bcelAnchorEarlierGate1 : Fin 2 := ⟨1, by decide⟩

/-- Two redundant false gates feed one ambient gate.  Selecting the first two
    gives a proper two-gate open support whose two outputs are both constant
    false, hence have a zero-gate semantic realization. -/
def bcelAnchorProgram : Program 0 3 :=
  .snoc
    (.snoc
      (.snoc .empty
        { left := .constant true, right := .constant true })
      { left := .constant true, right := .constant true })
    { left := .gate bcelAnchorEarlierGate0,
      right := .gate bcelAnchorEarlierGate1 }

def bcelAnchorWord : DirectWireWord 0 3 1 :=
  ⟨fun _output => .gate bcelAnchorGate2⟩

def bcelAnchorCandidate : Candidate 0 3 1 :=
  Candidate.ofDirectWireWord bcelAnchorProgram bcelAnchorWord

def bcelAnchorProfile0 : Fin 1 := ⟨0, by decide⟩

def bcelAnchorReadyProfileSystem : TerminalProfileSystem 0 1 1 :=
  { role := fun _coordinate => .kernel
    observe := fun _implementation _coordinate => false }

def bcelAnchorReadyObserver
    (implementation : Implementation 3 3) : TerminalProfile 1 :=
  fun _coordinate => decide (2 <= implementation.gateCount)

def bcelAnchorReadySaturationSystem : TerminalSaturationSystem 0 3 1 1 :=
  { profileSystem := bcelAnchorReadyProfileSystem
    requires := fun _kind _dependent _required => false }

def bcelAnchorTwoGateSeed :
    List (TerminalPrimitiveRecord 0 3 1 1) :=
  [.gate bcelAnchorGate0, .gate bcelAnchorGate1]

def bcelAnchorReadySupport : TerminalProperPositiveSupport
    bcelAnchorCandidate bcelAnchorReadySaturationSystem :=
  { seed := bcelAnchorTwoGateSeed
    governed := by decide
    proper := by
      unfold TerminalSupportProper
      decide
    positive := by
      unfold TerminalSupportPositive
      decide }

def bcelAnchorForgetAll : TerminalProfileProjection 1 :=
  { keep := fun _coordinate => false }

def bcelAnchorReadyProblem : TerminalBCELAnchorProblem
    bcelAnchorCandidate bcelAnchorReadySaturationSystem :=
  { support := bcelAnchorReadySupport
    projection := bcelAnchorForgetAll
    observe := bcelAnchorReadyObserver }

theorem bcelAnchorReadyWholePositive :
    0 < bcelAnchorReadyProblem.familyDefect
      bcelAnchorReadyProblem.anchorRecords := by
  decide

def bcelAnchorReadyFoundLength : Option Nat :=
  match findTerminalPositiveAnchorNucleus bcelAnchorReadyProblem with
  | some nucleus => some nucleus.anchors.length
  | none => none

example : bcelAnchorReadyFoundLength = some 2 := by decide

def bcelAnchorReadyOutcome : Nat × Nat :=
  match classifyTerminalBCELAnchorNucleus bcelAnchorReadyProblem
      bcelAnchorReadyWholePositive with
  | .insufficient _failure => (0, 0)
  | .algebraFailure _nucleus _first _failure => (1, 0)
  | .cutDefectFailure _nucleus _first _failure => (2, 0)
  | .cutRouteFailure _nucleus _first _failure => (3, 0)
  | .ready result => (4, result.nucleus.anchors.length)

def bcelAnchorSingletonProfileSystem : TerminalProfileSystem 0 1 1 :=
  { role := fun _coordinate => .kernel
    observe := fun _implementation _coordinate => false }

def bcelAnchorSingletonObserver
    (implementation : Implementation 3 3) : TerminalProfile 1 :=
  fun _coordinate => decide (1 <= implementation.gateCount)

def bcelAnchorSingletonSystem : TerminalSaturationSystem 0 3 1 1 :=
  { profileSystem := bcelAnchorSingletonProfileSystem
    requires := fun _kind _dependent _required => false }

def bcelAnchorSingletonSupportForSystem : TerminalProperPositiveSupport
    bcelAnchorCandidate bcelAnchorSingletonSystem :=
  { seed := [.gate bcelAnchorGate0]
    governed := by decide
    proper := by
      unfold TerminalSupportProper
      decide
    positive := by
      unfold TerminalSupportPositive
      decide }

def bcelAnchorSingletonProblem : TerminalBCELAnchorProblem
    bcelAnchorCandidate bcelAnchorSingletonSystem :=
  { support := bcelAnchorSingletonSupportForSystem
    projection := bcelAnchorForgetAll
    observe := bcelAnchorSingletonObserver }

theorem bcelAnchorSingletonWholePositive :
    0 < bcelAnchorSingletonProblem.familyDefect
      bcelAnchorSingletonProblem.anchorRecords := by
  decide

def bcelAnchorSingletonOutcome : Nat × Nat :=
  match classifyTerminalBCELAnchorNucleus bcelAnchorSingletonProblem
      bcelAnchorSingletonWholePositive with
  | .insufficient failure => (0, failure.nucleus.anchors.length)
  | .algebraFailure _nucleus _first _failure => (1, 0)
  | .cutDefectFailure _nucleus _first _failure => (2, 0)
  | .cutRouteFailure _nucleus _first _failure => (3, 0)
  | .ready _result => (4, 0)

example : bcelAnchorSingletonOutcome = (0, 1) := by decide

def bcelAnchorSharedProfileSystem : TerminalProfileSystem 0 1 1 :=
  bcelAnchorReadyProfileSystem

def bcelAnchorSharedDependencySystem : TerminalSaturationSystem 0 3 1 1 :=
  { profileSystem := bcelAnchorSharedProfileSystem
    requires := fun kind dependent required =>
      match kind, dependent, required with
      | .kernel, .gate gate, .profile coordinate =>
          decide (gate = bcelAnchorGate0 ∨ gate = bcelAnchorGate1) &&
            decide (coordinate = bcelAnchorProfile0)
      | _, _, _ => false }

def bcelAnchorSharedSupport : TerminalProperPositiveSupport
    bcelAnchorCandidate bcelAnchorSharedDependencySystem :=
  { seed := bcelAnchorTwoGateSeed
    governed := by decide
    proper := by
      unfold TerminalSupportProper
      decide
    positive := by
      unfold TerminalSupportPositive
      decide }

def bcelAnchorSharedProblem : TerminalBCELAnchorProblem
    bcelAnchorCandidate bcelAnchorSharedDependencySystem :=
  { support := bcelAnchorSharedSupport
    projection := bcelAnchorForgetAll
    observe := bcelAnchorReadyObserver }

theorem bcelAnchorSharedWholePositive :
    0 < bcelAnchorSharedProblem.familyDefect
      bcelAnchorSharedProblem.anchorRecords := by
  decide

def bcelAnchorSharedOutcome : Nat × Bool :=
  match classifyTerminalBCELAnchorNucleus bcelAnchorSharedProblem
      bcelAnchorSharedWholePositive with
  | .insufficient _failure => (0, false)
  | .algebraFailure _nucleus _first failure =>
      (1, decide (failure.check.law = .meet))
  | .cutDefectFailure _nucleus _first _failure => (2, false)
  | .cutRouteFailure _nucleus _first _failure => (3, false)
  | .ready _result => (4, false)

example : bcelAnchorSharedOutcome = (1, true) := by decide

def bcelAnchorRouteCoordinate0 : Fin 2 := ⟨0, by decide⟩
def bcelAnchorRouteCoordinate1 : Fin 2 := ⟨1, by decide⟩

def bcelAnchorRouteProfileSystem : TerminalProfileSystem 0 1 2 :=
  { role := fun coordinate =>
      if coordinate = bcelAnchorRouteCoordinate0 then .kernel else .obligation
    observe := fun _implementation _coordinate => false }

def bcelAnchorRouteObserver
    (implementation : Implementation 3 3) : TerminalProfile 2 :=
  fun coordinate =>
    if coordinate = bcelAnchorRouteCoordinate0 then
      decide (2 <= implementation.gateCount)
    else
      true

def bcelAnchorRouteSystem : TerminalSaturationSystem 0 3 1 2 :=
  { profileSystem := bcelAnchorRouteProfileSystem
    requires := fun _kind _dependent _required => false }

def bcelAnchorRouteSupport : TerminalProperPositiveSupport
    bcelAnchorCandidate bcelAnchorRouteSystem :=
  { seed :=
      ([.gate bcelAnchorGate0, .gate bcelAnchorGate1] :
        List (TerminalPrimitiveRecord 0 3 1 2))
    governed := by decide
    proper := by
      unfold TerminalSupportProper
      decide
    positive := by
      unfold TerminalSupportPositive
      decide }

def bcelAnchorForgetDefectKeepObligation : TerminalProfileProjection 2 :=
  { keep := fun coordinate => coordinate = bcelAnchorRouteCoordinate1 }

def bcelAnchorRouteProblem : TerminalBCELAnchorProblem
    bcelAnchorCandidate bcelAnchorRouteSystem :=
  { support := bcelAnchorRouteSupport
    projection := bcelAnchorForgetDefectKeepObligation
    observe := bcelAnchorRouteObserver }

theorem bcelAnchorRouteWholePositive :
    0 < bcelAnchorRouteProblem.familyDefect
      bcelAnchorRouteProblem.anchorRecords := by
  decide

def bcelAnchorRouteOutcome : Nat × Bool :=
  match classifyTerminalBCELAnchorNucleus bcelAnchorRouteProblem
      bcelAnchorRouteWholePositive with
  | .insufficient _failure => (0, false)
  | .algebraFailure _nucleus _first _failure => (1, false)
  | .cutDefectFailure _nucleus _first _failure => (2, false)
  | .cutRouteFailure _nucleus _first failure =>
      (3, decide (failure.selected.mode = .full))
  | .ready _result => (4, false)

example : bcelAnchorRouteOutcome = (3, true) := by decide

end DirectWire
end PNP
