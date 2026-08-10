import PNP.ResidualTerminalBN3RequestEnvelope

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire

/-- Two redundant false gates feed one ambient gate.  The canonical
    two-record proper support gives the regression a nontrivial ready nucleus
    with exactly two oriented proper cuts. -/
def bn3EnvelopeGate0 : Fin 3 := ⟨0, by decide⟩
def bn3EnvelopeGate1 : Fin 3 := ⟨1, by decide⟩
def bn3EnvelopeGate2 : Fin 3 := ⟨2, by decide⟩
def bn3EnvelopeEarlierGate0 : Fin 2 := ⟨0, by decide⟩
def bn3EnvelopeEarlierGate1 : Fin 2 := ⟨1, by decide⟩

def bn3EnvelopeProgram : Program 0 3 :=
  .snoc
    (.snoc
      (.snoc .empty
        { left := .constant true, right := .constant true })
      { left := .constant true, right := .constant true })
    { left := .gate bn3EnvelopeEarlierGate0,
      right := .gate bn3EnvelopeEarlierGate1 }

def bn3EnvelopeWord : DirectWireWord 0 3 1 :=
  ⟨fun _output => .gate bn3EnvelopeGate2⟩

def bn3EnvelopeCandidate : Candidate 0 3 1 :=
  Candidate.ofDirectWireWord bn3EnvelopeProgram bn3EnvelopeWord

def bn3EnvelopeProfileSystem : TerminalProfileSystem 0 1 1 :=
  { role := fun _coordinate => .kernel
    observe := fun _implementation _coordinate => false }

def bn3EnvelopeObserver
    (implementation : Implementation 3 3) : TerminalProfile 1 :=
  fun _coordinate => decide (2 <= implementation.gateCount)

def bn3EnvelopeSaturationSystem : TerminalSaturationSystem 0 3 1 1 :=
  { profileSystem := bn3EnvelopeProfileSystem
    requires := fun _kind _dependent _required => false }

def bn3EnvelopeSeed : List (TerminalPrimitiveRecord 0 3 1 1) :=
  [.gate bn3EnvelopeGate0, .gate bn3EnvelopeGate1]

def bn3EnvelopeSupport : TerminalProperPositiveSupport
    bn3EnvelopeCandidate bn3EnvelopeSaturationSystem :=
  { seed := bn3EnvelopeSeed
    governed := by decide
    proper := by
      unfold TerminalSupportProper
      decide
    positive := by
      unfold TerminalSupportPositive
      decide }

def bn3EnvelopeForgetAll : TerminalProfileProjection 1 :=
  { keep := fun _coordinate => false }

def bn3EnvelopeProblem : TerminalBCELAnchorProblem
    bn3EnvelopeCandidate bn3EnvelopeSaturationSystem :=
  { support := bn3EnvelopeSupport
    projection := bn3EnvelopeForgetAll
    observe := bn3EnvelopeObserver }

theorem bn3EnvelopeWholePositive :
    0 < bn3EnvelopeProblem.familyDefect bn3EnvelopeProblem.anchorRecords := by
  decide

/-- The existing two-anchor ready example now reaches the constructed finite
    BN3 envelope rather than only a per-cut existential boundary. -/
def bcelAnchorBN3ReadyOutcome : Nat × Nat :=
  match classifyTerminalBN3RequestEnvelope bn3EnvelopeProblem
      bn3EnvelopeWholePositive with
  | .insufficient _failure => (0, 0)
  | .algebraFailure _nucleus _first _failure => (1, 0)
  | .cutDefectFailure _nucleus _first _failure => (2, 0)
  | .cutRouteFailure _nucleus _first _failure => (3, 0)
  | .ready result _envelope =>
      (4, (allTerminalBCELProperCutSeeds result.requestAtoms).length)

example : bcelAnchorBN3ReadyOutcome = (4, 2) := by decide

example
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {problem : TerminalBCELAnchorProblem candidate system}
    (result : TerminalComputedBCELAnchorNucleus problem) :
    TerminalComputedBN3RequestEnvelope result :=
  result.computedBN3RequestEnvelope

#print axioms TerminalComputedBCELAnchorNucleus.computedBN3RequestEnvelope
#print axioms classifyTerminalBN3RequestEnvelope_exhaustive

end DirectWire
end PNP
