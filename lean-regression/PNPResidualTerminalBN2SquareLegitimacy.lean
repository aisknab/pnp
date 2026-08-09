import PNP.ResidualTerminalBN2SquareLegitimacy

set_option maxRecDepth 100000

namespace PNP
namespace DirectWire

def bn2LegitimacyInput0 : Fin 2 := ⟨0, by decide⟩
def bn2LegitimacyInput1 : Fin 2 := ⟨1, by decide⟩
def bn2LegitimacyGate0 : Fin 1 := ⟨0, by decide⟩

def bn2LegitimacyProgram : Program 2 1 :=
  .snoc .empty
    { left := .input bn2LegitimacyInput0
      right := .input bn2LegitimacyInput1 }

def bn2LegitimacyWord : DirectWireWord 2 1 1 :=
  ⟨fun _output => .gate bn2LegitimacyGate0⟩

def bn2LegitimacyCandidate : Candidate 2 1 1 :=
  Candidate.ofDirectWireWord bn2LegitimacyProgram bn2LegitimacyWord

def bn2LegitimacyProfileSystem : TerminalProfileSystem 2 1 0 :=
  { role := fun coordinate => Fin.elim0 coordinate
    observe := fun _implementation coordinate => Fin.elim0 coordinate }

def bn2LegitimacySaturationSystem : TerminalSaturationSystem 2 1 1 0 :=
  { profileSystem := bn2LegitimacyProfileSystem
    requires := fun _kind _dependent _required => false }

def bn2LegitimacySquare :
    TerminalSaturatedSupportSquare bn2LegitimacySaturationSystem :=
  terminalSaturatedSupportSquare bn2LegitimacySaturationSystem
    [.gate bn2LegitimacyGate0] [.gate bn2LegitimacyGate0]

def bn2LegitimacyProjection : TerminalProfileProjection 0 :=
  { keep := fun coordinate => Fin.elim0 coordinate }

def bn2LegitimacyCarrier :
    TerminalFourCornerCarrier bn2LegitimacySaturationSystem :=
  bn2LegitimacySquare.fourCornerCarrier bn2LegitimacyCandidate
    bn2LegitimacyProjection

def bn2LegitimacyObserver
    (_implementation : Implementation 3 1) : TerminalProfile 0 :=
  fun coordinate => Fin.elim0 coordinate

example : TerminalComputedBN2SquareLegitimate bn2LegitimacyCarrier :=
  bn2LegitimacyCarrier.computedBN2SquareLegitimate

example (corner : TerminalSupportSquareCorner) :
    (bn2LegitimacyCarrier.support corner).Compatible :=
  bn2LegitimacyCarrier.computedBN2SquareLegitimate.cornerCompatible corner

example (role : TerminalProfileRole) (coordinate : Fin 0) :
    coordinate ∈
          (bn2LegitimacyCarrier.support .meet).frontier.profiles role ↔
      coordinate ∈
            (bn2LegitimacyCarrier.support .left).frontier.profiles role ∧
        coordinate ∈
          (bn2LegitimacyCarrier.support .right).frontier.profiles role :=
  bn2LegitimacyCarrier.computedBN2SquareLegitimate.meetProfile
    role coordinate

example : bn2LegitimacyCarrier.square.ProjectionCompatible
    bn2LegitimacyCarrier.candidate bn2LegitimacyCarrier.projection :=
  bn2LegitimacyCarrier.computedBN2SquareLegitimate.projectionCompatible

example : TerminalComputedBN2SquareQuantities
    bn2LegitimacyCarrier bn2LegitimacyObserver :=
  bn2LegitimacyCarrier.computedBN2SquareQuantities bn2LegitimacyObserver

example :
    (bn2LegitimacyCarrier.optimizationCorners
      bn2LegitimacyObserver).projection = bn2LegitimacyCarrier.projection :=
  (bn2LegitimacyCarrier.computedBN2SquareQuantities
    bn2LegitimacyObserver).sharedProjection

example (corner : TerminalSupportSquareCorner) :
    referenceMinimum (bn2LegitimacyCarrier.ambientImplementation corner) =
      referenceMinimum (bn2LegitimacyCarrier.cornerImplementation corner) :=
  (bn2LegitimacyCarrier.computedBN2SquareQuantities
    bn2LegitimacyObserver).referenceMinimumPreserved corner

example : bn2LegitimacyCarrier.NoOptimumCoherenceRoutes
    bn2LegitimacyObserver := by
  constructor <;>
    change bn2LegitimacyCarrier.firstOptimumCoherenceFailure?
      bn2LegitimacyObserver _ = none <;> decide

def bn2LegitimacyConclusion : TerminalComputedBN2LocalConclusion
    bn2LegitimacyCarrier bn2LegitimacyObserver :=
  bn2LegitimacyCarrier.computedBN2LocalConclusion
    bn2LegitimacyObserver (by
      constructor <;>
        change bn2LegitimacyCarrier.firstOptimumCoherenceFailure?
          bn2LegitimacyObserver _ = none <;> decide)

example : Nonempty (TerminalFourCornerCoherentOptimumTuple
    bn2LegitimacyCarrier bn2LegitimacyObserver .full) :=
  bn2LegitimacyConclusion.fullTuple

example : Nonempty (TerminalFourCornerCoherentOptimumTuple
    bn2LegitimacyCarrier bn2LegitimacyObserver .quotient) :=
  bn2LegitimacyConclusion.quotientTuple

example : bn2LegitimacyCarrier.tightBasisMaximum?
      bn2LegitimacyObserver .full =
    some (bn2LegitimacyCarrier.optimizationCorners
      bn2LegitimacyObserver).fullDelta :=
  bn2LegitimacyConclusion.fullMaximum

example : bn2LegitimacyCarrier.tightBasisMaximum?
      bn2LegitimacyObserver .quotient =
    some (bn2LegitimacyCarrier.optimizationCorners
      bn2LegitimacyObserver).quotientDelta :=
  bn2LegitimacyConclusion.quotientMaximum

example :
    Nonempty (TerminalComputedBN2LocalConclusion
      bn2LegitimacyCarrier bn2LegitimacyObserver) ∨
      Nonempty (TerminalFourCornerOptimumRoutedFailure
        bn2LegitimacyCarrier bn2LegitimacyObserver (.coherence .full)) ∨
      Nonempty (TerminalFourCornerOptimumRoutedFailure
        bn2LegitimacyCarrier bn2LegitimacyObserver (.coherence .quotient)) :=
  bn2LegitimacyCarrier.computedBN2LocalConclusionOrFirstRoute
    bn2LegitimacyObserver

def bn2LegitimacyFailureProfileSystem : TerminalProfileSystem 2 1 1 :=
  { role := fun _coordinate => .obligation
    observe := fun _implementation _coordinate => false }

def bn2LegitimacyFailureSystem : TerminalSaturationSystem 2 1 1 1 :=
  { profileSystem := bn2LegitimacyFailureProfileSystem
    requires := fun _kind _dependent _required => false }

def bn2LegitimacyFailureSquare :
    TerminalSaturatedSupportSquare bn2LegitimacyFailureSystem :=
  terminalSaturatedSupportSquare bn2LegitimacyFailureSystem [] []

def bn2LegitimacyFailureCarrier :
    TerminalFourCornerCarrier bn2LegitimacyFailureSystem :=
  bn2LegitimacyFailureSquare.fourCornerCarrier bn2LegitimacyCandidate
    { keep := fun _coordinate => true }

def bn2LegitimacyOpenObserver
    (_implementation : Implementation 3 1) : TerminalProfile 1 :=
  fun _coordinate => true

example : bn2LegitimacyFailureCarrier.firstOptimumCoherenceFailure?
    bn2LegitimacyOpenObserver .full =
      some (.openObligation .meet ⟨0, by decide⟩ true) := by rfl

example : match bn2LegitimacyFailureCarrier.firstOptimumCoherenceFailure?
    bn2LegitimacyOpenObserver .full with
  | some failure => failure.Sound
  | none => False := by
  exact bn2LegitimacyFailureCarrier.firstOptimumCoherenceFailure?_sound
    bn2LegitimacyOpenObserver .full _ rfl

end DirectWire
end PNP
