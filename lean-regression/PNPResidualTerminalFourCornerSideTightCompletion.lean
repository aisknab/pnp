import PNP.ResidualTerminalFourCornerSideTightCompletion

set_option maxRecDepth 100000

namespace PNP
namespace DirectWire

abbrev completionRecord := TerminalPrimitiveRecord 1 3 1 2

def completionInput0 : Fin 1 := ⟨0, by decide⟩
def completionGate0 : Fin 3 := ⟨0, by decide⟩
def completionGate1 : Fin 3 := ⟨1, by decide⟩
def completionGate2 : Fin 3 := ⟨2, by decide⟩
def completionProfile0 : Fin 2 := ⟨0, by decide⟩
def completionProfile1 : Fin 2 := ⟨1, by decide⟩

def completionProgram0 : Program 1 1 :=
  .snoc .empty
    { left := .input completionInput0
      right := .input completionInput0 }

def completionProgram1 : Program 1 2 :=
  .snoc completionProgram0
    { left := .gate ⟨0, by decide⟩
      right := .input completionInput0 }

def completionProgram : Program 1 3 :=
  .snoc completionProgram1
    { left := .gate ⟨1, by decide⟩
      right := .input completionInput0 }

def completionWord : DirectWireWord 1 3 1 :=
  ⟨fun _output => .gate completionGate2⟩

def completionCandidate : Candidate 1 3 1 :=
  Candidate.ofDirectWireWord completionProgram completionWord

def completionProfileSystem : TerminalProfileSystem 1 1 2 :=
  { role := fun coordinate =>
      if coordinate.val = 0 then .origin else .charge
    observe := fun _implementation _coordinate => false }

def completionSaturationSystem : TerminalSaturationSystem 1 3 1 2 :=
  { profileSystem := completionProfileSystem
    requires := fun _kind _dependent _required => false }

def completionSquare :
    TerminalSaturatedSupportSquare completionSaturationSystem :=
  terminalSaturatedSupportSquare completionSaturationSystem
    [.gate completionGate0, .profile completionProfile0]
    [.gate completionGate1, .profile completionProfile0,
      .profile completionProfile1]

def completionProjection : TerminalProfileProjection 2 :=
  { keep := fun coordinate => coordinate.val = 0 }

def completionCarrier : TerminalFourCornerCarrier completionSaturationSystem :=
  completionSquare.fourCornerCarrier completionCandidate completionProjection

def completionEmptySquare :
    TerminalSaturatedSupportSquare completionSaturationSystem :=
  terminalSaturatedSupportSquare completionSaturationSystem [] []

def completionEmptyCarrier :
    TerminalFourCornerCarrier completionSaturationSystem :=
  completionEmptySquare.fourCornerCarrier completionCandidate
    completionProjection

def completionConstantObserver
    (_implementation : Implementation 4 3) : TerminalProfile 2 :=
  fun _coordinate => false

def completionProfileObserver
    (implementation : Implementation 4 3) : TerminalProfile 2 :=
  fun _coordinate => implementation.candidate.semantics
    (fun _input => false) completionGate0

def completionModeObserver
    (implementation : Implementation 4 3) : TerminalProfile 2 :=
  fun coordinate =>
    if coordinate.val = 0 then false
    else implementation.candidate.semantics
      (fun _input => true) completionGate1

example (mode : TerminalOptimumCoherenceMode) :
    completionCarrier.firstOptimumRoute? completionConstantObserver
        (.coherence mode) =
      completionCarrier.firstOptimumCoherenceFailure?
        completionConstantObserver mode :=
  rfl

example : completionCarrier.firstOptimumRoute? completionModeObserver
      .quotientPromotion =
    completionCarrier.firstOptimumModeMismatch? completionModeObserver :=
  rfl

example : completionEmptyCarrier.NoOptimumCoherenceRoutes
    completionConstantObserver := by
  constructor
  · change completionEmptyCarrier.firstOptimumCoherenceFailure?
      completionConstantObserver .full = none
    decide
  · change completionEmptyCarrier.firstOptimumCoherenceFailure?
      completionConstantObserver .quotient = none
    decide

example : completionEmptyCarrier.NoOptimumPromotionRoute
    completionConstantObserver := by
  change completionEmptyCarrier.firstOptimumModeMismatch?
    completionConstantObserver = none
  decide

example : Nonempty (TerminalFourCornerCoherentOptimumTuple
      completionEmptyCarrier completionConstantObserver .full) ∧
    Nonempty (TerminalFourCornerCoherentOptimumTuple
      completionEmptyCarrier completionConstantObserver .quotient) :=
  completionEmptyCarrier.sideTightCompletionExistsEachMode
    completionConstantObserver (by
      constructor
      · change completionEmptyCarrier.firstOptimumCoherenceFailure?
          completionConstantObserver .full = none
        decide
      · change completionEmptyCarrier.firstOptimumCoherenceFailure?
          completionConstantObserver .quotient = none
        decide)

example :
    (completionEmptyCarrier.canonicalOptimumFamily
      completionConstantObserver).fullBasis.sizes.tightValue?
        (completionEmptyCarrier.optimizationCorners
          completionConstantObserver).fullMinimumSizes =
      some (completionEmptyCarrier.optimizationCorners
        completionConstantObserver).fullDelta :=
  completionEmptyCarrier.sideTightCompletion_fullValue
    completionConstantObserver (by
      change completionEmptyCarrier.firstOptimumCoherenceFailure?
        completionConstantObserver .full = none
      decide)

example :
    (completionEmptyCarrier.canonicalOptimumFamily
      completionConstantObserver).quotientBasis.sizes.tightValue?
        (completionEmptyCarrier.optimizationCorners
          completionConstantObserver).quotientMinimumSizes =
      some (completionEmptyCarrier.optimizationCorners
        completionConstantObserver).quotientDelta :=
  completionEmptyCarrier.sideTightCompletion_quotientValue
    completionConstantObserver (by
      change completionEmptyCarrier.firstOptimumCoherenceFailure?
        completionConstantObserver .quotient = none
      decide)

example (mode : TerminalOptimumCoherenceMode) :
    Nonempty (TerminalFourCornerCoherentOptimumTuple
        completionCarrier completionConstantObserver mode) ∨
      Nonempty (TerminalFourCornerOptimumRoutedFailure
        completionCarrier completionConstantObserver (.coherence mode)) :=
  completionCarrier.sideTightCompletionOrFirstRoute
    completionConstantObserver mode

example : match completionCarrier.firstOptimumRoute?
    completionConstantObserver (.coherence .full) with
  | some (.semanticMismatch _leg _input _producer _source _target) => True
  | _ => False := by exact True.intro

example : match completionCarrier.firstOptimumRoute?
    completionProfileObserver (.coherence .full) with
  | some (.profileMismatch .meetLeft .origin coordinate false true) =>
      coordinate = completionProfile0
  | _ => False := by rfl

example : match completionCarrier.firstOptimumRoute?
    completionModeObserver .quotientPromotion with
  | some (.modeMismatch .rightJoin .charge coordinate false true) =>
      coordinate = completionProfile1
  | _ => False := by rfl

example : ¬completionCarrier.NoOptimumPromotionRoute
    completionModeObserver := by
  change completionCarrier.firstOptimumModeMismatch?
    completionModeObserver ≠ none
  decide

def completionObligationProfileSystem : TerminalProfileSystem 1 1 1 :=
  { role := fun _coordinate => .obligation
    observe := fun _implementation _coordinate => false }

def completionObligationSystem : TerminalSaturationSystem 1 3 1 1 :=
  { profileSystem := completionObligationProfileSystem
    requires := fun _kind _dependent _required => false }

def completionObligationSquare :
    TerminalSaturatedSupportSquare completionObligationSystem :=
  terminalSaturatedSupportSquare completionObligationSystem [] []

def completionObligationCarrier :
    TerminalFourCornerCarrier completionObligationSystem :=
  completionObligationSquare.fourCornerCarrier completionCandidate
    { keep := fun _coordinate => true }

def completionOpenObserver
    (_implementation : Implementation 4 3) : TerminalProfile 1 :=
  fun _coordinate => true

example : completionObligationCarrier.firstOptimumRoute?
    completionOpenObserver (.coherence .full) =
      some (.openObligation .meet ⟨0, by decide⟩ true) := by rfl

def completionChargeProfileSystem : TerminalProfileSystem 1 1 2 :=
  { role := fun _coordinate => .charge
    observe := fun _implementation _coordinate => false }

def completionChargeSystem : TerminalSaturationSystem 1 3 1 2 :=
  { profileSystem := completionChargeProfileSystem
    requires := fun _kind _dependent _required => false }

def completionChargeSquare :
    TerminalSaturatedSupportSquare completionChargeSystem :=
  terminalSaturatedSupportSquare completionChargeSystem
    [.gate completionGate0, .profile completionProfile0]
    [.gate completionGate1, .profile completionProfile0,
      .profile completionProfile1]

def completionChargeCarrier : TerminalFourCornerCarrier completionChargeSystem :=
  completionChargeSquare.fourCornerCarrier completionCandidate
    completionProjection

example : match completionChargeCarrier.firstOptimumRoute?
    completionProfileObserver (.coherence .full) with
  | some (.chargeProfileMismatch .meetLeft coordinate false true) =>
      coordinate = completionProfile0
  | _ => False := by rfl

example (phase : TerminalOptimumRoutePhase)
    (failure : TerminalFourCornerOptimumFailure 4 3 2)
    (first : completionCarrier.firstOptimumRoute?
      completionConstantObserver phase = some failure) :
    failure.Sound :=
  completionCarrier.firstOptimumRoute?_sound
    completionConstantObserver phase failure first

example (mode : TerminalOptimumCoherenceMode)
    (route : TerminalFourCornerOptimumRoutedFailure
      completionCarrier completionConstantObserver (.coherence mode)) :
    ¬Nonempty (TerminalFourCornerCoherentOptimumTuple
      completionCarrier completionConstantObserver mode) :=
  route.excludesCoherentOptimum

end DirectWire
end PNP
