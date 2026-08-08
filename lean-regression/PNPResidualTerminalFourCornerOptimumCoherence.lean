import PNP.ResidualTerminalFourCornerOptimumCoherence

set_option maxRecDepth 100000

namespace PNP
namespace DirectWire

abbrev coherenceRecord := TerminalPrimitiveRecord 1 3 1 2

def coherenceInput0 : Fin 1 := ⟨0, by decide⟩
def coherenceGate0 : Fin 3 := ⟨0, by decide⟩
def coherenceGate1 : Fin 3 := ⟨1, by decide⟩
def coherenceGate2 : Fin 3 := ⟨2, by decide⟩
def coherenceProfile0 : Fin 2 := ⟨0, by decide⟩
def coherenceProfile1 : Fin 2 := ⟨1, by decide⟩

def coherenceProgram0 : Program 1 1 :=
  .snoc .empty
    { left := .input coherenceInput0
      right := .input coherenceInput0 }

def coherenceProgram1 : Program 1 2 :=
  .snoc coherenceProgram0
    { left := .gate ⟨0, by decide⟩
      right := .input coherenceInput0 }

def coherenceProgram : Program 1 3 :=
  .snoc coherenceProgram1
    { left := .gate ⟨1, by decide⟩
      right := .input coherenceInput0 }

def coherenceWord : DirectWireWord 1 3 1 :=
  ⟨fun _output => .gate coherenceGate2⟩

def coherenceCandidate : Candidate 1 3 1 :=
  Candidate.ofDirectWireWord coherenceProgram coherenceWord

def coherenceProfileSystem : TerminalProfileSystem 1 1 2 :=
  { role := fun coordinate =>
      if coordinate.val = 0 then .origin else .charge
    observe := fun _implementation _coordinate => false }

def coherenceSaturationSystem : TerminalSaturationSystem 1 3 1 2 :=
  { profileSystem := coherenceProfileSystem
    requires := fun _kind _dependent _required => false }

def coherenceSquare : TerminalSaturatedSupportSquare coherenceSaturationSystem :=
  terminalSaturatedSupportSquare coherenceSaturationSystem
    [.gate coherenceGate0, .profile coherenceProfile0]
    [.gate coherenceGate1, .profile coherenceProfile0,
      .profile coherenceProfile1]

def coherenceProjection : TerminalProfileProjection 2 :=
  { keep := fun coordinate => coordinate.val = 0 }

def coherenceCarrier : TerminalFourCornerCarrier coherenceSaturationSystem :=
  coherenceSquare.fourCornerCarrier coherenceCandidate coherenceProjection

def coherenceEmptySquare :
    TerminalSaturatedSupportSquare coherenceSaturationSystem :=
  terminalSaturatedSupportSquare coherenceSaturationSystem [] []

def coherenceEmptyCarrier :
    TerminalFourCornerCarrier coherenceSaturationSystem :=
  coherenceEmptySquare.fourCornerCarrier coherenceCandidate coherenceProjection

def coherenceConstantObserver
    (_implementation : Implementation 4 3) : TerminalProfile 2 :=
  fun _coordinate => false

def coherenceProfileObserver
    (implementation : Implementation 4 3) : TerminalProfile 2 :=
  fun _coordinate => implementation.candidate.semantics
    (fun _input => false) coherenceGate0

def coherenceModeObserver
    (implementation : Implementation 4 3) : TerminalProfile 2 :=
  fun coordinate =>
    if coordinate.val = 0 then false
    else implementation.candidate.semantics
      (fun _input => true) coherenceGate1

example : allTerminalOptimumSquareLegs =
    [.meetLeft, .meetRight, .leftJoin, .rightJoin] := rfl

example (leg : TerminalOptimumSquareLeg) :
    TerminalRawSupport.Subset
      (fun record => record ∈ coherenceCarrier.square.records leg.source)
      (fun record => record ∈ coherenceCarrier.square.records leg.target) :=
  (coherenceCarrier.optimumLegTransport leg).recordsSubset

example (leg : TerminalOptimumSquareLeg) (role : TerminalProfileRole)
    (coordinate : Fin 2)
    (member : coordinate ∈
      (coherenceCarrier.support leg.source).frontier.profiles role) :
    coordinate ∈
      (coherenceCarrier.support leg.target).frontier.profiles role :=
  (coherenceCarrier.optimumLegTransport leg).profileTransport
    role coordinate member

example :
    (coherenceCarrier.optimumLegTransport .leftJoin).OutputInternalized
      ⟨0, by decide⟩ := by rfl

example :
    (coherenceCarrier.optimumLegTransport .rightJoin).retainedOutput?
      ⟨0, by decide⟩ = some ⟨0, by decide⟩ := by decide

example (coordinate : Fin 4) :
    (coherenceCarrier.optimumLegTransport .leftJoin).ambientCoordinate
        ((coherenceCarrier.optimumLegTransport .meetLeft).ambientCoordinate
          coordinate) =
      (coherenceCarrier.optimumLegTransport .rightJoin).ambientCoordinate
        ((coherenceCarrier.optimumLegTransport .meetRight).ambientCoordinate
          coordinate) :=
  coherenceCarrier.optimumTransportTheta coordinate

example : coherenceEmptyCarrier.firstOptimumCoherenceFailure?
    coherenceConstantObserver .full = none := by decide

example : coherenceEmptyCarrier.firstOptimumCoherenceFailure?
    coherenceConstantObserver .quotient = none := by decide

example : Nonempty (TerminalFourCornerCoherentOptimumTuple
    coherenceEmptyCarrier coherenceConstantObserver .full) :=
  (coherenceEmptyCarrier.noFailure_iff_coherentOptimumTuple
    coherenceConstantObserver .full).1 (by decide)

example : Nonempty (TerminalFourCornerCoherentOptimumTuple
    coherenceEmptyCarrier coherenceConstantObserver .quotient) :=
  (coherenceEmptyCarrier.noFailure_iff_coherentOptimumTuple
    coherenceConstantObserver .quotient).1 (by decide)

example : match coherenceEmptyCarrier.classifyOptimumCoherence
    coherenceConstantObserver .full with
  | .coherent _tuple => True
  | .failure _reason _first => False := by exact True.intro

example : match coherenceCarrier.firstOptimumCoherenceFailure?
    coherenceConstantObserver .full with
  | some (.semanticMismatch _leg _input _producer _source _target) => True
  | _ => False := by exact True.intro

example : match coherenceCarrier.firstOptimumCoherenceFailure?
    coherenceProfileObserver .full with
  | some (.profileMismatch .meetLeft .origin coordinate false true) =>
      coordinate = coherenceProfile0
  | _ => False := by rfl

example : match coherenceCarrier.firstOptimumModeMismatch?
    coherenceModeObserver with
  | some (.modeMismatch .rightJoin .charge coordinate false true) =>
      coordinate = coherenceProfile1
  | _ => False := by rfl

def coherenceObligationProfileSystem : TerminalProfileSystem 1 1 1 :=
  { role := fun _coordinate => .obligation
    observe := fun _implementation _coordinate => false }

def coherenceObligationSystem : TerminalSaturationSystem 1 3 1 1 :=
  { profileSystem := coherenceObligationProfileSystem
    requires := fun _kind _dependent _required => false }

def coherenceObligationSquare :
    TerminalSaturatedSupportSquare coherenceObligationSystem :=
  terminalSaturatedSupportSquare coherenceObligationSystem [] []

def coherenceObligationCarrier :
    TerminalFourCornerCarrier coherenceObligationSystem :=
  coherenceObligationSquare.fourCornerCarrier coherenceCandidate
    { keep := fun _coordinate => true }

def coherenceOpenObserver
    (_implementation : Implementation 4 3) : TerminalProfile 1 :=
  fun _coordinate => true

example : coherenceObligationCarrier.firstOptimumCoherenceFailure?
    coherenceOpenObserver .full =
      some (.openObligation .meet ⟨0, by decide⟩ true) := by rfl

example : match coherenceObligationCarrier.classifyOptimumCoherence
    coherenceOpenObserver .full with
  | .failure (.openObligation .meet _coordinate true) _first => True
  | _ => False := by exact True.intro

def coherenceChargeProfileSystem : TerminalProfileSystem 1 1 2 :=
  { role := fun _coordinate => .charge
    observe := fun _implementation _coordinate => false }

def coherenceChargeSystem : TerminalSaturationSystem 1 3 1 2 :=
  { profileSystem := coherenceChargeProfileSystem
    requires := fun _kind _dependent _required => false }

def coherenceChargeSquare :
    TerminalSaturatedSupportSquare coherenceChargeSystem :=
  terminalSaturatedSupportSquare coherenceChargeSystem
    [.gate coherenceGate0, .profile coherenceProfile0]
    [.gate coherenceGate1, .profile coherenceProfile0,
      .profile coherenceProfile1]

def coherenceChargeCarrier : TerminalFourCornerCarrier coherenceChargeSystem :=
  coherenceChargeSquare.fourCornerCarrier coherenceCandidate coherenceProjection

example : match coherenceChargeCarrier.firstOptimumCoherenceFailure?
    coherenceProfileObserver .full with
  | some (.chargeProfileMismatch .meetLeft coordinate false true) =>
      coordinate = coherenceProfile0
  | _ => False := by rfl

example (mode : TerminalOptimumCoherenceMode) :
    Nonempty (TerminalFourCornerCoherentOptimumTuple
        coherenceCarrier coherenceConstantObserver mode) ∨
      ∃ failure,
        coherenceCarrier.firstOptimumCoherenceFailure?
            coherenceConstantObserver mode = some failure ∧
          failure.Sound :=
  coherenceCarrier.fourCornerOptimumCoherenceDichotomy
    coherenceConstantObserver mode

example (tuple : TerminalFourCornerCoherentOptimumTuple
    coherenceEmptyCarrier coherenceConstantObserver .full) :
    (coherenceEmptyCarrier.canonicalOptimumFamily
      coherenceConstantObserver).fullBasis.sizes =
        (coherenceEmptyCarrier.optimizationCorners
          coherenceConstantObserver).fullMinimumSizes :=
  tuple.fullSizes

example (tuple : TerminalFourCornerCoherentOptimumTuple
    coherenceEmptyCarrier coherenceConstantObserver .quotient) :
    (coherenceEmptyCarrier.canonicalOptimumFamily
      coherenceConstantObserver).quotientBasis.sizes.tightValue?
        (coherenceEmptyCarrier.optimizationCorners
          coherenceConstantObserver).quotientMinimumSizes =
      some (coherenceEmptyCarrier.optimizationCorners
        coherenceConstantObserver).quotientDelta :=
  tuple.quotientIncidenceValue

end DirectWire
end PNP
