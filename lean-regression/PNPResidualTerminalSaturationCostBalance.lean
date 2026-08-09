import PNP.ResidualTerminalSaturationCostBalance

namespace PNP
namespace DirectWire

abbrev derivedBalanceRecord := TerminalPrimitiveRecord 1 1 1 1

def derivedBalanceInput : Fin 1 := ⟨0, by decide⟩
def derivedBalanceGate : Fin 1 := ⟨0, by decide⟩
def derivedBalanceOutput : Fin 1 := ⟨0, by decide⟩
def derivedBalanceProfile : Fin 1 := ⟨0, by decide⟩

def derivedBalanceProgram : Program 1 1 :=
  .snoc .empty
    { left := .input derivedBalanceInput
      right := .input derivedBalanceInput }

def derivedBalanceWord : DirectWireWord 1 1 1 :=
  ⟨fun _output => .gate derivedBalanceGate⟩

def derivedBalanceCandidate : Candidate 1 1 1 :=
  Candidate.ofDirectWireWord derivedBalanceProgram derivedBalanceWord

def derivedBalanceProfileSystem : TerminalProfileSystem 1 1 1 :=
  { role := fun _coordinate => .carrier
    observe := fun _implementation _coordinate => false }

def derivedBalanceProjection : TerminalProfileProjection 1 :=
  { keep := fun _coordinate => false }

/-- The ambient observer makes the single carrier coordinate depend on
    whether a materializer gate is present. -/
def derivedBalanceModel :
    TerminalCandidateSaturationModel (profileWidth := 1)
      derivedBalanceCandidate :=
  { profileSystem := derivedBalanceProfileSystem
    projection := derivedBalanceProjection
    observe := fun implementation _coordinate =>
      decide (0 < implementation.gateCount) }

def derivedBalanceGateRecord : derivedBalanceRecord :=
  .gate derivedBalanceGate
def derivedBalanceBoundaryRecord : derivedBalanceRecord :=
  .boundary derivedBalanceInput
def derivedBalanceInterfaceRecord : derivedBalanceRecord :=
  .interface derivedBalanceOutput
def derivedBalanceProfileRecord : derivedBalanceRecord :=
  .profile derivedBalanceProfile

def derivedBalanceSystem : TerminalSaturationSystem 1 1 1 1 :=
  terminalCandidateSaturationSystem derivedBalanceCandidate derivedBalanceModel

/-! Physical and profile edges are all extracted, not supplied. -/

example : derivedBalanceSystem.requires .interfaceConsumer
    derivedBalanceInterfaceRecord derivedBalanceGateRecord = true := by
  decide

example : derivedBalanceSystem.requires .interfaceConsumer
    derivedBalanceGateRecord derivedBalanceInterfaceRecord = true := by
  decide

example : derivedBalanceSystem.requires .gateSource
    derivedBalanceGateRecord derivedBalanceBoundaryRecord = true := by
  decide

example : terminalGateInfluencesProfile derivedBalanceCandidate
    derivedBalanceModel derivedBalanceGate derivedBalanceProfile = true := by
  decide

example : derivedBalanceSystem.requires .gateSource
    derivedBalanceGateRecord derivedBalanceProfileRecord = true := by
  decide

/-! The trace retains the first deterministic rule and the existing exact
    saturation order. -/

def derivedBalanceTrace := terminalSaturateTrace derivedBalanceSystem
  [derivedBalanceInterfaceRecord]

example : derivedBalanceTrace.events.map (fun event => event.required) =
    [derivedBalanceGateRecord, derivedBalanceBoundaryRecord,
      derivedBalanceProfileRecord] := by
  decide

example : derivedBalanceTrace.events.map (fun event => event.kind?) =
    [some .interfaceConsumer, some .gateSource, some .gateSource] := by
  decide

example : derivedBalanceTrace.records =
    [derivedBalanceProfileRecord, derivedBalanceBoundaryRecord,
      derivedBalanceGateRecord, derivedBalanceInterfaceRecord] := by
  decide

example : derivedBalanceTrace.replayRecords = derivedBalanceTrace.records := by
  decide

/-! A genuine unit-cost materializer passes all three exact cost checks. -/

def derivedBalanceGateEvent : TerminalSaturationTraceEvent 1 1 1 1 :=
  { kind? := some .interfaceConsumer
    dependent := derivedBalanceInterfaceRecord
    required := derivedBalanceGateRecord
    beforeRecords := [derivedBalanceInterfaceRecord]
    afterRecords := [derivedBalanceGateRecord, derivedBalanceInterfaceRecord] }

example :
    (terminalSaturationCostSnapshot derivedBalanceCandidate
      derivedBalanceModel derivedBalanceGateEvent.beforeRecords).supportSize = 0 := by
  decide

example :
    (terminalSaturationCostSnapshot derivedBalanceCandidate
      derivedBalanceModel derivedBalanceGateEvent.afterRecords).supportSize = 1 := by
  decide

example :
    (terminalSaturationCostSnapshot derivedBalanceCandidate
      derivedBalanceModel derivedBalanceGateEvent.afterRecords).fullMinimum = 1 := by
  decide

example : terminalSaturationStepTransparentBool derivedBalanceCandidate
    derivedBalanceModel derivedBalanceGateEvent = true := by
  decide

/-! Metadata-only completion is checked as an exact zero-cost event. -/

def derivedBalanceBoundaryEvent : TerminalSaturationTraceEvent 1 1 1 1 :=
  { kind? := some .gateSource
    dependent := derivedBalanceGateRecord
    required := derivedBalanceBoundaryRecord
    beforeRecords := [derivedBalanceGateRecord, derivedBalanceInterfaceRecord]
    afterRecords := [derivedBalanceBoundaryRecord, derivedBalanceGateRecord,
      derivedBalanceInterfaceRecord] }

example : terminalSaturationStepTransparentBool derivedBalanceCandidate
    derivedBalanceModel derivedBalanceBoundaryEvent = true := by
  decide

/-! Two active owners fail closed at the exact gate event. -/

def derivedBalanceMultipleOwnerEvent :
    TerminalSaturationTraceEvent 1 1 1 1 :=
  { kind? := some .interfaceConsumer
    dependent := derivedBalanceInterfaceRecord
    required := derivedBalanceGateRecord
    beforeRecords :=
      [derivedBalanceProfileRecord, derivedBalanceInterfaceRecord]
    afterRecords := [derivedBalanceGateRecord, derivedBalanceProfileRecord,
      derivedBalanceInterfaceRecord] }

example : (terminalSaturationEventOwners derivedBalanceSystem
    derivedBalanceMultipleOwnerEvent).length = 2 := by
  decide

example : terminalSaturationStepFailureReason? derivedBalanceCandidate
    derivedBalanceModel derivedBalanceMultipleOwnerEvent =
      some .nonuniqueMaterializerOwner := by
  decide

/-! The complete single-owner trace is balanced; adding the profile seed
    records the gate as the first nontransparent event with an empty prefix. -/

example : terminalSaturationBalanceBalancedBool derivedBalanceCandidate
    derivedBalanceModel [derivedBalanceInterfaceRecord] = true := by
  decide

example : terminalSaturationBalanceFirstFailure? derivedBalanceCandidate
    derivedBalanceModel
      [derivedBalanceInterfaceRecord, derivedBalanceProfileRecord] =
        some (derivedBalanceGateRecord, .nonuniqueMaterializerOwner) := by
  decide

end DirectWire
end PNP
