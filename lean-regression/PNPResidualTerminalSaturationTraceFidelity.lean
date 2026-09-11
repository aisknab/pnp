/-
Generic theorem applications and adversarial execution fixtures. The fixtures
exercise, but do not replace, the arbitrary-dimension trace-fidelity theorems.
-/
import PNP.ResidualTerminalSaturationTraceFidelity
import PNP.ResidualTerminalOriginKernelObligationRouting

open PNP PNP.DirectWire

section
variable {inputs gates outputs profileWidth : Nat}
variable (system : TerminalSaturationSystem inputs gates outputs profileWidth)
variable (candidate : Candidate inputs gates outputs)
variable (model : TerminalCandidateSaturationModel
  (profileWidth := profileWidth) candidate)
variable (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))

example (record : TerminalPrimitiveRecord inputs gates outputs profileWidth) :
    record ∈ (terminalSaturateTrace system seed).replayRecords ↔
      record ∈ terminalSaturateRecords system seed :=
  terminalSaturateTrace_replayRecords_iff system seed record

example (event : TerminalSaturationTraceEvent inputs gates outputs profileWidth)
    (member : event ∈ (terminalSaturateTrace system seed).events) :
    event.afterRecords = event.required :: event.beforeRecords ∧
      ∃ kind, event.kind? = some kind ∧
        system.requires kind event.dependent event.required = true :=
  terminalSaturateTrace_event_valid system seed event member

example :
    terminalAmbientSupportImplementation candidate
        (terminalSaturateTrace
          (terminalCandidateSaturationSystem candidate model) seed).replayRecords =
      terminalAmbientSupportImplementation candidate
        (terminalSaturateRecords
          (terminalCandidateSaturationSystem candidate model) seed) :=
  terminalCandidateSaturateTrace_ambient_eq candidate model seed

example :
    terminalSaturationCostSnapshot candidate model
        (terminalSaturateTrace
          (terminalCandidateSaturationSystem candidate model) seed).replayRecords =
      { terminalSaturationCostSnapshot candidate model
          (terminalSaturateRecords
            (terminalCandidateSaturationSystem candidate model) seed) with
        records := (terminalSaturateTrace
          (terminalCandidateSaturationSystem candidate model) seed).replayRecords } :=
  terminalCandidateSaturateTrace_costSnapshot_eq candidate model seed

example (event : TerminalSaturationTraceEvent inputs gates outputs profileWidth)
    (member : event ∈ (terminalSaturateTrace
      (terminalCandidateSaturationSystem candidate model) seed).events)
    (metadata : ∀ gate, event.required ≠ TerminalPrimitiveRecord.gate gate) :
    TerminalTransparentSaturationStep candidate model event :=
  terminalCandidateSaturateTrace_metadata_transparent
    candidate model seed event member metadata
end

namespace TerminalSaturationTraceFidelityRegression

def zero : Fin 1 := ⟨0, by decide⟩
abbrev Record := TerminalPrimitiveRecord 1 1 1 1
abbrev Event := TerminalSaturationTraceEvent 1 1 1 1

def candidate : Candidate 1 1 1 :=
  Candidate.ofDirectWireWord
    (.snoc .empty { left := .input zero, right := .input zero })
    ⟨fun _ => .gate zero⟩

/-- Read the actual NAND output at a fixed ambient input. The observer is
    nonconstant over support implementations; the profile is an obligation. -/
def model : TerminalCandidateSaturationModel (profileWidth := 1) candidate :=
  { profileSystem := { role := fun _ => .obligation, observe := fun _ _ => false }
    projection := { keep := fun _ => false }
    observe := fun implementation _ =>
      implementation.candidate.semantics (fun _ => false) zero }

def system := terminalCandidateSaturationSystem candidate model
def gateRecord : Record := .gate zero
def boundaryRecord : Record := .boundary zero
def interfaceRecord : Record := .interface zero
def profileRecord : Record := .profile zero
def seed : List Record := [gateRecord]
def trace := terminalSaturateTrace system seed

example : terminalCandidateProfileObservation candidate model [] zero = false ∧
    terminalCandidateProfileObservation candidate model [zero] zero = true := by
  decide

/-! Empty and duplicate seeds retain the deterministic normalized execution. -/

example : (terminalSaturateTrace system []).events = [] ∧
    (terminalSaturateTrace system []).replayRecords = [] := by
  decide

example : (terminalSaturateTrace system [gateRecord, gateRecord]).events = trace.events ∧
    (terminalSaturateTrace system [gateRecord, gateRecord]).replayRecords =
      trace.replayRecords := by
  decide

/-! All three non-gate constructors occur as actual generated events. -/

def boundaryEvent : Event :=
  { kind? := some .gateSource
    dependent := gateRecord
    required := boundaryRecord
    beforeRecords := [gateRecord]
    afterRecords := [boundaryRecord, gateRecord] }

def interfaceEvent : Event :=
  { kind? := some .interfaceConsumer
    dependent := gateRecord
    required := interfaceRecord
    beforeRecords := [boundaryRecord, gateRecord]
    afterRecords := [interfaceRecord, boundaryRecord, gateRecord] }

def profileEvent : Event :=
  { kind? := some .obligation
    dependent := gateRecord
    required := profileRecord
    beforeRecords := [interfaceRecord, boundaryRecord, gateRecord]
    afterRecords := [profileRecord, interfaceRecord, boundaryRecord, gateRecord] }

example : trace.events = [boundaryEvent, interfaceEvent, profileEvent] := by
  decide

example : TerminalTransparentSaturationStep candidate model boundaryEvent :=
  terminalCandidateSaturateTrace_metadata_transparent
    candidate model seed boundaryEvent (by decide) (by decide)

example : TerminalTransparentSaturationStep candidate model interfaceEvent :=
  terminalCandidateSaturateTrace_metadata_transparent
    candidate model seed interfaceEvent (by decide) (by decide)

example : TerminalTransparentSaturationStep candidate model profileEvent :=
  terminalCandidateSaturateTrace_metadata_transparent
    candidate model seed profileEvent (by decide) (by decide)

/-! Malformed raw events cannot stand in for generated-event membership. -/

def missingRuleEvent : Event := { boundaryEvent with kind? := none }
def unrelatedAfterEvent : Event := { boundaryEvent with afterRecords := [boundaryRecord] }
def wrongRuleEvent : Event := { boundaryEvent with kind? := some .origin }

example : missingRuleEvent ∉ trace.events ∧
    unrelatedAfterEvent ∉ trace.events ∧ wrongRuleEvent ∉ trace.events := by
  decide

example : terminalSaturationStepTransparentBool candidate model missingRuleEvent = false ∧
    terminalSaturationStepTransparentBool candidate model unrelatedAfterEvent = false := by
  decide

example : system.requires .origin wrongRuleEvent.dependent wrongRuleEvent.required = false := by
  decide

/-! A generated gate is not covered by the metadata theorem. Its actual
    output observation already has a zero-gate reference implementation. -/

def constantCandidate : Candidate 0 1 1 :=
  Candidate.ofDirectWireWord
    (.snoc .empty { left := .constant false, right := .constant false })
    ⟨fun _ => .gate zero⟩

def constantModel :
    TerminalCandidateSaturationModel (profileWidth := 1) constantCandidate :=
  { profileSystem := { role := fun _ => .carrier, observe := fun _ _ => false }
    projection := { keep := fun _ => false }
    observe := fun implementation _ =>
      implementation.candidate.semantics (fun _ => false) zero }

def constantSystem := terminalCandidateSaturationSystem constantCandidate constantModel

def physicalGateEvent : TerminalSaturationTraceEvent 0 1 1 1 :=
  { kind? := some .interfaceConsumer
    dependent := .interface zero
    required := .gate zero
    beforeRecords := [.interface zero]
    afterRecords := [.gate zero, .interface zero] }

example : physicalGateEvent ∈
    (terminalSaturateTrace constantSystem [.interface zero]).events := by
  decide

example : (terminalSaturationCostSnapshot constantCandidate constantModel
      physicalGateEvent.beforeRecords).supportSize = 0 ∧
    (terminalSaturationCostSnapshot constantCandidate constantModel
      physicalGateEvent.afterRecords).supportSize = 1 ∧
    (terminalSaturationCostSnapshot constantCandidate constantModel
      physicalGateEvent.beforeRecords).fullMinimum = 0 ∧
    (terminalSaturationCostSnapshot constantCandidate constantModel
      physicalGateEvent.afterRecords).fullMinimum = 0 := by
  decide

example : terminalSaturationStepTransparentBool
    constantCandidate constantModel physicalGateEvent = false := by
  decide

/-! Balanced metadata cost does not discharge an open obligation. -/

def obligationCoordinate : TerminalOriginKernelObligationCoordinate 1 1 :=
  { role := .obligation
    coordinate := zero
    gate := zero
    orientation := .gateRequiresProfile }

example : terminalCandidateOriginKernelObligationCoordinate?
    candidate model profileEvent = some obligationCoordinate := by
  decide

example : ¬ Nonempty (TerminalOriginKernelObligationClosureSafe
    candidate model profileEvent obligationCoordinate) := by
  rintro ⟨safe⟩
  have discharged := safe.obligationDischarged rfl
  have stillOpen : terminalOriginKernelObligationProfileValue candidate model
      profileEvent.afterRecords zero = true := by decide
  change terminalOriginKernelObligationProfileValue candidate model
    profileEvent.afterRecords zero = false at discharged
  rw [stillOpen] at discharged
  cases discharged

/-! A low-level cyclic system exercises duplicate normalization and multiple
    valid rule candidates. It is a regression relation, not supplied authority
    for the candidate-derived theorems above. -/

abbrev CycleRecord := TerminalPrimitiveRecord 0 1 0 1
def cycleGate : CycleRecord := .gate zero
def cycleProfile : CycleRecord := .profile zero

def cycleSystem : TerminalSaturationSystem 0 1 0 1 :=
  { profileSystem := { role := fun _ => .origin, observe := fun _ _ => false }
    requires := fun kind dependent required =>
      decide ((kind = .origin ∨ kind = .kernel) ∧ dependent ≠ required) }

def cycleEvent : TerminalSaturationTraceEvent 0 1 0 1 :=
  { kind? := some .origin
    dependent := cycleGate
    required := cycleProfile
    beforeRecords := [cycleGate]
    afterRecords := [cycleProfile, cycleGate] }

example : cycleSystem.requires .origin cycleGate cycleProfile = true ∧
    cycleSystem.requires .kernel cycleGate cycleProfile = true ∧
    cycleSystem.requires .origin cycleProfile cycleGate = true := by
  decide

example : (terminalSaturateTrace cycleSystem [cycleGate, cycleGate]).events =
    [cycleEvent] := by
  decide

example : cycleEvent.afterRecords = cycleEvent.required :: cycleEvent.beforeRecords ∧
    ∃ kind, cycleEvent.kind? = some kind ∧
      cycleSystem.requires kind cycleEvent.dependent cycleEvent.required = true :=
  terminalSaturateTrace_event_valid cycleSystem [cycleGate, cycleGate] cycleEvent (by decide)

example (record : CycleRecord) :
    record ∈ (terminalSaturateTrace cycleSystem [cycleGate, cycleGate]).replayRecords ↔
      record ∈ terminalSaturateRecords cycleSystem [cycleGate, cycleGate] :=
  terminalSaturateTrace_replayRecords_iff cycleSystem [cycleGate, cycleGate] record

end TerminalSaturationTraceFidelityRegression
