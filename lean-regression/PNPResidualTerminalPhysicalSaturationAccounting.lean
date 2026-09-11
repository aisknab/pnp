/-
General applications of all five M235 interfaces and adversarial actual-execution
fixtures. Concrete cases are regression guards, not milestone proof substitutes.
-/
import PNP.ResidualTerminalPhysicalSaturationAccounting

open PNP PNP.DirectWire

example
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (event : TerminalSaturationTraceEvent inputs gates outputs profileWidth)
    (member : event ∈ (terminalSaturateTrace system seed).events) :
    event.dependent ∈ event.beforeRecords ∧ event.required ∉ event.beforeRecords :=
  terminalSaturateTrace_event_context system seed event member

example
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (event : TerminalSaturationTraceEvent inputs gates outputs profileWidth)
    (member : event ∈ (terminalSaturateTrace
      (terminalCandidateSaturationSystem candidate model) seed).events) :
    (terminalSaturationCostSnapshot candidate model event.afterRecords).supportSize =
      (terminalSaturationCostSnapshot candidate model event.beforeRecords).supportSize +
        terminalSaturationEventCost event :=
  terminalCandidateSaturateTrace_supportCostBalanced candidate model seed event member

example
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (event : TerminalSaturationTraceEvent inputs gates outputs profileWidth)
    (member : event ∈ (terminalSaturateTrace
      (terminalCandidateSaturationSystem candidate model) seed).events) :
    ∃ kind, event.kind? = some kind ∧
      (kind, event.dependent) ∈ terminalSaturationEventOwners
        (terminalCandidateSaturationSystem candidate model) event :=
  terminalCandidateSaturateTrace_event_owner candidate model seed event member

example
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (event : TerminalSaturationTraceEvent inputs gates outputs profileWidth)
    (member : event ∈ (terminalSaturateTrace
      (terminalCandidateSaturationSystem candidate model) seed).events)
    (failure : ¬TerminalTransparentSaturationStep candidate model event) :
    ∃ gate, event.required = TerminalPrimitiveRecord.gate gate ∧
      ((terminalSaturationEventOwners
          (terminalCandidateSaturationSystem candidate model) event).length ≠ 1 ∨
        (terminalSaturationCostSnapshot candidate model event.afterRecords).fullMinimum ≠
          (terminalSaturationCostSnapshot candidate model event.beforeRecords).fullMinimum + 1 ∨
        (terminalSaturationCostSnapshot candidate model event.beforeRecords).quotientMinimum + 1 <
          (terminalSaturationCostSnapshot candidate model event.afterRecords).quotientMinimum) :=
  terminalCandidateSaturateTrace_physicalObstruction candidate model seed event member failure

example
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    ((terminalSaturationCostSnapshot candidate model
        (terminalSaturateRecords
          (terminalCandidateSaturationSystem candidate model) seed)).fullSlack =
        (terminalSaturationCostSnapshot candidate model
          (terminalSaturateTrace
            (terminalCandidateSaturationSystem candidate model) seed).normalizedSeed.reverse).fullSlack ∧
      (terminalSaturationCostSnapshot candidate model
        (terminalSaturateTrace
          (terminalCandidateSaturationSystem candidate model) seed).normalizedSeed.reverse).projectionDefect ≤
        (terminalSaturationCostSnapshot candidate model
          (terminalSaturateRecords
            (terminalCandidateSaturationSystem candidate model) seed)).projectionDefect) ∨
    ∃ first : TerminalFirstNontransparentSaturationStep candidate model
        (terminalSaturateTrace
          (terminalCandidateSaturationSystem candidate model) seed).events,
      classifyTerminalSaturationBalance candidate model seed = .firstNontransparent first ∧
        ∃ gate, first.event.required = TerminalPrimitiveRecord.gate gate ∧
          ((terminalSaturationEventOwners
              (terminalCandidateSaturationSystem candidate model) first.event).length ≠ 1 ∨
            (terminalSaturationCostSnapshot candidate model first.event.afterRecords).fullMinimum ≠
              (terminalSaturationCostSnapshot candidate model first.event.beforeRecords).fullMinimum + 1 ∨
            (terminalSaturationCostSnapshot candidate model first.event.beforeRecords).quotientMinimum + 1 <
              (terminalSaturationCostSnapshot candidate model first.event.afterRecords).quotientMinimum) :=
  terminalCandidateSaturateTrace_balance_or_physicalObstruction candidate model seed

namespace TerminalPhysicalSaturationAccountingRegression

def gateZero : Fin 1 := ⟨0, by decide⟩
def outputZero : Fin 2 := ⟨0, by decide⟩
def outputOne : Fin 2 := ⟨1, by decide⟩

def candidate : Candidate 0 1 2 :=
  Candidate.ofDirectWireWord
    (.snoc .empty { left := .constant false, right := .constant false })
    ⟨fun _ => .gate gateZero⟩

def model : TerminalCandidateSaturationModel (profileWidth := 0) candidate :=
  { profileSystem := { role := Fin.elim0, observe := fun _ => Fin.elim0 }
    projection := { keep := Fin.elim0 }
    observe := fun _ => Fin.elim0 }

abbrev Record := TerminalPrimitiveRecord 0 1 2 0
abbrev Event := TerminalSaturationTraceEvent 0 1 2 0

def gateRecord : Record := .gate gateZero
def firstInterface : Record := .interface outputZero
def secondInterface : Record := .interface outputOne
def system := terminalCandidateSaturationSystem candidate model
def pairSeed : List Record := [firstInterface, secondInterface]
def pairTrace := terminalSaturateTrace system pairSeed

def pairGateEvent : Event :=
  { kind? := some .interfaceConsumer
    dependent := firstInterface
    required := gateRecord
    beforeRecords := [secondInterface, firstInterface]
    afterRecords := [gateRecord, secondInterface, firstInterface] }

example : pairTrace.events = [pairGateEvent] := by decide

/- Both required output records are active before their shared physical gate.
   There is one insertion but two actual dependency owners. -/
example : terminalSaturationEventOwners system pairGateEvent =
    [(.interfaceConsumer, secondInterface), (.interfaceConsumer, firstInterface)] := by
  decide

example : pairGateEvent.dependent ∈ pairGateEvent.beforeRecords ∧
    pairGateEvent.required ∉ pairGateEvent.beforeRecords :=
  terminalSaturateTrace_event_context system pairSeed pairGateEvent (by decide)

example :
    (terminalSaturationCostSnapshot candidate model pairGateEvent.afterRecords).supportSize =
      (terminalSaturationCostSnapshot candidate model pairGateEvent.beforeRecords).supportSize + 1 :=
  terminalCandidateSaturateTrace_supportCostBalanced
    candidate model pairSeed pairGateEvent (by decide)

example : terminalSaturationBalanceFirstFailure? candidate model pairSeed =
    some (gateRecord, .nonuniqueMaterializerOwner) := by decide

/- Duplicate seed records do not create another insertion or another owner. -/
example : (terminalSaturateTrace system
    [firstInterface, secondInterface, firstInterface, secondInterface]).events =
      pairTrace.events := by decide

example : (terminalSaturateTrace system []).events = [] := by decide

/- Even one active owner and exact unit support growth need not force one
   extra full-minimum gate. This checks the distinct minimum-cost branch. -/
example : terminalSaturationBalanceFirstFailure? candidate model [firstInterface] =
    some (gateRecord, .fullCostMismatch) := by decide

/- An apparently rule-labelled raw event with a missing active dependent is
   not generated. The new theorem, not an assumed provenance flag, rejects it. -/
def missingDependentEvent : Event :=
  { pairGateEvent with beforeRecords := [], afterRecords := [gateRecord] }

example : missingDependentEvent ∉ pairTrace.events := by
  intro member
  have active := (terminalSaturateTrace_event_context
    system pairSeed missingDependentEvent member).1
  change firstInterface ∈ [] at active
  cases active

/- The shape "required :: before" alone does not establish freshness. -/
def alreadyPresentEvent : Event :=
  { pairGateEvent with
    beforeRecords := gateRecord :: pairGateEvent.beforeRecords
    afterRecords := gateRecord :: gateRecord :: pairGateEvent.beforeRecords }

example : alreadyPresentEvent ∉ pairTrace.events := by
  intro member
  have fresh := (terminalSaturateTrace_event_context
    system pairSeed alreadyPresentEvent member).2
  apply fresh
  exact List.Mem.head _

end TerminalPhysicalSaturationAccountingRegression

/-
The unchanged M234 regression also exercises cyclic dependencies, every metadata
constructor, nonconstant observers and an open obligation that cost balance
does not discharge. Keep that regression in the durable root verification.
-/
