/- General physical-charge partition applications and hostile executable cases. -/
import PNP.ResidualTerminalPhysicalChargeLedger

open PNP PNP.DirectWire

example
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    ((terminalSaturatePhysicalCharges system seed).map TerminalPhysicalCharge.gate).Nodup :=
  terminalSaturatePhysicalCharges_nodup system seed

example
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (gate : Fin gates) :
    gate ∈ (terminalSaturatePhysicalCharges system seed).map TerminalPhysicalCharge.gate ↔
      TerminalPrimitiveRecord.gate gate ∈ terminalSaturateRecords system seed :=
  terminalSaturatePhysicalCharges_complete system seed gate

example
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (charge : TerminalPhysicalCharge inputs gates outputs profileWidth)
    (member : charge ∈ terminalSaturatePhysicalCharges system seed) :
    (charge.provenance = .seed ∧
      TerminalPrimitiveRecord.gate charge.gate ∈
        (terminalSaturateTrace system seed).normalizedSeed.reverse) ∨
    ∃ event, event ∈ (terminalSaturateTrace system seed).events ∧
      ∃ kind, charge.provenance = .generated kind event.dependent ∧
        event.required = TerminalPrimitiveRecord.gate charge.gate ∧
        event.kind? = some kind ∧
        system.requires kind event.dependent (TerminalPrimitiveRecord.gate charge.gate) = true ∧
        event.dependent ∈ event.beforeRecords ∧
        TerminalPrimitiveRecord.gate charge.gate ∉ event.beforeRecords :=
  terminalSaturatePhysicalCharges_provenance system seed charge member

example
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (gate : Fin gates)
    (provenance : TerminalPhysicalChargeProvenance inputs gates outputs profileWidth) :
    terminalSaturatePhysicalChargeProvenance? system seed gate = some provenance ↔
      (⟨gate, provenance⟩ : TerminalPhysicalCharge inputs gates outputs profileWidth) ∈
        terminalSaturatePhysicalCharges system seed :=
  terminalSaturatePhysicalChargeProvenance?_iff system seed gate provenance

example
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (terminalSaturationCostSnapshot candidate model
      (terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed)).supportSize =
      (terminalSaturatePhysicalCharges (terminalCandidateSaturationSystem candidate model) seed).length :=
  terminalCandidateSaturatePhysicalCharges_size candidate model seed

namespace TerminalPhysicalChargeLedgerRegression

def gateZero : Fin 1 := ⟨0, by decide⟩
def inputZero : Fin 2 := ⟨0, by decide⟩
def inputOne : Fin 2 := ⟨1, by decide⟩
def outputZero : Fin 2 := ⟨0, by decide⟩
def outputOne : Fin 2 := ⟨1, by decide⟩

def candidate : Candidate 2 1 2 :=
  Candidate.ofDirectWireWord
    (.snoc .empty { left := .input inputZero, right := .input inputOne })
    ⟨fun _ => .gate gateZero⟩

def model : TerminalCandidateSaturationModel (profileWidth := 0) candidate :=
  { profileSystem := { role := Fin.elim0, observe := fun _ => Fin.elim0 }
    projection := { keep := Fin.elim0 }
    observe := fun _ => Fin.elim0 }

abbrev Record := TerminalPrimitiveRecord 2 1 2 0
abbrev Event := TerminalSaturationTraceEvent 2 1 2 0

def gateRecord : Record := .gate gateZero
def firstInterface : Record := .interface outputZero
def secondInterface : Record := .interface outputOne
def system := terminalCandidateSaturationSystem candidate model
def seed : List Record := [firstInterface, secondInterface]
def event : Event :=
  { kind? := some .interfaceConsumer
    dependent := firstInterface
    required := gateRecord
    beforeRecords := [secondInterface, firstInterface]
    afterRecords := [gateRecord, secondInterface, firstInterface] }

example : event ∈ (terminalSaturateTrace system seed).events := by decide

example : (terminalSaturationEventOwners system event).length = 2 := by decide

example : (terminalSaturationCostSnapshot candidate model event.beforeRecords).supportSize = 0 := by decide
example : (terminalSaturationCostSnapshot candidate model event.afterRecords).supportSize = 1 := by decide

set_option maxRecDepth 2048 in
example : (terminalSaturationCostSnapshot candidate model event.beforeRecords).fullMinimum = 0 := by decide

set_option maxRecDepth 2048 in
example : (terminalSaturationCostSnapshot candidate model event.afterRecords).fullMinimum = 1 := by decide

set_option maxRecDepth 2048 in
example : (terminalSaturationCostSnapshot candidate model event.beforeRecords).quotientMinimum = 0 := by decide

set_option maxRecDepth 2048 in
example : (terminalSaturationCostSnapshot candidate model event.afterRecords).quotientMinimum = 1 := by decide

example : terminalSaturationBalanceFirstFailure? candidate model seed =
    some (gateRecord, .nonuniqueMaterializerOwner) := by decide


example : terminalSaturatePhysicalCharges system seed =
    [⟨gateZero, .generated .interfaceConsumer firstInterface⟩] := by decide

example : terminalSaturatePhysicalChargeProvenance? system seed gateZero =
    some (.generated .interfaceConsumer firstInterface) := by decide

example : terminalSaturatePhysicalCharges system [gateRecord, firstInterface, secondInterface] =
    [⟨gateZero, .seed⟩] := by decide

example : terminalSaturatePhysicalChargeProvenance? system [gateRecord] gateZero =
    some .seed := by decide

example : terminalSaturatePhysicalCharges system [firstInterface, secondInterface, firstInterface] =
    terminalSaturatePhysicalCharges system seed := by decide

example : terminalSaturatePhysicalCharges system [] = [] := by decide

example : terminalSaturatePhysicalChargeProvenance? system [] gateZero = none := by decide

end TerminalPhysicalChargeLedgerRegression

namespace TerminalPhysicalChargeCycleRegression

def firstGate : Fin 3 := ⟨0, by decide⟩
def secondGate : Fin 3 := ⟨1, by decide⟩
def thirdGate : Fin 3 := ⟨2, by decide⟩
def profileZero : Fin 1 := ⟨0, by decide⟩

abbrev Record := TerminalPrimitiveRecord 0 3 0 1

def cycleSystem : TerminalSaturationSystem 0 3 0 1 :=
  { profileSystem := { role := fun _ => .obligation, observe := fun _ _ => false }
    requires := fun kind dependent required =>
      match kind, dependent, required with
      | .gateSource, .gate left, .gate right =>
          decide ((left = firstGate ∧ right = secondGate) ∨
            (left = secondGate ∧ right = thirdGate) ∨
            (left = thirdGate ∧ right = firstGate))
      | .obligation, .gate gate, .profile _ => decide (gate = thirdGate)
      | .charge, .profile _, .gate gate => decide (gate = firstGate)
      | _, _, _ => false }

def seed : List Record := [.gate firstGate]
def expected : List (TerminalPhysicalCharge 0 3 0 1) :=
  [⟨firstGate, .seed⟩,
   ⟨secondGate, .generated .gateSource (.gate firstGate)⟩,
   ⟨thirdGate, .generated .gateSource (.gate secondGate)⟩]

/- The cycle is closed, two new physical gates are inserted, and the generated
   profile metadata introduces no additional physical charge. -/
example : terminalSaturatePhysicalCharges cycleSystem seed = expected := by decide
example : TerminalPrimitiveRecord.profile profileZero ∈
    terminalSaturateRecords cycleSystem seed := by decide
example : (terminalSaturateTrace cycleSystem seed).events.length = 3 := by decide
example : (terminalSaturatePhysicalCharges cycleSystem seed).length = 3 := by decide
example : terminalSaturatePhysicalCharges cycleSystem
    [.gate firstGate, .gate firstGate] = expected := by decide
example : terminalSaturatePhysicalChargeProvenance? cycleSystem seed thirdGate =
    some (.generated .gateSource (.gate secondGate)) := by decide

end TerminalPhysicalChargeCycleRegression

namespace TerminalPhysicalChargeEmptyRegression

def emptySystem : TerminalSaturationSystem 0 0 0 0 :=
  { profileSystem := { role := Fin.elim0, observe := fun _ => Fin.elim0 }
    requires := fun _ _ _ => false }

example : terminalSaturatePhysicalCharges emptySystem [] = [] := by decide

def metadataSystem : TerminalSaturationSystem 0 0 0 1 :=
  { profileSystem := { role := fun _ => .obligation, observe := fun _ _ => false }
    requires := fun _ _ _ => false }

example : terminalSaturatePhysicalCharges metadataSystem [.profile ⟨0, by decide⟩] =
    [] := by decide

end TerminalPhysicalChargeEmptyRegression
