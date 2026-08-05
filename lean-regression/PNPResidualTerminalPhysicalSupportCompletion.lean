import PNP.ResidualTerminalPhysicalSupportCompletion

namespace PNP
namespace DirectWire

abbrev physicalSupportRecord := TerminalPrimitiveRecord 2 3 1 0

def physicalSupportInput0 : Fin 2 := ⟨0, by decide⟩
def physicalSupportInput1 : Fin 2 := ⟨1, by decide⟩
def physicalSupportGate0 : Fin 3 := ⟨0, by decide⟩
def physicalSupportGate1 : Fin 3 := ⟨1, by decide⟩
def physicalSupportGate2 : Fin 3 := ⟨2, by decide⟩

def physicalSupportProgram0 : Program 2 1 :=
  .snoc .empty
    { left := .input physicalSupportInput0
      right := .constant true }

def physicalSupportProgram1 : Program 2 2 :=
  .snoc physicalSupportProgram0
    { left := .gate ⟨0, by decide⟩
      right := .input physicalSupportInput1 }

def physicalSupportProgram : Program 2 3 :=
  .snoc physicalSupportProgram1
    { left := .gate ⟨1, by decide⟩
      right := .gate ⟨0, by decide⟩ }

def physicalSupportWord : DirectWireWord 2 3 1 :=
  ⟨fun _output => .gate physicalSupportGate2⟩

def physicalSupportCandidate : Candidate 2 3 1 :=
  Candidate.ofDirectWireWord physicalSupportProgram physicalSupportWord

def physicalSupportProfileSystem : TerminalProfileSystem 2 1 0 :=
  { role := fun coordinate => Fin.elim0 coordinate
    observe := fun _implementation coordinate => Fin.elim0 coordinate }

/-- Saturating gate one adds gate two.  Gate zero remains deliberately
    unrelated, so exactness and boundary extraction can both detect overreach. -/
def physicalSupportSaturationSystem : TerminalSaturationSystem 2 3 1 0 :=
  { profileSystem := physicalSupportProfileSystem
    requires := fun kind dependent required =>
      match kind with
      | .gateSource => decide (
          dependent = TerminalPrimitiveRecord.gate physicalSupportGate1 ∧
            required = TerminalPrimitiveRecord.gate physicalSupportGate2)
      | _ => false }

def physicalSupportGate1Record : physicalSupportRecord :=
  .gate physicalSupportGate1

def physicalSupportGate2Record : physicalSupportRecord :=
  .gate physicalSupportGate2

def physicalSupportGate0Record : physicalSupportRecord :=
  .gate physicalSupportGate0

example : allTerminalSaturationRuleKinds.length = 10 := by decide

example : terminalSaturateRecords physicalSupportSaturationSystem [] = [] := by
  decide

/-- Duplicate and scrambled input records normalize to one deterministic
    visitation result. -/
example :
    terminalSaturateRecords physicalSupportSaturationSystem
        [physicalSupportGate2Record, physicalSupportGate1Record,
          physicalSupportGate2Record] =
      [physicalSupportGate2Record, physicalSupportGate1Record] := by
  decide

/-- The work list follows the dependency and excludes the unrelated gate. -/
example :
    terminalSaturateRecords physicalSupportSaturationSystem
        [physicalSupportGate1Record, physicalSupportGate1Record] =
      [physicalSupportGate2Record, physicalSupportGate1Record] := by
  decide

example :
    physicalSupportGate0Record ∉
      terminalSaturateRecords physicalSupportSaturationSystem
        [physicalSupportGate1Record] := by
  decide

example :
    terminalSaturate physicalSupportSaturationSystem
      (fun record => record ∈ [physicalSupportGate1Record])
      physicalSupportGate2Record :=
  (mem_terminalSaturateRecords_iff physicalSupportSaturationSystem
    [physicalSupportGate1Record] physicalSupportGate2Record).1 (by decide)

def physicalSupportGate1Only : List physicalSupportRecord :=
  [physicalSupportGate1Record]

def physicalSupportAllGates : List physicalSupportRecord :=
  [physicalSupportGate0Record, physicalSupportGate1Record,
    physicalSupportGate2Record]

/-- Gate one receives primary input one and gate zero.  Its constant-free
    physical boundary is in canonical input-then-gate order. -/
example :
    terminalBoundaryPorts physicalSupportProgram physicalSupportGate1Only =
      [.input physicalSupportInput1, .gate physicalSupportGate0] := by
  decide

/-- Gate one is exposed when its gate-two consumer remains outside. -/
example :
    terminalInterfacePorts physicalSupportCandidate physicalSupportGate1Only =
      [physicalSupportGate1] := by
  decide

example :
    terminalBoundaryPorts physicalSupportProgram ([] : List physicalSupportRecord) =
      [] := by
  decide

example :
    terminalInterfacePorts physicalSupportCandidate
        ([] : List physicalSupportRecord) = [] := by
  decide

/-- Selecting every gate exposes both primary inputs, omits the local
    constant, and retains only the global output gate as an interface. -/
example :
    terminalBoundaryPorts physicalSupportProgram physicalSupportAllGates =
      [.input physicalSupportInput0, .input physicalSupportInput1] := by
  decide

example :
    terminalInterfacePorts physicalSupportCandidate physicalSupportAllGates =
      [physicalSupportGate2] := by
  decide

/-- The composed constructor uses the saturated gate-one/gate-two support.
    Gate zero and input one cross inward; gate two crosses outward as the
    candidate's global output. -/
example :
    (completeSaturatedTerminalPhysicalSupport physicalSupportCandidate
      physicalSupportSaturationSystem [physicalSupportGate1Record]).boundary =
      [.input physicalSupportInput1, .gate physicalSupportGate0] := by
  decide

example :
    (completeSaturatedTerminalPhysicalSupport physicalSupportCandidate
      physicalSupportSaturationSystem [physicalSupportGate1Record]).interface =
      [physicalSupportGate2] := by
  decide

example :
    (completeSaturatedTerminalPhysicalSupport physicalSupportCandidate
      physicalSupportSaturationSystem
        [physicalSupportGate1Record]).Compatible :=
  completeSaturatedTerminalPhysicalSupport_compatible
    physicalSupportCandidate physicalSupportSaturationSystem
      [physicalSupportGate1Record]

/-! A cycle is visited once per record and terminates within the finite fuel. -/

def physicalSupportCycleProfileSystem : TerminalProfileSystem 0 0 2 :=
  { role := fun _coordinate => .saturation
    observe := fun _implementation _coordinate => false }

def physicalSupportCycleFirst : TerminalPrimitiveRecord 0 0 0 2 :=
  .profile ⟨0, by decide⟩

def physicalSupportCycleSecond : TerminalPrimitiveRecord 0 0 0 2 :=
  .profile ⟨1, by decide⟩

def physicalSupportCycleSystem : TerminalSaturationSystem 0 0 0 2 :=
  { profileSystem := physicalSupportCycleProfileSystem
    requires := fun kind dependent required =>
      match kind with
      | .saturation => decide (
          (dependent = physicalSupportCycleFirst ∧
            required = physicalSupportCycleSecond) ∨
          (dependent = physicalSupportCycleSecond ∧
            required = physicalSupportCycleFirst))
      | _ => false }

example :
    terminalSaturateRecords physicalSupportCycleSystem
        [physicalSupportCycleFirst] =
      [physicalSupportCycleSecond, physicalSupportCycleFirst] := by
  decide

end DirectWire
end PNP
