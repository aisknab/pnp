import PNP.ResidualTerminalInterfaceExposureRouting

namespace PNP
namespace DirectWire

abbrev interfaceRouteRecord := TerminalPrimitiveRecord 1 1 1 1

def interfaceRouteInput : Fin 1 := ⟨0, by decide⟩
def interfaceRouteGate : Fin 1 := ⟨0, by decide⟩
def interfaceRouteOutput : Fin 1 := ⟨0, by decide⟩
def interfaceRouteProfile : Fin 1 := ⟨0, by decide⟩

def interfaceRouteProgram : Program 1 1 :=
  .snoc .empty
    { left := .input interfaceRouteInput
      right := .input interfaceRouteInput }

def interfaceRouteWord : DirectWireWord 1 1 1 :=
  ⟨fun _output => .gate interfaceRouteGate⟩

def interfaceRouteCandidate : Candidate 1 1 1 :=
  Candidate.ofDirectWireWord interfaceRouteProgram interfaceRouteWord

def interfaceRouteProfileSystem : TerminalProfileSystem 1 1 1 :=
  { role := fun _coordinate => .carrier
    observe := fun _implementation _coordinate => false }

def interfaceRouteProjection : TerminalProfileProjection 1 :=
  { keep := fun _coordinate => false }

def interfaceRouteModel :
    TerminalCandidateSaturationModel (profileWidth := 1)
      interfaceRouteCandidate :=
  { profileSystem := interfaceRouteProfileSystem
    projection := interfaceRouteProjection
    observe := fun implementation _coordinate =>
      decide (0 < implementation.gateCount) }

def interfaceRouteSystem : TerminalSaturationSystem 1 1 1 1 :=
  terminalCandidateSaturationSystem interfaceRouteCandidate interfaceRouteModel

def interfaceRouteGateRecord : interfaceRouteRecord :=
  .gate interfaceRouteGate
def interfaceRouteInterfaceRecord : interfaceRouteRecord :=
  .interface interfaceRouteOutput
def interfaceRouteProfileRecord : interfaceRouteRecord :=
  .profile interfaceRouteProfile

/-! The production query recovers the exact interface output and materializer. -/

def interfaceRouteBalancedMaterializer :
    TerminalSaturationTraceEvent 1 1 1 1 :=
  { kind? := some .interfaceConsumer
    dependent := interfaceRouteInterfaceRecord
    required := interfaceRouteGateRecord
    beforeRecords := [interfaceRouteInterfaceRecord]
    afterRecords := [interfaceRouteGateRecord, interfaceRouteInterfaceRecord] }

example : terminalCandidateInterfaceExposureCoordinate?
    interfaceRouteCandidate interfaceRouteModel interfaceRouteBalancedMaterializer =
      some (.gateMaterializer interfaceRouteOutput interfaceRouteGate) := by
  decide

example : terminalInterfaceExposureStepRoutedBool
    interfaceRouteCandidate interfaceRouteModel interfaceRouteBalancedMaterializer =
      false := by
  decide

example : terminalSaturationStepTransparentBool
    interfaceRouteCandidate interfaceRouteModel interfaceRouteBalancedMaterializer =
      true := by
  decide

/-! Adding the outgoing coordinate itself is an exact zero-cost retract. -/

def interfaceRouteOutgoingCoordinate :
    TerminalSaturationTraceEvent 1 1 1 1 :=
  { kind? := some .interfaceConsumer
    dependent := interfaceRouteGateRecord
    required := interfaceRouteInterfaceRecord
    beforeRecords := [interfaceRouteGateRecord]
    afterRecords := [interfaceRouteInterfaceRecord, interfaceRouteGateRecord] }

def interfaceRouteOutgoingRetract :
    TerminalInterfaceExposureZeroCostRetract
      interfaceRouteCandidate interfaceRouteModel interfaceRouteOutgoingCoordinate :=
  by
    have selected : terminalCandidateInterfaceExposureCoordinate?
        interfaceRouteCandidate interfaceRouteModel interfaceRouteOutgoingCoordinate =
          some (.outgoingCoordinate interfaceRouteOutput) := by
      decide
    cases classifiedAt : classifyTerminalSaturationStepBalance
        interfaceRouteCandidate interfaceRouteModel interfaceRouteOutgoingCoordinate with
    | transparent evidence =>
        exact
          { output := interfaceRouteOutput
            selected := selected
            transparent := evidence }
    | nontransparent reason failure =>
        have expected : terminalSaturationStepTransparentBool
            interfaceRouteCandidate interfaceRouteModel
              interfaceRouteOutgoingCoordinate = true := by
          decide
        simp [terminalSaturationStepTransparentBool, classifiedAt] at expected

example : terminalSaturationEventCost interfaceRouteOutgoingCoordinate = 0 :=
  interfaceRouteOutgoingRetract.eventCost_zero

example :
    (terminalSaturationCostSnapshot interfaceRouteCandidate interfaceRouteModel
      interfaceRouteOutgoingCoordinate.afterRecords).fullSlack =
    (terminalSaturationCostSnapshot interfaceRouteCandidate interfaceRouteModel
      interfaceRouteOutgoingCoordinate.beforeRecords).fullSlack :=
  interfaceRouteOutgoingRetract.fullSlack_preserved

/-! A second active owner makes the interface-driven materializer the exact
    local E-route rather than silently accepting it. -/

def interfaceRouteMultipleOwner :
    TerminalSaturationTraceEvent 1 1 1 1 :=
  { kind? := some .interfaceConsumer
    dependent := interfaceRouteInterfaceRecord
    required := interfaceRouteGateRecord
    beforeRecords := [interfaceRouteProfileRecord, interfaceRouteInterfaceRecord]
    afterRecords := [interfaceRouteGateRecord, interfaceRouteProfileRecord,
      interfaceRouteInterfaceRecord] }

example : terminalSaturationStepFailureReason?
    interfaceRouteCandidate interfaceRouteModel interfaceRouteMultipleOwner =
      some .nonuniqueMaterializerOwner := by
  decide

example : terminalInterfaceExposureStepRoutedBool
    interfaceRouteCandidate interfaceRouteModel interfaceRouteMultipleOwner =
      true := by
  decide

def interfaceRouteMultipleOwnerERoute : TerminalInterfaceExposureERoute
    interfaceRouteCandidate interfaceRouteModel interfaceRouteMultipleOwner := by
  have selected : terminalCandidateInterfaceExposureCoordinate?
      interfaceRouteCandidate interfaceRouteModel interfaceRouteMultipleOwner =
        some (.gateMaterializer interfaceRouteOutput interfaceRouteGate) := by
    decide
  cases classifiedAt : classifyTerminalSaturationStepBalance
      interfaceRouteCandidate interfaceRouteModel interfaceRouteMultipleOwner with
  | transparent _evidence =>
      have rejected : terminalSaturationStepFailureReason?
          interfaceRouteCandidate interfaceRouteModel interfaceRouteMultipleOwner =
            some .nonuniqueMaterializerOwner := by
        decide
      simp [terminalSaturationStepFailureReason?, classifiedAt] at rejected
  | nontransparent reason failure =>
      exact
        { coordinate := .gateMaterializer interfaceRouteOutput interfaceRouteGate
          selected := selected
          reason := reason
          reasonSelected := by
            simp [terminalSaturationStepFailureReason?, classifiedAt]
          failure := failure }

example : Nonempty (TerminalInterfaceExposureERoute
    interfaceRouteCandidate interfaceRouteModel interfaceRouteMultipleOwner) :=
  ⟨interfaceRouteMultipleOwnerERoute⟩

example : TerminalTransparentSaturationStep
      interfaceRouteCandidate interfaceRouteModel interfaceRouteMultipleOwner ∨
    Nonempty (TerminalInterfaceExposureERoute
      interfaceRouteCandidate interfaceRouteModel interfaceRouteMultipleOwner) := by
  have selected : terminalCandidateInterfaceExposureCoordinate?
      interfaceRouteCandidate interfaceRouteModel interfaceRouteMultipleOwner =
        some (.gateMaterializer interfaceRouteOutput interfaceRouteGate) := by
    decide
  exact terminalInterfaceExposure_transparent_or_eRoute
    interfaceRouteCandidate interfaceRouteModel interfaceRouteMultipleOwner
    (.gateMaterializer interfaceRouteOutput interfaceRouteGate) selected

/-! Kind tampering cannot be relabeled as an interface route. -/

def interfaceRouteWrongKind : TerminalSaturationTraceEvent 1 1 1 1 :=
  { interfaceRouteMultipleOwner with kind? := some .gateSource }

example : terminalCandidateInterfaceExposureCoordinate?
    interfaceRouteCandidate interfaceRouteModel interfaceRouteWrongKind = none := by
  decide

example : terminalInterfaceExposureStepRoutedBool
    interfaceRouteCandidate interfaceRouteModel interfaceRouteWrongKind = false := by
  decide

/-! The complete production trace routes its exact first interface failure. -/

example : terminalSaturationInterfaceBalancedBool
    interfaceRouteCandidate interfaceRouteModel
      [interfaceRouteInterfaceRecord] = true := by
  decide

example : terminalSaturationInterfaceERoutedBool
    interfaceRouteCandidate interfaceRouteModel
      [interfaceRouteInterfaceRecord, interfaceRouteProfileRecord] = true := by
  decide

/-! A separate two-profile fixture proves that a non-interface first failure
    remains in the fail-closed fallback branch. -/

abbrev noninterfaceRouteRecord := TerminalPrimitiveRecord 1 1 1 2

def noninterfaceRouteProfile0 : Fin 2 := ⟨0, by decide⟩
def noninterfaceRouteProfile1 : Fin 2 := ⟨1, by decide⟩

def noninterfaceRouteWord : DirectWireWord 1 1 1 :=
  ⟨fun _output => .constant false⟩

def noninterfaceRouteCandidate : Candidate 1 1 1 :=
  Candidate.ofDirectWireWord interfaceRouteProgram noninterfaceRouteWord

def noninterfaceRouteProfileSystem : TerminalProfileSystem 1 1 2 :=
  { role := fun _coordinate => .carrier
    observe := fun _implementation _coordinate => false }

def noninterfaceRouteProjection : TerminalProfileProjection 2 :=
  { keep := fun _coordinate => false }

def noninterfaceRouteModel :
    TerminalCandidateSaturationModel (profileWidth := 2)
      noninterfaceRouteCandidate :=
  { profileSystem := noninterfaceRouteProfileSystem
    projection := noninterfaceRouteProjection
    observe := fun implementation _coordinate =>
      decide (0 < implementation.gateCount) }

def noninterfaceRouteRecord0 : noninterfaceRouteRecord :=
  .profile noninterfaceRouteProfile0
def noninterfaceRouteRecord1 : noninterfaceRouteRecord :=
  .profile noninterfaceRouteProfile1

example : terminalSaturationInterfaceOtherNontransparentBool
    noninterfaceRouteCandidate noninterfaceRouteModel
      [noninterfaceRouteRecord0, noninterfaceRouteRecord1] = true := by
  decide

example : terminalSaturationInterfaceERoutedBool
    noninterfaceRouteCandidate noninterfaceRouteModel
      [noninterfaceRouteRecord0, noninterfaceRouteRecord1] = false := by
  decide

end DirectWire
end PNP
