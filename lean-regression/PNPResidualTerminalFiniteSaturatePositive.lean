import PNP.ResidualTerminalFiniteSaturatePositive

namespace PNP
namespace DirectWire

abbrev finiteSaturateRecord := TerminalPrimitiveRecord 1 1 1 3

def finiteSaturateInput : Fin 1 := ⟨0, by decide⟩
def finiteSaturateGate : Fin 1 := ⟨0, by decide⟩
def finiteSaturateOutput : Fin 1 := ⟨0, by decide⟩
def finiteSaturateOrigin : Fin 3 := ⟨0, by decide⟩
def finiteSaturateKernel : Fin 3 := ⟨1, by decide⟩
def finiteSaturateObligation : Fin 3 := ⟨2, by decide⟩

def finiteSaturateProgram : Program 1 1 :=
  .snoc .empty
    { left := .input finiteSaturateInput
      right := .input finiteSaturateInput }

def finiteSaturateWord : DirectWireWord 1 1 1 :=
  ⟨fun _output => .gate finiteSaturateGate⟩

def finiteSaturateCandidate : Candidate 1 1 1 :=
  Candidate.ofDirectWireWord finiteSaturateProgram finiteSaturateWord

def finiteSaturateRole (coordinate : Fin 3) : TerminalProfileRole :=
  if coordinate = finiteSaturateOrigin then .origin
  else if coordinate = finiteSaturateKernel then .kernel
  else .obligation

def finiteSaturateProfileSystem : TerminalProfileSystem 1 1 3 :=
  { role := finiteSaturateRole
    observe := fun _implementation _coordinate => false }

def finiteSaturateProjection : TerminalProfileProjection 3 :=
  { keep := fun _coordinate => true }

def finiteSaturateForgottenProjection : TerminalProfileProjection 3 :=
  { keep := fun _coordinate => false }

def finiteSaturateModel :
    TerminalCandidateSaturationModel (profileWidth := 3)
      finiteSaturateCandidate :=
  { profileSystem := finiteSaturateProfileSystem
    projection := finiteSaturateProjection
    observe := fun implementation _coordinate =>
      decide (0 < implementation.gateCount) }

def finiteSaturateForgottenModel :
    TerminalCandidateSaturationModel (profileWidth := 3)
      finiteSaturateCandidate :=
  { profileSystem := finiteSaturateProfileSystem
    projection := finiteSaturateForgottenProjection
    observe := fun implementation _coordinate =>
      decide (0 < implementation.gateCount) }

def finiteSaturateGateRecord : finiteSaturateRecord :=
  .gate finiteSaturateGate
def finiteSaturateInterfaceRecord : finiteSaturateRecord :=
  .interface finiteSaturateOutput
def finiteSaturateOriginRecord : finiteSaturateRecord :=
  .profile finiteSaturateOrigin
def finiteSaturateKernelRecord : finiteSaturateRecord :=
  .profile finiteSaturateKernel
def finiteSaturateObligationRecord : finiteSaturateRecord :=
  .profile finiteSaturateObligation

/-! Origin and kernel closures are accepted in both exact orientations when
    they are transparent, discharged, and visible to the projection. -/

def finiteSaturateOriginSafeEvent :
    TerminalSaturationTraceEvent 1 1 1 3 :=
  { kind? := some .origin
    dependent := finiteSaturateOriginRecord
    required := finiteSaturateGateRecord
    beforeRecords := [finiteSaturateOriginRecord]
    afterRecords := [finiteSaturateGateRecord, finiteSaturateOriginRecord] }

def finiteSaturateKernelSafeEvent :
    TerminalSaturationTraceEvent 1 1 1 3 :=
  { kind? := some .kernel
    dependent := finiteSaturateGateRecord
    required := finiteSaturateKernelRecord
    beforeRecords := [finiteSaturateGateRecord]
    afterRecords := [finiteSaturateKernelRecord, finiteSaturateGateRecord] }

example : terminalCandidateOriginKernelObligationCoordinate?
    finiteSaturateCandidate finiteSaturateModel finiteSaturateOriginSafeEvent =
      some
        { role := .origin
          coordinate := finiteSaturateOrigin
          gate := finiteSaturateGate
          orientation := .profileRequiresGate } := by
  decide

example : terminalCandidateOriginKernelObligationCoordinate?
    finiteSaturateCandidate finiteSaturateModel finiteSaturateKernelSafeEvent =
      some
        { role := .kernel
          coordinate := finiteSaturateKernel
          gate := finiteSaturateGate
          orientation := .gateRequiresProfile } := by
  decide

def finiteSaturateStepSafeBool
    (model : TerminalCandidateSaturationModel (profileWidth := 3)
      finiteSaturateCandidate)
    (event : TerminalSaturationTraceEvent 1 1 1 3) : Bool :=
  match classifyTerminalOriginKernelObligationStep
      finiteSaturateCandidate model event with
  | .safe _coordinate _selected _evidence => true
  | _ => false

example : finiteSaturateStepSafeBool finiteSaturateModel
    finiteSaturateOriginSafeEvent = true := by
  decide

example : finiteSaturateStepSafeBool finiteSaturateModel
    finiteSaturateKernelSafeEvent = true := by
  decide

/-! Unsafe recognized closures carry deterministic proof-bearing reasons. -/

def finiteSaturateObligationOpenEvent :
    TerminalSaturationTraceEvent 1 1 1 3 :=
  { kind? := some .obligation
    dependent := finiteSaturateObligationRecord
    required := finiteSaturateGateRecord
    beforeRecords := [finiteSaturateObligationRecord]
    afterRecords := [finiteSaturateGateRecord,
      finiteSaturateObligationRecord] }

def finiteSaturateForgottenMismatchEvent :
    TerminalSaturationTraceEvent 1 1 1 3 :=
  finiteSaturateOriginSafeEvent

def finiteSaturateNontransparentEvent :
    TerminalSaturationTraceEvent 1 1 1 3 :=
  { kind? := some .kernel
    dependent := finiteSaturateKernelRecord
    required := finiteSaturateGateRecord
    beforeRecords := [finiteSaturateOriginRecord,
      finiteSaturateKernelRecord]
    afterRecords := [finiteSaturateGateRecord, finiteSaturateOriginRecord,
      finiteSaturateKernelRecord] }

def finiteSaturateRouteReason?
    (model : TerminalCandidateSaturationModel (profileWidth := 3)
      finiteSaturateCandidate)
    (event : TerminalSaturationTraceEvent 1 1 1 3) :
    Option TerminalOriginKernelObligationClosureFailureReason :=
  match classifyTerminalOriginKernelObligationStep
      finiteSaturateCandidate model event with
  | .route route => some route.reason
  | _ => none

example : terminalSaturationStepTransparentBool finiteSaturateCandidate
    finiteSaturateModel finiteSaturateObligationOpenEvent = true := by
  decide

example : finiteSaturateRouteReason? finiteSaturateModel
    finiteSaturateObligationOpenEvent = some .openObligation := by
  decide

example : finiteSaturateRouteReason? finiteSaturateForgottenModel
    finiteSaturateForgottenMismatchEvent =
      some .forgottenProfileMismatch := by
  decide

example : terminalSaturationStepFailureReason? finiteSaturateCandidate
    finiteSaturateModel finiteSaturateNontransparentEvent =
      some .nonuniqueMaterializerOwner := by
  decide

example : finiteSaturateRouteReason? finiteSaturateModel
    finiteSaturateNontransparentEvent =
      some (.nontransparent .nonuniqueMaterializerOwner) := by
  decide

/-! Role or kind tampering is rejected before any local route is issued. -/

def finiteSaturateWrongKindEvent :
    TerminalSaturationTraceEvent 1 1 1 3 :=
  { finiteSaturateOriginSafeEvent with kind? := some .kernel }

example : terminalCandidateOriginKernelObligationCoordinate?
    finiteSaturateCandidate finiteSaturateModel finiteSaturateWrongKindEvent =
      none := by
  decide

/-! The production trace exposes the open obligation as its exact first
    composed failure. -/

def finiteSaturateRoutingKind : Nat :=
  match classifyTerminalSaturationClosureRouting finiteSaturateCandidate
      finiteSaturateModel [finiteSaturateObligationRecord] with
  | .balanced _allSafe => 0
  | .interfaceExposure _first _route => 1
  | .originKernelObligation _first _route => 2
  | .otherNontransparent _first _failure => 3

def finiteSaturateRoutingPriorLength? : Option Nat :=
  match classifyTerminalSaturationClosureRouting finiteSaturateCandidate
      finiteSaturateModel [finiteSaturateObligationRecord] with
  | .originKernelObligation first _route => some first.prior.length
  | _ => none

example : finiteSaturateRoutingKind = 2 := by decide
example : finiteSaturateRoutingPriorLength? = some 0 := by decide

/-! The final composition is total and every branch exposes its exact kernel
    proposition for arbitrary finite proof-bearing problems. -/

example
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (problem : TerminalFiniteSaturatePositiveProblem candidate model) :
    Nonempty (TerminalFiniteSaturatePositiveOutcome
      candidate model problem) :=
  classifyTerminalFiniteSaturatePositive_exhaustive candidate model problem

example
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    {problem : TerminalFiniteSaturatePositiveProblem candidate model}
    (outcome : TerminalFiniteSaturatePositiveOutcome
      candidate model problem) : outcome.Sound :=
  outcome.sound

end DirectWire
end PNP
