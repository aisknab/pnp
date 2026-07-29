/-
Copyright (c) 2026 PNP Labs.

Constructive work bounds for the three fixed primitive-program blocks used
while the grammar-only locked-NAND target emitter traverses one raw gate.

Classification, source capture, and cursor restoration already have literal
step formulae in the exact trace.  This layer supplies the missing bounded
physical paths for the left-source macro, right-source macro, and fixed
right-trace macro.  All runtime data remains proof-side only.
-/

import PNP.Concrete.LockedNANDTargetEmitterControllerGateTrace
import PNP.Concrete.LockedNANDTargetEmitterControllerNormalizationBound
import PNP.Concrete.LockedNANDTargetEmitterRuntimeProgramBound

namespace PNP.Concrete.LockedNAND.TargetEmitterControllerGateBound

open PNP.Concrete
open WorkMachineProgramGraph
open WorkMachineProgramPath
open TargetEmitterController
open TargetEmitterPrimitiveCompiler
open TargetEmitterBlockCompiler

set_option maxRecDepth 100000

abbrev Runtime := TargetEmitterProgramSemantics.Runtime
abbrev SourceKind := TargetEmitterPlan.SourceKind
abbrev ProgramSafe := TargetEmitterRuntimeProgram.ProgramSafe
abbrev SourceContext := TargetEmitterRuntimeProgram.SourceContext
abbrev MarkedWorkspace :=
  TargetEmitterRuntimeProgramSafety.MarkedWorkspace
abbrev ControllerRange :=
  TargetEmitterCapacity.ControllerRange
abbrev SourceReady :=
  TargetEmitterControllerGateTrace.SourceReady
abbrev TapeRepresents :=
  TargetEmitterControllerGateTrace.TapeRepresents
abbrev FocusTapeRepresents :=
  TargetEmitterControllerGateTrace.FocusTapeRepresents

private def leftSourceDescriptor (kind : SourceKind) :
    BlockDescriptor :=
  { code := Block.leftSource kind
    primitives := Plan.source kind 0
    continuation := .node (leftRestoreRef kind) }

private def rightSourceDescriptor (kind : SourceKind) :
    BlockDescriptor :=
  { code := Block.rightSource kind
    primitives := Plan.source kind 1
    continuation := .node (rightTraceRef kind) }

private def rightTraceDescriptor (kind : SourceKind) :
    BlockDescriptor :=
  { code := Block.rightTrace kind
    primitives := Plan.rightTrace
    continuation := .node (rightRestoreRef kind) }

private def leftSourcePrograms (kind : SourceKind) :
    List WorkMachine :=
  (compileProgram (Plan.source kind 0)).getD []

private def rightSourcePrograms (kind : SourceKind) :
    List WorkMachine :=
  (compileProgram (Plan.source kind 1)).getD []

private def rightTracePrograms : List WorkMachine :=
  (compileProgram Plan.rightTrace).getD []

private theorem leftSourceDescriptor_member (kind : SourceKind) :
    leftSourceDescriptor kind ∈ blockDescriptors := by
  cases kind <;>
    simp [leftSourceDescriptor, blockDescriptors,
      leftBlockDescriptors, Plan.sourceKinds]

private theorem rightSourceDescriptor_member (kind : SourceKind) :
    rightSourceDescriptor kind ∈ blockDescriptors := by
  cases kind <;>
    simp [rightSourceDescriptor, blockDescriptors,
      rightBlockDescriptors, Plan.sourceKinds]

private theorem rightTraceDescriptor_member (kind : SourceKind) :
    rightTraceDescriptor kind ∈ blockDescriptors := by
  cases kind <;>
    simp [rightTraceDescriptor, blockDescriptors,
      rightBlockDescriptors, Plan.sourceKinds]

private theorem leftSource_compiled (kind : SourceKind) :
    compileProgram (Plan.source kind 0) =
      some (leftSourcePrograms kind) := by
  cases kind <;> rfl

private theorem rightSource_compiled (kind : SourceKind) :
    compileProgram (Plan.source kind 1) =
      some (rightSourcePrograms kind) := by
  cases kind <;> rfl

private theorem rightTrace_compiled :
    compileProgram Plan.rightTrace =
      some rightTracePrograms := by
  rfl

private theorem leftSource_startState (kind : SourceKind) :
    (leftSourceRef kind).startState =
      TargetEmitterRuntimeProgram.entryState 0
        (leftSourcePrograms kind) := by
  cases kind <;> rfl

private theorem rightSource_startState (kind : SourceKind) :
    (rightSourceRef kind).startState =
      TargetEmitterRuntimeProgram.entryState 0
        (rightSourcePrograms kind) := by
  cases kind <;> rfl

private theorem rightTrace_startState (kind : SourceKind) :
    (rightTraceRef kind).startState =
      TargetEmitterRuntimeProgram.entryState 0
        rightTracePrograms := by
  cases kind <;> rfl

private theorem leftSourcePrograms_nonempty (kind : SourceKind) :
    leftSourcePrograms kind ≠ [] := by
  cases kind <;> decide

private theorem rightSourcePrograms_nonempty (kind : SourceKind) :
    rightSourcePrograms kind ≠ [] := by
  cases kind <;> decide

private theorem rightTracePrograms_nonempty :
    rightTracePrograms ≠ [] := by
  decide

private theorem represents_at_state
    {oldState newState capacity scratch : Nat}
    {registers : TargetEmitter.UnaryRegisters}
    {checks : List Nat} {source : List WorkSymbol}
    {target : List Token} {actual : WorkConfiguration}
    (represents :
      TargetEmitterRuntime.Represents oldState capacity scratch
        registers checks source target actual) :
    TargetEmitterRuntime.Represents newState capacity scratch
      registers checks source target
      { state := newState, tape := actual.tape } := by
  refine ⟨?_, ?_⟩
  · simpa using
      (TargetEmitterRuntime.logicalConfiguration_state
        newState capacity scratch registers checks source target).symm
  · simpa only [TargetEmitterRuntime.logicalConfiguration_tape] using
      represents.tape

private theorem configAtWord_tape_irrel
    (firstState secondState : Nat)
    (left word : List WorkSymbol) :
    (TargetEmitter.configAtWord firstState left word).tape =
      (TargetEmitter.configAtWord secondState left word).tape := by
  cases word <;> rfl

private theorem sourceFocusConfiguration_state
    (state capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (before remaining : List WorkSymbol)
    (target : List Token) :
    (TargetEmitterRuntimeSourceControl.sourceFocusConfiguration
      state capacity scratch registers checks before remaining target).state =
        state := by
  unfold
    TargetEmitterRuntimeSourceControl.sourceFocusConfiguration
  cases remaining <;> rfl

private theorem focusRepresents_at_state
    {oldState newState capacity scratch : Nat}
    {registers : TargetEmitter.UnaryRegisters}
    {checks : List Nat}
    {crossed remaining : List WorkSymbol}
    {target : List Token} {actual : WorkConfiguration}
    (represents :
      TargetEmitterRuntimeSourceControl.SourceFocusRepresents
        oldState capacity scratch registers checks crossed remaining
        target actual) :
    TargetEmitterRuntimeSourceControl.SourceFocusRepresents
      newState capacity scratch registers checks crossed remaining
      target { state := newState, tape := actual.tape } := by
  refine ⟨?_, ?_⟩
  · simpa using
      (sourceFocusConfiguration_state
        newState capacity scratch registers checks crossed remaining
        target).symm
  · have canonicalTapeEq :
        (TargetEmitterRuntimeSourceControl.sourceFocusConfiguration
          oldState capacity scratch registers checks crossed remaining
          target).tape =
        (TargetEmitterRuntimeSourceControl.sourceFocusConfiguration
          newState capacity scratch registers checks crossed remaining
          target).tape := by
      unfold
        TargetEmitterRuntimeSourceControl.sourceFocusConfiguration
      exact configAtWord_tape_irrel _ _ _ _
    rw [← canonicalTapeEq]
    exact represents.tape

private theorem originalCell_eq_cursorOriginal
    (kind : SourceKind) :
    Plan.originalCell kind =
      TargetEmitterRuntimeLayout.cursorOriginal
        (Plan.captureKind kind) := by
  cases kind <;> rfl

private theorem source_safe
    {raw : RawCircuit} {source : List WorkSymbol}
    {runtime : Runtime} {side : Nat}
    (kind : SourceKind)
    (workspace : MarkedWorkspace source)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (ready : SourceReady raw source runtime.captured kind)
    (sideBound : side ≤ 1) :
    ProgramSafe
      (TargetEmitterLedger.slotCapacity raw) source workspace.context
      (Plan.source kind side) runtime
      (TargetEmitterProgramSemantics.macroResult runtime
        (TargetEmitterPlan.sourcePlan kind side)
        (TargetEmitterPlan.sourceCheckRelative kind)
        (TargetEmitterPlan.sourceGateCount kind)) := by
  cases kind with
  | input =>
      cases ready with
      | input captured =>
          exact
            TargetEmitterRuntimeProgramSafety.sourceInput_safe
              workspace range capturedBound scratchBound captured
              sideBound
  | constantFalse =>
      cases ready
      exact
        TargetEmitterRuntimeProgramSafety.sourceConstantFalse_safe
          workspace range capturedBound scratchBound sideBound
  | constantTrue =>
      cases ready
      exact
        TargetEmitterRuntimeProgramSafety.sourceConstantTrue_safe
          workspace range capturedBound scratchBound sideBound
  | gate =>
      cases ready with
      | gate captured =>
          exact
            TargetEmitterRuntimeProgramSafety.sourceGate_safe
              workspace range capturedBound scratchBound captured
              sideBound

/-- Runtime-sensitive envelope for the left-source primitive block. -/
def leftSourceBlockEnvelope
    (raw : RawCircuit) (source : List WorkSymbol)
    (runtime : Runtime) (kind : SourceKind) : Nat :=
  TargetEmitterRuntimeProgramBound.programWorkEnvelope
    (TargetEmitterLedger.slotCapacity raw) source runtime
    (Plan.source kind 0)

/-- Runtime-sensitive envelope for the right-source primitive block. -/
def rightSourceBlockEnvelope
    (raw : RawCircuit) (source : List WorkSymbol)
    (runtime : Runtime) (kind : SourceKind) : Nat :=
  TargetEmitterRuntimeProgramBound.programWorkEnvelope
    (TargetEmitterLedger.slotCapacity raw) source runtime
    (Plan.source kind 1)

/-- Runtime-sensitive envelope for the fixed right-trace primitive block. -/
def rightTraceBlockEnvelope
    (raw : RawCircuit) (source : List WorkSymbol)
    (runtime : Runtime) : Nat :=
  TargetEmitterRuntimeProgramBound.programWorkEnvelope
    (TargetEmitterLedger.slotCapacity raw) source runtime
    Plan.rightTrace

/-- Bounded physical execution of the left-source primitive block. -/
theorem leftSourceBlock_path_bounded
    {raw : RawCircuit} {source : List WorkSymbol}
    (kind : SourceKind)
    (workspace : MarkedWorkspace source)
    (runtime : Runtime)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (ready : SourceReady raw source runtime.captured kind)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents (leftSourceRef kind).startState
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node (leftSourceRef kind))
          (.node (leftRestoreRef kind)) steps
          initialTape finalTape ∧
      TapeRepresents (leftRestoreRef kind).startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterProgramSemantics.macroResult runtime
          (TargetEmitterPlan.sourcePlan kind 0)
          (TargetEmitterPlan.sourceCheckRelative kind)
          (TargetEmitterPlan.sourceGateCount kind)).scratch
        (TargetEmitterProgramSemantics.macroResult runtime
          (TargetEmitterPlan.sourcePlan kind 0)
          (TargetEmitterPlan.sourceCheckRelative kind)
          (TargetEmitterPlan.sourceGateCount kind)).registers
        (TargetEmitterProgramSemantics.macroResult runtime
          (TargetEmitterPlan.sourcePlan kind 0)
          (TargetEmitterPlan.sourceCheckRelative kind)
          (TargetEmitterPlan.sourceGateCount kind)).checks
        source
        (TargetEmitterProgramSemantics.macroResult runtime
          (TargetEmitterPlan.sourcePlan kind 0)
          (TargetEmitterPlan.sourceCheckRelative kind)
          (TargetEmitterPlan.sourceGateCount kind)).targetTokens
        finalTape ∧
      steps ≤ leftSourceBlockEnvelope raw source runtime kind := by
  let final :=
    TargetEmitterProgramSemantics.macroResult runtime
      (TargetEmitterPlan.sourcePlan kind 0)
      (TargetEmitterPlan.sourceCheckRelative kind)
      (TargetEmitterPlan.sourceGateCount kind)
  let initial : WorkConfiguration :=
    { state :=
        TargetEmitterRuntimeProgram.entryState 0
          (leftSourcePrograms kind)
      tape := initialTape }
  have inputRepresents :
      TargetEmitterRuntime.Represents initial.state
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initial := by
    have atEntry :
        TapeRepresents
          (TargetEmitterRuntimeProgram.entryState 0
            (leftSourcePrograms kind))
          (TargetEmitterLedger.slotCapacity raw)
          runtime.scratch runtime.registers runtime.checks
          source runtime.targetTokens initialTape := by
      rw [← leftSource_startState]
      exact represents
    exact atEntry
  have safe :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        (leftSourceDescriptor kind).primitives runtime final := by
    simpa [leftSourceDescriptor, final] using
      (source_safe kind workspace range capturedBound scratchBound
        ready (side := 0) (by omega))
  rcases
      TargetEmitterRuntimeProgramBound.ProgramSafe.descriptor_acceptPath_bounded
        (leftSourceDescriptor kind)
        (leftSourceDescriptor_member kind) safe
        (Nat.le_of_lt scratchBound)
        (leftSourcePrograms kind)
        (by simpa [leftSourceDescriptor] using
          leftSource_compiled kind)
        (leftSourcePrograms_nonempty kind) 0 initial
        inputRepresents with
    ⟨steps, actualFinal, path, finalRepresents, bound⟩
  refine ⟨steps, actualFinal.tape, ?_, ?_, ?_⟩
  · simpa [leftSourceDescriptor, leftSourceRef] using path
  · exact
      represents_at_state
        (newState := (leftRestoreRef kind).startState)
        finalRepresents
  · simpa [leftSourceBlockEnvelope, leftSourceDescriptor] using bound

/-- Bounded physical execution of the right-source primitive block. -/
theorem rightSourceBlock_path_bounded
    {raw : RawCircuit} {source : List WorkSymbol}
    (kind : SourceKind)
    (workspace : MarkedWorkspace source)
    (runtime : Runtime)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (ready : SourceReady raw source runtime.captured kind)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents (rightSourceRef kind).startState
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node (rightSourceRef kind))
          (.node (rightTraceRef kind)) steps
          initialTape finalTape ∧
      TapeRepresents (rightTraceRef kind).startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterProgramSemantics.macroResult runtime
          (TargetEmitterPlan.sourcePlan kind 1)
          (TargetEmitterPlan.sourceCheckRelative kind)
          (TargetEmitterPlan.sourceGateCount kind)).scratch
        (TargetEmitterProgramSemantics.macroResult runtime
          (TargetEmitterPlan.sourcePlan kind 1)
          (TargetEmitterPlan.sourceCheckRelative kind)
          (TargetEmitterPlan.sourceGateCount kind)).registers
        (TargetEmitterProgramSemantics.macroResult runtime
          (TargetEmitterPlan.sourcePlan kind 1)
          (TargetEmitterPlan.sourceCheckRelative kind)
          (TargetEmitterPlan.sourceGateCount kind)).checks
        source
        (TargetEmitterProgramSemantics.macroResult runtime
          (TargetEmitterPlan.sourcePlan kind 1)
          (TargetEmitterPlan.sourceCheckRelative kind)
          (TargetEmitterPlan.sourceGateCount kind)).targetTokens
        finalTape ∧
      steps ≤ rightSourceBlockEnvelope raw source runtime kind := by
  let final :=
    TargetEmitterProgramSemantics.macroResult runtime
      (TargetEmitterPlan.sourcePlan kind 1)
      (TargetEmitterPlan.sourceCheckRelative kind)
      (TargetEmitterPlan.sourceGateCount kind)
  let initial : WorkConfiguration :=
    { state :=
        TargetEmitterRuntimeProgram.entryState 0
          (rightSourcePrograms kind)
      tape := initialTape }
  have inputRepresents :
      TargetEmitterRuntime.Represents initial.state
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initial := by
    have atEntry :
        TapeRepresents
          (TargetEmitterRuntimeProgram.entryState 0
            (rightSourcePrograms kind))
          (TargetEmitterLedger.slotCapacity raw)
          runtime.scratch runtime.registers runtime.checks
          source runtime.targetTokens initialTape := by
      rw [← rightSource_startState]
      exact represents
    exact atEntry
  have safe :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        (rightSourceDescriptor kind).primitives runtime final := by
    simpa [rightSourceDescriptor, final] using
      (source_safe kind workspace range capturedBound scratchBound
        ready (side := 1) (by omega))
  rcases
      TargetEmitterRuntimeProgramBound.ProgramSafe.descriptor_acceptPath_bounded
        (rightSourceDescriptor kind)
        (rightSourceDescriptor_member kind) safe
        (Nat.le_of_lt scratchBound)
        (rightSourcePrograms kind)
        (by simpa [rightSourceDescriptor] using
          rightSource_compiled kind)
        (rightSourcePrograms_nonempty kind) 0 initial
        inputRepresents with
    ⟨steps, actualFinal, path, finalRepresents, bound⟩
  refine ⟨steps, actualFinal.tape, ?_, ?_, ?_⟩
  · simpa [rightSourceDescriptor, rightSourceRef] using path
  · exact
      represents_at_state
        (newState := (rightTraceRef kind).startState)
        finalRepresents
  · simpa [rightSourceBlockEnvelope, rightSourceDescriptor] using bound

/-- Bounded physical execution of the fixed right-trace primitive block. -/
theorem rightTraceBlock_path_bounded
    {raw : RawCircuit} {source : List WorkSymbol}
    (kind : SourceKind)
    (workspace : MarkedWorkspace source)
    (runtime : Runtime)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (nextGate :
      runtime.registers.currentGate + 1 ≤
        TargetEmitterLedger.normalizedGateCount raw)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents (rightTraceRef kind).startState
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node (rightTraceRef kind))
          (.node (rightRestoreRef kind)) steps
          initialTape finalTape ∧
      TapeRepresents (rightRestoreRef kind).startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterRuntimeProgramSafety.rightTraceResult runtime).scratch
        (TargetEmitterRuntimeProgramSafety.rightTraceResult runtime).registers
        (TargetEmitterRuntimeProgramSafety.rightTraceResult runtime).checks
        source
        (TargetEmitterRuntimeProgramSafety.rightTraceResult
          runtime).targetTokens finalTape ∧
      steps ≤ rightTraceBlockEnvelope raw source runtime := by
  let initial : WorkConfiguration :=
    { state :=
        TargetEmitterRuntimeProgram.entryState 0 rightTracePrograms
      tape := initialTape }
  have inputRepresents :
      TargetEmitterRuntime.Represents initial.state
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initial := by
    have atEntry :
        TapeRepresents
          (TargetEmitterRuntimeProgram.entryState 0 rightTracePrograms)
          (TargetEmitterLedger.slotCapacity raw)
          runtime.scratch runtime.registers runtime.checks
          source runtime.targetTokens initialTape := by
      rw [← rightTrace_startState kind]
      exact represents
    exact atEntry
  have safe :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        (rightTraceDescriptor kind).primitives runtime
        (TargetEmitterRuntimeProgramSafety.rightTraceResult runtime) := by
    simpa [rightTraceDescriptor] using
      (TargetEmitterRuntimeProgramSafety.rightTrace_safe
        workspace range capturedBound scratchBound nextGate)
  rcases
      TargetEmitterRuntimeProgramBound.ProgramSafe.descriptor_acceptPath_bounded
        (rightTraceDescriptor kind)
        (rightTraceDescriptor_member kind) safe
        (Nat.le_of_lt scratchBound)
        rightTracePrograms
        (by simpa [rightTraceDescriptor] using rightTrace_compiled)
        rightTracePrograms_nonempty 0 initial inputRepresents with
    ⟨steps, actualFinal, path, finalRepresents, bound⟩
  refine ⟨steps, actualFinal.tape, ?_, ?_, ?_⟩
  · simpa [rightTraceDescriptor, rightTraceRef] using path
  · exact
      represents_at_state
        (newState := (rightRestoreRef kind).startState)
        finalRepresents
  · simpa [rightTraceBlockEnvelope, rightTraceDescriptor] using bound

/-! ### One complete bounded left-source phase -/

/-- Runtime-sensitive envelope for classification, capture, the left-source
primitive block, and cursor restoration. -/
def leftSourcePhaseEnvelope
    (raw : RawCircuit) (before after : List WorkSymbol)
    (source : RawSource) (runtime : Runtime) : Nat :=
  let kind :=
    TargetEmitterControllerTrace.sourceKind source
  let value :=
    TargetEmitterControllerGateTrace.sourceValue source
  let marked :=
    before ++
      TargetEmitterControllerSourceTrace.captureMarkedSourceCells
        kind value ++ after
  let captured :=
    TargetEmitterControllerGateTrace.capturedRuntime runtime kind value
  let restoreBefore :=
    before ++
      TargetEmitterRuntimeLayout.localCursorBefore
        (Plan.captureKind kind)
        (TargetEmitterControllerSourceTrace.capturedValue kind value)
  TargetEmitterControllerGateTrace.sourceCapturePhaseSteps
      before source runtime.scratch +
    leftSourceBlockEnvelope raw marked captured kind +
    TargetEmitterControllerSourceTrace.restorePathSteps
      restoreBefore.length

/-- Bounded classification, capture, left-source macro, and restoration path. -/
theorem leftSourcePhase_path_bounded
    {raw : RawCircuit}
    (runtime : Runtime)
    (range : ControllerRange raw runtime.registers)
    (head : WorkSymbol) (prefixTail after : List WorkSymbol)
    (source : RawSource) (target : List Token)
    (initialTape : WorkTape)
    (captureReserve :
      runtime.scratch +
          TargetEmitterControllerSourceTrace.capturedValue
            (TargetEmitterControllerTrace.sourceKind source)
            (TargetEmitterControllerGateTrace.sourceValue source) +
          1 ≤
        TargetEmitterLedger.slotCapacity raw)
    (capturedBound :
      TargetEmitterControllerSourceTrace.capturedValue
          (TargetEmitterControllerTrace.sourceKind source)
          (TargetEmitterControllerGateTrace.sourceValue source) +
          1 ≤
        (SourceParser.circuitCells raw).length)
    (originalPacked :
      ∀ symbol,
        symbol ∈
            (head :: prefixTail) ++
              SourceParser.sourceCells source ++ after →
          TargetEmitter.PackedSymbol symbol)
    (targetEq : target = runtime.targetTokens)
    (represents :
      FocusTapeRepresents
        leftFirstRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        (head :: prefixTail)
        (SourceParser.sourceCells source ++ after)
        target initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node leftFirstRef)
          (.node rightFirstRef) steps initialTape finalTape ∧
      FocusTapeRepresents
        rightFirstRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterProgramSemantics.macroResult
          (TargetEmitterControllerGateTrace.capturedRuntime runtime
            (TargetEmitterControllerTrace.sourceKind source)
            (TargetEmitterControllerGateTrace.sourceValue source))
          (TargetEmitterPlan.sourcePlan
            (TargetEmitterControllerTrace.sourceKind source) 0)
          (TargetEmitterPlan.sourceCheckRelative
            (TargetEmitterControllerTrace.sourceKind source))
          (TargetEmitterPlan.sourceGateCount
            (TargetEmitterControllerTrace.sourceKind source))).scratch
        (TargetEmitterProgramSemantics.macroResult
          (TargetEmitterControllerGateTrace.capturedRuntime runtime
            (TargetEmitterControllerTrace.sourceKind source)
            (TargetEmitterControllerGateTrace.sourceValue source))
          (TargetEmitterPlan.sourcePlan
            (TargetEmitterControllerTrace.sourceKind source) 0)
          (TargetEmitterPlan.sourceCheckRelative
            (TargetEmitterControllerTrace.sourceKind source))
          (TargetEmitterPlan.sourceGateCount
            (TargetEmitterControllerTrace.sourceKind source))).registers
        (TargetEmitterProgramSemantics.macroResult
          (TargetEmitterControllerGateTrace.capturedRuntime runtime
            (TargetEmitterControllerTrace.sourceKind source)
            (TargetEmitterControllerGateTrace.sourceValue source))
          (TargetEmitterPlan.sourcePlan
            (TargetEmitterControllerTrace.sourceKind source) 0)
          (TargetEmitterPlan.sourceCheckRelative
            (TargetEmitterControllerTrace.sourceKind source))
          (TargetEmitterPlan.sourceGateCount
            (TargetEmitterControllerTrace.sourceKind source))).checks
        ((head :: prefixTail) ++ SourceParser.sourceCells source)
        after
        (TargetEmitterProgramSemantics.macroResult
          (TargetEmitterControllerGateTrace.capturedRuntime runtime
            (TargetEmitterControllerTrace.sourceKind source)
            (TargetEmitterControllerGateTrace.sourceValue source))
          (TargetEmitterPlan.sourcePlan
            (TargetEmitterControllerTrace.sourceKind source) 0)
          (TargetEmitterPlan.sourceCheckRelative
            (TargetEmitterControllerTrace.sourceKind source))
          (TargetEmitterPlan.sourceGateCount
            (TargetEmitterControllerTrace.sourceKind source))).targetTokens
        finalTape ∧
      steps ≤
        leftSourcePhaseEnvelope raw (head :: prefixTail)
          after source runtime := by
  let kind := TargetEmitterControllerTrace.sourceKind source
  let value := TargetEmitterControllerGateTrace.sourceValue source
  let before := head :: prefixTail
  let marked :=
    before ++
      TargetEmitterControllerSourceTrace.captureMarkedSourceCells
        kind value ++ after
  let capturedState :=
    TargetEmitterControllerGateTrace.capturedRuntime runtime kind value
  let final :=
    TargetEmitterProgramSemantics.macroResult capturedState
      (TargetEmitterPlan.sourcePlan kind 0)
      (TargetEmitterPlan.sourceCheckRelative kind)
      (TargetEmitterPlan.sourceGateCount kind)
  have beforePacked :
      ∀ symbol, symbol ∈ before →
        TargetEmitter.PackedSymbol symbol := by
    intro symbol member
    exact originalPacked symbol
      (List.mem_append.mpr
        (Or.inl (List.mem_append.mpr (Or.inl member))))
  have originalCapturePacked :
      ∀ symbol,
        symbol ∈
            before ++
              TargetEmitterControllerSourceTrace.captureSourceCells
                kind value ++ after →
          TargetEmitter.PackedSymbol symbol := by
    simpa [before, kind, value,
      ← TargetEmitterControllerGateTrace.sourceCells_eq_captureSourceCells
        source] using originalPacked
  rcases
      TargetEmitterControllerGateTrace.leftClassifyCapture_path
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        before after source target initialTape
        captureReserve beforePacked represents with
    ⟨capturedTape, capturePath, capturedRepresents⟩
  let workspace :=
    TargetEmitterControllerGateTrace.markedWorkspace
      kind value head prefixTail after
      (by simpa [before] using originalCapturePacked)
  have valueBound :
      TargetEmitterControllerSourceTrace.capturedValue kind value + 1 ≤
        TargetEmitterLedger.slotCapacity raw := by
    simp [kind, value] at captureReserve ⊢
    omega
  let ready :=
    TargetEmitterControllerGateTrace.sourceReady
      raw kind value before after beforePacked valueBound
  have capturedLogical :
      TapeRepresents (leftSourceRef kind).startState
        (TargetEmitterLedger.slotCapacity raw)
        capturedState.scratch capturedState.registers
        capturedState.checks marked capturedState.targetTokens
        capturedTape := by
    simpa [capturedState,
      TargetEmitterControllerGateTrace.capturedRuntime,
      marked, kind, value, targetEq] using capturedRepresents
  have capturedScratchBound :
      capturedState.scratch <
        TargetEmitterLedger.slotCapacity raw := by
    simp [capturedState,
      TargetEmitterControllerGateTrace.capturedRuntime, kind, value]
    omega
  have capturedIndexBound :
      capturedState.captured + 1 ≤
        (SourceParser.circuitCells raw).length := by
    simpa [capturedState,
      TargetEmitterControllerGateTrace.capturedRuntime,
      kind, value] using capturedBound
  rcases
      leftSourceBlock_path_bounded kind workspace capturedState range
        capturedIndexBound capturedScratchBound ready
        capturedTape capturedLogical with
    ⟨blockSteps, blockTape, blockPath,
      blockRepresents, blockBound⟩
  let restoreBefore :=
    before ++
      TargetEmitterRuntimeLayout.localCursorBefore
        (Plan.captureKind kind)
        (TargetEmitterControllerSourceTrace.capturedValue kind value)
  let restoreActual : WorkConfiguration :=
    { state := TargetEmitterCursorControl.restoreState
      tape := blockTape }
  have restoreLogical :
      TargetEmitterRuntime.Represents
        TargetEmitterCursorControl.restoreState
        (TargetEmitterLedger.slotCapacity raw)
        final.scratch final.registers final.checks marked
        final.targetTokens restoreActual := by
    exact represents_at_state blockRepresents
  have restoreRepresents :
      TargetEmitterRuntime.Represents
        TargetEmitterCursorControl.restoreState
        (TargetEmitterLedger.slotCapacity raw)
        final.scratch final.registers final.checks
        (restoreBefore ++
          TargetEmitterCursorControl.cursorMark :: after)
        final.targetTokens restoreActual := by
    simpa [marked, restoreBefore,
      TargetEmitterControllerSourceTrace.captureMarkedSourceCells,
      TargetEmitterCursorControl.cursorMark,
      TargetEmitterCursorAppender.cursorMarker,
      TargetEmitterRuntimeLayout.markedSourceCells_eq_cursor,
      kind, value, List.append_assoc] using restoreLogical
  have restorePrefixPacked :
      ∀ symbol, symbol ∈ restoreBefore →
        TargetEmitter.PackedSymbol symbol := by
    intro symbol member
    rcases List.mem_append.mp member with
      beforeMember | localMember
    · exact beforePacked symbol beforeMember
    · apply originalPacked symbol
      apply List.mem_append.mpr
      apply Or.inl
      apply List.mem_append.mpr
      apply Or.inr
      rw [TargetEmitterControllerGateTrace.sourceCells_eq_captureSourceCells]
      unfold
        TargetEmitterControllerSourceTrace.captureSourceCells
      rw [TargetEmitterRuntimeLayout.sourceCells_eq_original]
      exact List.mem_append.mpr (Or.inl localMember)
  rcases
      TargetEmitterControllerSourceTrace.leftRestore_path
        kind (TargetEmitterLedger.slotCapacity raw)
        final.scratch final.registers final.checks
        restoreBefore after final.targetTokens restoreActual
        restorePrefixPacked restoreRepresents with
    ⟨restored, restorePath, restoredRepresents⟩
  have restoredAtRight :=
    focusRepresents_at_state
      (newState := rightFirstRef.startState)
      restoredRepresents
  have finalFocus :
      FocusTapeRepresents
        rightFirstRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        final.scratch final.registers final.checks
        (before ++ SourceParser.sourceCells source) after
        final.targetTokens restored.tape := by
    simpa [TargetEmitterControllerGateTrace.FocusTapeRepresents,
      restoreBefore, before, kind, value,
      TargetEmitterControllerGateTrace.sourceCells_eq_captureSourceCells,
      TargetEmitterControllerSourceTrace.captureSourceCells,
      originalCell_eq_cursorOriginal,
      TargetEmitterRuntimeLayout.sourceCells_eq_original,
      List.append_assoc] using restoredAtRight
  have firstTwo :=
    AcceptPath.trans graph (.node leftFirstRef)
      (.node (leftSourceRef kind)) (.node (leftRestoreRef kind))
      (TargetEmitterControllerGateTrace.sourceCapturePhaseSteps
        before source runtime.scratch)
      blockSteps initialTape capturedTape blockTape
      capturePath blockPath
  have all :=
    AcceptPath.trans graph (.node leftFirstRef)
      (.node (leftRestoreRef kind)) (.node rightFirstRef)
      (TargetEmitterControllerGateTrace.sourceCapturePhaseSteps
          before source runtime.scratch + blockSteps)
      (TargetEmitterControllerSourceTrace.restorePathSteps
        restoreBefore.length)
      initialTape blockTape restored.tape firstTwo restorePath
  refine
    ⟨TargetEmitterControllerGateTrace.sourceCapturePhaseSteps
          before source runtime.scratch +
        blockSteps +
        TargetEmitterControllerSourceTrace.restorePathSteps
          restoreBefore.length,
      restored.tape, by simpa [Nat.add_assoc] using all,
      ?_, ?_⟩
  · simpa [final, capturedState, before, kind, value] using finalFocus
  · unfold leftSourcePhaseEnvelope
    dsimp only
    simpa [before, kind, value, marked, capturedState,
      restoreBefore] using
      Nat.add_le_add_right
        (Nat.add_le_add_left blockBound
          (TargetEmitterControllerGateTrace.sourceCapturePhaseSteps
            before source runtime.scratch))
        (TargetEmitterControllerSourceTrace.restorePathSteps
          restoreBefore.length)

/-! ### One complete bounded right-source and trace phase -/

/-- Runtime-sensitive envelope for right classification/capture, the source
macro, the fixed trace macro, and cursor restoration. -/
def rightSourceTracePhaseEnvelope
    (raw : RawCircuit) (before after : List WorkSymbol)
    (source : RawSource) (runtime : Runtime) : Nat :=
  let kind :=
    TargetEmitterControllerTrace.sourceKind source
  let value :=
    TargetEmitterControllerGateTrace.sourceValue source
  let marked :=
    before ++
      TargetEmitterControllerSourceTrace.captureMarkedSourceCells
        kind value ++ after
  let captured :=
    TargetEmitterControllerGateTrace.capturedRuntime runtime kind value
  let sourceFinal :=
    TargetEmitterProgramSemantics.macroResult captured
      (TargetEmitterPlan.sourcePlan kind 1)
      (TargetEmitterPlan.sourceCheckRelative kind)
      (TargetEmitterPlan.sourceGateCount kind)
  let restoreBefore :=
    before ++
      TargetEmitterRuntimeLayout.localCursorBefore
        (Plan.captureKind kind)
        (TargetEmitterControllerSourceTrace.capturedValue kind value)
  TargetEmitterControllerGateTrace.sourceCapturePhaseSteps
      before source runtime.scratch +
    rightSourceBlockEnvelope raw marked captured kind +
    rightTraceBlockEnvelope raw marked sourceFinal +
    TargetEmitterControllerSourceTrace.restorePathSteps
      restoreBefore.length

/-- Bounded right-source capture, source macro, trace macro, and restoration
path. -/
theorem rightSourceTracePhase_path_bounded
    {raw : RawCircuit}
    (runtime : Runtime)
    (range : ControllerRange raw runtime.registers)
    (head : WorkSymbol) (prefixTail after : List WorkSymbol)
    (source : RawSource) (target : List Token)
    (initialTape : WorkTape)
    (captureReserve :
      runtime.scratch +
          TargetEmitterControllerSourceTrace.capturedValue
            (TargetEmitterControllerTrace.sourceKind source)
            (TargetEmitterControllerGateTrace.sourceValue source) +
          1 ≤
        TargetEmitterLedger.slotCapacity raw)
    (capturedBound :
      TargetEmitterControllerSourceTrace.capturedValue
          (TargetEmitterControllerTrace.sourceKind source)
          (TargetEmitterControllerGateTrace.sourceValue source) +
          1 ≤
        (SourceParser.circuitCells raw).length)
    (afterSourceRange :
      ControllerRange raw
        (TargetEmitterProgramSemantics.macroResult
          (TargetEmitterControllerGateTrace.capturedRuntime runtime
            (TargetEmitterControllerTrace.sourceKind source)
            (TargetEmitterControllerGateTrace.sourceValue source))
          (TargetEmitterPlan.sourcePlan
            (TargetEmitterControllerTrace.sourceKind source) 1)
          (TargetEmitterPlan.sourceCheckRelative
            (TargetEmitterControllerTrace.sourceKind source))
          (TargetEmitterPlan.sourceGateCount
            (TargetEmitterControllerTrace.sourceKind source))).registers)
    (nextGate :
      (TargetEmitterProgramSemantics.macroResult
        (TargetEmitterControllerGateTrace.capturedRuntime runtime
          (TargetEmitterControllerTrace.sourceKind source)
          (TargetEmitterControllerGateTrace.sourceValue source))
        (TargetEmitterPlan.sourcePlan
          (TargetEmitterControllerTrace.sourceKind source) 1)
        (TargetEmitterPlan.sourceCheckRelative
          (TargetEmitterControllerTrace.sourceKind source))
        (TargetEmitterPlan.sourceGateCount
          (TargetEmitterControllerTrace.sourceKind source))).registers.currentGate +
          1 ≤
        TargetEmitterLedger.normalizedGateCount raw)
    (originalPacked :
      ∀ symbol,
        symbol ∈
            (head :: prefixTail) ++
              SourceParser.sourceCells source ++ after →
          TargetEmitter.PackedSymbol symbol)
    (targetEq : target = runtime.targetTokens)
    (represents :
      FocusTapeRepresents rightFirstRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        (head :: prefixTail)
        (SourceParser.sourceCells source ++ after)
        target initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node rightFirstRef)
          (.node gateAdvanceRef) steps initialTape finalTape ∧
      FocusTapeRepresents gateAdvanceRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterRuntimeProgramSafety.rightTraceResult
          (TargetEmitterProgramSemantics.macroResult
            (TargetEmitterControllerGateTrace.capturedRuntime runtime
              (TargetEmitterControllerTrace.sourceKind source)
              (TargetEmitterControllerGateTrace.sourceValue source))
            (TargetEmitterPlan.sourcePlan
              (TargetEmitterControllerTrace.sourceKind source) 1)
            (TargetEmitterPlan.sourceCheckRelative
              (TargetEmitterControllerTrace.sourceKind source))
            (TargetEmitterPlan.sourceGateCount
              (TargetEmitterControllerTrace.sourceKind source)))).scratch
        (TargetEmitterRuntimeProgramSafety.rightTraceResult
          (TargetEmitterProgramSemantics.macroResult
            (TargetEmitterControllerGateTrace.capturedRuntime runtime
              (TargetEmitterControllerTrace.sourceKind source)
              (TargetEmitterControllerGateTrace.sourceValue source))
            (TargetEmitterPlan.sourcePlan
              (TargetEmitterControllerTrace.sourceKind source) 1)
            (TargetEmitterPlan.sourceCheckRelative
              (TargetEmitterControllerTrace.sourceKind source))
            (TargetEmitterPlan.sourceGateCount
              (TargetEmitterControllerTrace.sourceKind source)))).registers
        (TargetEmitterRuntimeProgramSafety.rightTraceResult
          (TargetEmitterProgramSemantics.macroResult
            (TargetEmitterControllerGateTrace.capturedRuntime runtime
              (TargetEmitterControllerTrace.sourceKind source)
              (TargetEmitterControllerGateTrace.sourceValue source))
            (TargetEmitterPlan.sourcePlan
              (TargetEmitterControllerTrace.sourceKind source) 1)
            (TargetEmitterPlan.sourceCheckRelative
              (TargetEmitterControllerTrace.sourceKind source))
            (TargetEmitterPlan.sourceGateCount
              (TargetEmitterControllerTrace.sourceKind source)))).checks
        ((head :: prefixTail) ++ SourceParser.sourceCells source)
        after
        (TargetEmitterRuntimeProgramSafety.rightTraceResult
          (TargetEmitterProgramSemantics.macroResult
            (TargetEmitterControllerGateTrace.capturedRuntime runtime
              (TargetEmitterControllerTrace.sourceKind source)
              (TargetEmitterControllerGateTrace.sourceValue source))
            (TargetEmitterPlan.sourcePlan
              (TargetEmitterControllerTrace.sourceKind source) 1)
            (TargetEmitterPlan.sourceCheckRelative
              (TargetEmitterControllerTrace.sourceKind source))
            (TargetEmitterPlan.sourceGateCount
              (TargetEmitterControllerTrace.sourceKind source)))).targetTokens
        finalTape ∧
      steps ≤
        rightSourceTracePhaseEnvelope raw (head :: prefixTail)
          after source runtime := by
  let kind := TargetEmitterControllerTrace.sourceKind source
  let value := TargetEmitterControllerGateTrace.sourceValue source
  let before := head :: prefixTail
  let marked :=
    before ++
      TargetEmitterControllerSourceTrace.captureMarkedSourceCells
        kind value ++ after
  let capturedState :=
    TargetEmitterControllerGateTrace.capturedRuntime runtime kind value
  let sourceFinal :=
    TargetEmitterProgramSemantics.macroResult capturedState
      (TargetEmitterPlan.sourcePlan kind 1)
      (TargetEmitterPlan.sourceCheckRelative kind)
      (TargetEmitterPlan.sourceGateCount kind)
  let traced :=
    TargetEmitterRuntimeProgramSafety.rightTraceResult sourceFinal
  have beforePacked :
      ∀ symbol, symbol ∈ before →
        TargetEmitter.PackedSymbol symbol := by
    intro symbol member
    exact originalPacked symbol
      (List.mem_append.mpr
        (Or.inl (List.mem_append.mpr (Or.inl member))))
  have originalCapturePacked :
      ∀ symbol,
        symbol ∈
            before ++
              TargetEmitterControllerSourceTrace.captureSourceCells
                kind value ++ after →
          TargetEmitter.PackedSymbol symbol := by
    simpa [before, kind, value,
      ← TargetEmitterControllerGateTrace.sourceCells_eq_captureSourceCells
        source] using originalPacked
  rcases
      TargetEmitterControllerGateTrace.rightClassifyCapture_path
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        before after source target initialTape
        captureReserve beforePacked represents with
    ⟨capturedTape, capturePath, capturedRepresents⟩
  let workspace :=
    TargetEmitterControllerGateTrace.markedWorkspace
      kind value head prefixTail after
      (by simpa [before] using originalCapturePacked)
  have valueBound :
      TargetEmitterControllerSourceTrace.capturedValue kind value + 1 ≤
        TargetEmitterLedger.slotCapacity raw := by
    simp [kind, value] at captureReserve ⊢
    omega
  let ready :=
    TargetEmitterControllerGateTrace.sourceReady
      raw kind value before after beforePacked valueBound
  have capturedLogical :
      TapeRepresents (rightSourceRef kind).startState
        (TargetEmitterLedger.slotCapacity raw)
        capturedState.scratch capturedState.registers
        capturedState.checks marked capturedState.targetTokens
        capturedTape := by
    simpa [capturedState,
      TargetEmitterControllerGateTrace.capturedRuntime,
      marked, kind, value, targetEq] using capturedRepresents
  have capturedScratchBound :
      capturedState.scratch <
        TargetEmitterLedger.slotCapacity raw := by
    simp [capturedState,
      TargetEmitterControllerGateTrace.capturedRuntime, kind, value]
    omega
  have capturedIndexBound :
      capturedState.captured + 1 ≤
        (SourceParser.circuitCells raw).length := by
    simpa [capturedState,
      TargetEmitterControllerGateTrace.capturedRuntime,
      kind, value] using capturedBound
  rcases
      rightSourceBlock_path_bounded kind workspace capturedState range
        capturedIndexBound capturedScratchBound ready
        capturedTape capturedLogical with
    ⟨sourceSteps, sourceTape, sourcePath,
      sourceRepresents, sourceBound⟩
  have sourceScratchBound :
      sourceFinal.scratch <
        TargetEmitterLedger.slotCapacity raw := by
    simp [sourceFinal,
      TargetEmitterProgramSemantics.macroResult_scratch,
      TargetEmitterLedger.slotCapacity]
  have sourceCapturedBound :
      sourceFinal.captured + 1 ≤
        (SourceParser.circuitCells raw).length := by
    rw [TargetEmitterControllerGateTrace.macroResult_captured]
    exact capturedIndexBound
  rcases
      rightTraceBlock_path_bounded kind workspace sourceFinal
        (by simpa [sourceFinal, capturedState, kind, value] using
          afterSourceRange)
        sourceCapturedBound sourceScratchBound
        (by simpa [sourceFinal, capturedState, kind, value] using
          nextGate)
        sourceTape
        (by simpa [sourceFinal] using sourceRepresents) with
    ⟨traceSteps, traceTape, tracePath,
      traceRepresents, traceBound⟩
  let restoreBefore :=
    before ++
      TargetEmitterRuntimeLayout.localCursorBefore
        (Plan.captureKind kind)
        (TargetEmitterControllerSourceTrace.capturedValue kind value)
  let restoreActual : WorkConfiguration :=
    { state := TargetEmitterCursorControl.restoreState
      tape := traceTape }
  have restoreLogical :
      TargetEmitterRuntime.Represents
        TargetEmitterCursorControl.restoreState
        (TargetEmitterLedger.slotCapacity raw)
        traced.scratch traced.registers traced.checks marked
        traced.targetTokens restoreActual := by
    exact represents_at_state traceRepresents
  have restoreRepresents :
      TargetEmitterRuntime.Represents
        TargetEmitterCursorControl.restoreState
        (TargetEmitterLedger.slotCapacity raw)
        traced.scratch traced.registers traced.checks
        (restoreBefore ++
          TargetEmitterCursorControl.cursorMark :: after)
        traced.targetTokens restoreActual := by
    simpa [marked, restoreBefore,
      TargetEmitterControllerSourceTrace.captureMarkedSourceCells,
      TargetEmitterCursorControl.cursorMark,
      TargetEmitterCursorAppender.cursorMarker,
      TargetEmitterRuntimeLayout.markedSourceCells_eq_cursor,
      kind, value, List.append_assoc] using restoreLogical
  have restorePrefixPacked :
      ∀ symbol, symbol ∈ restoreBefore →
        TargetEmitter.PackedSymbol symbol := by
    intro symbol member
    rcases List.mem_append.mp member with
      beforeMember | localMember
    · exact beforePacked symbol beforeMember
    · apply originalPacked symbol
      apply List.mem_append.mpr
      apply Or.inl
      apply List.mem_append.mpr
      apply Or.inr
      rw [TargetEmitterControllerGateTrace.sourceCells_eq_captureSourceCells]
      unfold
        TargetEmitterControllerSourceTrace.captureSourceCells
      rw [TargetEmitterRuntimeLayout.sourceCells_eq_original]
      exact List.mem_append.mpr (Or.inl localMember)
  rcases
      TargetEmitterControllerSourceTrace.rightRestore_path
        kind (TargetEmitterLedger.slotCapacity raw)
        traced.scratch traced.registers traced.checks
        restoreBefore after traced.targetTokens restoreActual
        restorePrefixPacked restoreRepresents with
    ⟨restored, restorePath, restoredRepresents⟩
  have restoredAtAdvance :=
    focusRepresents_at_state
      (newState := gateAdvanceRef.startState)
      restoredRepresents
  have finalFocus :
      FocusTapeRepresents gateAdvanceRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        traced.scratch traced.registers traced.checks
        (before ++ SourceParser.sourceCells source) after
        traced.targetTokens restored.tape := by
    simpa [TargetEmitterControllerGateTrace.FocusTapeRepresents,
      restoreBefore, before, kind, value,
      TargetEmitterControllerGateTrace.sourceCells_eq_captureSourceCells,
      TargetEmitterControllerSourceTrace.captureSourceCells,
      originalCell_eq_cursorOriginal,
      TargetEmitterRuntimeLayout.sourceCells_eq_original,
      List.append_assoc] using restoredAtAdvance
  have firstTwo :=
    AcceptPath.trans graph (.node rightFirstRef)
      (.node (rightSourceRef kind)) (.node (rightTraceRef kind))
      (TargetEmitterControllerGateTrace.sourceCapturePhaseSteps
        before source runtime.scratch)
      sourceSteps initialTape capturedTape sourceTape
      capturePath sourcePath
  have firstThree :=
    AcceptPath.trans graph (.node rightFirstRef)
      (.node (rightTraceRef kind)) (.node (rightRestoreRef kind))
      (TargetEmitterControllerGateTrace.sourceCapturePhaseSteps
          before source runtime.scratch + sourceSteps)
      traceSteps initialTape sourceTape traceTape
      firstTwo tracePath
  have all :=
    AcceptPath.trans graph (.node rightFirstRef)
      (.node (rightRestoreRef kind)) (.node gateAdvanceRef)
      (TargetEmitterControllerGateTrace.sourceCapturePhaseSteps
          before source runtime.scratch +
        sourceSteps + traceSteps)
      (TargetEmitterControllerSourceTrace.restorePathSteps
        restoreBefore.length)
      initialTape traceTape restored.tape firstThree restorePath
  refine
    ⟨TargetEmitterControllerGateTrace.sourceCapturePhaseSteps
          before source runtime.scratch +
        sourceSteps + traceSteps +
        TargetEmitterControllerSourceTrace.restorePathSteps
          restoreBefore.length,
      restored.tape, by simpa [Nat.add_assoc] using all,
      ?_, ?_⟩
  · simpa [traced, sourceFinal, capturedState, before, kind, value]
      using finalFocus
  · unfold rightSourceTracePhaseEnvelope
    dsimp only
    have blocksBound :=
      Nat.add_le_add sourceBound traceBound
    have withCapture :=
      Nat.add_le_add_left blocksBound
        (TargetEmitterControllerGateTrace.sourceCapturePhaseSteps
          before source runtime.scratch)
    have completeBound :=
      Nat.add_le_add_right withCapture
        (TargetEmitterControllerSourceTrace.restorePathSteps
          restoreBefore.length)
    simpa [before, kind, value, marked, capturedState,
      sourceFinal, restoreBefore, Nat.add_assoc] using completeBound

/-! ### Both bounded sources of one raw gate -/

/-- Runtime-sensitive envelope for both source phases of one raw gate. -/
def gateSourcesTraceEnvelope
    (raw : RawCircuit) (before afterGate : List WorkSymbol)
    (gate : RawGate) (runtime : Runtime) : Nat :=
  let leftFinal :=
    TargetEmitterProgramSemantics.macroResult
      (TargetEmitterControllerGateTrace.capturedRuntime runtime
        (TargetEmitterControllerTrace.sourceKind gate.left)
        (TargetEmitterControllerGateTrace.sourceValue gate.left))
      (TargetEmitterPlan.sourcePlan
        (TargetEmitterControllerTrace.sourceKind gate.left) 0)
      (TargetEmitterPlan.sourceCheckRelative
        (TargetEmitterControllerTrace.sourceKind gate.left))
      (TargetEmitterPlan.sourceGateCount
        (TargetEmitterControllerTrace.sourceKind gate.left))
  leftSourcePhaseEnvelope raw before
      (SourceParser.sourceCells gate.right ++ afterGate)
      gate.left runtime +
    rightSourceTracePhaseEnvelope raw
      (before ++ SourceParser.sourceCells gate.left)
      afterGate gate.right leftFinal

/-- Bounded traversal of both sources and the fixed trace macro for one raw
gate. -/
theorem gateSourcesTrace_path_bounded
    {raw : RawCircuit}
    (runtime : Runtime)
    (range : ControllerRange raw runtime.registers)
    (head : WorkSymbol) (prefixTail afterGate : List WorkSymbol)
    (gate : RawGate) (target : List Token)
    (initialTape : WorkTape)
    (leftCaptureReserve :
      runtime.scratch +
          TargetEmitterControllerSourceTrace.capturedValue
            (TargetEmitterControllerTrace.sourceKind gate.left)
            (TargetEmitterControllerGateTrace.sourceValue gate.left) +
          1 ≤
        TargetEmitterLedger.slotCapacity raw)
    (leftCapturedBound :
      TargetEmitterControllerSourceTrace.capturedValue
          (TargetEmitterControllerTrace.sourceKind gate.left)
          (TargetEmitterControllerGateTrace.sourceValue gate.left) +
          1 ≤
        (SourceParser.circuitCells raw).length)
    (afterLeftRange :
      ControllerRange raw
        (TargetEmitterProgramSemantics.macroResult
          (TargetEmitterControllerGateTrace.capturedRuntime runtime
            (TargetEmitterControllerTrace.sourceKind gate.left)
            (TargetEmitterControllerGateTrace.sourceValue gate.left))
          (TargetEmitterPlan.sourcePlan
            (TargetEmitterControllerTrace.sourceKind gate.left) 0)
          (TargetEmitterPlan.sourceCheckRelative
            (TargetEmitterControllerTrace.sourceKind gate.left))
          (TargetEmitterPlan.sourceGateCount
            (TargetEmitterControllerTrace.sourceKind gate.left))).registers)
    (rightCaptureReserve :
      (TargetEmitterProgramSemantics.macroResult
          (TargetEmitterControllerGateTrace.capturedRuntime runtime
            (TargetEmitterControllerTrace.sourceKind gate.left)
            (TargetEmitterControllerGateTrace.sourceValue gate.left))
          (TargetEmitterPlan.sourcePlan
            (TargetEmitterControllerTrace.sourceKind gate.left) 0)
          (TargetEmitterPlan.sourceCheckRelative
            (TargetEmitterControllerTrace.sourceKind gate.left))
          (TargetEmitterPlan.sourceGateCount
            (TargetEmitterControllerTrace.sourceKind gate.left))).scratch +
          TargetEmitterControllerSourceTrace.capturedValue
            (TargetEmitterControllerTrace.sourceKind gate.right)
            (TargetEmitterControllerGateTrace.sourceValue gate.right) +
          1 ≤
        TargetEmitterLedger.slotCapacity raw)
    (rightCapturedBound :
      TargetEmitterControllerSourceTrace.capturedValue
          (TargetEmitterControllerTrace.sourceKind gate.right)
          (TargetEmitterControllerGateTrace.sourceValue gate.right) +
          1 ≤
        (SourceParser.circuitCells raw).length)
    (afterRightRange :
      ControllerRange raw
        (TargetEmitterProgramSemantics.macroResult
          (TargetEmitterControllerGateTrace.capturedRuntime
            (TargetEmitterProgramSemantics.macroResult
              (TargetEmitterControllerGateTrace.capturedRuntime runtime
                (TargetEmitterControllerTrace.sourceKind gate.left)
                (TargetEmitterControllerGateTrace.sourceValue gate.left))
              (TargetEmitterPlan.sourcePlan
                (TargetEmitterControllerTrace.sourceKind gate.left) 0)
              (TargetEmitterPlan.sourceCheckRelative
                (TargetEmitterControllerTrace.sourceKind gate.left))
              (TargetEmitterPlan.sourceGateCount
                (TargetEmitterControllerTrace.sourceKind gate.left)))
            (TargetEmitterControllerTrace.sourceKind gate.right)
            (TargetEmitterControllerGateTrace.sourceValue gate.right))
          (TargetEmitterPlan.sourcePlan
            (TargetEmitterControllerTrace.sourceKind gate.right) 1)
          (TargetEmitterPlan.sourceCheckRelative
            (TargetEmitterControllerTrace.sourceKind gate.right))
          (TargetEmitterPlan.sourceGateCount
            (TargetEmitterControllerTrace.sourceKind gate.right))).registers)
    (nextGate :
      (TargetEmitterProgramSemantics.macroResult
        (TargetEmitterControllerGateTrace.capturedRuntime
          (TargetEmitterProgramSemantics.macroResult
            (TargetEmitterControllerGateTrace.capturedRuntime runtime
              (TargetEmitterControllerTrace.sourceKind gate.left)
              (TargetEmitterControllerGateTrace.sourceValue gate.left))
            (TargetEmitterPlan.sourcePlan
              (TargetEmitterControllerTrace.sourceKind gate.left) 0)
            (TargetEmitterPlan.sourceCheckRelative
              (TargetEmitterControllerTrace.sourceKind gate.left))
            (TargetEmitterPlan.sourceGateCount
              (TargetEmitterControllerTrace.sourceKind gate.left)))
          (TargetEmitterControllerTrace.sourceKind gate.right)
          (TargetEmitterControllerGateTrace.sourceValue gate.right))
        (TargetEmitterPlan.sourcePlan
          (TargetEmitterControllerTrace.sourceKind gate.right) 1)
        (TargetEmitterPlan.sourceCheckRelative
          (TargetEmitterControllerTrace.sourceKind gate.right))
        (TargetEmitterPlan.sourceGateCount
          (TargetEmitterControllerTrace.sourceKind gate.right))).registers.currentGate +
          1 ≤
        TargetEmitterLedger.normalizedGateCount raw)
    (originalPacked :
      ∀ symbol,
        symbol ∈
            (head :: prefixTail) ++
              SourceParser.sourceCells gate.left ++
              SourceParser.sourceCells gate.right ++ afterGate →
          TargetEmitter.PackedSymbol symbol)
    (targetEq : target = runtime.targetTokens)
    (represents :
      FocusTapeRepresents leftFirstRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        (head :: prefixTail)
        (SourceParser.sourceCells gate.left ++
          SourceParser.sourceCells gate.right ++ afterGate)
        target initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node leftFirstRef)
          (.node gateAdvanceRef) steps initialTape finalTape ∧
      ∃ finalRuntime,
        finalRuntime =
          TargetEmitterRuntimeProgramSafety.rightTraceResult
            (TargetEmitterProgramSemantics.macroResult
              (TargetEmitterControllerGateTrace.capturedRuntime
                (TargetEmitterProgramSemantics.macroResult
                  (TargetEmitterControllerGateTrace.capturedRuntime runtime
                    (TargetEmitterControllerTrace.sourceKind gate.left)
                    (TargetEmitterControllerGateTrace.sourceValue
                      gate.left))
                  (TargetEmitterPlan.sourcePlan
                    (TargetEmitterControllerTrace.sourceKind gate.left) 0)
                  (TargetEmitterPlan.sourceCheckRelative
                    (TargetEmitterControllerTrace.sourceKind gate.left))
                  (TargetEmitterPlan.sourceGateCount
                    (TargetEmitterControllerTrace.sourceKind gate.left)))
                (TargetEmitterControllerTrace.sourceKind gate.right)
                (TargetEmitterControllerGateTrace.sourceValue gate.right))
              (TargetEmitterPlan.sourcePlan
                (TargetEmitterControllerTrace.sourceKind gate.right) 1)
              (TargetEmitterPlan.sourceCheckRelative
                (TargetEmitterControllerTrace.sourceKind gate.right))
              (TargetEmitterPlan.sourceGateCount
                (TargetEmitterControllerTrace.sourceKind gate.right))) ∧
        FocusTapeRepresents gateAdvanceRef.startState
          (TargetEmitterLedger.slotCapacity raw)
          finalRuntime.scratch finalRuntime.registers finalRuntime.checks
          ((head :: prefixTail) ++
            SourceParser.sourceCells gate.left ++
            SourceParser.sourceCells gate.right)
          afterGate finalRuntime.targetTokens finalTape ∧
      steps ≤
        gateSourcesTraceEnvelope raw (head :: prefixTail)
          afterGate gate runtime := by
  let leftFinal :=
    TargetEmitterProgramSemantics.macroResult
      (TargetEmitterControllerGateTrace.capturedRuntime runtime
        (TargetEmitterControllerTrace.sourceKind gate.left)
        (TargetEmitterControllerGateTrace.sourceValue gate.left))
      (TargetEmitterPlan.sourcePlan
        (TargetEmitterControllerTrace.sourceKind gate.left) 0)
      (TargetEmitterPlan.sourceCheckRelative
        (TargetEmitterControllerTrace.sourceKind gate.left))
      (TargetEmitterPlan.sourceGateCount
        (TargetEmitterControllerTrace.sourceKind gate.left))
  let rightBase :=
    TargetEmitterControllerGateTrace.capturedRuntime leftFinal
      (TargetEmitterControllerTrace.sourceKind gate.right)
      (TargetEmitterControllerGateTrace.sourceValue gate.right)
  let rightFinal :=
    TargetEmitterProgramSemantics.macroResult rightBase
      (TargetEmitterPlan.sourcePlan
        (TargetEmitterControllerTrace.sourceKind gate.right) 1)
      (TargetEmitterPlan.sourceCheckRelative
        (TargetEmitterControllerTrace.sourceKind gate.right))
      (TargetEmitterPlan.sourceGateCount
        (TargetEmitterControllerTrace.sourceKind gate.right))
  let finalRuntime :=
    TargetEmitterRuntimeProgramSafety.rightTraceResult rightFinal
  have leftPacked :
      ∀ symbol,
        symbol ∈
            (head :: prefixTail) ++
              SourceParser.sourceCells gate.left ++
              (SourceParser.sourceCells gate.right ++ afterGate) →
          TargetEmitter.PackedSymbol symbol := by
    simpa [List.append_assoc] using originalPacked
  rcases
      leftSourcePhase_path_bounded runtime range head prefixTail
        (SourceParser.sourceCells gate.right ++ afterGate)
        gate.left target initialTape
        leftCaptureReserve leftCapturedBound leftPacked targetEq
        (by simpa [TargetEmitterControllerGateTrace.FocusTapeRepresents,
          List.append_assoc]
          using represents) with
    ⟨leftSteps, leftTape, leftPath,
      leftRepresents, leftBound⟩
  have rightPacked :
      ∀ symbol,
        symbol ∈
            (head ::
              (prefixTail ++ SourceParser.sourceCells gate.left)) ++
              SourceParser.sourceCells gate.right ++ afterGate →
          TargetEmitter.PackedSymbol symbol := by
    simpa [List.append_assoc] using originalPacked
  rcases
      rightSourceTracePhase_path_bounded leftFinal
        (by simpa [leftFinal] using afterLeftRange)
        head (prefixTail ++ SourceParser.sourceCells gate.left)
        afterGate gate.right leftFinal.targetTokens leftTape
        (by simpa [leftFinal] using rightCaptureReserve)
        rightCapturedBound
        (by simpa [rightFinal, rightBase, leftFinal] using
          afterRightRange)
        (by simpa [rightFinal, rightBase, leftFinal] using nextGate)
        rightPacked rfl
        (by simpa [TargetEmitterControllerGateTrace.FocusTapeRepresents,
          leftFinal,
          List.append_assoc] using leftRepresents) with
    ⟨rightSteps, finalTape, rightPath,
      rightRepresents, rightBound⟩
  have path :=
    AcceptPath.trans graph (.node leftFirstRef)
      (.node rightFirstRef) (.node gateAdvanceRef)
      leftSteps rightSteps initialTape leftTape finalTape
      leftPath rightPath
  refine
    ⟨leftSteps + rightSteps, finalTape, path,
      finalRuntime, rfl, ?_, ?_⟩
  · simpa [finalRuntime, rightFinal, rightBase, leftFinal,
      List.append_assoc] using rightRepresents
  · unfold gateSourcesTraceEnvelope
    dsimp only
    simpa [leftFinal, List.append_assoc] using
      Nat.add_le_add leftBound rightBound

/-! ### Uniform one-gate domination -/

/-- One fixed upper bound for each of the two source programs and the
right-trace program used while traversing a raw gate. -/
def gateProgramLimit : Nat := 512

/-- Maximum logical target/check-cell growth charged to one fixed gate
program. -/
def gateBlockGrowth (capacity : Nat) : Nat :=
  gateProgramLimit * (capacity + 1)

/-- Target-token budget shared by every program reached in a gate-list
traversal. -/
def gateTargetLimit (capacity : Nat) (origin : Runtime)
    (gateBudget : Nat) : Nat :=
  origin.targetTokens.length +
    3 * gateBudget * gateBlockGrowth capacity

/-- Check-stack cell budget shared by every program reached in a gate-list
traversal. -/
def gateCheckLimit (capacity : Nat) (origin : Runtime)
    (gateBudget : Nat) : Nat :=
  TargetEmitterRuntimeProgramBound.checkCells origin.checks +
    3 * gateBudget * gateBlockGrowth capacity

/-- One physical footprint dominating every fixed program in a bounded
gate-list traversal. -/
def gateMasterSize (capacity sourceLength : Nat)
    (origin : Runtime) (gateBudget : Nat) : Nat :=
  capacity + sourceLength +
    2 * gateTargetLimit capacity origin gateBudget +
    gateCheckLimit capacity origin gateBudget +
    gateProgramLimit * (3 * capacity + 3) + 1

/-- Uniform charge for any source or trace program in one gate. -/
def gateBlockUnit (capacity sourceLength : Nat)
    (origin : Runtime) (gateBudget : Nat) : Nat :=
  gateProgramLimit *
    (TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
      (gateMasterSize capacity sourceLength origin gateBudget) + 1)

/-- Uniform charge for one classifier/capture pass. -/
def gateCaptureUnit (capacity sourceLength : Nat) : Nat :=
  TargetEmitterControllerNormalizationBound.sourceCaptureTimePolynomial.eval
    (capacity + sourceLength)

/-- Uniform charge for restoring one captured source cursor. -/
def gateRestoreUnit (sourceLength : Nat) : Nat :=
  sourceLength + 2

/-- One closed charge for both source captures, all three fixed programs,
and both cursor restorations of a raw gate. -/
def gateUniformUnit (capacity sourceLength : Nat)
    (origin : Runtime) (gateBudget : Nat) : Nat :=
  2 * gateCaptureUnit capacity sourceLength +
    3 * gateBlockUnit capacity sourceLength origin gateBudget +
    2 * gateRestoreUnit sourceLength

private theorem leftSource_length_le_limit (kind : SourceKind) :
    (Plan.source kind 0).length ≤ gateProgramLimit := by
  cases kind <;> decide

private theorem rightSource_length_le_limit (kind : SourceKind) :
    (Plan.source kind 1).length ≤ gateProgramLimit := by
  cases kind <;> decide

private theorem rightTrace_length_le_limit :
    Plan.rightTrace.length ≤ gateProgramLimit := by
  decide

private theorem ProgramSafe.target_length_le
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    {primitives : List TargetEmitterPlan.Primitive}
    {initial final : Runtime}
    (safe :
      ProgramSafe capacity source context primitives initial final) :
    final.targetTokens.length ≤
      initial.targetTokens.length +
        primitives.length * (capacity + 1) := by
  induction safe with
  | nil =>
      simp
  | cons primitive rest initial middle final head tail
      inductionHypothesis =>
      have headBound :=
        TargetEmitterRuntimeProgramBound.PrimitiveSafe.target_length_le
          head
      simp only [List.length_cons, Nat.succ_mul]
      omega

private theorem ProgramSafe.checkCells_le
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    {primitives : List TargetEmitterPlan.Primitive}
    {initial final : Runtime}
    (safe :
      ProgramSafe capacity source context primitives initial final) :
    TargetEmitterRuntimeProgramBound.checkCells final.checks ≤
      TargetEmitterRuntimeProgramBound.checkCells initial.checks +
        primitives.length * (capacity + 1) := by
  induction safe with
  | nil =>
      simp
  | cons primitive rest initial middle final head tail
      inductionHypothesis =>
      have headBound :=
        TargetEmitterRuntimeProgramBound.PrimitiveSafe.checkCells_le
          head
      simp only [List.length_cons, Nat.succ_mul]
      omega

private theorem programEnvelope_le_gateBlockUnit
    (capacity sourceLength : Nat) (source : List WorkSymbol)
    (origin current : Runtime) (gateBudget : Nat)
    (primitives : List TargetEmitterPlan.Primitive)
    (programLength : primitives.length ≤ gateProgramLimit)
    (sourceBound : source.length ≤ sourceLength)
    (targetBound :
      current.targetTokens.length ≤
        gateTargetLimit capacity origin gateBudget)
    (checkBound :
      TargetEmitterRuntimeProgramBound.checkCells current.checks ≤
        gateCheckLimit capacity origin gateBudget) :
    TargetEmitterRuntimeProgramBound.programWorkEnvelope
        capacity source current primitives ≤
      gateBlockUnit capacity sourceLength origin gateBudget := by
  have footprintBound :
      TargetEmitterRuntimeProgramBound.runtimeFootprint
          capacity source current primitives.length ≤
        gateMasterSize capacity sourceLength origin gateBudget := by
    unfold TargetEmitterRuntimeProgramBound.runtimeFootprint
      gateMasterSize
    have reserved :
        primitives.length * (3 * capacity + 3) ≤
          gateProgramLimit * (3 * capacity + 3) :=
      Nat.mul_le_mul_right (3 * capacity + 3) programLength
    omega
  have squareBound :
      TargetEmitterRuntimeProgramBound.runtimeFootprint
            capacity source current primitives.length *
          TargetEmitterRuntimeProgramBound.runtimeFootprint
            capacity source current primitives.length ≤
        gateMasterSize capacity sourceLength origin gateBudget *
          gateMasterSize capacity sourceLength origin gateBudget :=
    Nat.mul_le_mul footprintBound footprintBound
  have primitiveBound :
      TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
            (TargetEmitterRuntimeProgramBound.runtimeFootprint
              capacity source current primitives.length) + 1 ≤
        TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
            (gateMasterSize capacity sourceLength origin gateBudget) + 1 := by
    unfold TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_left 100 squareBound) 101
  have totalBound :=
    Nat.mul_le_mul programLength primitiveBound
  simpa [TargetEmitterRuntimeProgramBound.programWorkEnvelope,
    gateBlockUnit] using totalBound

private theorem sourceValue_le_sourceCells_length
    (source : RawSource) :
    TargetEmitterControllerGateTrace.sourceValue source ≤
      (SourceParser.sourceCells source).length := by
  cases source with
  | input value =>
      simp [TargetEmitterControllerGateTrace.sourceValue,
        SourceParser.sourceCells, SourceParser.natCells_length]
      omega
  | gate value =>
      simp [TargetEmitterControllerGateTrace.sourceValue,
        SourceParser.sourceCells, SourceParser.natCells_length]
      omega
  | constant value =>
      cases value <;>
        simp [TargetEmitterControllerGateTrace.sourceValue,
          SourceParser.sourceCells]

private theorem markedWord_length_eq
    (before after : List WorkSymbol) (source : RawSource) :
    let kind := TargetEmitterControllerTrace.sourceKind source
    let value := TargetEmitterControllerGateTrace.sourceValue source
    (before ++
        TargetEmitterControllerSourceTrace.captureMarkedSourceCells
          kind value ++ after).length =
      (before ++ SourceParser.sourceCells source ++ after).length := by
  cases source with
  | input value =>
      simp [TargetEmitterControllerTrace.sourceKind,
        TargetEmitterControllerGateTrace.sourceValue,
        TargetEmitterControllerSourceTrace.captureMarkedSourceCells,
        TargetEmitterControllerSourceTrace.capturedValue,
        TargetEmitterSourceCapture.markedSourceCells,
        Plan.captureKind,
        TargetEmitterSourceCapture.unitPrefix_length,
        SourceParser.sourceCells, SourceParser.natCells_length]
      omega
  | gate value =>
      simp [TargetEmitterControllerTrace.sourceKind,
        TargetEmitterControllerGateTrace.sourceValue,
        TargetEmitterControllerSourceTrace.captureMarkedSourceCells,
        TargetEmitterControllerSourceTrace.capturedValue,
        TargetEmitterSourceCapture.markedSourceCells,
        Plan.captureKind,
        TargetEmitterSourceCapture.unitPrefix_length,
        SourceParser.sourceCells, SourceParser.natCells_length]
      omega
  | constant value =>
      cases value <;>
        simp [TargetEmitterControllerTrace.sourceKind,
          TargetEmitterControllerSourceTrace.captureMarkedSourceCells,
          TargetEmitterSourceCapture.markedSourceCells,
          Plan.captureKind,
          SourceParser.sourceCells]

private theorem restoreBefore_length_le_word
    (before after : List WorkSymbol) (source : RawSource) :
    let kind := TargetEmitterControllerTrace.sourceKind source
    let value := TargetEmitterControllerGateTrace.sourceValue source
    (before ++
        TargetEmitterRuntimeLayout.localCursorBefore
          (Plan.captureKind kind)
          (TargetEmitterControllerSourceTrace.capturedValue
            kind value)).length ≤
      (before ++ SourceParser.sourceCells source ++ after).length := by
  cases source with
  | input value =>
      simp [TargetEmitterControllerTrace.sourceKind,
        TargetEmitterControllerGateTrace.sourceValue,
        TargetEmitterControllerSourceTrace.capturedValue,
        TargetEmitterRuntimeLayout.localCursorBefore,
        Plan.captureKind,
        TargetEmitterSourceCapture.unitPrefix_length,
        SourceParser.sourceCells, SourceParser.natCells_length]
      omega
  | gate value =>
      simp [TargetEmitterControllerTrace.sourceKind,
        TargetEmitterControllerGateTrace.sourceValue,
        TargetEmitterControllerSourceTrace.capturedValue,
        TargetEmitterRuntimeLayout.localCursorBefore,
        Plan.captureKind,
        TargetEmitterSourceCapture.unitPrefix_length,
        SourceParser.sourceCells, SourceParser.natCells_length]
      omega
  | constant value =>
      cases value <;>
        simp [TargetEmitterControllerTrace.sourceKind,
          TargetEmitterRuntimeLayout.localCursorBefore,
          Plan.captureKind, SourceParser.sourceCells]

private theorem leftSourceProgram_bounds
    {raw : RawCircuit} {source : List WorkSymbol}
    {runtime origin : Runtime} {kind : SourceKind}
    (workspace : MarkedWorkspace source)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (ready : SourceReady raw source runtime.captured kind)
    (sourceLength gateBudget : Nat)
    (sourceBound : source.length ≤ sourceLength)
    (targetBound :
      runtime.targetTokens.length ≤
        gateTargetLimit
          (TargetEmitterLedger.slotCapacity raw) origin gateBudget)
    (checkBound :
      TargetEmitterRuntimeProgramBound.checkCells runtime.checks ≤
        gateCheckLimit
          (TargetEmitterLedger.slotCapacity raw) origin gateBudget) :
    let final :=
      TargetEmitterProgramSemantics.macroResult runtime
        (TargetEmitterPlan.sourcePlan kind 0)
        (TargetEmitterPlan.sourceCheckRelative kind)
        (TargetEmitterPlan.sourceGateCount kind)
    TargetEmitterRuntimeProgramBound.programWorkEnvelope
          (TargetEmitterLedger.slotCapacity raw) source runtime
          (Plan.source kind 0) ≤
        gateBlockUnit
          (TargetEmitterLedger.slotCapacity raw) sourceLength
          origin gateBudget ∧
      final.targetTokens.length ≤
        runtime.targetTokens.length +
          gateBlockGrowth (TargetEmitterLedger.slotCapacity raw) ∧
      TargetEmitterRuntimeProgramBound.checkCells final.checks ≤
        TargetEmitterRuntimeProgramBound.checkCells runtime.checks +
          gateBlockGrowth
            (TargetEmitterLedger.slotCapacity raw) := by
  let final :=
    TargetEmitterProgramSemantics.macroResult runtime
      (TargetEmitterPlan.sourcePlan kind 0)
      (TargetEmitterPlan.sourceCheckRelative kind)
      (TargetEmitterPlan.sourceGateCount kind)
  have safe :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        (Plan.source kind 0) runtime final := by
    simpa [final] using
      source_safe kind workspace range capturedBound scratchBound
        ready (by omega)
  have targetGrowth := ProgramSafe.target_length_le safe
  have checkGrowth := ProgramSafe.checkCells_le safe
  have lengthBound := leftSource_length_le_limit kind
  refine
    ⟨programEnvelope_le_gateBlockUnit
        (TargetEmitterLedger.slotCapacity raw) sourceLength source
        origin runtime gateBudget (Plan.source kind 0)
        lengthBound sourceBound targetBound checkBound, ?_, ?_⟩
  · simpa [final, gateBlockGrowth] using
      Nat.le_trans targetGrowth
        (Nat.add_le_add_left
          (Nat.mul_le_mul_right
            (TargetEmitterLedger.slotCapacity raw + 1)
            lengthBound)
          runtime.targetTokens.length)
  · simpa [final, gateBlockGrowth] using
      Nat.le_trans checkGrowth
        (Nat.add_le_add_left
          (Nat.mul_le_mul_right
            (TargetEmitterLedger.slotCapacity raw + 1)
            lengthBound)
          (TargetEmitterRuntimeProgramBound.checkCells
            runtime.checks))

private theorem rightSourceProgram_bounds
    {raw : RawCircuit} {source : List WorkSymbol}
    {runtime origin : Runtime} {kind : SourceKind}
    (workspace : MarkedWorkspace source)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (ready : SourceReady raw source runtime.captured kind)
    (sourceLength gateBudget : Nat)
    (sourceBound : source.length ≤ sourceLength)
    (targetBound :
      runtime.targetTokens.length ≤
        gateTargetLimit
          (TargetEmitterLedger.slotCapacity raw) origin gateBudget)
    (checkBound :
      TargetEmitterRuntimeProgramBound.checkCells runtime.checks ≤
        gateCheckLimit
          (TargetEmitterLedger.slotCapacity raw) origin gateBudget) :
    let final :=
      TargetEmitterProgramSemantics.macroResult runtime
        (TargetEmitterPlan.sourcePlan kind 1)
        (TargetEmitterPlan.sourceCheckRelative kind)
        (TargetEmitterPlan.sourceGateCount kind)
    TargetEmitterRuntimeProgramBound.programWorkEnvelope
          (TargetEmitterLedger.slotCapacity raw) source runtime
          (Plan.source kind 1) ≤
        gateBlockUnit
          (TargetEmitterLedger.slotCapacity raw) sourceLength
          origin gateBudget ∧
      final.targetTokens.length ≤
        runtime.targetTokens.length +
          gateBlockGrowth (TargetEmitterLedger.slotCapacity raw) ∧
      TargetEmitterRuntimeProgramBound.checkCells final.checks ≤
        TargetEmitterRuntimeProgramBound.checkCells runtime.checks +
          gateBlockGrowth
            (TargetEmitterLedger.slotCapacity raw) := by
  let final :=
    TargetEmitterProgramSemantics.macroResult runtime
      (TargetEmitterPlan.sourcePlan kind 1)
      (TargetEmitterPlan.sourceCheckRelative kind)
      (TargetEmitterPlan.sourceGateCount kind)
  have safe :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        (Plan.source kind 1) runtime final := by
    simpa [final] using
      source_safe kind workspace range capturedBound scratchBound
        ready (by omega)
  have targetGrowth := ProgramSafe.target_length_le safe
  have checkGrowth := ProgramSafe.checkCells_le safe
  have lengthBound := rightSource_length_le_limit kind
  refine
    ⟨programEnvelope_le_gateBlockUnit
        (TargetEmitterLedger.slotCapacity raw) sourceLength source
        origin runtime gateBudget (Plan.source kind 1)
        lengthBound sourceBound targetBound checkBound, ?_, ?_⟩
  · simpa [final, gateBlockGrowth] using
      Nat.le_trans targetGrowth
        (Nat.add_le_add_left
          (Nat.mul_le_mul_right
            (TargetEmitterLedger.slotCapacity raw + 1)
            lengthBound)
          runtime.targetTokens.length)
  · simpa [final, gateBlockGrowth] using
      Nat.le_trans checkGrowth
        (Nat.add_le_add_left
          (Nat.mul_le_mul_right
            (TargetEmitterLedger.slotCapacity raw + 1)
            lengthBound)
          (TargetEmitterRuntimeProgramBound.checkCells
            runtime.checks))

private theorem rightTraceProgram_bounds
    {raw : RawCircuit} {source : List WorkSymbol}
    {runtime origin : Runtime}
    (workspace : MarkedWorkspace source)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (nextGate :
      runtime.registers.currentGate + 1 ≤
        TargetEmitterLedger.normalizedGateCount raw)
    (sourceLength gateBudget : Nat)
    (sourceBound : source.length ≤ sourceLength)
    (targetBound :
      runtime.targetTokens.length ≤
        gateTargetLimit
          (TargetEmitterLedger.slotCapacity raw) origin gateBudget)
    (checkBound :
      TargetEmitterRuntimeProgramBound.checkCells runtime.checks ≤
        gateCheckLimit
          (TargetEmitterLedger.slotCapacity raw) origin gateBudget) :
    let final :=
      TargetEmitterRuntimeProgramSafety.rightTraceResult runtime
    TargetEmitterRuntimeProgramBound.programWorkEnvelope
          (TargetEmitterLedger.slotCapacity raw) source runtime
          Plan.rightTrace ≤
        gateBlockUnit
          (TargetEmitterLedger.slotCapacity raw) sourceLength
          origin gateBudget ∧
      final.targetTokens.length ≤
        runtime.targetTokens.length +
          gateBlockGrowth (TargetEmitterLedger.slotCapacity raw) ∧
      TargetEmitterRuntimeProgramBound.checkCells final.checks ≤
        TargetEmitterRuntimeProgramBound.checkCells runtime.checks +
          gateBlockGrowth
            (TargetEmitterLedger.slotCapacity raw) := by
  let final :=
    TargetEmitterRuntimeProgramSafety.rightTraceResult runtime
  have safe :
      ProgramSafe
        (TargetEmitterLedger.slotCapacity raw) source workspace.context
        Plan.rightTrace runtime final := by
    simpa [final] using
      TargetEmitterRuntimeProgramSafety.rightTrace_safe
        workspace range capturedBound scratchBound nextGate
  have targetGrowth := ProgramSafe.target_length_le safe
  have checkGrowth := ProgramSafe.checkCells_le safe
  refine
    ⟨programEnvelope_le_gateBlockUnit
        (TargetEmitterLedger.slotCapacity raw) sourceLength source
        origin runtime gateBudget Plan.rightTrace
        rightTrace_length_le_limit sourceBound targetBound checkBound,
      ?_, ?_⟩
  · simpa [final, gateBlockGrowth] using
      Nat.le_trans targetGrowth
        (Nat.add_le_add_left
          (Nat.mul_le_mul_right
            (TargetEmitterLedger.slotCapacity raw + 1)
            rightTrace_length_le_limit)
          runtime.targetTokens.length)
  · simpa [final, gateBlockGrowth] using
      Nat.le_trans checkGrowth
        (Nat.add_le_add_left
          (Nat.mul_le_mul_right
            (TargetEmitterLedger.slotCapacity raw + 1)
            rightTrace_length_le_limit)
          (TargetEmitterRuntimeProgramBound.checkCells
            runtime.checks))

/-- Both source phases of one raw gate are dominated by one closed uniform
unit.  The additional conjunctions expose the bounded logical growth needed
to carry the same budget through the recursive gate-list traversal. -/
theorem gateSourcesTraceEnvelope_le_uniform
    {raw : RawCircuit}
    (runtime origin : Runtime)
    (range : ControllerRange raw runtime.registers)
    (head : WorkSymbol) (prefixTail afterGate : List WorkSymbol)
    (gate : RawGate)
    (leftCaptureReserve :
      runtime.scratch +
          TargetEmitterControllerSourceTrace.capturedValue
            (TargetEmitterControllerTrace.sourceKind gate.left)
            (TargetEmitterControllerGateTrace.sourceValue gate.left) +
          1 ≤
        TargetEmitterLedger.slotCapacity raw)
    (leftCapturedBound :
      TargetEmitterControllerSourceTrace.capturedValue
          (TargetEmitterControllerTrace.sourceKind gate.left)
          (TargetEmitterControllerGateTrace.sourceValue gate.left) +
          1 ≤
        (SourceParser.circuitCells raw).length)
    (afterLeftRange :
      ControllerRange raw
        (TargetEmitterProgramSemantics.macroResult
          (TargetEmitterControllerGateTrace.capturedRuntime runtime
            (TargetEmitterControllerTrace.sourceKind gate.left)
            (TargetEmitterControllerGateTrace.sourceValue gate.left))
          (TargetEmitterPlan.sourcePlan
            (TargetEmitterControllerTrace.sourceKind gate.left) 0)
          (TargetEmitterPlan.sourceCheckRelative
            (TargetEmitterControllerTrace.sourceKind gate.left))
          (TargetEmitterPlan.sourceGateCount
            (TargetEmitterControllerTrace.sourceKind gate.left))).registers)
    (rightCaptureReserve :
      (TargetEmitterProgramSemantics.macroResult
          (TargetEmitterControllerGateTrace.capturedRuntime runtime
            (TargetEmitterControllerTrace.sourceKind gate.left)
            (TargetEmitterControllerGateTrace.sourceValue gate.left))
          (TargetEmitterPlan.sourcePlan
            (TargetEmitterControllerTrace.sourceKind gate.left) 0)
          (TargetEmitterPlan.sourceCheckRelative
            (TargetEmitterControllerTrace.sourceKind gate.left))
          (TargetEmitterPlan.sourceGateCount
            (TargetEmitterControllerTrace.sourceKind gate.left))).scratch +
          TargetEmitterControllerSourceTrace.capturedValue
            (TargetEmitterControllerTrace.sourceKind gate.right)
            (TargetEmitterControllerGateTrace.sourceValue gate.right) +
          1 ≤
        TargetEmitterLedger.slotCapacity raw)
    (rightCapturedBound :
      TargetEmitterControllerSourceTrace.capturedValue
          (TargetEmitterControllerTrace.sourceKind gate.right)
          (TargetEmitterControllerGateTrace.sourceValue gate.right) +
          1 ≤
        (SourceParser.circuitCells raw).length)
    (afterRightRange :
      ControllerRange raw
        (TargetEmitterProgramSemantics.macroResult
          (TargetEmitterControllerGateTrace.capturedRuntime
            (TargetEmitterProgramSemantics.macroResult
              (TargetEmitterControllerGateTrace.capturedRuntime runtime
                (TargetEmitterControllerTrace.sourceKind gate.left)
                (TargetEmitterControllerGateTrace.sourceValue gate.left))
              (TargetEmitterPlan.sourcePlan
                (TargetEmitterControllerTrace.sourceKind gate.left) 0)
              (TargetEmitterPlan.sourceCheckRelative
                (TargetEmitterControllerTrace.sourceKind gate.left))
              (TargetEmitterPlan.sourceGateCount
                (TargetEmitterControllerTrace.sourceKind gate.left)))
            (TargetEmitterControllerTrace.sourceKind gate.right)
            (TargetEmitterControllerGateTrace.sourceValue gate.right))
          (TargetEmitterPlan.sourcePlan
            (TargetEmitterControllerTrace.sourceKind gate.right) 1)
          (TargetEmitterPlan.sourceCheckRelative
            (TargetEmitterControllerTrace.sourceKind gate.right))
          (TargetEmitterPlan.sourceGateCount
            (TargetEmitterControllerTrace.sourceKind gate.right))).registers)
    (nextGate :
      (TargetEmitterProgramSemantics.macroResult
        (TargetEmitterControllerGateTrace.capturedRuntime
          (TargetEmitterProgramSemantics.macroResult
            (TargetEmitterControllerGateTrace.capturedRuntime runtime
              (TargetEmitterControllerTrace.sourceKind gate.left)
              (TargetEmitterControllerGateTrace.sourceValue gate.left))
            (TargetEmitterPlan.sourcePlan
              (TargetEmitterControllerTrace.sourceKind gate.left) 0)
            (TargetEmitterPlan.sourceCheckRelative
              (TargetEmitterControllerTrace.sourceKind gate.left))
            (TargetEmitterPlan.sourceGateCount
              (TargetEmitterControllerTrace.sourceKind gate.left)))
          (TargetEmitterControllerTrace.sourceKind gate.right)
          (TargetEmitterControllerGateTrace.sourceValue gate.right))
        (TargetEmitterPlan.sourcePlan
          (TargetEmitterControllerTrace.sourceKind gate.right) 1)
        (TargetEmitterPlan.sourceCheckRelative
          (TargetEmitterControllerTrace.sourceKind gate.right))
        (TargetEmitterPlan.sourceGateCount
          (TargetEmitterControllerTrace.sourceKind gate.right))).registers.currentGate +
          1 ≤
        TargetEmitterLedger.normalizedGateCount raw)
    (originalPacked :
      ∀ symbol,
        symbol ∈
            (head :: prefixTail) ++
              SourceParser.sourceCells gate.left ++
              SourceParser.sourceCells gate.right ++ afterGate →
          TargetEmitter.PackedSymbol symbol)
    (sourceLength gateBudget : Nat)
    (sourceLengthBound :
      ((head :: prefixTail) ++
          SourceParser.sourceCells gate.left ++
          SourceParser.sourceCells gate.right ++ afterGate).length ≤
        sourceLength)
    (targetBudget :
      runtime.targetTokens.length +
          2 * gateBlockGrowth
            (TargetEmitterLedger.slotCapacity raw) ≤
        gateTargetLimit
          (TargetEmitterLedger.slotCapacity raw) origin gateBudget)
    (checkBudget :
      TargetEmitterRuntimeProgramBound.checkCells runtime.checks +
          2 * gateBlockGrowth
            (TargetEmitterLedger.slotCapacity raw) ≤
        gateCheckLimit
          (TargetEmitterLedger.slotCapacity raw) origin gateBudget) :
    let leftFinal :=
      TargetEmitterProgramSemantics.macroResult
        (TargetEmitterControllerGateTrace.capturedRuntime runtime
          (TargetEmitterControllerTrace.sourceKind gate.left)
          (TargetEmitterControllerGateTrace.sourceValue gate.left))
        (TargetEmitterPlan.sourcePlan
          (TargetEmitterControllerTrace.sourceKind gate.left) 0)
        (TargetEmitterPlan.sourceCheckRelative
          (TargetEmitterControllerTrace.sourceKind gate.left))
        (TargetEmitterPlan.sourceGateCount
          (TargetEmitterControllerTrace.sourceKind gate.left))
    let rightFinal :=
      TargetEmitterProgramSemantics.macroResult
        (TargetEmitterControllerGateTrace.capturedRuntime leftFinal
          (TargetEmitterControllerTrace.sourceKind gate.right)
          (TargetEmitterControllerGateTrace.sourceValue gate.right))
        (TargetEmitterPlan.sourcePlan
          (TargetEmitterControllerTrace.sourceKind gate.right) 1)
        (TargetEmitterPlan.sourceCheckRelative
          (TargetEmitterControllerTrace.sourceKind gate.right))
        (TargetEmitterPlan.sourceGateCount
          (TargetEmitterControllerTrace.sourceKind gate.right))
    let final :=
      TargetEmitterRuntimeProgramSafety.rightTraceResult rightFinal
    gateSourcesTraceEnvelope raw (head :: prefixTail)
          afterGate gate runtime ≤
        gateUniformUnit
          (TargetEmitterLedger.slotCapacity raw) sourceLength
          origin gateBudget ∧
      final.targetTokens.length ≤
        runtime.targetTokens.length +
          3 * gateBlockGrowth
            (TargetEmitterLedger.slotCapacity raw) ∧
      TargetEmitterRuntimeProgramBound.checkCells final.checks ≤
        TargetEmitterRuntimeProgramBound.checkCells runtime.checks +
          3 * gateBlockGrowth
            (TargetEmitterLedger.slotCapacity raw) := by
  let capacity := TargetEmitterLedger.slotCapacity raw
  let before := head :: prefixTail
  let leftKind := TargetEmitterControllerTrace.sourceKind gate.left
  let leftValue := TargetEmitterControllerGateTrace.sourceValue gate.left
  let leftMarked :=
    before ++
      TargetEmitterControllerSourceTrace.captureMarkedSourceCells
        leftKind leftValue ++
      (SourceParser.sourceCells gate.right ++ afterGate)
  let leftCaptured :=
    TargetEmitterControllerGateTrace.capturedRuntime
      runtime leftKind leftValue
  let leftFinal :=
    TargetEmitterProgramSemantics.macroResult leftCaptured
      (TargetEmitterPlan.sourcePlan leftKind 0)
      (TargetEmitterPlan.sourceCheckRelative leftKind)
      (TargetEmitterPlan.sourceGateCount leftKind)
  have leftBeforePacked :
      ∀ symbol, symbol ∈ before →
        TargetEmitter.PackedSymbol symbol := by
    intro symbol member
    exact originalPacked symbol
      (List.mem_append.mpr
        (Or.inl
          (List.mem_append.mpr
            (Or.inl (List.mem_append.mpr (Or.inl member))))))
  have leftOriginalCapturePacked :
      ∀ symbol,
        symbol ∈
            before ++
              TargetEmitterControllerSourceTrace.captureSourceCells
                leftKind leftValue ++
              (SourceParser.sourceCells gate.right ++ afterGate) →
          TargetEmitter.PackedSymbol symbol := by
    simpa [before, leftKind, leftValue,
      ← TargetEmitterControllerGateTrace.sourceCells_eq_captureSourceCells
        gate.left,
      List.append_assoc] using originalPacked
  let leftWorkspace :=
    TargetEmitterControllerGateTrace.markedWorkspace
      leftKind leftValue head prefixTail
      (SourceParser.sourceCells gate.right ++ afterGate)
      (by simpa [before] using leftOriginalCapturePacked)
  have leftValueCapacity :
      TargetEmitterControllerSourceTrace.capturedValue
            leftKind leftValue + 1 ≤ capacity := by
    dsimp only [capacity]
    simp [leftKind, leftValue] at leftCaptureReserve ⊢
    omega
  let leftReady :=
    TargetEmitterControllerGateTrace.sourceReady
      raw leftKind leftValue before
      (SourceParser.sourceCells gate.right ++ afterGate)
      leftBeforePacked leftValueCapacity
  have leftCapturedScratch :
      leftCaptured.scratch < capacity := by
    dsimp only [leftCaptured, capacity]
    simp [TargetEmitterControllerGateTrace.capturedRuntime,
      leftKind, leftValue]
    omega
  have leftCapturedIndex :
      leftCaptured.captured + 1 ≤
        (SourceParser.circuitCells raw).length := by
    simpa [leftCaptured,
      TargetEmitterControllerGateTrace.capturedRuntime,
      leftKind, leftValue] using leftCapturedBound
  have leftMarkedLength :
      leftMarked.length ≤ sourceLength := by
    have equal :=
      markedWord_length_eq before
        (SourceParser.sourceCells gate.right ++ afterGate)
        gate.left
    calc
      leftMarked.length =
          (before ++ SourceParser.sourceCells gate.left ++
            (SourceParser.sourceCells gate.right ++ afterGate)).length := by
        simpa [leftMarked, leftKind, leftValue] using equal
      _ =
          ((head :: prefixTail) ++
            SourceParser.sourceCells gate.left ++
            SourceParser.sourceCells gate.right ++ afterGate).length := by
        simp [before, List.append_assoc]
      _ ≤ sourceLength := sourceLengthBound
  have currentTarget :
      runtime.targetTokens.length ≤
        gateTargetLimit capacity origin gateBudget := by
    exact Nat.le_trans
      (Nat.le_add_right runtime.targetTokens.length
        (2 * gateBlockGrowth capacity))
      (by simpa [capacity] using targetBudget)
  have currentChecks :
      TargetEmitterRuntimeProgramBound.checkCells runtime.checks ≤
        gateCheckLimit capacity origin gateBudget := by
    exact Nat.le_trans
      (Nat.le_add_right
        (TargetEmitterRuntimeProgramBound.checkCells runtime.checks)
        (2 * gateBlockGrowth capacity))
      (by simpa [capacity] using checkBudget)
  have leftProgram :=
    leftSourceProgram_bounds leftWorkspace
      (by simpa [leftCaptured,
        TargetEmitterControllerGateTrace.capturedRuntime] using range)
      leftCapturedIndex leftCapturedScratch leftReady
      sourceLength gateBudget leftMarkedLength
      (by simpa [leftCaptured,
        TargetEmitterControllerGateTrace.capturedRuntime] using
          currentTarget)
      (by simpa [leftCaptured,
        TargetEmitterControllerGateTrace.capturedRuntime] using
          currentChecks)
  rcases leftProgram with
    ⟨leftBlockBound, leftTargetGrowth, leftCheckGrowth⟩
  have leftTargetLimit :
      leftFinal.targetTokens.length ≤
        gateTargetLimit capacity origin gateBudget := by
    have room :
        runtime.targetTokens.length + gateBlockGrowth capacity ≤
          gateTargetLimit capacity origin gateBudget := by
      have := targetBudget
      dsimp only [capacity] at this ⊢
      omega
    exact Nat.le_trans
      (by
        simpa [leftFinal, leftCaptured,
          TargetEmitterControllerGateTrace.capturedRuntime, capacity] using
            leftTargetGrowth)
      room
  have leftCheckLimit :
      TargetEmitterRuntimeProgramBound.checkCells leftFinal.checks ≤
        gateCheckLimit capacity origin gateBudget := by
    have room :
        TargetEmitterRuntimeProgramBound.checkCells runtime.checks +
              gateBlockGrowth capacity ≤
          gateCheckLimit capacity origin gateBudget := by
      have := checkBudget
      dsimp only [capacity] at this ⊢
      omega
    exact Nat.le_trans
      (by
        simpa [leftFinal, leftCaptured,
          TargetEmitterControllerGateTrace.capturedRuntime, capacity] using
            leftCheckGrowth)
      room
  let rightKind :=
    TargetEmitterControllerTrace.sourceKind gate.right
  let rightValue :=
    TargetEmitterControllerGateTrace.sourceValue gate.right
  let rightBefore :=
    before ++ SourceParser.sourceCells gate.left
  let rightMarked :=
    rightBefore ++
      TargetEmitterControllerSourceTrace.captureMarkedSourceCells
        rightKind rightValue ++ afterGate
  let rightCaptured :=
    TargetEmitterControllerGateTrace.capturedRuntime
      leftFinal rightKind rightValue
  let rightFinal :=
    TargetEmitterProgramSemantics.macroResult rightCaptured
      (TargetEmitterPlan.sourcePlan rightKind 1)
      (TargetEmitterPlan.sourceCheckRelative rightKind)
      (TargetEmitterPlan.sourceGateCount rightKind)
  have rightBeforePacked :
      ∀ symbol, symbol ∈ rightBefore →
        TargetEmitter.PackedSymbol symbol := by
    intro symbol member
    exact originalPacked symbol
      (List.mem_append.mpr
        (Or.inl (List.mem_append.mpr (Or.inl member))))
  have rightOriginalCapturePacked :
      ∀ symbol,
        symbol ∈
            rightBefore ++
              TargetEmitterControllerSourceTrace.captureSourceCells
                rightKind rightValue ++ afterGate →
          TargetEmitter.PackedSymbol symbol := by
    simpa [rightBefore, before, rightKind, rightValue,
      ← TargetEmitterControllerGateTrace.sourceCells_eq_captureSourceCells
        gate.right,
      List.append_assoc] using originalPacked
  let rightWorkspace :=
    TargetEmitterControllerGateTrace.markedWorkspace
      rightKind rightValue head
      (prefixTail ++ SourceParser.sourceCells gate.left)
      afterGate
      (by simpa [rightBefore, before, List.append_assoc] using
        rightOriginalCapturePacked)
  have rightValueCapacity :
      TargetEmitterControllerSourceTrace.capturedValue
            rightKind rightValue + 1 ≤ capacity := by
    dsimp only [capacity]
    simp [rightKind, rightValue] at rightCaptureReserve ⊢
    omega
  have afterLeftRange' :
      ControllerRange raw leftFinal.registers := by
    simpa [leftFinal, leftCaptured, leftKind, leftValue,
      TargetEmitterControllerGateTrace.capturedRuntime] using
        afterLeftRange
  have rightCaptureReserve' :
      leftFinal.scratch +
            TargetEmitterControllerSourceTrace.capturedValue
              rightKind rightValue + 1 ≤ capacity := by
    simpa [leftFinal, leftCaptured, leftKind, leftValue,
      rightKind, rightValue,
      TargetEmitterControllerGateTrace.capturedRuntime, capacity] using
        rightCaptureReserve
  let rightReady :=
    TargetEmitterControllerGateTrace.sourceReady
      raw rightKind rightValue rightBefore afterGate
      rightBeforePacked rightValueCapacity
  have rightCapturedScratch :
      rightCaptured.scratch < capacity := by
    change
      leftFinal.scratch +
          TargetEmitterControllerSourceTrace.capturedValue
            rightKind rightValue <
        capacity
    omega
  have rightCapturedIndex :
      rightCaptured.captured + 1 ≤
        (SourceParser.circuitCells raw).length := by
    simpa [rightCaptured,
      TargetEmitterControllerGateTrace.capturedRuntime,
      rightKind, rightValue] using rightCapturedBound
  have rightMarkedLength :
      rightMarked.length ≤ sourceLength := by
    have equal :=
      markedWord_length_eq rightBefore afterGate gate.right
    calc
      rightMarked.length =
          (rightBefore ++ SourceParser.sourceCells gate.right ++
            afterGate).length := by
        simpa [rightMarked, rightKind, rightValue] using equal
      _ =
          ((head :: prefixTail) ++
            SourceParser.sourceCells gate.left ++
            SourceParser.sourceCells gate.right ++ afterGate).length := by
        simp [rightBefore, before, List.append_assoc]
      _ ≤ sourceLength := sourceLengthBound
  have rightProgram :=
    rightSourceProgram_bounds rightWorkspace
      (by simpa [rightCaptured,
        TargetEmitterControllerGateTrace.capturedRuntime] using
          afterLeftRange')
      rightCapturedIndex rightCapturedScratch rightReady
      sourceLength gateBudget rightMarkedLength
      (by simpa [rightCaptured,
        TargetEmitterControllerGateTrace.capturedRuntime] using
          leftTargetLimit)
      (by simpa [rightCaptured,
        TargetEmitterControllerGateTrace.capturedRuntime] using
          leftCheckLimit)
  rcases rightProgram with
    ⟨rightBlockBound, rightTargetGrowth, rightCheckGrowth⟩
  have rightTargetLimit :
      rightFinal.targetTokens.length ≤
        gateTargetLimit capacity origin gateBudget := by
    have leftFromOrigin :
        leftFinal.targetTokens.length ≤
          runtime.targetTokens.length + gateBlockGrowth capacity := by
      simpa [leftFinal, leftCaptured,
        TargetEmitterControllerGateTrace.capturedRuntime, capacity] using
          leftTargetGrowth
    have rightFromOrigin :
        rightFinal.targetTokens.length ≤
          runtime.targetTokens.length + 2 * gateBlockGrowth capacity := by
      have growth :
          rightFinal.targetTokens.length ≤
            leftFinal.targetTokens.length + gateBlockGrowth capacity := by
        simpa [rightFinal, rightCaptured,
          TargetEmitterControllerGateTrace.capturedRuntime, capacity] using
            rightTargetGrowth
      omega
    exact Nat.le_trans rightFromOrigin
      (by simpa [capacity] using targetBudget)
  have rightCheckLimit :
      TargetEmitterRuntimeProgramBound.checkCells rightFinal.checks ≤
        gateCheckLimit capacity origin gateBudget := by
    have leftFromOrigin :
        TargetEmitterRuntimeProgramBound.checkCells leftFinal.checks ≤
          TargetEmitterRuntimeProgramBound.checkCells runtime.checks +
            gateBlockGrowth capacity := by
      simpa [leftFinal, leftCaptured,
        TargetEmitterControllerGateTrace.capturedRuntime, capacity] using
          leftCheckGrowth
    have rightFromOrigin :
        TargetEmitterRuntimeProgramBound.checkCells rightFinal.checks ≤
          TargetEmitterRuntimeProgramBound.checkCells runtime.checks +
            2 * gateBlockGrowth capacity := by
      have growth :
          TargetEmitterRuntimeProgramBound.checkCells rightFinal.checks ≤
            TargetEmitterRuntimeProgramBound.checkCells leftFinal.checks +
              gateBlockGrowth capacity := by
        simpa [rightFinal, rightCaptured,
          TargetEmitterControllerGateTrace.capturedRuntime, capacity] using
            rightCheckGrowth
      omega
    exact Nat.le_trans rightFromOrigin
      (by simpa [capacity] using checkBudget)
  have rightFinalScratch :
      rightFinal.scratch < capacity := by
    simp [rightFinal, TargetEmitterProgramSemantics.macroResult_scratch,
      capacity, TargetEmitterLedger.slotCapacity]
  have rightFinalCaptured :
      rightFinal.captured + 1 ≤
        (SourceParser.circuitCells raw).length := by
    rw [show rightFinal.captured = rightCaptured.captured by
      exact TargetEmitterControllerGateTrace.macroResult_captured
        rightCaptured
          (TargetEmitterPlan.sourcePlan rightKind 1)
          (TargetEmitterPlan.sourceCheckRelative rightKind)
          (TargetEmitterPlan.sourceGateCount rightKind)]
    exact rightCapturedIndex
  have afterRightRange' :
      ControllerRange raw rightFinal.registers := by
    simpa [rightFinal, rightCaptured, leftFinal, leftCaptured,
      leftKind, leftValue, rightKind, rightValue,
      TargetEmitterControllerGateTrace.capturedRuntime] using
        afterRightRange
  have nextGate' :
      rightFinal.registers.currentGate + 1 ≤
        TargetEmitterLedger.normalizedGateCount raw := by
    simpa [rightFinal, rightCaptured, leftFinal, leftCaptured,
      leftKind, leftValue, rightKind, rightValue,
      TargetEmitterControllerGateTrace.capturedRuntime] using
        nextGate
  have traceProgram :=
    rightTraceProgram_bounds rightWorkspace
      afterRightRange'
      rightFinalCaptured rightFinalScratch
      nextGate'
      sourceLength gateBudget rightMarkedLength
      rightTargetLimit rightCheckLimit
  rcases traceProgram with
    ⟨traceBlockBound, traceTargetGrowth, traceCheckGrowth⟩
  have leftBeforeLength :
      before.length ≤ capacity + sourceLength := by
    have beforeToWord :
        before.length ≤
          (before ++ SourceParser.sourceCells gate.left ++
            SourceParser.sourceCells gate.right ++ afterGate).length := by
      simp
    have beforeToSource :=
      Nat.le_trans beforeToWord
        (by simpa [before, List.append_assoc] using sourceLengthBound)
    omega
  have leftScratchBound :
      runtime.scratch ≤ capacity + sourceLength := by
    have : runtime.scratch ≤ capacity := by
      dsimp only [capacity]
      omega
    omega
  have leftValueBound :
      TargetEmitterControllerGateTrace.sourceValue gate.left ≤
        capacity + sourceLength := by
    have valueToCells :=
      sourceValue_le_sourceCells_length gate.left
    have cellsToWord :
        (SourceParser.sourceCells gate.left).length ≤
          (before ++ SourceParser.sourceCells gate.left ++
            SourceParser.sourceCells gate.right ++ afterGate).length := by
      simp only [List.length_append]
      omega
    have cellsToSource :=
      Nat.le_trans cellsToWord
        (by simpa [before, List.append_assoc] using sourceLengthBound)
    omega
  have leftCaptureBound :=
    TargetEmitterControllerNormalizationBound.sourceCapturePhaseSteps_le_timePolynomial
      before gate.left runtime.scratch (capacity + sourceLength)
      leftBeforeLength leftScratchBound leftValueBound
  have rightBeforeLength :
      rightBefore.length ≤ capacity + sourceLength := by
    have beforeToWord :
        rightBefore.length ≤
          (rightBefore ++ SourceParser.sourceCells gate.right ++
            afterGate).length := by
      simp
    have wordEq :
        (rightBefore ++ SourceParser.sourceCells gate.right ++
            afterGate).length =
          (before ++ SourceParser.sourceCells gate.left ++
            SourceParser.sourceCells gate.right ++ afterGate).length := by
      simp [rightBefore, List.append_assoc]
    have beforeToSource : rightBefore.length ≤ sourceLength := by
      exact Nat.le_trans beforeToWord
        (by
          rw [wordEq]
          simpa [before, List.append_assoc] using sourceLengthBound)
    omega
  have rightScratchBound :
      leftFinal.scratch ≤ capacity + sourceLength := by
    simp [leftFinal, TargetEmitterProgramSemantics.macroResult_scratch]
  have rightValueBound :
      TargetEmitterControllerGateTrace.sourceValue gate.right ≤
        capacity + sourceLength := by
    have valueToCells :=
      sourceValue_le_sourceCells_length gate.right
    have cellsToWord :
        (SourceParser.sourceCells gate.right).length ≤
          (rightBefore ++ SourceParser.sourceCells gate.right ++
            afterGate).length := by
      simp only [List.length_append]
      omega
    have wordEq :
        (rightBefore ++ SourceParser.sourceCells gate.right ++
            afterGate).length =
          (before ++ SourceParser.sourceCells gate.left ++
            SourceParser.sourceCells gate.right ++ afterGate).length := by
      simp [rightBefore, List.append_assoc]
    have cellsToSource :
        (SourceParser.sourceCells gate.right).length ≤ sourceLength := by
      exact Nat.le_trans cellsToWord
        (by
          rw [wordEq]
          simpa [before, List.append_assoc] using sourceLengthBound)
    omega
  have rightCaptureBound :=
    TargetEmitterControllerNormalizationBound.sourceCapturePhaseSteps_le_timePolynomial
      rightBefore gate.right leftFinal.scratch
      (capacity + sourceLength)
      rightBeforeLength rightScratchBound rightValueBound
  let leftRestoreBefore :=
    before ++
      TargetEmitterRuntimeLayout.localCursorBefore
        (Plan.captureKind leftKind)
        (TargetEmitterControllerSourceTrace.capturedValue
          leftKind leftValue)
  have leftRestoreBound :
      TargetEmitterControllerSourceTrace.restorePathSteps
          leftRestoreBefore.length ≤
        gateRestoreUnit sourceLength := by
    have restoreLocal :=
      restoreBefore_length_le_word before
        (SourceParser.sourceCells gate.right ++ afterGate) gate.left
    have sourceWordBound :
        (before ++ SourceParser.sourceCells gate.left ++
            (SourceParser.sourceCells gate.right ++ afterGate)).length ≤
          sourceLength := by
      simpa only [before, List.append_assoc] using sourceLengthBound
    have lengthBound :
        leftRestoreBefore.length ≤ sourceLength := by
      exact Nat.le_trans restoreLocal sourceWordBound
    simp [TargetEmitterControllerSourceTrace.restorePathSteps,
      gateRestoreUnit]
    omega
  let rightRestoreBefore :=
    rightBefore ++
      TargetEmitterRuntimeLayout.localCursorBefore
        (Plan.captureKind rightKind)
        (TargetEmitterControllerSourceTrace.capturedValue
          rightKind rightValue)
  have rightRestoreBound :
      TargetEmitterControllerSourceTrace.restorePathSteps
          rightRestoreBefore.length ≤
        gateRestoreUnit sourceLength := by
    have restoreLocal :=
      restoreBefore_length_le_word rightBefore afterGate gate.right
    have sourceWordBound :
        (rightBefore ++ SourceParser.sourceCells gate.right ++
            afterGate).length ≤ sourceLength := by
      simpa only [rightBefore, before, List.append_assoc] using
        sourceLengthBound
    have lengthBound :
        rightRestoreBefore.length ≤ sourceLength := by
      exact Nat.le_trans restoreLocal sourceWordBound
    simp [TargetEmitterControllerSourceTrace.restorePathSteps,
      gateRestoreUnit]
    omega
  have envelopeBound :
      gateSourcesTraceEnvelope raw before afterGate gate runtime ≤
        gateUniformUnit capacity sourceLength origin gateBudget := by
    have leftCaptureBound' :
        TargetEmitterControllerGateTrace.sourceCapturePhaseSteps
              before gate.left runtime.scratch ≤
            gateCaptureUnit capacity sourceLength := by
      simpa only [gateCaptureUnit] using leftCaptureBound
    have leftBlockBound' :
        leftSourceBlockEnvelope raw leftMarked leftCaptured leftKind ≤
          gateBlockUnit capacity sourceLength origin gateBudget := by
      simpa only [leftSourceBlockEnvelope, capacity] using leftBlockBound
    have rightCaptureBound' :
        TargetEmitterControllerGateTrace.sourceCapturePhaseSteps
              rightBefore gate.right leftFinal.scratch ≤
            gateCaptureUnit capacity sourceLength := by
      simpa only [gateCaptureUnit] using rightCaptureBound
    have rightBlockBound' :
        rightSourceBlockEnvelope raw rightMarked rightCaptured rightKind ≤
          gateBlockUnit capacity sourceLength origin gateBudget := by
      have rightMarkedEq :
          rightMarked =
            (head :: (prefixTail ++ SourceParser.sourceCells gate.left)) ++
              TargetEmitterControllerSourceTrace.captureMarkedSourceCells
                rightKind rightValue ++ afterGate := by
        simp [rightMarked, rightBefore, before, List.append_assoc]
      unfold rightSourceBlockEnvelope
      rw [rightMarkedEq]
      simpa only [capacity] using rightBlockBound
    have traceBlockBound' :
        rightTraceBlockEnvelope raw rightMarked rightFinal ≤
          gateBlockUnit capacity sourceLength origin gateBudget := by
      have rightMarkedEq :
          rightMarked =
            (head :: (prefixTail ++ SourceParser.sourceCells gate.left)) ++
              TargetEmitterControllerSourceTrace.captureMarkedSourceCells
                rightKind rightValue ++ afterGate := by
        simp [rightMarked, rightBefore, before, List.append_assoc]
      unfold rightTraceBlockEnvelope
      rw [rightMarkedEq]
      simpa only [capacity] using traceBlockBound
    have leftPhaseBound :
        leftSourcePhaseEnvelope raw before
              (SourceParser.sourceCells gate.right ++ afterGate)
              gate.left runtime ≤
            gateCaptureUnit capacity sourceLength +
              gateBlockUnit capacity sourceLength origin gateBudget +
              gateRestoreUnit sourceLength := by
      change
        TargetEmitterControllerGateTrace.sourceCapturePhaseSteps
              before gate.left runtime.scratch +
              leftSourceBlockEnvelope raw leftMarked leftCaptured leftKind +
              TargetEmitterControllerSourceTrace.restorePathSteps
                leftRestoreBefore.length ≤
            gateCaptureUnit capacity sourceLength +
              gateBlockUnit capacity sourceLength origin gateBudget +
              gateRestoreUnit sourceLength
      omega
    have rightPhaseBound :
        rightSourceTracePhaseEnvelope raw rightBefore afterGate
              gate.right leftFinal ≤
            gateCaptureUnit capacity sourceLength +
              gateBlockUnit capacity sourceLength origin gateBudget +
              gateBlockUnit capacity sourceLength origin gateBudget +
              gateRestoreUnit sourceLength := by
      change
        TargetEmitterControllerGateTrace.sourceCapturePhaseSteps
              rightBefore gate.right leftFinal.scratch +
              rightSourceBlockEnvelope raw rightMarked rightCaptured rightKind +
              rightTraceBlockEnvelope raw rightMarked rightFinal +
              TargetEmitterControllerSourceTrace.restorePathSteps
                rightRestoreBefore.length ≤
            gateCaptureUnit capacity sourceLength +
              gateBlockUnit capacity sourceLength origin gateBudget +
              gateBlockUnit capacity sourceLength origin gateBudget +
              gateRestoreUnit sourceLength
      omega
    change
      leftSourcePhaseEnvelope raw before
            (SourceParser.sourceCells gate.right ++ afterGate)
            gate.left runtime +
          rightSourceTracePhaseEnvelope raw rightBefore afterGate
            gate.right leftFinal ≤
        gateUniformUnit capacity sourceLength origin gateBudget
    unfold gateUniformUnit
    omega
  let final :=
    TargetEmitterRuntimeProgramSafety.rightTraceResult rightFinal
  have finalTarget :
      final.targetTokens.length ≤
        runtime.targetTokens.length +
          3 * gateBlockGrowth capacity := by
    have first :
        leftFinal.targetTokens.length ≤
          runtime.targetTokens.length + gateBlockGrowth capacity := by
      simpa [leftFinal, leftCaptured,
        TargetEmitterControllerGateTrace.capturedRuntime, capacity] using
          leftTargetGrowth
    have second :
        rightFinal.targetTokens.length ≤
          leftFinal.targetTokens.length + gateBlockGrowth capacity := by
      simpa [rightFinal, rightCaptured,
        TargetEmitterControllerGateTrace.capturedRuntime, capacity] using
          rightTargetGrowth
    have third :
        final.targetTokens.length ≤
          rightFinal.targetTokens.length + gateBlockGrowth capacity := by
      simpa [final, capacity] using traceTargetGrowth
    omega
  have finalChecks :
      TargetEmitterRuntimeProgramBound.checkCells final.checks ≤
        TargetEmitterRuntimeProgramBound.checkCells runtime.checks +
          3 * gateBlockGrowth capacity := by
    have first :
        TargetEmitterRuntimeProgramBound.checkCells leftFinal.checks ≤
          TargetEmitterRuntimeProgramBound.checkCells runtime.checks +
            gateBlockGrowth capacity := by
      simpa [leftFinal, leftCaptured,
        TargetEmitterControllerGateTrace.capturedRuntime, capacity] using
          leftCheckGrowth
    have second :
        TargetEmitterRuntimeProgramBound.checkCells rightFinal.checks ≤
          TargetEmitterRuntimeProgramBound.checkCells leftFinal.checks +
            gateBlockGrowth capacity := by
      simpa [rightFinal, rightCaptured,
        TargetEmitterControllerGateTrace.capturedRuntime, capacity] using
          rightCheckGrowth
    have third :
        TargetEmitterRuntimeProgramBound.checkCells final.checks ≤
          TargetEmitterRuntimeProgramBound.checkCells rightFinal.checks +
            gateBlockGrowth capacity := by
      simpa [final, capacity] using traceCheckGrowth
    omega
  exact
    ⟨by simpa [capacity, before] using envelopeBound,
      by simpa [capacity, final, leftFinal, rightFinal] using finalTarget,
      by simpa [capacity, final, leftFinal, rightFinal] using finalChecks⟩

end PNP.Concrete.LockedNAND.TargetEmitterControllerGateBound
