/-
Copyright (c) 2026 PNP Labs.

Exact source-template and gate-traversal paths for the fixed grammar-only
locked-NAND target emitter.

The executable graph contains only the materialized finite controller and
literal primitive tables.  The runtime values and safety witnesses below are
proof-only descriptions of those fixed paths; they are not consulted by the
machine.
-/

import PNP.Concrete.LockedNANDTargetEmitterControllerSourceTrace
import PNP.Concrete.LockedNANDTargetEmitterRuntimeLayout
import PNP.Concrete.LockedNANDTargetEmitterRuntimeProgramSafety
import PNP.Concrete.WorkMachineProgramPathBlankEquivalence

namespace PNP.Concrete.LockedNAND.TargetEmitterControllerGateTrace

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
abbrev MarkedWorkspace :=
  TargetEmitterRuntimeProgramSafety.MarkedWorkspace
abbrev CapturedReady :=
  TargetEmitterRuntimeProgramSafety.CapturedReady
abbrev ControllerRange :=
  TargetEmitterCapacity.ControllerRange

inductive SourceReady
    (raw : RawCircuit) (source : List WorkSymbol)
    (captured : Nat) : SourceKind → Type where
  | input
      (ready : CapturedReady raw source captured) :
      SourceReady raw source captured .input
  | constantFalse :
      SourceReady raw source captured .constantFalse
  | constantTrue :
      SourceReady raw source captured .constantTrue
  | gate
      (ready : CapturedReady raw source captured) :
      SourceReady raw source captured .gate

def TapeRepresents (state capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (source : List WorkSymbol)
    (target : List Token) (tape : WorkTape) : Prop :=
  TargetEmitterRuntime.Represents state capacity scratch
    registers checks source target
    { state := state, tape := tape }

def FocusTapeRepresents (state capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (crossed remaining : List WorkSymbol)
    (target : List Token) (tape : WorkTape) : Prop :=
  TargetEmitterRuntimeSourceControl.SourceFocusRepresents
    state capacity scratch registers checks crossed remaining target
    { state := state, tape := tape }

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

/-! ### Materialized source and trace blocks -/

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

private theorem leftSource_startState
    (kind : SourceKind) :
    (leftSourceRef kind).startState =
      TargetEmitterRuntimeProgram.entryState 0
        (leftSourcePrograms kind) := by
  cases kind <;> rfl

private theorem rightSource_startState
    (kind : SourceKind) :
    (rightSourceRef kind).startState =
      TargetEmitterRuntimeProgram.entryState 0
        (rightSourcePrograms kind) := by
  cases kind <;> rfl

private theorem rightTrace_startState
    (kind : SourceKind) :
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
          workspace range capturedBound scratchBound captured sideBound
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
          workspace range capturedBound scratchBound captured sideBound

/-! ### Constructive marked-source witnesses -/

def sourceValue : RawSource → Nat
  | .input value => value
  | .gate value => value
  | .constant _ => 0

theorem sourceCells_eq_captureSourceCells
    (source : RawSource) :
    SourceParser.sourceCells source =
      TargetEmitterControllerSourceTrace.captureSourceCells
        (TargetEmitterControllerTrace.sourceKind source)
        (sourceValue source) := by
  cases source with
  | input value =>
      simp [SourceParser.sourceCells,
        SourceParser.cell00, SourceParser.cell11,
        TargetEmitterSourceCapture.sourceCells,
        TargetEmitterSourceCapture.cell00,
        TargetEmitterSourceCapture.cell11,
        sourceValue, TargetEmitterControllerTrace.sourceKind,
        TargetEmitterControllerSourceTrace.captureSourceCells,
        TargetEmitterControllerSourceTrace.capturedValue,
        Plan.captureKind]
  | gate value =>
      simp [SourceParser.sourceCells,
        SourceParser.cell01, SourceParser.cell10,
        TargetEmitterSourceCapture.sourceCells,
        TargetEmitterSourceCapture.cell01,
        TargetEmitterSourceCapture.cell10,
        sourceValue, TargetEmitterControllerTrace.sourceKind,
        TargetEmitterControllerSourceTrace.captureSourceCells,
        TargetEmitterControllerSourceTrace.capturedValue,
        Plan.captureKind]
  | constant value =>
      cases value <;>
        simp [SourceParser.sourceCells,
          SourceParser.cell00, SourceParser.cell01,
          TargetEmitterSourceCapture.sourceCells,
          TargetEmitterSourceCapture.cell00,
          TargetEmitterSourceCapture.cell01,
          TargetEmitterControllerTrace.sourceKind,
          TargetEmitterControllerSourceTrace.captureSourceCells,
          Plan.captureKind]

private theorem originalCell_eq_cursorOriginal
    (kind : SourceKind) :
    Plan.originalCell kind =
      TargetEmitterRuntimeLayout.cursorOriginal
        (Plan.captureKind kind) := by
  cases kind <;> rfl

def capturedRuntime
    (runtime : Runtime) (kind : SourceKind) (value : Nat) :
    Runtime :=
  { runtime with
    captured :=
      TargetEmitterControllerSourceTrace.capturedValue kind value
    scratch :=
      runtime.scratch +
        TargetEmitterControllerSourceTrace.capturedValue kind value }

private theorem gatesResult_captured
    (runtime : Runtime) (gates : List TargetEmitterPlan.PlannedGate) :
    (TargetEmitterProgramSemantics.gatesResult runtime gates).captured =
      runtime.captured := by
  induction gates generalizing runtime with
  | nil =>
      rfl
  | cons gate rest inductionHypothesis =>
      simp only [TargetEmitterProgramSemantics.gatesResult]
      rw [inductionHypothesis]
      rw [TargetEmitterProgramSemantics.gateResult_eq]

theorem macroResult_captured
    (runtime : Runtime) (gates : List TargetEmitterPlan.PlannedGate)
    (relative count : Nat) :
    (TargetEmitterProgramSemantics.macroResult
      runtime gates relative count).captured =
        runtime.captured := by
  simp [TargetEmitterProgramSemantics.macroResult,
    TargetEmitterProgramSemantics.resetScratchResult,
    TargetEmitterProgramSemantics.incrementOutputResult,
    TargetEmitterProgramSemantics.checkPushResult,
    gatesResult_captured]

theorem rightTraceResult_captured (runtime : Runtime) :
    (TargetEmitterRuntimeProgramSafety.rightTraceResult runtime).captured =
      runtime.captured := by
  simp [TargetEmitterRuntimeProgramSafety.rightTraceResult,
    macroResult_captured]

def markedWorkspace
    (kind : SourceKind) (value : Nat)
    (head : WorkSymbol) (prefixTail after : List WorkSymbol)
    (originalPacked :
      ∀ symbol,
        symbol ∈
            (head :: prefixTail) ++
              TargetEmitterControllerSourceTrace.captureSourceCells
                kind value ++ after →
          TargetEmitter.PackedSymbol symbol) :
    MarkedWorkspace
      ((head :: prefixTail) ++
        TargetEmitterControllerSourceTrace.captureMarkedSourceCells
          kind value ++ after) := by
  let sourceKind := Plan.captureKind kind
  let captured :=
    TargetEmitterControllerSourceTrace.capturedValue kind value
  have originalPacked' :
      ∀ symbol,
        symbol ∈
            (head :: prefixTail) ++
              TargetEmitterSourceCapture.sourceCells
                sourceKind captured ++ after →
          TargetEmitter.PackedSymbol symbol := by
    simpa [sourceKind, captured,
      TargetEmitterControllerSourceTrace.captureSourceCells] using
      originalPacked
  refine
    { context := ?_
      cursor := ?_ }
  · simpa [TargetEmitterControllerSourceTrace.captureMarkedSourceCells,
      sourceKind, captured, List.append_assoc] using
      (TargetEmitterRuntimeLayout.sourceContext_of_nonempty_packed_prefix
        head prefixTail
        (TargetEmitterSourceCapture.markedSourceCells
          sourceKind captured)
        after
        (originalPacked' head (by simp)))
  · simpa [TargetEmitterControllerSourceTrace.captureMarkedSourceCells,
      sourceKind, captured] using
      (TargetEmitterRuntimeLayout.cursorLayout
        sourceKind captured (head :: prefixTail) after
        originalPacked')

def sourceReady
    (raw : RawCircuit) (kind : SourceKind) (value : Nat)
    (before after : List WorkSymbol)
    (beforePacked :
      ∀ symbol, symbol ∈ before →
        TargetEmitter.PackedSymbol symbol)
    (valueBound :
      TargetEmitterControllerSourceTrace.capturedValue kind value + 1 ≤
        TargetEmitterLedger.slotCapacity raw) :
    SourceReady raw
      (before ++
        TargetEmitterControllerSourceTrace.captureMarkedSourceCells
          kind value ++ after)
      (TargetEmitterControllerSourceTrace.capturedValue kind value)
      kind := by
  cases kind with
  | input =>
      apply SourceReady.input
      let layout :=
        TargetEmitterRuntimeLayout.reloadLayout
          TargetEmitterSourceCapture.NatKind.input
          value before after beforePacked
      refine
        { layout := layout
          capturedEq := ?_
          valueBound := by
            exact valueBound }
      · rfl
  | constantFalse =>
      exact SourceReady.constantFalse
  | constantTrue =>
      exact SourceReady.constantTrue
  | gate =>
      apply SourceReady.gate
      let layout :=
        TargetEmitterRuntimeLayout.reloadLayout
          TargetEmitterSourceCapture.NatKind.gate
          value before after beforePacked
      refine
        { layout := layout
          capturedEq := ?_
          valueBound := by
            exact valueBound }
      · rfl

/-! ### Classification and capture -/

def sourceCapturePhaseSteps
    (before : List WorkSymbol) (source : RawSource)
    (scratch : Nat) : Nat :=
  TargetEmitterControllerTrace.classifierSteps source +
    TargetEmitterControllerSourceTrace.capturePathSteps
      (TargetEmitterControllerTrace.sourceKind source)
      before.length scratch (sourceValue source)

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
  unfold TargetEmitterRuntimeSourceControl.sourceFocusConfiguration
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

private theorem canonicalFocusTape
    (state capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (before after : List WorkSymbol)
    (source : RawSource) (target : List Token) :
    TargetEmitterControllerTrace.sourceFocusTape
        (before.reverse ++
          TargetEmitterRuntime.logicalLeftWorkspace
            capacity scratch registers checks)
        source
        (after ++
          TargetEmitterRuntimeSourceControl.targetSuffix target) =
      (TargetEmitterRuntimeSourceControl.sourceFocusConfiguration
        state capacity scratch registers checks before
        (SourceParser.sourceCells source ++ after) target).tape := by
  simpa [TargetEmitterControllerTrace.sourceFocusTape,
    TargetEmitterRuntimeSourceControl.sourceFocusConfiguration,
    TargetEmitterRuntimeSourceControl.targetSuffix,
    List.append_assoc] using
    (configAtWord_tape_irrel 0 state
      (before.reverse ++
        TargetEmitterRuntime.logicalLeftWorkspace
          capacity scratch registers checks)
      (SourceParser.sourceCells source ++
        (after ++
          TargetEmitterRuntimeSourceControl.targetSuffix target)))

/-- Classify and capture one left source through the fixed control nodes.
The retained source is rewound and contains exactly one contextual cursor. -/
theorem leftClassifyCapture_path
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat)
    (before after : List WorkSymbol)
    (source : RawSource) (target : List Token)
    (initialTape : WorkTape)
    (capacityBound :
      scratch +
          TargetEmitterControllerSourceTrace.capturedValue
            (TargetEmitterControllerTrace.sourceKind source)
            (sourceValue source) +
          1 ≤
        capacity)
    (beforePacked :
      ∀ symbol, symbol ∈ before →
        TargetEmitter.PackedSymbol symbol)
    (represents :
      FocusTapeRepresents leftFirstRef.startState
        capacity scratch registers checks before
        (SourceParser.sourceCells source ++ after)
        target initialTape) :
    ∃ finalTape,
      AcceptPath graph (.node leftFirstRef)
          (.node
            (leftSourceRef
              (TargetEmitterControllerTrace.sourceKind source)))
          (sourceCapturePhaseSteps before source scratch)
          initialTape finalTape ∧
      TapeRepresents
        (leftSourceRef
          (TargetEmitterControllerTrace.sourceKind source)).startState
        capacity
        (scratch +
          TargetEmitterControllerSourceTrace.capturedValue
            (TargetEmitterControllerTrace.sourceKind source)
            (sourceValue source))
        registers checks
        (before ++
          TargetEmitterControllerSourceTrace.captureMarkedSourceCells
            (TargetEmitterControllerTrace.sourceKind source)
            (sourceValue source) ++ after)
        target finalTape := by
  let kind := TargetEmitterControllerTrace.sourceKind source
  let value := sourceValue source
  let canonical :=
    (TargetEmitterRuntimeSourceControl.sourceFocusConfiguration
      leftFirstRef.startState capacity scratch registers checks before
      (SourceParser.sourceCells source ++ after) target).tape
  have classifierCanonical :
      AcceptPath graph (.node leftFirstRef)
        (.node (leftCaptureRef kind))
        (TargetEmitterControllerTrace.classifierSteps source)
        canonical canonical := by
    have path :=
      TargetEmitterControllerTrace.left_classifier_path
        (before.reverse ++
          TargetEmitterRuntime.logicalLeftWorkspace
            capacity scratch registers checks)
        (after ++
          TargetEmitterRuntimeSourceControl.targetSuffix target)
        source
    rw [canonicalFocusTape
      leftFirstRef.startState capacity scratch registers checks
      before after source target] at path
    exact path
  rcases
      classifierCanonical.transport represents.tape with
    ⟨classifiedTape, classifierPath, classifiedEquivalent⟩
  let classified : WorkConfiguration :=
    { state := TargetEmitterSourceCapture.startState
      tape := classifiedTape }
  have canonicalEq :
      canonical =
        (TargetEmitterRuntimeSourceControl.sourceFocusConfiguration
          TargetEmitterSourceCapture.startState
          capacity scratch registers checks before
          (TargetEmitterControllerSourceTrace.captureSourceCells
            kind value ++ after) target).tape := by
    unfold canonical
    rw [sourceCells_eq_captureSourceCells]
    exact configAtWord_tape_irrel _ _ _ _
  have captureRepresents :
      TargetEmitterRuntimeSourceControl.SourceFocusRepresents
        TargetEmitterSourceCapture.startState
        capacity scratch registers checks before
        (TargetEmitterControllerSourceTrace.captureSourceCells
          kind value ++ after)
        target classified := by
    refine ⟨?_, ?_⟩
    · simpa [classified] using
        (sourceFocusConfiguration_state
          TargetEmitterSourceCapture.startState
          capacity scratch registers checks before
          (TargetEmitterControllerSourceTrace.captureSourceCells
            kind value ++ after) target).symm
    · change WorkTape.BlankEquivalent classifiedTape _
      rw [← canonicalEq]
      exact classifiedEquivalent
  rcases
      TargetEmitterControllerSourceTrace.leftCapture_path
        kind capacity scratch value registers checks before after
        target classified capacityBound beforePacked captureRepresents with
    ⟨captured, capturePath, capturedRepresents⟩
  refine ⟨captured.tape, ?_, ?_⟩
  · simpa [sourceCapturePhaseSteps, kind, value] using
      AcceptPath.trans graph (.node leftFirstRef)
        (.node (leftCaptureRef kind))
        (.node (leftSourceRef kind))
        (TargetEmitterControllerTrace.classifierSteps source)
        (TargetEmitterControllerSourceTrace.capturePathSteps
          kind before.length scratch value)
        initialTape classifiedTape captured.tape
        classifierPath capturePath
  · exact
      represents_at_state
        (newState := (leftSourceRef kind).startState)
        capturedRepresents

/-- Classify and capture one right source through the fixed control nodes. -/
theorem rightClassifyCapture_path
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat)
    (before after : List WorkSymbol)
    (source : RawSource) (target : List Token)
    (initialTape : WorkTape)
    (capacityBound :
      scratch +
          TargetEmitterControllerSourceTrace.capturedValue
            (TargetEmitterControllerTrace.sourceKind source)
            (sourceValue source) +
          1 ≤
        capacity)
    (beforePacked :
      ∀ symbol, symbol ∈ before →
        TargetEmitter.PackedSymbol symbol)
    (represents :
      FocusTapeRepresents rightFirstRef.startState
        capacity scratch registers checks before
        (SourceParser.sourceCells source ++ after)
        target initialTape) :
    ∃ finalTape,
      AcceptPath graph (.node rightFirstRef)
          (.node
            (rightSourceRef
              (TargetEmitterControllerTrace.sourceKind source)))
          (sourceCapturePhaseSteps before source scratch)
          initialTape finalTape ∧
      TapeRepresents
        (rightSourceRef
          (TargetEmitterControllerTrace.sourceKind source)).startState
        capacity
        (scratch +
          TargetEmitterControllerSourceTrace.capturedValue
            (TargetEmitterControllerTrace.sourceKind source)
            (sourceValue source))
        registers checks
        (before ++
          TargetEmitterControllerSourceTrace.captureMarkedSourceCells
            (TargetEmitterControllerTrace.sourceKind source)
            (sourceValue source) ++ after)
        target finalTape := by
  let kind := TargetEmitterControllerTrace.sourceKind source
  let value := sourceValue source
  let canonical :=
    (TargetEmitterRuntimeSourceControl.sourceFocusConfiguration
      rightFirstRef.startState capacity scratch registers checks before
      (SourceParser.sourceCells source ++ after) target).tape
  have classifierCanonical :
      AcceptPath graph (.node rightFirstRef)
        (.node (rightCaptureRef kind))
        (TargetEmitterControllerTrace.classifierSteps source)
        canonical canonical := by
    have path :=
      TargetEmitterControllerTrace.right_classifier_path
        (before.reverse ++
          TargetEmitterRuntime.logicalLeftWorkspace
            capacity scratch registers checks)
        (after ++
          TargetEmitterRuntimeSourceControl.targetSuffix target)
        source
    rw [canonicalFocusTape
      rightFirstRef.startState capacity scratch registers checks
      before after source target] at path
    exact path
  rcases
      classifierCanonical.transport represents.tape with
    ⟨classifiedTape, classifierPath, classifiedEquivalent⟩
  let classified : WorkConfiguration :=
    { state := TargetEmitterSourceCapture.startState
      tape := classifiedTape }
  have canonicalEq :
      canonical =
        (TargetEmitterRuntimeSourceControl.sourceFocusConfiguration
          TargetEmitterSourceCapture.startState
          capacity scratch registers checks before
          (TargetEmitterControllerSourceTrace.captureSourceCells
            kind value ++ after) target).tape := by
    unfold canonical
    rw [sourceCells_eq_captureSourceCells]
    exact configAtWord_tape_irrel _ _ _ _
  have captureRepresents :
      TargetEmitterRuntimeSourceControl.SourceFocusRepresents
        TargetEmitterSourceCapture.startState
        capacity scratch registers checks before
        (TargetEmitterControllerSourceTrace.captureSourceCells
          kind value ++ after)
        target classified := by
    refine ⟨?_, ?_⟩
    · simpa [classified] using
        (sourceFocusConfiguration_state
          TargetEmitterSourceCapture.startState
          capacity scratch registers checks before
          (TargetEmitterControllerSourceTrace.captureSourceCells
            kind value ++ after) target).symm
    · change WorkTape.BlankEquivalent classifiedTape _
      rw [← canonicalEq]
      exact classifiedEquivalent
  rcases
      TargetEmitterControllerSourceTrace.rightCapture_path
        kind capacity scratch value registers checks before after
        target classified capacityBound beforePacked captureRepresents with
    ⟨captured, capturePath, capturedRepresents⟩
  refine ⟨captured.tape, ?_, ?_⟩
  · simpa [sourceCapturePhaseSteps, kind, value] using
      AcceptPath.trans graph (.node rightFirstRef)
        (.node (rightCaptureRef kind))
        (.node (rightSourceRef kind))
        (TargetEmitterControllerTrace.classifierSteps source)
        (TargetEmitterControllerSourceTrace.capturePathSteps
          kind before.length scratch value)
        initialTape classifiedTape captured.tape
        classifierPath capturePath
  · exact
      represents_at_state
        (newState := (rightSourceRef kind).startState)
        capturedRepresents

/-- Classify and capture the circuit output through the fixed control nodes,
then branch only through the source-kind continuation embedded in the graph. -/
theorem outputClassifyCapture_path
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat)
    (before after : List WorkSymbol)
    (source : RawSource) (target : List Token)
    (initialTape : WorkTape)
    (capacityBound :
      scratch +
          TargetEmitterControllerSourceTrace.capturedValue
            (TargetEmitterControllerTrace.sourceKind source)
            (sourceValue source) +
          1 ≤
        capacity)
    (beforePacked :
      ∀ symbol, symbol ∈ before →
        TargetEmitter.PackedSymbol symbol)
    (represents :
      FocusTapeRepresents outputFirstRef.startState
        capacity scratch registers checks before
        (SourceParser.sourceCells source ++ after)
        target initialTape) :
    ∃ finalTape,
      AcceptPath graph (.node outputFirstRef)
          (.node
            (outputCaptureContinuation
              (TargetEmitterControllerTrace.sourceKind source)))
          (sourceCapturePhaseSteps before source scratch)
          initialTape finalTape ∧
      TapeRepresents
        (outputCaptureContinuation
          (TargetEmitterControllerTrace.sourceKind source)).startState
        capacity
        (scratch +
          TargetEmitterControllerSourceTrace.capturedValue
            (TargetEmitterControllerTrace.sourceKind source)
            (sourceValue source))
        registers checks
        (before ++
          TargetEmitterControllerSourceTrace.captureMarkedSourceCells
            (TargetEmitterControllerTrace.sourceKind source)
            (sourceValue source) ++ after)
        target finalTape := by
  let kind := TargetEmitterControllerTrace.sourceKind source
  let value := sourceValue source
  let canonical :=
    (TargetEmitterRuntimeSourceControl.sourceFocusConfiguration
      outputFirstRef.startState capacity scratch registers checks before
      (SourceParser.sourceCells source ++ after) target).tape
  have classifierCanonical :
      AcceptPath graph (.node outputFirstRef)
        (.node (outputCaptureRef kind))
        (TargetEmitterControllerTrace.classifierSteps source)
        canonical canonical := by
    have path :=
      TargetEmitterControllerTrace.output_classifier_path
        (before.reverse ++
          TargetEmitterRuntime.logicalLeftWorkspace
            capacity scratch registers checks)
        (after ++
          TargetEmitterRuntimeSourceControl.targetSuffix target)
        source
    rw [canonicalFocusTape
      outputFirstRef.startState capacity scratch registers checks
      before after source target] at path
    exact path
  rcases classifierCanonical.transport represents.tape with
    ⟨classifiedTape, classifierPath, classifiedEquivalent⟩
  let classified : WorkConfiguration :=
    { state := TargetEmitterSourceCapture.startState
      tape := classifiedTape }
  have canonicalEq :
      canonical =
        (TargetEmitterRuntimeSourceControl.sourceFocusConfiguration
          TargetEmitterSourceCapture.startState
          capacity scratch registers checks before
          (TargetEmitterControllerSourceTrace.captureSourceCells
            kind value ++ after) target).tape := by
    unfold canonical
    rw [sourceCells_eq_captureSourceCells]
    exact configAtWord_tape_irrel _ _ _ _
  have captureRepresents :
      TargetEmitterRuntimeSourceControl.SourceFocusRepresents
        TargetEmitterSourceCapture.startState
        capacity scratch registers checks before
        (TargetEmitterControllerSourceTrace.captureSourceCells
          kind value ++ after)
        target classified := by
    refine ⟨?_, ?_⟩
    · simpa [classified] using
        (sourceFocusConfiguration_state
          TargetEmitterSourceCapture.startState
          capacity scratch registers checks before
          (TargetEmitterControllerSourceTrace.captureSourceCells
            kind value ++ after) target).symm
    · change WorkTape.BlankEquivalent classifiedTape _
      rw [← canonicalEq]
      exact classifiedEquivalent
  rcases
      TargetEmitterControllerSourceTrace.outputCapture_path
        kind capacity scratch value registers checks before after
        target classified capacityBound beforePacked captureRepresents with
    ⟨captured, capturePath, capturedRepresents⟩
  refine ⟨captured.tape, ?_, ?_⟩
  · simpa [sourceCapturePhaseSteps, kind, value] using
      AcceptPath.trans graph (.node outputFirstRef)
        (.node (outputCaptureRef kind))
        (.node (outputCaptureContinuation kind))
        (TargetEmitterControllerTrace.classifierSteps source)
        (TargetEmitterControllerSourceTrace.capturePathSteps
          kind before.length scratch value)
        initialTape classifiedTape captured.tape
        classifierPath capturePath
  · exact
      represents_at_state
        (newState := (outputCaptureContinuation kind).startState)
        capturedRepresents

/-- Execute the already-materialized left-source block and arrive at its
kind-specific cursor-restoration controller. -/
theorem leftSourceBlock_path
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
        finalTape := by
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
      safe.descriptor_acceptPath_exact
        (leftSourceDescriptor kind)
        (leftSourceDescriptor_member kind)
        (leftSourcePrograms kind)
        (by simpa [leftSourceDescriptor] using
          leftSource_compiled kind)
        (leftSourcePrograms_nonempty kind) 0 initial
        inputRepresents with
    ⟨steps, actualFinal, path, finalRepresents⟩
  refine ⟨steps, actualFinal.tape, ?_, ?_⟩
  · simpa [leftSourceDescriptor, leftSourceRef] using path
  · exact
      represents_at_state
        (newState := (leftRestoreRef kind).startState)
        finalRepresents

/-- Execute the already-materialized right-source block and arrive at its
kind-specific trace block. -/
theorem rightSourceBlock_path
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
        finalTape := by
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
      safe.descriptor_acceptPath_exact
        (rightSourceDescriptor kind)
        (rightSourceDescriptor_member kind)
        (rightSourcePrograms kind)
        (by simpa [rightSourceDescriptor] using
          rightSource_compiled kind)
        (rightSourcePrograms_nonempty kind) 0 initial
        inputRepresents with
    ⟨steps, actualFinal, path, finalRepresents⟩
  refine ⟨steps, actualFinal.tape, ?_, ?_⟩
  · simpa [rightSourceDescriptor, rightSourceRef] using path
  · exact
      represents_at_state
        (newState := (rightTraceRef kind).startState)
        finalRepresents

/-- Execute the fixed eighteen-gate trace macro, advance `currentGate`
exactly once, and arrive at the right-source restoration controller. -/
theorem rightTraceBlock_path
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
        (TargetEmitterRuntimeProgramSafety.rightTraceResult runtime).targetTokens
        finalTape := by
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
      safe.descriptor_acceptPath_exact
        (rightTraceDescriptor kind)
        (rightTraceDescriptor_member kind)
        rightTracePrograms
        (by simpa [rightTraceDescriptor] using rightTrace_compiled)
        rightTracePrograms_nonempty 0 initial inputRepresents with
    ⟨steps, actualFinal, path, finalRepresents⟩
  refine ⟨steps, actualFinal.tape, ?_, ?_⟩
  · simpa [rightTraceDescriptor, rightTraceRef] using path
  · exact
      represents_at_state
        (newState := (rightRestoreRef kind).startState)
        finalRepresents

/-! ### One complete left-source phase -/

/-- Classify, capture, emit the left literal macro, restore the retained
source, and arrive at the right-source classifier. -/
theorem leftSourcePhase_path
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
            (sourceValue source) +
          1 ≤
        TargetEmitterLedger.slotCapacity raw)
    (capturedBound :
      TargetEmitterControllerSourceTrace.capturedValue
          (TargetEmitterControllerTrace.sourceKind source)
          (sourceValue source) +
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
      FocusTapeRepresents leftFirstRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        (head :: prefixTail)
        (SourceParser.sourceCells source ++ after)
        target initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node leftFirstRef)
          (.node rightFirstRef) steps initialTape finalTape ∧
      FocusTapeRepresents rightFirstRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterProgramSemantics.macroResult
          (capturedRuntime runtime
            (TargetEmitterControllerTrace.sourceKind source)
            (sourceValue source))
          (TargetEmitterPlan.sourcePlan
            (TargetEmitterControllerTrace.sourceKind source) 0)
          (TargetEmitterPlan.sourceCheckRelative
            (TargetEmitterControllerTrace.sourceKind source))
          (TargetEmitterPlan.sourceGateCount
            (TargetEmitterControllerTrace.sourceKind source))).scratch
        (TargetEmitterProgramSemantics.macroResult
          (capturedRuntime runtime
            (TargetEmitterControllerTrace.sourceKind source)
            (sourceValue source))
          (TargetEmitterPlan.sourcePlan
            (TargetEmitterControllerTrace.sourceKind source) 0)
          (TargetEmitterPlan.sourceCheckRelative
            (TargetEmitterControllerTrace.sourceKind source))
          (TargetEmitterPlan.sourceGateCount
            (TargetEmitterControllerTrace.sourceKind source))).registers
        (TargetEmitterProgramSemantics.macroResult
          (capturedRuntime runtime
            (TargetEmitterControllerTrace.sourceKind source)
            (sourceValue source))
          (TargetEmitterPlan.sourcePlan
            (TargetEmitterControllerTrace.sourceKind source) 0)
          (TargetEmitterPlan.sourceCheckRelative
            (TargetEmitterControllerTrace.sourceKind source))
          (TargetEmitterPlan.sourceGateCount
            (TargetEmitterControllerTrace.sourceKind source))).checks
        ((head :: prefixTail) ++ SourceParser.sourceCells source)
        after
        (TargetEmitterProgramSemantics.macroResult
          (capturedRuntime runtime
            (TargetEmitterControllerTrace.sourceKind source)
            (sourceValue source))
          (TargetEmitterPlan.sourcePlan
            (TargetEmitterControllerTrace.sourceKind source) 0)
          (TargetEmitterPlan.sourceCheckRelative
            (TargetEmitterControllerTrace.sourceKind source))
          (TargetEmitterPlan.sourceGateCount
            (TargetEmitterControllerTrace.sourceKind source))).targetTokens
        finalTape := by
  let kind := TargetEmitterControllerTrace.sourceKind source
  let value := sourceValue source
  let before := head :: prefixTail
  let marked :=
    before ++
      TargetEmitterControllerSourceTrace.captureMarkedSourceCells
        kind value ++ after
  let capturedState := capturedRuntime runtime kind value
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
      ← sourceCells_eq_captureSourceCells source] using originalPacked
  rcases
      leftClassifyCapture_path
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        before after source target initialTape
        captureReserve beforePacked represents with
    ⟨capturedTape, capturePath, capturedRepresents⟩
  let workspace :=
    markedWorkspace kind value head prefixTail after
      (by simpa [before] using originalCapturePacked)
  have valueBound :
      TargetEmitterControllerSourceTrace.capturedValue kind value + 1 ≤
        TargetEmitterLedger.slotCapacity raw := by
    simp [kind, value] at captureReserve ⊢
    omega
  let ready :=
    sourceReady raw kind value before after beforePacked valueBound
  have capturedLogical :
      TapeRepresents (leftSourceRef kind).startState
        (TargetEmitterLedger.slotCapacity raw)
        capturedState.scratch capturedState.registers
        capturedState.checks marked capturedState.targetTokens
        capturedTape := by
    simpa [capturedState, capturedRuntime, marked, kind, value,
      targetEq] using
      capturedRepresents
  have capturedScratchBound :
      capturedState.scratch <
        TargetEmitterLedger.slotCapacity raw := by
    simp [capturedState, capturedRuntime, kind, value]
    omega
  have capturedIndexBound :
      capturedState.captured + 1 ≤
        (SourceParser.circuitCells raw).length := by
    simpa [capturedState, capturedRuntime, kind, value] using
      capturedBound
  rcases
      leftSourceBlock_path kind workspace capturedState range
        capturedIndexBound capturedScratchBound ready
        capturedTape capturedLogical with
    ⟨blockSteps, blockTape, blockPath, blockRepresents⟩
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
      rw [sourceCells_eq_captureSourceCells]
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
      FocusTapeRepresents rightFirstRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        final.scratch final.registers final.checks
        (before ++ SourceParser.sourceCells source) after
        final.targetTokens restored.tape := by
    simpa [FocusTapeRepresents, restoreBefore, before, kind, value,
      sourceCells_eq_captureSourceCells,
      TargetEmitterControllerSourceTrace.captureSourceCells,
      originalCell_eq_cursorOriginal,
      TargetEmitterRuntimeLayout.sourceCells_eq_original,
      List.append_assoc] using restoredAtRight
  have firstTwo :=
    AcceptPath.trans graph (.node leftFirstRef)
      (.node (leftSourceRef kind)) (.node (leftRestoreRef kind))
      (sourceCapturePhaseSteps before source runtime.scratch)
      blockSteps initialTape capturedTape blockTape
      capturePath blockPath
  have all :=
    AcceptPath.trans graph (.node leftFirstRef)
      (.node (leftRestoreRef kind)) (.node rightFirstRef)
      (sourceCapturePhaseSteps before source runtime.scratch + blockSteps)
      (TargetEmitterControllerSourceTrace.restorePathSteps
        restoreBefore.length)
      initialTape blockTape restored.tape firstTwo restorePath
  exact
    ⟨sourceCapturePhaseSteps before source runtime.scratch +
        blockSteps +
        TargetEmitterControllerSourceTrace.restorePathSteps
          restoreBefore.length,
      restored.tape, by simpa [Nat.add_assoc] using all,
      by simpa [final, capturedState, before, kind, value] using finalFocus⟩

/-! ### One complete right-source and trace phase -/

/-- Classify and capture the right literal, emit its source macro, emit the
eighteen-gate trace macro, advance `currentGate`, restore the retained source,
and arrive at the gate-list navigator. -/
theorem rightSourceTracePhase_path
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
            (sourceValue source) +
          1 ≤
        TargetEmitterLedger.slotCapacity raw)
    (capturedBound :
      TargetEmitterControllerSourceTrace.capturedValue
          (TargetEmitterControllerTrace.sourceKind source)
          (sourceValue source) +
          1 ≤
        (SourceParser.circuitCells raw).length)
    (afterSourceRange :
      ControllerRange raw
        (TargetEmitterProgramSemantics.macroResult
          (capturedRuntime runtime
            (TargetEmitterControllerTrace.sourceKind source)
            (sourceValue source))
          (TargetEmitterPlan.sourcePlan
            (TargetEmitterControllerTrace.sourceKind source) 1)
          (TargetEmitterPlan.sourceCheckRelative
            (TargetEmitterControllerTrace.sourceKind source))
          (TargetEmitterPlan.sourceGateCount
            (TargetEmitterControllerTrace.sourceKind source))).registers)
    (nextGate :
      (TargetEmitterProgramSemantics.macroResult
        (capturedRuntime runtime
          (TargetEmitterControllerTrace.sourceKind source)
          (sourceValue source))
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
            (capturedRuntime runtime
              (TargetEmitterControllerTrace.sourceKind source)
              (sourceValue source))
            (TargetEmitterPlan.sourcePlan
              (TargetEmitterControllerTrace.sourceKind source) 1)
            (TargetEmitterPlan.sourceCheckRelative
              (TargetEmitterControllerTrace.sourceKind source))
            (TargetEmitterPlan.sourceGateCount
              (TargetEmitterControllerTrace.sourceKind source)))).scratch
        (TargetEmitterRuntimeProgramSafety.rightTraceResult
          (TargetEmitterProgramSemantics.macroResult
            (capturedRuntime runtime
              (TargetEmitterControllerTrace.sourceKind source)
              (sourceValue source))
            (TargetEmitterPlan.sourcePlan
              (TargetEmitterControllerTrace.sourceKind source) 1)
            (TargetEmitterPlan.sourceCheckRelative
              (TargetEmitterControllerTrace.sourceKind source))
            (TargetEmitterPlan.sourceGateCount
              (TargetEmitterControllerTrace.sourceKind source)))).registers
        (TargetEmitterRuntimeProgramSafety.rightTraceResult
          (TargetEmitterProgramSemantics.macroResult
            (capturedRuntime runtime
              (TargetEmitterControllerTrace.sourceKind source)
              (sourceValue source))
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
            (capturedRuntime runtime
              (TargetEmitterControllerTrace.sourceKind source)
              (sourceValue source))
            (TargetEmitterPlan.sourcePlan
              (TargetEmitterControllerTrace.sourceKind source) 1)
            (TargetEmitterPlan.sourceCheckRelative
              (TargetEmitterControllerTrace.sourceKind source))
            (TargetEmitterPlan.sourceGateCount
              (TargetEmitterControllerTrace.sourceKind source)))).targetTokens
        finalTape := by
  let kind := TargetEmitterControllerTrace.sourceKind source
  let value := sourceValue source
  let before := head :: prefixTail
  let marked :=
    before ++
      TargetEmitterControllerSourceTrace.captureMarkedSourceCells
        kind value ++ after
  let capturedState := capturedRuntime runtime kind value
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
      ← sourceCells_eq_captureSourceCells source] using originalPacked
  rcases
      rightClassifyCapture_path
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        before after source target initialTape
        captureReserve beforePacked represents with
    ⟨capturedTape, capturePath, capturedRepresents⟩
  let workspace :=
    markedWorkspace kind value head prefixTail after
      (by simpa [before] using originalCapturePacked)
  have valueBound :
      TargetEmitterControllerSourceTrace.capturedValue kind value + 1 ≤
        TargetEmitterLedger.slotCapacity raw := by
    simp [kind, value] at captureReserve ⊢
    omega
  let ready :=
    sourceReady raw kind value before after beforePacked valueBound
  have capturedLogical :
      TapeRepresents (rightSourceRef kind).startState
        (TargetEmitterLedger.slotCapacity raw)
        capturedState.scratch capturedState.registers
        capturedState.checks marked capturedState.targetTokens
        capturedTape := by
    simpa [capturedState, capturedRuntime, marked, kind, value,
      targetEq] using capturedRepresents
  have capturedScratchBound :
      capturedState.scratch <
        TargetEmitterLedger.slotCapacity raw := by
    simp [capturedState, capturedRuntime, kind, value]
    omega
  have capturedIndexBound :
      capturedState.captured + 1 ≤
        (SourceParser.circuitCells raw).length := by
    simpa [capturedState, capturedRuntime, kind, value] using
      capturedBound
  rcases
      rightSourceBlock_path kind workspace capturedState range
        capturedIndexBound capturedScratchBound ready
        capturedTape capturedLogical with
    ⟨sourceSteps, sourceTape, sourcePath, sourceRepresents⟩
  have sourceScratchBound :
      sourceFinal.scratch <
        TargetEmitterLedger.slotCapacity raw := by
    simp [sourceFinal,
      TargetEmitterProgramSemantics.macroResult_scratch,
      TargetEmitterLedger.slotCapacity]
  have sourceCapturedBound :
      sourceFinal.captured + 1 ≤
        (SourceParser.circuitCells raw).length := by
    rw [macroResult_captured]
    exact capturedIndexBound
  rcases
      rightTraceBlock_path kind workspace sourceFinal
        (by simpa [sourceFinal, capturedState, kind, value] using
          afterSourceRange)
        sourceCapturedBound sourceScratchBound
        (by simpa [sourceFinal, capturedState, kind, value] using
          nextGate)
        sourceTape
        (by simpa [sourceFinal] using sourceRepresents) with
    ⟨traceSteps, traceTape, tracePath, traceRepresents⟩
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
      rw [sourceCells_eq_captureSourceCells]
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
    simpa [FocusTapeRepresents, restoreBefore, before, kind, value,
      sourceCells_eq_captureSourceCells,
      TargetEmitterControllerSourceTrace.captureSourceCells,
      originalCell_eq_cursorOriginal,
      TargetEmitterRuntimeLayout.sourceCells_eq_original,
      List.append_assoc] using restoredAtAdvance
  have firstTwo :=
    AcceptPath.trans graph (.node rightFirstRef)
      (.node (rightSourceRef kind)) (.node (rightTraceRef kind))
      (sourceCapturePhaseSteps before source runtime.scratch)
      sourceSteps initialTape capturedTape sourceTape
      capturePath sourcePath
  have firstThree :=
    AcceptPath.trans graph (.node rightFirstRef)
      (.node (rightTraceRef kind)) (.node (rightRestoreRef kind))
      (sourceCapturePhaseSteps before source runtime.scratch +
        sourceSteps)
      traceSteps initialTape sourceTape traceTape
      firstTwo tracePath
  have all :=
    AcceptPath.trans graph (.node rightFirstRef)
      (.node (rightRestoreRef kind)) (.node gateAdvanceRef)
      (sourceCapturePhaseSteps before source runtime.scratch +
        sourceSteps + traceSteps)
      (TargetEmitterControllerSourceTrace.restorePathSteps
        restoreBefore.length)
      initialTape traceTape restored.tape firstThree restorePath
  exact
    ⟨sourceCapturePhaseSteps before source runtime.scratch +
        sourceSteps + traceSteps +
        TargetEmitterControllerSourceTrace.restorePathSteps
          restoreBefore.length,
      restored.tape, by simpa [Nat.add_assoc] using all,
      by simpa [traced, sourceFinal, capturedState, before, kind, value]
        using finalFocus⟩

/-! ### Both sources of one raw gate -/

/-- Traverse both sources of one raw gate and its trace macro.  The theorem
stops at the fixed gate-advance navigator so the caller can select the
already-materialized next-gate or program-end branch from the retained source
suffix. -/
theorem gateSourcesTrace_path
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
            (sourceValue gate.left) +
          1 ≤
        TargetEmitterLedger.slotCapacity raw)
    (leftCapturedBound :
      TargetEmitterControllerSourceTrace.capturedValue
          (TargetEmitterControllerTrace.sourceKind gate.left)
          (sourceValue gate.left) +
          1 ≤
        (SourceParser.circuitCells raw).length)
    (afterLeftRange :
      ControllerRange raw
        (TargetEmitterProgramSemantics.macroResult
          (capturedRuntime runtime
            (TargetEmitterControllerTrace.sourceKind gate.left)
            (sourceValue gate.left))
          (TargetEmitterPlan.sourcePlan
            (TargetEmitterControllerTrace.sourceKind gate.left) 0)
          (TargetEmitterPlan.sourceCheckRelative
            (TargetEmitterControllerTrace.sourceKind gate.left))
          (TargetEmitterPlan.sourceGateCount
            (TargetEmitterControllerTrace.sourceKind gate.left))).registers)
    (rightCaptureReserve :
      (TargetEmitterProgramSemantics.macroResult
          (capturedRuntime runtime
            (TargetEmitterControllerTrace.sourceKind gate.left)
            (sourceValue gate.left))
          (TargetEmitterPlan.sourcePlan
            (TargetEmitterControllerTrace.sourceKind gate.left) 0)
          (TargetEmitterPlan.sourceCheckRelative
            (TargetEmitterControllerTrace.sourceKind gate.left))
          (TargetEmitterPlan.sourceGateCount
            (TargetEmitterControllerTrace.sourceKind gate.left))).scratch +
          TargetEmitterControllerSourceTrace.capturedValue
            (TargetEmitterControllerTrace.sourceKind gate.right)
            (sourceValue gate.right) +
          1 ≤
        TargetEmitterLedger.slotCapacity raw)
    (rightCapturedBound :
      TargetEmitterControllerSourceTrace.capturedValue
          (TargetEmitterControllerTrace.sourceKind gate.right)
          (sourceValue gate.right) +
          1 ≤
        (SourceParser.circuitCells raw).length)
    (afterRightRange :
      ControllerRange raw
        (TargetEmitterProgramSemantics.macroResult
          (capturedRuntime
            (TargetEmitterProgramSemantics.macroResult
              (capturedRuntime runtime
                (TargetEmitterControllerTrace.sourceKind gate.left)
                (sourceValue gate.left))
              (TargetEmitterPlan.sourcePlan
                (TargetEmitterControllerTrace.sourceKind gate.left) 0)
              (TargetEmitterPlan.sourceCheckRelative
                (TargetEmitterControllerTrace.sourceKind gate.left))
              (TargetEmitterPlan.sourceGateCount
                (TargetEmitterControllerTrace.sourceKind gate.left)))
            (TargetEmitterControllerTrace.sourceKind gate.right)
            (sourceValue gate.right))
          (TargetEmitterPlan.sourcePlan
            (TargetEmitterControllerTrace.sourceKind gate.right) 1)
          (TargetEmitterPlan.sourceCheckRelative
            (TargetEmitterControllerTrace.sourceKind gate.right))
          (TargetEmitterPlan.sourceGateCount
            (TargetEmitterControllerTrace.sourceKind gate.right))).registers)
    (nextGate :
      (TargetEmitterProgramSemantics.macroResult
        (capturedRuntime
          (TargetEmitterProgramSemantics.macroResult
            (capturedRuntime runtime
              (TargetEmitterControllerTrace.sourceKind gate.left)
              (sourceValue gate.left))
            (TargetEmitterPlan.sourcePlan
              (TargetEmitterControllerTrace.sourceKind gate.left) 0)
            (TargetEmitterPlan.sourceCheckRelative
              (TargetEmitterControllerTrace.sourceKind gate.left))
            (TargetEmitterPlan.sourceGateCount
              (TargetEmitterControllerTrace.sourceKind gate.left)))
          (TargetEmitterControllerTrace.sourceKind gate.right)
          (sourceValue gate.right))
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
              (capturedRuntime
                (TargetEmitterProgramSemantics.macroResult
                  (capturedRuntime runtime
                    (TargetEmitterControllerTrace.sourceKind gate.left)
                    (sourceValue gate.left))
                  (TargetEmitterPlan.sourcePlan
                    (TargetEmitterControllerTrace.sourceKind gate.left) 0)
                  (TargetEmitterPlan.sourceCheckRelative
                    (TargetEmitterControllerTrace.sourceKind gate.left))
                  (TargetEmitterPlan.sourceGateCount
                    (TargetEmitterControllerTrace.sourceKind gate.left)))
                (TargetEmitterControllerTrace.sourceKind gate.right)
                (sourceValue gate.right))
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
          afterGate finalRuntime.targetTokens finalTape := by
  let leftFinal :=
    TargetEmitterProgramSemantics.macroResult
      (capturedRuntime runtime
        (TargetEmitterControllerTrace.sourceKind gate.left)
        (sourceValue gate.left))
      (TargetEmitterPlan.sourcePlan
        (TargetEmitterControllerTrace.sourceKind gate.left) 0)
      (TargetEmitterPlan.sourceCheckRelative
        (TargetEmitterControllerTrace.sourceKind gate.left))
      (TargetEmitterPlan.sourceGateCount
        (TargetEmitterControllerTrace.sourceKind gate.left))
  let rightBase :=
    capturedRuntime leftFinal
      (TargetEmitterControllerTrace.sourceKind gate.right)
      (sourceValue gate.right)
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
      leftSourcePhase_path runtime range head prefixTail
        (SourceParser.sourceCells gate.right ++ afterGate)
        gate.left target initialTape
        leftCaptureReserve leftCapturedBound leftPacked targetEq
        (by simpa [List.append_assoc] using represents) with
    ⟨leftSteps, leftTape, leftPath, leftRepresents⟩
  have rightPacked :
      ∀ symbol,
        symbol ∈
            (head ::
              (prefixTail ++ SourceParser.sourceCells gate.left)) ++
              SourceParser.sourceCells gate.right ++ afterGate →
          TargetEmitter.PackedSymbol symbol := by
    simpa [List.append_assoc] using originalPacked
  rcases
      rightSourceTracePhase_path leftFinal
        (by simpa [leftFinal] using afterLeftRange)
        head (prefixTail ++ SourceParser.sourceCells gate.left)
        afterGate gate.right leftFinal.targetTokens leftTape
        (by simpa [leftFinal] using rightCaptureReserve)
        rightCapturedBound
        (by simpa [rightFinal, rightBase, leftFinal] using
          afterRightRange)
        (by simpa [rightFinal, rightBase, leftFinal] using nextGate)
        rightPacked rfl
        (by simpa [leftFinal, List.append_assoc] using
          leftRepresents) with
    ⟨rightSteps, finalTape, rightPath, rightRepresents⟩
  have path :=
    AcceptPath.trans graph (.node leftFirstRef)
      (.node rightFirstRef) (.node gateAdvanceRef)
      leftSteps rightSteps initialTape leftTape finalTape
      leftPath rightPath
  refine
    ⟨leftSteps + rightSteps, finalTape, path,
      finalRuntime, rfl, ?_⟩
  simpa [finalRuntime, rightFinal, rightBase, leftFinal,
    List.append_assoc] using rightRepresents

/-! ### Gate-list advance -/

private theorem canonicalGateEndTape
    (state capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (crossed rest : List WorkSymbol)
    (target : List Token) :
    TargetEmitterControllerTrace.gateEndFocusTape
        (crossed.reverse ++
          TargetEmitterRuntime.logicalLeftWorkspace
            capacity scratch registers checks)
        (rest ++
          TargetEmitterRuntimeSourceControl.targetSuffix target) =
      (TargetEmitterRuntimeSourceControl.sourceFocusConfiguration
        state capacity scratch registers checks crossed
        ([SourceParser.cell01, SourceParser.cell11] ++ rest)
        target).tape := by
  simpa [TargetEmitterControllerTrace.gateEndFocusTape,
    TargetEmitterRuntimeSourceControl.sourceFocusConfiguration,
    TargetEmitterRuntimeSourceControl.targetSuffix,
    List.append_assoc] using
    (configAtWord_tape_irrel 0 state
      (crossed.reverse ++
        TargetEmitterRuntime.logicalLeftWorkspace
          capacity scratch registers checks)
      ([SourceParser.cell01, SourceParser.cell11] ++
        (rest ++
          TargetEmitterRuntimeSourceControl.targetSuffix target)))

private theorem canonicalAdvancedSourceTape
    (state capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (crossed after : List WorkSymbol)
    (source : RawSource) (target : List Token) :
    TargetEmitterControllerTrace.sourceFocusTape
        (SourceParser.cell11 :: SourceParser.cell01 ::
          (crossed.reverse ++
            TargetEmitterRuntime.logicalLeftWorkspace
              capacity scratch registers checks))
        source
        (after ++
          TargetEmitterRuntimeSourceControl.targetSuffix target) =
      (TargetEmitterRuntimeSourceControl.sourceFocusConfiguration
        state capacity scratch registers checks
        (crossed ++ [SourceParser.cell01, SourceParser.cell11])
        (SourceParser.sourceCells source ++ after) target).tape := by
  simpa [TargetEmitterControllerTrace.sourceFocusTape,
    TargetEmitterRuntimeSourceControl.sourceFocusConfiguration,
    TargetEmitterRuntimeSourceControl.targetSuffix,
    List.reverse_append, List.append_assoc] using
    (configAtWord_tape_irrel 0 state
      (SourceParser.cell11 :: SourceParser.cell01 ::
        (crossed.reverse ++
          TargetEmitterRuntime.logicalLeftWorkspace
            capacity scratch registers checks))
      (SourceParser.sourceCells source ++
        (after ++
          TargetEmitterRuntimeSourceControl.targetSuffix target)))

/-- Follow the literal next-gate branch while retaining the exact runtime
workspace and moving the source focus across the consumed gate delimiter. -/
theorem gateAdvanceNext_path
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (crossed after : List WorkSymbol)
    (source : RawSource) (target : List Token)
    (initialTape : WorkTape)
    (represents :
      FocusTapeRepresents gateAdvanceRef.startState
        capacity scratch registers checks crossed
        ([SourceParser.cell01, SourceParser.cell11] ++
          SourceParser.sourceCells source ++ after)
        target initialTape) :
    ∃ finalTape,
      AcceptPath graph (.node gateAdvanceRef)
          (.node leftFirstRef) 4 initialTape finalTape ∧
      FocusTapeRepresents leftFirstRef.startState
        capacity scratch registers checks
        (crossed ++ [SourceParser.cell01, SourceParser.cell11])
        (SourceParser.sourceCells source ++ after)
        target finalTape := by
  let canonical :=
    (TargetEmitterRuntimeSourceControl.sourceFocusConfiguration
      gateAdvanceRef.startState capacity scratch registers checks crossed
      ([SourceParser.cell01, SourceParser.cell11] ++
        SourceParser.sourceCells source ++ after) target).tape
  have canonicalPath :
      AcceptPath graph (.node gateAdvanceRef)
        (.node leftFirstRef) 4 canonical
        (TargetEmitterRuntimeSourceControl.sourceFocusConfiguration
          leftFirstRef.startState capacity scratch registers checks
          (crossed ++ [SourceParser.cell01, SourceParser.cell11])
          (SourceParser.sourceCells source ++ after) target).tape := by
    have path :=
      TargetEmitterControllerTrace.gate_advance_next_path
        (crossed.reverse ++
          TargetEmitterRuntime.logicalLeftWorkspace
            capacity scratch registers checks)
        source
        (after ++
          TargetEmitterRuntimeSourceControl.targetSuffix target)
    have inputRestEq :
        SourceParser.sourceCells source ++
            (after ++
              TargetEmitterRuntimeSourceControl.targetSuffix target) =
          (SourceParser.sourceCells source ++ after) ++
            TargetEmitterRuntimeSourceControl.targetSuffix target :=
      (List.append_assoc _ _ _).symm
    rw [inputRestEq] at path
    rw [canonicalGateEndTape
      gateAdvanceRef.startState capacity scratch registers checks
      crossed (SourceParser.sourceCells source ++ after) target] at path
    rw [canonicalAdvancedSourceTape
      leftFirstRef.startState capacity scratch registers checks
      crossed after source target] at path
    simpa [canonical, List.append_assoc] using path
  rcases canonicalPath.transport represents.tape with
    ⟨finalTape, path, finalEquivalent⟩
  refine ⟨finalTape, path, ?_⟩
  exact
    ⟨by
        simpa using
          (sourceFocusConfiguration_state
            leftFirstRef.startState capacity scratch registers checks
            (crossed ++ [SourceParser.cell01, SourceParser.cell11])
            (SourceParser.sourceCells source ++ after) target).symm,
      finalEquivalent⟩

/-- Canonical source-focus tape after the last gate delimiter and the
program-end marker have been crossed. -/
private theorem canonicalOutputSourceTape
    (state capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (crossed : List WorkSymbol)
    (output : RawSource) (target : List Token) :
    TargetEmitterControllerTrace.sourceFocusTape
        (SourceParser.cell00 :: SourceParser.cell10 ::
          SourceParser.cell11 :: SourceParser.cell01 ::
            (crossed.reverse ++
              TargetEmitterRuntime.logicalLeftWorkspace
                capacity scratch registers checks))
        output
        (TargetEmitterControllerTrace.circuitTerminatorCells ++
          TargetEmitterRuntimeSourceControl.targetSuffix target) =
      (TargetEmitterRuntimeSourceControl.sourceFocusConfiguration
        state capacity scratch registers checks
        (crossed ++
          [SourceParser.cell01, SourceParser.cell11,
            SourceParser.cell10, SourceParser.cell00])
        (SourceParser.sourceCells output ++
          TargetEmitterControllerTrace.circuitTerminatorCells)
        target).tape := by
  simpa [TargetEmitterControllerTrace.sourceFocusTape,
    TargetEmitterRuntimeSourceControl.sourceFocusConfiguration,
    TargetEmitterRuntimeSourceControl.targetSuffix,
    List.reverse_append, List.append_assoc] using
    (configAtWord_tape_irrel 0 state
      (SourceParser.cell00 :: SourceParser.cell10 ::
        SourceParser.cell11 :: SourceParser.cell01 ::
          (crossed.reverse ++
            TargetEmitterRuntime.logicalLeftWorkspace
              capacity scratch registers checks))
      (SourceParser.sourceCells output ++
        (TargetEmitterControllerTrace.circuitTerminatorCells ++
          TargetEmitterRuntimeSourceControl.targetSuffix target)))

/-- Follow the literal last-gate branch through the program-end navigator and
focus the retained circuit output without changing the runtime workspace. -/
theorem gateAdvanceOutput_path
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (crossed : List WorkSymbol)
    (output : RawSource) (target : List Token)
    (initialTape : WorkTape)
    (represents :
      FocusTapeRepresents gateAdvanceRef.startState
        capacity scratch registers checks crossed
        ([SourceParser.cell01, SourceParser.cell11] ++
          TargetEmitterControllerTrace.circuitFooterCells output)
        target initialTape) :
    ∃ finalTape,
      AcceptPath graph (.node gateAdvanceRef)
          (.node outputFirstRef) 7 initialTape finalTape ∧
      FocusTapeRepresents outputFirstRef.startState
        capacity scratch registers checks
        (crossed ++
          [SourceParser.cell01, SourceParser.cell11,
            SourceParser.cell10, SourceParser.cell00])
        (SourceParser.sourceCells output ++
          TargetEmitterControllerTrace.circuitTerminatorCells)
        target finalTape := by
  let canonical :=
    (TargetEmitterRuntimeSourceControl.sourceFocusConfiguration
      gateAdvanceRef.startState capacity scratch registers checks crossed
      ([SourceParser.cell01, SourceParser.cell11] ++
        TargetEmitterControllerTrace.circuitFooterCells output)
      target).tape
  have canonicalPath :
      AcceptPath graph (.node gateAdvanceRef)
        (.node outputFirstRef) 7 canonical
        (TargetEmitterRuntimeSourceControl.sourceFocusConfiguration
          outputFirstRef.startState capacity scratch registers checks
          (crossed ++
            [SourceParser.cell01, SourceParser.cell11,
              SourceParser.cell10, SourceParser.cell00])
          (SourceParser.sourceCells output ++
            TargetEmitterControllerTrace.circuitTerminatorCells)
          target).tape := by
    have path :=
      TargetEmitterControllerTrace.gate_advance_to_output_path
        (crossed.reverse ++
          TargetEmitterRuntime.logicalLeftWorkspace
            capacity scratch registers checks)
        output target
    change
      AcceptPath graph (.node gateAdvanceRef)
        (.node outputFirstRef) 7
        (TargetEmitterControllerTrace.gateEndFocusTape
          (crossed.reverse ++
            TargetEmitterRuntime.logicalLeftWorkspace
              capacity scratch registers checks)
          (TargetEmitterControllerTrace.circuitFooterCells output ++
            TargetEmitterRuntimeSourceControl.targetSuffix target))
        _ at path
    rw [canonicalGateEndTape
      gateAdvanceRef.startState capacity scratch registers checks
      crossed
      (TargetEmitterControllerTrace.circuitFooterCells output)
      target] at path
    change
      AcceptPath graph (.node gateAdvanceRef)
        (.node outputFirstRef) 7 canonical
        (TargetEmitterControllerTrace.sourceFocusTape
          (SourceParser.cell00 :: SourceParser.cell10 ::
            SourceParser.cell11 :: SourceParser.cell01 ::
              (crossed.reverse ++
                TargetEmitterRuntime.logicalLeftWorkspace
                  capacity scratch registers checks))
          output
          (TargetEmitterControllerTrace.circuitTerminatorCells ++
            TargetEmitterRuntimeSourceControl.targetSuffix target)) at path
    rw [canonicalOutputSourceTape
      outputFirstRef.startState capacity scratch registers checks
      crossed output target] at path
    simpa [canonical, List.append_assoc] using path
  rcases canonicalPath.transport represents.tape with
    ⟨finalTape, path, finalEquivalent⟩
  refine ⟨finalTape, path, ?_⟩
  exact
    ⟨by
        simpa using
          (sourceFocusConfiguration_state
            outputFirstRef.startState capacity scratch registers checks
            (crossed ++
              [SourceParser.cell01, SourceParser.cell11,
                SourceParser.cell10, SourceParser.cell00])
            (SourceParser.sourceCells output ++
              TargetEmitterControllerTrace.circuitTerminatorCells)
            target).symm,
      finalEquivalent⟩

end PNP.Concrete.LockedNAND.TargetEmitterControllerGateTrace
