/-
Copyright (c) 2026 PNP Labs.

Closed physical execution of the grammar-only locked-NAND target emitter.

The proof joins the literal gate-list traversal, output-selected
normalization, newest-first prefix fold, final template, and output loop.
All schedules, layouts, and capacity facts are derived from the decoded raw
circuit and remain proof-side; the fixed executable graph receives only the
retained source word.
-/

import PNP.Concrete.LockedNANDTargetEmitterControllerGateListTrace
import PNP.Concrete.LockedNANDTargetEmitterControllerNormalizationTrace
import PNP.Concrete.LockedNANDTargetEmitterControllerNormalizationBound
import PNP.Concrete.LockedNANDTargetEmitterControllerPrefixTrace
import PNP.Concrete.LockedNANDTargetEmitterControllerPrefixBound
import PNP.Concrete.LockedNANDTargetEmitterControllerOutputBound
import PNP.Concrete.LockedNANDTargetEmitterSemanticPrefixBridge
import PNP.Concrete.LockedNANDTargetEmitterSemanticCompletion

namespace PNP.Concrete.LockedNAND.TargetEmitterControllerCompletionTrace

open PNP.Concrete
open WorkMachineProgramGraph
open WorkMachineProgramPath
open TargetEmitterController

set_option maxRecDepth 200000
set_option maxHeartbeats 1000000

abbrev Runtime := TargetEmitterProgramSemantics.Runtime
abbrev FocusTapeRepresents :=
  TargetEmitterControllerGateTrace.FocusTapeRepresents
abbrev TapeRepresents :=
  TargetEmitterControllerPrefixTrace.TapeRepresents
abbrev MarkedWorkspace :=
  TargetEmitterRuntimeProgramSafety.MarkedWorkspace
abbrev ControllerRange :=
  TargetEmitterCapacity.ControllerRange

/-- The retained source after the output field has been captured. -/
def markedSource (raw : RawCircuit) : List WorkSymbol :=
  TargetEmitterControllerGateListTrace.outputCrossedCells raw ++
    TargetEmitterControllerSourceTrace.captureMarkedSourceCells
      (TargetEmitterControllerTrace.sourceKind raw.output)
      (TargetEmitterControllerGateTrace.sourceValue raw.output) ++
    TargetEmitterControllerTrace.circuitTerminatorCells

/-- Capturing the output cursor only changes marker symbols; it preserves the
retained packed source length exactly. -/
theorem markedSource_length (raw : RawCircuit) :
    (markedSource raw).length =
      (SourceParser.circuitCells raw).length := by
  cases raw with
  | mk inputs gates output =>
      cases output with
      | input index =>
          simp [markedSource,
            TargetEmitterControllerGateListTrace.outputCrossedCells,
            TargetEmitterControllerTrace.circuitHeaderCells,
            TargetEmitterControllerTrace.circuitTerminatorCells,
            TargetEmitterControllerSourceTrace.captureMarkedSourceCells,
            TargetEmitterControllerSourceTrace.capturedValue,
            TargetEmitterControllerGateTrace.sourceValue,
            TargetEmitterControllerTrace.sourceKind,
            TargetEmitterController.Plan.captureKind,
            TargetEmitterSourceCapture.markedSourceCells,
            TargetEmitterSourceCapture.unitPrefix_length,
            SourceParser.circuitCells, SourceParser.sourceCells,
            SourceParser.natCells_length]
          omega
      | gate index =>
          simp [markedSource,
            TargetEmitterControllerGateListTrace.outputCrossedCells,
            TargetEmitterControllerTrace.circuitHeaderCells,
            TargetEmitterControllerTrace.circuitTerminatorCells,
            TargetEmitterControllerSourceTrace.captureMarkedSourceCells,
            TargetEmitterControllerSourceTrace.capturedValue,
            TargetEmitterControllerGateTrace.sourceValue,
            TargetEmitterControllerTrace.sourceKind,
            TargetEmitterController.Plan.captureKind,
            TargetEmitterSourceCapture.markedSourceCells,
            TargetEmitterSourceCapture.unitPrefix_length,
            SourceParser.circuitCells, SourceParser.sourceCells,
            SourceParser.natCells_length]
          omega
      | constant value =>
          cases value <;>
            simp [markedSource,
              TargetEmitterControllerGateListTrace.outputCrossedCells,
              TargetEmitterControllerTrace.circuitHeaderCells,
              TargetEmitterControllerTrace.circuitTerminatorCells,
              TargetEmitterControllerSourceTrace.captureMarkedSourceCells,
              TargetEmitterControllerTrace.sourceKind,
              TargetEmitterController.Plan.captureKind,
              TargetEmitterSourceCapture.markedSourceCells,
              SourceParser.circuitCells, SourceParser.sourceCells]

private def outputPrefixTail (raw : RawCircuit) : List WorkSymbol :=
  SourceParser.cell00 ::
    (SourceParser.natCells raw.inputCount ++
      SourceParser.natCells raw.gates.length ++
      SourceParser.gateListCells raw.gates ++
      [SourceParser.cell10, SourceParser.cell00])

private theorem outputCrossedCells_eq
    (raw : RawCircuit) :
    TargetEmitterControllerGateListTrace.outputCrossedCells raw =
      SourceParser.cell00 :: outputPrefixTail raw := by
  simp [TargetEmitterControllerGateListTrace.outputCrossedCells,
    TargetEmitterControllerTrace.circuitHeaderCells,
    outputPrefixTail, List.append_assoc]

private theorem originalOutputWord_packed
    (raw : RawCircuit) :
    ∀ symbol,
      symbol ∈
          TargetEmitterControllerGateListTrace.outputCrossedCells raw ++
            SourceParser.sourceCells raw.output ++
            TargetEmitterControllerTrace.circuitTerminatorCells →
        TargetEmitter.PackedSymbol symbol := by
  intro symbol member
  apply TargetEmitter.circuitCells_packed raw symbol
  simpa [TargetEmitterControllerGateListTrace.outputCrossedCells,
    TargetEmitterControllerTrace.circuitHeaderCells,
    TargetEmitterControllerTrace.circuitTerminatorCells,
    SourceParser.circuitCells, List.append_assoc] using member

private def outputWorkspace
    (raw : RawCircuit) : MarkedWorkspace (markedSource raw) := by
  unfold markedSource
  rw [outputCrossedCells_eq]
  simpa [markedSource,
    TargetEmitterControllerGateTrace.sourceCells_eq_captureSourceCells,
    List.append_assoc] using
    (TargetEmitterControllerGateTrace.markedWorkspace
      (TargetEmitterControllerTrace.sourceKind raw.output)
      (TargetEmitterControllerGateTrace.sourceValue raw.output)
      SourceParser.cell00 (outputPrefixTail raw)
      TargetEmitterControllerTrace.circuitTerminatorCells
      (by
        have packed := originalOutputWord_packed raw
        rw [
          TargetEmitterControllerGateTrace.sourceCells_eq_captureSourceCells
            raw.output] at packed
        simpa [outputCrossedCells_eq] using packed))

private theorem appendGateListResults_nonempty_scratch
    (gate : RawGate) (rest : List RawGate) (runtime : Runtime) :
    (TargetEmitterSemanticSchedule.appendGateListResults
      (gate :: rest) runtime).scratch = 0 := by
  induction rest generalizing gate runtime with
  | nil =>
      rfl
  | cons next tail inductionHypothesis =>
      simp only [
        TargetEmitterSemanticSchedule.appendGateListResults]
      exact inductionHypothesis next
        (TargetEmitterSemanticSchedule.appendGateResult gate runtime)

private theorem gateListRuntime_scratch_shape
    (raw : RawCircuit) :
    (TargetEmitterControllerGateListTrace.gateListRuntime raw).scratch = 0 ∨
      (TargetEmitterControllerGateListTrace.gateListRuntime raw).scratch =
        TargetEmitterLedger.baselineValue raw + 1 := by
  cases raw with
  | mk inputs gates output =>
      cases gates with
      | nil =>
          right
          simp [TargetEmitterControllerGateListTrace.gateListRuntime,
            TargetEmitterSemanticSchedule.appendGateListResults,
            TargetEmitterControllerHeaderTrace.initialRuntime,
            TargetEmitterProgramSemantics.headerResult_scratch,
            TargetEmitterLedger.ledgerRegisters]
      | cons gate rest =>
          left
          exact appendGateListResults_nonempty_scratch gate rest
            (TargetEmitterProgramSemantics.headerResult
              (TargetEmitterControllerHeaderTrace.initialRuntime
                { inputCount := inputs
                  gates := gate :: rest
                  output := output }))

private theorem output_capture_reserve
    (raw : RawCircuit) :
    let runtime :=
      TargetEmitterControllerGateListTrace.gateListRuntime raw
    runtime.scratch +
        TargetEmitterCapacity.sourceCaptureValue raw.output + 1 ≤
      TargetEmitterLedger.slotCapacity raw := by
  dsimp only
  have member :
      TargetEmitterCapacity.CircuitSource raw raw.output := .output
  rcases gateListRuntime_scratch_shape raw with zero | header
  · exact
      TargetEmitterCapacity.focusedSourceCaptureReserve_of_equal
        member zero rfl
  · exact
      TargetEmitterCapacity.headerFocusedSourceCaptureReserve_of_equal
        member header rfl

private theorem runtime_ext
    (left right : Runtime)
    (captured : left.captured = right.captured)
    (scratch : left.scratch = right.scratch)
    (registers : left.registers = right.registers)
    (checks : left.checks = right.checks)
    (targetTokens : left.targetTokens = right.targetTokens) :
    left = right := by
  cases left
  cases right
  simp_all

private theorem sourceGateCount_eq_rawBuilder
    (source : RawSource) :
    TargetEmitterPlan.sourceGateCount
        (TargetEmitterSemanticSchedule.sourceKind source) =
      RawBuilder.sourceMacroGateCount source := by
  cases source with
  | input index => rfl
  | gate index => rfl
  | constant value => cases value <;> rfl

private theorem appendGateResult_registers
    (gate : RawGate) (runtime : Runtime) :
    (TargetEmitterSemanticSchedule.appendGateResult
        gate runtime).registers =
      { runtime.registers with
        currentGate := runtime.registers.currentGate + 1
        outputIndex :=
          runtime.registers.outputIndex +
            RawBuilder.gateMacroGateCount gate } := by
  simp [TargetEmitterSemanticSchedule.appendGateResult,
    TargetEmitterSemanticSchedule.appendSourceResult,
    TargetEmitterSemanticSchedule.withCaptured,
    TargetEmitterProgramSemantics.macroResult_registers,
    TargetEmitterProgramSemantics.incrementCurrentGateResult,
    sourceGateCount_eq_rawBuilder,
    TargetEmitterPlan.traceGateCount,
    RawBuilder.gateMacroGateCount, Nat.add_assoc]

private theorem appendGateListResults_registers
    (gates : List RawGate) (runtime : Runtime) :
    (TargetEmitterSemanticSchedule.appendGateListResults
        gates runtime).registers =
      { runtime.registers with
        currentGate := runtime.registers.currentGate + gates.length
        outputIndex :=
          runtime.registers.outputIndex +
            RawBuilder.gateListMacroGateCount gates } := by
  induction gates generalizing runtime with
  | nil =>
      rfl
  | cons gate rest inductionHypothesis =>
      rw [TargetEmitterSemanticSchedule.appendGateListResults,
        inductionHypothesis, appendGateResult_registers]
      simp only [List.length_cons,
        RawBuilder.gateListMacroGateCount]
      congr 1 <;> omega

private theorem rawPrefixRuntime_registers_constructive
    (raw : RawCircuit) :
    (TargetEmitterSemanticNormalization.rawPrefixRuntime raw).registers =
      { TargetEmitterLedger.ledgerRegisters raw with
        currentGate := raw.gates.length
        outputIndex :=
          RawBuilder.gateListMacroGateCount raw.gates } := by
  rw [TargetEmitterSemanticNormalization.rawPrefixRuntime,
    appendGateListResults_registers]
  simp [TargetEmitterSemanticSchedule.normalizedMacroStartRuntime,
    TargetEmitterSemanticSchedule.initialRuntime,
    TargetEmitterProgramSemantics.headerResult_registers,
    TargetEmitterLedger.ledgerRegisters]

private structure MacroCursor
    (assembly : RawBuilder.MacroAssembly)
    (runtime : Runtime) : Prop where
  outputIndex :
    runtime.registers.outputIndex = assembly.gates.length
  checks :
    runtime.checks =
      TargetEmitterSemanticSchedule.checkCoordinates assembly.checks

private theorem appendSourceResult_cursor
    (inputs totalGates gate side : Nat)
    (assembly : RawBuilder.MacroAssembly) (source : RawSource)
    (runtime : Runtime)
    (cursor : MacroCursor assembly runtime) :
    MacroCursor
      (RawBuilder.appendSourceMacro inputs totalGates gate side
        assembly source)
      (TargetEmitterSemanticSchedule.appendSourceResult
        side source runtime) := by
  unfold TargetEmitterSemanticSchedule.appendSourceResult
  refine
    { outputIndex := ?_
      checks := ?_ }
  · rw [TargetEmitterProgramSemantics.macroResult_registers,
      RawBuilder.appendSourceMacro_gates_length]
    simp only [TargetEmitterSemanticSchedule.withCaptured]
    rw [cursor.outputIndex, sourceGateCount_eq_rawBuilder]
  · rw [TargetEmitterProgramSemantics.macroResult_checks]
    cases source with
    | input index =>
        simp [TargetEmitterSemanticSchedule.withCaptured,
          TargetEmitterSemanticSchedule.sourceKind,
          TargetEmitterPlan.sourceCheckRelative,
          RawBuilder.appendSourceMacro,
          TargetEmitterSemanticSchedule.checkCoordinates,
          RawBuilder.outputGateIndex, cursor.checks,
          cursor.outputIndex, List.map_append]
    | gate index =>
        simp [TargetEmitterSemanticSchedule.withCaptured,
          TargetEmitterSemanticSchedule.sourceKind,
          TargetEmitterPlan.sourceCheckRelative,
          RawBuilder.appendSourceMacro,
          TargetEmitterSemanticSchedule.checkCoordinates,
          RawBuilder.outputGateIndex, cursor.checks,
          cursor.outputIndex, List.map_append]
    | constant value =>
        cases value <;>
          simp [TargetEmitterSemanticSchedule.withCaptured,
            TargetEmitterSemanticSchedule.sourceKind,
            TargetEmitterPlan.sourceCheckRelative,
            RawBuilder.appendSourceMacro,
            TargetEmitterSemanticSchedule.checkCoordinates,
            RawBuilder.outputGateIndex, cursor.checks,
            cursor.outputIndex, List.map_append]

private theorem appendTraceResult_cursor
    (inputs totalGates gate : Nat)
    (assembly : RawBuilder.MacroAssembly)
    (runtime : Runtime)
    (cursor : MacroCursor assembly runtime) :
    MacroCursor
      (RawBuilder.appendTraceMacro inputs totalGates gate assembly)
      (TargetEmitterProgramSemantics.macroResult runtime
        TargetEmitterPlan.tracePlan
        TargetEmitterPlan.traceCheckRelative
        TargetEmitterPlan.traceGateCount) := by
  refine
    { outputIndex := ?_
      checks := ?_ }
  · rw [TargetEmitterProgramSemantics.macroResult_registers,
      RawBuilder.appendTraceMacro_gates_length, cursor.outputIndex]
    rfl
  · rw [TargetEmitterProgramSemantics.macroResult_checks]
    simp [RawBuilder.appendTraceMacro,
      TargetEmitterSemanticSchedule.checkCoordinates,
      RawBuilder.outputGateIndex, cursor.checks,
      cursor.outputIndex, TargetEmitterPlan.traceCheckRelative,
      List.map_append]

private theorem appendGateResult_cursor
    (inputs totalGates gate : Nat)
    (assembly : RawBuilder.MacroAssembly)
    (sourceGate : RawGate) (runtime : Runtime)
    (cursor : MacroCursor assembly runtime) :
    let left :=
      RawBuilder.appendSourceMacro inputs totalGates gate 0
        assembly sourceGate.left
    let right :=
      RawBuilder.appendSourceMacro inputs totalGates gate 1
        left sourceGate.right
    let trace :=
      RawBuilder.appendTraceMacro inputs totalGates gate right
    MacroCursor trace
      (TargetEmitterSemanticSchedule.appendGateResult
        sourceGate runtime) := by
  dsimp only
  let afterLeft :=
    TargetEmitterSemanticSchedule.appendSourceResult
      0 sourceGate.left runtime
  let afterRight :=
    TargetEmitterSemanticSchedule.appendSourceResult
      1 sourceGate.right afterLeft
  let traced :=
    TargetEmitterProgramSemantics.macroResult afterRight
      TargetEmitterPlan.tracePlan
      TargetEmitterPlan.traceCheckRelative
      TargetEmitterPlan.traceGateCount
  have leftCursor :=
    appendSourceResult_cursor inputs totalGates gate 0
      assembly sourceGate.left runtime cursor
  have rightCursor :=
    appendSourceResult_cursor inputs totalGates gate 1
      (RawBuilder.appendSourceMacro inputs totalGates gate 0
        assembly sourceGate.left)
      sourceGate.right afterLeft (by simpa [afterLeft] using leftCursor)
  have traceCursor :=
    appendTraceResult_cursor inputs totalGates gate
      (RawBuilder.appendSourceMacro inputs totalGates gate 1
        (RawBuilder.appendSourceMacro inputs totalGates gate 0
          assembly sourceGate.left)
        sourceGate.right)
      afterRight (by simpa [afterRight] using rightCursor)
  refine
    { outputIndex := ?_
      checks := ?_ }
  · simpa [TargetEmitterSemanticSchedule.appendGateResult,
      afterLeft, afterRight, traced,
      TargetEmitterProgramSemantics.incrementCurrentGateResult] using
      traceCursor.outputIndex
  · simpa [TargetEmitterSemanticSchedule.appendGateResult,
      afterLeft, afterRight, traced,
      TargetEmitterProgramSemantics.incrementCurrentGateResult] using
      traceCursor.checks

private theorem appendGateListResults_cursor
    (inputs totalGates gate : Nat)
    (assembly : RawBuilder.MacroAssembly)
    (gates : List RawGate) (runtime : Runtime)
    (cursor : MacroCursor assembly runtime) :
    MacroCursor
      (RawBuilder.assembleGates inputs totalGates gate assembly gates)
      (TargetEmitterSemanticSchedule.appendGateListResults
        gates runtime) := by
  induction gates generalizing gate assembly runtime with
  | nil =>
      simpa [RawBuilder.assembleGates,
        TargetEmitterSemanticSchedule.appendGateListResults] using cursor
  | cons sourceGate rest inductionHypothesis =>
      let left :=
        RawBuilder.appendSourceMacro inputs totalGates gate 0
          assembly sourceGate.left
      let right :=
        RawBuilder.appendSourceMacro inputs totalGates gate 1
          left sourceGate.right
      let trace :=
        RawBuilder.appendTraceMacro inputs totalGates gate right
      let after :=
        TargetEmitterSemanticSchedule.appendGateResult sourceGate runtime
      have afterCursor : MacroCursor trace after := by
        simpa [left, right, trace, after] using
          (appendGateResult_cursor inputs totalGates gate assembly
            sourceGate runtime cursor)
      have tail :=
        inductionHypothesis (gate + 1) trace after afterCursor
      simpa [RawBuilder.assembleGates,
        TargetEmitterSemanticSchedule.appendGateListResults,
        left, right, trace, after] using tail

private theorem rawPrefixRuntime_cursor
    (raw : RawCircuit) :
    MacroCursor
      (TargetEmitterSemanticNormalization.rawPrefixAssembly raw)
      (TargetEmitterSemanticNormalization.rawPrefixRuntime raw) := by
  let initial :=
    TargetEmitterSemanticSchedule.normalizedMacroStartRuntime raw
  have initialCursor :
      MacroCursor RawBuilder.emptyAssembly initial := by
    refine
      { outputIndex := ?_
        checks := ?_ }
    · simp [initial,
        TargetEmitterSemanticSchedule.normalizedMacroStartRuntime,
        TargetEmitterSemanticSchedule.initialRuntime,
        TargetEmitterProgramSemantics.headerResult_registers,
        TargetEmitterLedger.ledgerRegisters,
        RawBuilder.emptyAssembly]
    · simp [initial,
        TargetEmitterSemanticSchedule.normalizedMacroStartRuntime,
        TargetEmitterSemanticSchedule.initialRuntime,
        TargetEmitterProgramSemantics.headerResult_checks,
        RawBuilder.emptyAssembly,
        TargetEmitterSemanticSchedule.checkCoordinates]
  simpa [TargetEmitterSemanticNormalization.rawPrefixAssembly,
    TargetEmitterSemanticNormalization.rawPrefixRuntime, initial] using
    (appendGateListResults_cursor raw.normalize.inputCount
      raw.normalize.gates.length 0 RawBuilder.emptyAssembly
      raw.gates initial initialCursor)

private theorem rawPrefix_controllerRange_constructive
    (raw : RawCircuit) :
    ControllerRange raw
      (TargetEmitterSemanticNormalization.rawPrefixRuntime
        raw).registers := by
  rw [rawPrefixRuntime_registers_constructive]
  refine
    { inputCount_eq := rfl
      normalizedGateCount_eq := rfl
      carrierWidth_eq := rfl
      baseline_eq := rfl
      currentGate_le := ?_
      outputIndex_le := ?_ }
  · cases raw with
    | mk inputs gates output =>
        cases output with
        | gate index =>
            simp [TargetEmitterLedger.normalizedGateCount,
              TargetEmitterLedger.normalizationAddedGates]
        | input index =>
            simp [TargetEmitterLedger.normalizedGateCount,
              TargetEmitterLedger.normalizationAddedGates]
        | constant value =>
            cases value <;>
              simp [TargetEmitterLedger.normalizedGateCount,
                TargetEmitterLedger.normalizationAddedGates]
  · rw [← TargetEmitterLedger.gateListMacroWeight_eq_rawBuilder]
    simp [TargetEmitterLedger.baselineValue]
    omega

private theorem controllerRange_outputOffset
    {raw : RawCircuit}
    {registers : TargetEmitter.UnaryRegisters}
    (range : ControllerRange raw registers)
    (offset : Nat)
    (room :
      registers.outputIndex + offset ≤
        TargetEmitterLedger.baselineValue raw + 4) :
    ControllerRange raw
      { registers with
        outputIndex := registers.outputIndex + offset } := by
  exact
    { inputCount_eq := range.inputCount_eq
      normalizedGateCount_eq := range.normalizedGateCount_eq
      carrierWidth_eq := range.carrierWidth_eq
      baseline_eq := range.baseline_eq
      currentGate_le := range.currentGate_le
      outputIndex_le := room }

private theorem rawPrefix_output_room_constructive
    (raw : RawCircuit) :
    (TargetEmitterSemanticNormalization.rawPrefixRuntime
          raw).registers.outputIndex +
          TargetEmitterLedger.normalizationMacroWeight raw.output ≤
      TargetEmitterLedger.baselineValue raw + 4 := by
  rw [rawPrefixRuntime_registers_constructive]
  simp only
  rw [← TargetEmitterLedger.gateListMacroWeight_eq_rawBuilder]
  simp [TargetEmitterLedger.baselineValue]
  omega

private theorem inputNormalizationRanges_constructive
    (inputs : Nat) (gates : List RawGate) (index : Nat) :
    let raw : RawCircuit :=
      { inputCount := inputs
        gates := gates
        output := .input index }
    TargetEmitterRuntimeProgramSafety.InputNormalizationRanges raw
      (TargetEmitterSemanticNormalization.outputCapturedRuntime raw) := by
  dsimp only
  let raw : RawCircuit :=
    { inputCount := inputs
      gates := gates
      output := .input index }
  let runtime :=
    TargetEmitterSemanticNormalization.outputCapturedRuntime raw
  have initialRange :
      ControllerRange raw runtime.registers := by
    simpa [runtime,
      TargetEmitterSemanticNormalization.outputCapturedRuntime] using
      (rawPrefix_controllerRange_constructive raw)
  have fullRoom :
      runtime.registers.outputIndex + 68 ≤
        TargetEmitterLedger.baselineValue raw + 4 := by
    simpa [runtime,
      TargetEmitterSemanticNormalization.outputCapturedRuntime, raw,
      TargetEmitterLedger.normalizationMacroWeight] using
      (rawPrefix_output_room_constructive raw)
  have room (offset : Nat) (bound : offset ≤ 68) :
      runtime.registers.outputIndex + offset ≤
        TargetEmitterLedger.baselineValue raw + 4 := by
    omega
  refine
    { initial := initialRange
      afterFirstLeft := ?_
      afterFirstRight := ?_
      afterFirstTrace := ?_
      afterSecondLeft := ?_
      afterSecondRight := ?_
      afterSecondTrace := ?_
      nextGate := ?_ }
  · simpa [TargetEmitterProgramSemantics.macroResult_registers,
      TargetEmitterPlan.sourceGateCount] using
      controllerRange_outputOffset initialRange 10
        (room 10 (by omega))
  · simpa [TargetEmitterProgramSemantics.macroResult_registers,
      TargetEmitterPlan.sourceGateCount, Nat.add_assoc] using
      controllerRange_outputOffset initialRange 12
        (room 12 (by omega))
  · simpa [TargetEmitterProgramSemantics.macroResult_registers,
      TargetEmitterPlan.sourceGateCount,
      TargetEmitterPlan.traceGateCount, Nat.add_assoc] using
      controllerRange_outputOffset initialRange 30
        (room 30 (by omega))
  · simpa [TargetEmitterProgramSemantics.macroResult_registers,
      TargetEmitterPlan.sourceGateCount,
      TargetEmitterPlan.traceGateCount, Nat.add_assoc] using
      controllerRange_outputOffset initialRange 40
        (room 40 (by omega))
  · simpa [TargetEmitterProgramSemantics.macroResult_registers,
      TargetEmitterPlan.sourceGateCount,
      TargetEmitterPlan.traceGateCount, Nat.add_assoc] using
      controllerRange_outputOffset initialRange 50
        (room 50 (by omega))
  · simpa [TargetEmitterProgramSemantics.macroResult_registers,
      TargetEmitterPlan.sourceGateCount,
      TargetEmitterPlan.traceGateCount, Nat.add_assoc] using
      controllerRange_outputOffset initialRange 68 fullRoom
  · have registersEq := rawPrefixRuntime_registers_constructive raw
    have currentEq :
        (TargetEmitterSemanticNormalization.rawPrefixRuntime
            raw).registers.currentGate = gates.length := by
      simpa [raw] using congrArg
        (fun registers : TargetEmitter.UnaryRegisters =>
          registers.currentGate)
        registersEq
    have bound :
        (TargetEmitterSemanticNormalization.rawPrefixRuntime
            raw).registers.currentGate ≤ gates.length + 1 := by
      rw [currentEq]
      omega
    simpa [runtime,
      TargetEmitterSemanticNormalization.outputCapturedRuntime,
      TargetEmitterProgramSemantics.macroResult_registers,
      TargetEmitterPlan.sourceGateCount,
      TargetEmitterPlan.traceGateCount,
      TargetEmitterLedger.normalizedGateCount,
      TargetEmitterLedger.normalizationAddedGates,
      Nat.add_assoc] using bound

private theorem constantNormalizationRanges_constructive
    (inputs : Nat) (gates : List RawGate) (value : Bool) :
    let raw : RawCircuit :=
      { inputCount := inputs
        gates := gates
        output := .constant value }
    TargetEmitterRuntimeProgramSafety.ConstantNormalizationRanges
      raw value
      (TargetEmitterSemanticNormalization.outputCapturedRuntime raw) := by
  dsimp only
  let raw : RawCircuit :=
    { inputCount := inputs
      gates := gates
      output := .constant value }
  let runtime :=
    TargetEmitterSemanticNormalization.outputCapturedRuntime raw
  have initialRange :
      ControllerRange raw runtime.registers := by
    simpa [runtime,
      TargetEmitterSemanticNormalization.outputCapturedRuntime] using
      (rawPrefix_controllerRange_constructive raw)
  cases value with
  | false =>
      have fullRoom :
          runtime.registers.outputIndex + 22 ≤
            TargetEmitterLedger.baselineValue raw + 4 := by
        simpa [runtime,
          TargetEmitterSemanticNormalization.outputCapturedRuntime, raw,
          TargetEmitterLedger.normalizationMacroWeight] using
          (rawPrefix_output_room_constructive raw)
      refine
        { initial := initialRange
          afterLeft := ?_
          afterRight := ?_ }
      · simpa [TargetEmitterProgramSemantics.macroResult_registers,
          TargetEmitterPlan.constantNormalizationKind,
          TargetEmitterPlan.sourceGateCount] using
          controllerRange_outputOffset initialRange 2 (by omega)
      · simpa [TargetEmitterProgramSemantics.macroResult_registers,
          TargetEmitterPlan.constantNormalizationKind,
          TargetEmitterPlan.sourceGateCount, Nat.add_assoc] using
          controllerRange_outputOffset initialRange 4 (by omega)
  | true =>
      have fullRoom :
          runtime.registers.outputIndex + 24 ≤
            TargetEmitterLedger.baselineValue raw + 4 := by
        simpa [runtime,
          TargetEmitterSemanticNormalization.outputCapturedRuntime, raw,
          TargetEmitterLedger.normalizationMacroWeight] using
          (rawPrefix_output_room_constructive raw)
      refine
        { initial := initialRange
          afterLeft := ?_
          afterRight := ?_ }
      · simpa [TargetEmitterProgramSemantics.macroResult_registers,
          TargetEmitterPlan.constantNormalizationKind,
          TargetEmitterPlan.sourceGateCount] using
          controllerRange_outputOffset initialRange 3 (by omega)
      · simpa [TargetEmitterProgramSemantics.macroResult_registers,
          TargetEmitterPlan.constantNormalizationKind,
          TargetEmitterPlan.sourceGateCount, Nat.add_assoc] using
          controllerRange_outputOffset initialRange 6 (by omega)

private theorem unaryRegisters_ext
    {left right : TargetEmitter.UnaryRegisters}
    (inputCount : left.inputCount = right.inputCount)
    (normalizedGateCount :
      left.normalizedGateCount = right.normalizedGateCount)
    (carrierWidth : left.carrierWidth = right.carrierWidth)
    (baseline : left.baseline = right.baseline)
    (currentGate : left.currentGate = right.currentGate)
    (outputIndex : left.outputIndex = right.outputIndex) :
    left = right := by
  cases left with
  | mk leftInput leftNormalized leftWidth leftBaseline
      leftCurrent leftOutput =>
      cases right with
      | mk rightInput rightNormalized rightWidth rightBaseline
          rightCurrent rightOutput =>
          change leftInput = rightInput at inputCount
          change leftNormalized = rightNormalized at normalizedGateCount
          change leftWidth = rightWidth at carrierWidth
          change leftBaseline = rightBaseline at baseline
          change leftCurrent = rightCurrent at currentGate
          change leftOutput = rightOutput at outputIndex
          subst rightInput
          subst rightNormalized
          subst rightWidth
          subst rightBaseline
          subst rightCurrent
          subst rightOutput
          rfl

private theorem normalizationRuntime_registers_constructive
    (raw : RawCircuit) :
    (TargetEmitterSemanticNormalization.normalizationRuntime
          raw).registers =
      { TargetEmitterLedger.ledgerRegisters raw with
        currentGate :=
          TargetEmitterSemanticNormalization.normalizationCurrentGate raw
        outputIndex :=
          (RawBuilder.macroAssembly raw.normalize).gates.length } := by
  have macroLength :=
    TargetEmitterSemanticNormalization.normalizedMacroAssembly_gates_length
      raw
  cases raw with
  | mk inputs gates output =>
      cases output with
      | gate index =>
          rw [TargetEmitterSemanticNormalization.normalizationRuntime]
          apply unaryRegisters_ext <;>
            simp [
              TargetEmitterSemanticNormalization.outputCapturedRuntime,
              TargetEmitterProgramSemantics.resetScratchResult,
              TargetEmitterSemanticNormalization.normalizationCurrentGate,
              rawPrefixRuntime_registers_constructive,
              TargetEmitterSemanticNormalization.rawPrefixAssembly_gates_length,
              TargetEmitterLedger.normalizationMacroWeight,
              RawCircuit.normalize] at macroLength ⊢ <;>
            omega
      | input index =>
          rw [TargetEmitterSemanticNormalization.normalizationRuntime]
          apply unaryRegisters_ext
          all_goals
            simp [
              TargetEmitterSemanticNormalization.outputCapturedRuntime,
              TargetEmitterProgramSemantics.inputNormalizationResult,
              TargetEmitterProgramSemantics.macroResult_registers,
              TargetEmitterProgramSemantics.incrementCurrentGateResult,
              TargetEmitterPlan.sourceGateCount,
              TargetEmitterPlan.traceGateCount,
              TargetEmitterSemanticNormalization.normalizationCurrentGate,
              rawPrefixRuntime_registers_constructive,
              TargetEmitterSemanticNormalization.rawPrefixAssembly_gates_length,
              TargetEmitterLedger.normalizationMacroWeight,
              RawCircuit.normalize, Nat.add_assoc] at macroLength ⊢ <;>
            omega
      | constant value =>
          cases value <;>
            rw [TargetEmitterSemanticNormalization.normalizationRuntime] <;>
            apply unaryRegisters_ext
          all_goals
            simp [
              TargetEmitterSemanticNormalization.outputCapturedRuntime,
              TargetEmitterProgramSemantics.constantNormalizationResult,
              TargetEmitterProgramSemantics.macroResult_registers,
              TargetEmitterPlan.constantNormalizationKind,
              TargetEmitterPlan.sourceGateCount,
              TargetEmitterPlan.traceGateCount,
              TargetEmitterSemanticNormalization.normalizationCurrentGate,
              rawPrefixRuntime_registers_constructive,
              TargetEmitterSemanticNormalization.rawPrefixAssembly_gates_length,
              TargetEmitterLedger.normalizationMacroWeight,
              RawCircuit.normalize, Nat.add_assoc] at macroLength ⊢ <;>
            omega

private theorem normalizationRuntime_checks_constructive
    (raw : RawCircuit) :
    (TargetEmitterSemanticNormalization.normalizationRuntime raw).checks =
      TargetEmitterSemanticSchedule.checkCoordinates
        (RawBuilder.macroAssembly raw.normalize).checks := by
  have cursor := rawPrefixRuntime_cursor raw
  have prefixChecks := cursor.checks
  have prefixOutput := cursor.outputIndex
  rw [←
    TargetEmitterSemanticNormalization.normalizationAssembly_eq_macroAssembly]
  cases raw with
  | mk inputs gates output =>
      cases output with
      | gate index =>
          simpa [TargetEmitterSemanticNormalization.normalizationRuntime,
            TargetEmitterSemanticNormalization.normalizationAssembly,
            TargetEmitterSemanticNormalization.normalizationSuffix,
            TargetEmitterSemanticNormalization.outputCapturedRuntime,
            TargetEmitterProgramSemantics.resetScratchResult,
            RawBuilder.assembleGates] using prefixChecks
      | input index =>
          rw [TargetEmitterSemanticNormalization.normalizationRuntime,
            TargetEmitterProgramSemantics.inputNormalizationResult_checks]
          simp [TargetEmitterSemanticNormalization.outputCapturedRuntime,
            TargetEmitterSemanticNormalization.normalizationAssembly,
            TargetEmitterSemanticNormalization.normalizationSuffix,
            RawBuilder.assembleGates,
            RawBuilder.appendSourceMacro,
            RawBuilder.appendTraceMacro,
            RawBuilder.appendTemplate,
            RawBuilder.equalityTemplate_length,
            RawBuilder.constantOneTemplate_length,
            RawBuilder.traceTemplate_length,
            TargetEmitterSemanticSchedule.checkCoordinates,
            RawBuilder.outputGateIndex,
            prefixChecks, prefixOutput, List.append_assoc]
      | constant value =>
          cases value with
          | false =>
              rw [TargetEmitterSemanticNormalization.normalizationRuntime,
                TargetEmitterProgramSemantics.constantNormalizationResult_false_checks]
              simp [
                TargetEmitterSemanticNormalization.outputCapturedRuntime,
                TargetEmitterSemanticNormalization.normalizationAssembly,
                TargetEmitterSemanticNormalization.normalizationSuffix,
                RawBuilder.assembleGates,
                RawBuilder.appendSourceMacro,
                RawBuilder.appendTraceMacro,
                RawBuilder.appendTemplate,
                RawBuilder.constantOneTemplate_length,
                TargetEmitterSemanticSchedule.checkCoordinates,
                RawBuilder.outputGateIndex,
                prefixChecks, prefixOutput, List.append_assoc]
          | true =>
              rw [TargetEmitterSemanticNormalization.normalizationRuntime,
                TargetEmitterProgramSemantics.constantNormalizationResult_true_checks]
              simp [
                TargetEmitterSemanticNormalization.outputCapturedRuntime,
                TargetEmitterSemanticNormalization.normalizationAssembly,
                TargetEmitterSemanticNormalization.normalizationSuffix,
                RawBuilder.assembleGates,
                RawBuilder.appendSourceMacro,
                RawBuilder.appendTraceMacro,
                RawBuilder.appendTemplate,
                RawBuilder.constantZeroTemplate_length,
                TargetEmitterSemanticSchedule.checkCoordinates,
                RawBuilder.outputGateIndex,
                prefixChecks, prefixOutput, List.append_assoc]

private theorem macroResult_scratch_irrel
    (runtime : Runtime) (scratch : Nat)
    (gates : List TargetEmitterPlan.PlannedGate)
    (relative count : Nat) :
    TargetEmitterProgramSemantics.macroResult
        { runtime with scratch := scratch } gates relative count =
      TargetEmitterProgramSemantics.macroResult
        runtime gates relative count := by
  apply runtime_ext
  · exact
      (TargetEmitterControllerGateTrace.macroResult_captured
        _ gates relative count).trans
        (TargetEmitterControllerGateTrace.macroResult_captured
          runtime gates relative count).symm
  · rfl
  · simp only [TargetEmitterProgramSemantics.macroResult_registers]
  · simp only [TargetEmitterProgramSemantics.macroResult_checks]
  · simp only [TargetEmitterProgramSemantics.macroResult_targetTokens,
      TargetEmitterProgramSemantics.plannedGateTokens,
      TargetEmitterProgramSemantics.evaluatedGates]

private theorem appendSourceResult_scratch_irrel
    (runtime : Runtime) (scratch side : Nat)
    (source : RawSource) :
    TargetEmitterSemanticSchedule.appendSourceResult side source
        { runtime with scratch := scratch } =
      TargetEmitterSemanticSchedule.appendSourceResult side source
        runtime := by
  unfold TargetEmitterSemanticSchedule.appendSourceResult
  change
    TargetEmitterProgramSemantics.macroResult
        { TargetEmitterSemanticSchedule.withCaptured source runtime with
          scratch := scratch }
        _ _ _ =
      TargetEmitterProgramSemantics.macroResult
        (TargetEmitterSemanticSchedule.withCaptured source runtime)
        _ _ _
  exact macroResult_scratch_irrel _ _ _ _ _

private theorem appendGateResult_scratch_irrel
    (runtime : Runtime) (scratch : Nat) (gate : RawGate) :
    TargetEmitterSemanticSchedule.appendGateResult gate
        { runtime with scratch := scratch } =
      TargetEmitterSemanticSchedule.appendGateResult gate runtime := by
  unfold TargetEmitterSemanticSchedule.appendGateResult
  rw [appendSourceResult_scratch_irrel runtime scratch 0 gate.left]

private theorem gateListRuntime_eq_rawPrefixRuntime_of_nonempty
    (raw : RawCircuit) (nonempty : raw.gates ≠ []) :
    TargetEmitterControllerGateListTrace.gateListRuntime raw =
      TargetEmitterSemanticNormalization.rawPrefixRuntime raw := by
  cases raw with
  | mk inputs gates output =>
      cases gates with
      | nil =>
          exact False.elim (nonempty rfl)
      | cons gate rest =>
          simp only [
            TargetEmitterControllerGateListTrace.gateListRuntime,
            TargetEmitterSemanticNormalization.rawPrefixRuntime,
            TargetEmitterSemanticSchedule.appendGateListResults]
          change
            TargetEmitterSemanticSchedule.appendGateListResults rest
                (TargetEmitterSemanticSchedule.appendGateResult gate
                  (TargetEmitterProgramSemantics.headerResult
                    (TargetEmitterControllerHeaderTrace.initialRuntime
                      { inputCount := inputs
                        gates := gate :: rest
                        output := output }))) =
              TargetEmitterSemanticSchedule.appendGateListResults rest
                (TargetEmitterSemanticSchedule.appendGateResult gate
                  { TargetEmitterProgramSemantics.headerResult
                      (TargetEmitterSemanticSchedule.initialRuntime
                        { inputCount := inputs
                          gates := gate :: rest
                          output := output }) with
                    scratch := 0 })
          congr 1
          rw [show
            TargetEmitterControllerHeaderTrace.initialRuntime
                { inputCount := inputs
                  gates := gate :: rest
                  output := output } =
              TargetEmitterSemanticSchedule.initialRuntime
                { inputCount := inputs
                  gates := gate :: rest
                  output := output } by rfl]
          exact (appendGateResult_scratch_irrel
            (TargetEmitterProgramSemantics.headerResult
              (TargetEmitterSemanticSchedule.initialRuntime
                { inputCount := inputs
                  gates := gate :: rest
                  output := output }))
            0 gate).symm

/-! ### Output capture with either canonical scratch shape -/

private theorem outputInputNormalization_path
    {raw : RawCircuit}
    (runtime : Runtime) (index : Nat)
    (head : WorkSymbol) (prefixTail after : List WorkSymbol)
    (outputEq : raw.output = .input index)
    (captureReserve :
      runtime.scratch +
          TargetEmitterControllerSourceTrace.capturedValue .input index +
          1 ≤
        TargetEmitterLedger.slotCapacity raw)
    (ranges :
      TargetEmitterRuntimeProgramSafety.InputNormalizationRanges raw
        (TargetEmitterControllerGateTrace.capturedRuntime
          runtime .input index))
    (originalPacked :
      ∀ symbol,
        symbol ∈
            (head :: prefixTail) ++
              SourceParser.sourceCells (.input index) ++ after →
          TargetEmitter.PackedSymbol symbol)
    (initialTape : WorkTape)
    (represents :
      FocusTapeRepresents outputFirstRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        (head :: prefixTail)
        (SourceParser.sourceCells (.input index) ++ after)
        runtime.targetTokens initialTape) :
    let marked :=
      (head :: prefixTail) ++
        TargetEmitterControllerSourceTrace.captureMarkedSourceCells
          .input index ++ after
    let captured :=
      TargetEmitterControllerGateTrace.capturedRuntime
        runtime .input index
    ∃ steps finalTape,
      AcceptPath graph (.node outputFirstRef)
          (.node normalizedInitialPopRef) steps
          initialTape finalTape ∧
      TapeRepresents normalizedInitialPopRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterProgramSemantics.inputNormalizationResult
          captured).scratch
        (TargetEmitterProgramSemantics.inputNormalizationResult
          captured).registers
        (TargetEmitterProgramSemantics.inputNormalizationResult
          captured).checks
        marked
        (TargetEmitterProgramSemantics.inputNormalizationResult
          captured).targetTokens finalTape := by
  let marked :=
    (head :: prefixTail) ++
      TargetEmitterControllerSourceTrace.captureMarkedSourceCells
        .input index ++ after
  let captured :=
    TargetEmitterControllerGateTrace.capturedRuntime
      runtime .input index
  have outputMember :
      TargetEmitterCapacity.CircuitSource raw (.input index) := by
    rw [← outputEq]
    exact .output
  have capturedBound :
      index + 1 ≤
        (SourceParser.circuitCells raw).length :=
    TargetEmitterCapacity.circuitInputIndex_succ_le_cells
      outputMember
  have beforePacked :
      ∀ symbol, symbol ∈ (head :: prefixTail) →
        TargetEmitter.PackedSymbol symbol := by
    intro symbol member
    apply originalPacked
    simp only [List.mem_append, List.mem_cons]
    have member' : symbol = head ∨ symbol ∈ prefixTail := by
      simpa only [List.mem_cons] using member
    exact Or.inl (Or.inl member')
  have capturedCapacity :
      index + 1 ≤ TargetEmitterLedger.slotCapacity raw := by
    simpa [TargetEmitterCapacity.sourceCaptureValue] using
      (TargetEmitterCapacity.focusedSourceCaptureReserve
        outputMember)
  let workspace : MarkedWorkspace marked :=
    TargetEmitterControllerGateTrace.markedWorkspace
      .input index head prefixTail after originalPacked
  have capturedReady :
      TargetEmitterRuntimeProgramSafety.CapturedReady
        raw marked captured.captured := by
    have ready :=
      TargetEmitterControllerGateTrace.sourceReady
        raw .input index (head :: prefixTail) after
        beforePacked capturedCapacity
    cases ready with
    | input ready =>
        simpa [marked, captured,
          TargetEmitterControllerGateTrace.capturedRuntime,
          TargetEmitterControllerSourceTrace.capturedValue] using ready
  rcases
      TargetEmitterControllerGateTrace.outputClassifyCapture_path
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        (head :: prefixTail) after (.input index)
        runtime.targetTokens initialTape captureReserve beforePacked
        represents with
    ⟨capturedTape, capturePath, capturedRepresents⟩
  have capturedLogical :
      TargetEmitterControllerGateTrace.TapeRepresents
        inputNormalizationRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        captured.scratch captured.registers captured.checks
        marked captured.targetTokens capturedTape := by
    simpa [marked, captured,
      TargetEmitterControllerGateTrace.capturedRuntime,
      TargetEmitterControllerGateTrace.sourceValue,
      TargetEmitterControllerTrace.sourceKind,
      TargetEmitterControllerSourceTrace.capturedValue,
      TargetEmitterController.outputCaptureContinuation] using
        capturedRepresents
  have capturedScratchBound :
      captured.scratch <
        TargetEmitterLedger.slotCapacity raw := by
    simp only [captured,
      TargetEmitterControllerGateTrace.capturedRuntime,
      TargetEmitterControllerSourceTrace.capturedValue]
    have reserve := captureReserve
    exact Nat.lt_of_succ_le reserve
  have capturedIndexBound :
      captured.captured + 1 ≤
        (SourceParser.circuitCells raw).length := by
    simpa [captured,
      TargetEmitterControllerGateTrace.capturedRuntime,
      TargetEmitterControllerSourceTrace.capturedValue] using
        capturedBound
  rcases
      TargetEmitterControllerNormalizationTrace.inputNormalizationBlock_path
        workspace captured ranges capturedIndexBound
        capturedScratchBound capturedReady capturedTape
        capturedLogical with
    ⟨blockSteps, finalTape, blockPath, finalRepresents⟩
  refine
    ⟨TargetEmitterControllerGateTrace.sourceCapturePhaseSteps
        (head :: prefixTail) (.input index) runtime.scratch +
      blockSteps,
      finalTape, ?_, finalRepresents⟩
  exact
    AcceptPath.trans graph (.node outputFirstRef)
      (.node inputNormalizationRef)
      (.node normalizedInitialPopRef)
      (TargetEmitterControllerGateTrace.sourceCapturePhaseSteps
        (head :: prefixTail) (.input index) runtime.scratch)
      blockSteps initialTape capturedTape finalTape
      capturePath blockPath

private theorem outputConstantNormalization_path
    {raw : RawCircuit}
    (runtime : Runtime) (value : Bool)
    (head : WorkSymbol) (prefixTail after : List WorkSymbol)
    (outputEq : raw.output = .constant value)
    (captureReserve :
      let kind :=
        if value then TargetEmitterPlan.SourceKind.constantTrue
        else TargetEmitterPlan.SourceKind.constantFalse
      runtime.scratch +
          TargetEmitterControllerSourceTrace.capturedValue kind 0 + 1 ≤
        TargetEmitterLedger.slotCapacity raw)
    (ranges :
      TargetEmitterRuntimeProgramSafety.ConstantNormalizationRanges
        raw value
        (TargetEmitterControllerGateTrace.capturedRuntime runtime
          (if value then .constantTrue else .constantFalse) 0))
    (originalPacked :
      ∀ symbol,
        symbol ∈
            (head :: prefixTail) ++
              SourceParser.sourceCells (.constant value) ++ after →
          TargetEmitter.PackedSymbol symbol)
    (initialTape : WorkTape)
    (represents :
      FocusTapeRepresents outputFirstRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        (head :: prefixTail)
        (SourceParser.sourceCells (.constant value) ++ after)
        runtime.targetTokens initialTape) :
    let kind :=
      if value then TargetEmitterPlan.SourceKind.constantTrue
      else TargetEmitterPlan.SourceKind.constantFalse
    let marked :=
      (head :: prefixTail) ++
        TargetEmitterControllerSourceTrace.captureMarkedSourceCells
          kind 0 ++ after
    let captured :=
      TargetEmitterControllerGateTrace.capturedRuntime runtime kind 0
    ∃ steps finalTape,
      AcceptPath graph (.node outputFirstRef)
          (.node normalizedInitialPopRef) steps
          initialTape finalTape ∧
      TapeRepresents normalizedInitialPopRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterProgramSemantics.constantNormalizationResult
          value captured).scratch
        (TargetEmitterProgramSemantics.constantNormalizationResult
          value captured).registers
        (TargetEmitterProgramSemantics.constantNormalizationResult
          value captured).checks
        marked
        (TargetEmitterProgramSemantics.constantNormalizationResult
          value captured).targetTokens finalTape := by
  let kind :=
    if value then TargetEmitterPlan.SourceKind.constantTrue
    else TargetEmitterPlan.SourceKind.constantFalse
  let marked :=
    (head :: prefixTail) ++
      TargetEmitterControllerSourceTrace.captureMarkedSourceCells
        kind 0 ++ after
  let captured :=
    TargetEmitterControllerGateTrace.capturedRuntime runtime kind 0
  have outputMember :
      TargetEmitterCapacity.CircuitSource raw (.constant value) := by
    rw [← outputEq]
    exact .output
  have beforePacked :
      ∀ symbol, symbol ∈ (head :: prefixTail) →
        TargetEmitter.PackedSymbol symbol := by
    intro symbol member
    apply originalPacked
    simp only [List.mem_append, List.mem_cons]
    have member' : symbol = head ∨ symbol ∈ prefixTail := by
      simpa only [List.mem_cons] using member
    exact Or.inl (Or.inl member')
  have originalPackedByKind :
      ∀ symbol,
        symbol ∈
            (head :: prefixTail) ++
              TargetEmitterControllerSourceTrace.captureSourceCells
                (TargetEmitterControllerTrace.sourceKind
                  (.constant value))
                (TargetEmitterControllerGateTrace.sourceValue
                  (.constant value)) ++ after →
          TargetEmitter.PackedSymbol symbol := by
    rw [←
      TargetEmitterControllerGateTrace.sourceCells_eq_captureSourceCells
        (.constant value)]
    exact originalPacked
  let workspace : MarkedWorkspace marked :=
    TargetEmitterControllerGateTrace.markedWorkspace
      kind 0 head prefixTail after
      (by
        cases value <;>
          simpa [kind,
            TargetEmitterControllerTrace.sourceKind,
            TargetEmitterControllerGateTrace.sourceValue] using
              originalPackedByKind)
  rcases
      TargetEmitterControllerGateTrace.outputClassifyCapture_path
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        (head :: prefixTail) after (.constant value)
        runtime.targetTokens initialTape
        (by
          cases value <;>
            simpa [kind,
              TargetEmitterControllerTrace.sourceKind,
              TargetEmitterControllerGateTrace.sourceValue] using
                captureReserve)
        beforePacked represents with
    ⟨capturedTape, capturePath, capturedRepresents⟩
  have capturedLogical :
      TargetEmitterControllerGateTrace.TapeRepresents
        (if value then constantTrueNormalizationRef
          else constantFalseNormalizationRef).startState
        (TargetEmitterLedger.slotCapacity raw)
        captured.scratch captured.registers captured.checks
        marked captured.targetTokens capturedTape := by
    cases value <;>
      simpa [kind, marked, captured,
        TargetEmitterControllerGateTrace.capturedRuntime,
        TargetEmitterControllerGateTrace.sourceValue,
        TargetEmitterControllerTrace.sourceKind,
        TargetEmitterControllerSourceTrace.capturedValue,
        TargetEmitterController.outputCaptureContinuation] using
          capturedRepresents
  have capturedScratchBound :
      captured.scratch <
        TargetEmitterLedger.slotCapacity raw := by
    have reserve := captureReserve
    exact Nat.lt_of_succ_le
      (by
        simpa [captured, kind,
          TargetEmitterControllerGateTrace.capturedRuntime] using
            reserve)
  have capturedIndexBound :
      captured.captured + 1 ≤
        (SourceParser.circuitCells raw).length := by
    have cells :=
      TargetEmitterCapacity.fourteen_le_circuitCells_length raw
    cases value <;>
      simp [captured, kind,
        TargetEmitterControllerGateTrace.capturedRuntime,
        TargetEmitterControllerSourceTrace.capturedValue]
    all_goals omega
  rcases
      TargetEmitterControllerNormalizationTrace.constantNormalizationBlock_path
        value workspace captured ranges capturedIndexBound
        capturedScratchBound capturedTape capturedLogical with
    ⟨blockSteps, finalTape, blockPath, finalRepresents⟩
  refine
    ⟨TargetEmitterControllerGateTrace.sourceCapturePhaseSteps
        (head :: prefixTail) (.constant value) runtime.scratch +
      blockSteps,
      finalTape, ?_, finalRepresents⟩
  have capturePath' :
      AcceptPath graph (.node outputFirstRef)
        (.node
          (if value then constantTrueNormalizationRef
            else constantFalseNormalizationRef))
        (TargetEmitterControllerGateTrace.sourceCapturePhaseSteps
          (head :: prefixTail) (.constant value) runtime.scratch)
        initialTape capturedTape := by
    cases value <;>
      simpa [TargetEmitterControllerTrace.sourceKind,
        TargetEmitterController.outputCaptureContinuation] using
          capturePath
  exact
    AcceptPath.trans graph (.node outputFirstRef)
      (.node
        (if value then constantTrueNormalizationRef
          else constantFalseNormalizationRef))
      (.node normalizedInitialPopRef)
      (TargetEmitterControllerGateTrace.sourceCapturePhaseSteps
        (head :: prefixTail) (.constant value) runtime.scratch)
      blockSteps initialTape capturedTape finalTape
      capturePath' blockPath

private theorem outputGateNormalization_path
    {raw : RawCircuit}
    (runtime : Runtime) (index : Nat)
    (head : WorkSymbol) (prefixTail after : List WorkSymbol)
    (outputEq : raw.output = .gate index)
    (captureReserve :
      runtime.scratch +
          TargetEmitterControllerSourceTrace.capturedValue .gate index +
          1 ≤
        TargetEmitterLedger.slotCapacity raw)
    (originalPacked :
      ∀ symbol,
        symbol ∈
            (head :: prefixTail) ++
              SourceParser.sourceCells (.gate index) ++ after →
          TargetEmitter.PackedSymbol symbol)
    (initialTape : WorkTape)
    (represents :
      FocusTapeRepresents outputFirstRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        (head :: prefixTail)
        (SourceParser.sourceCells (.gate index) ++ after)
        runtime.targetTokens initialTape) :
    let marked :=
      (head :: prefixTail) ++
        TargetEmitterControllerSourceTrace.captureMarkedSourceCells
          .gate index ++ after
    let captured :=
      TargetEmitterControllerGateTrace.capturedRuntime
        runtime .gate index
    ∃ steps finalTape,
      AcceptPath graph (.node outputFirstRef)
          (.node rawInitialPopRef) steps
          initialTape finalTape ∧
      TapeRepresents rawInitialPopRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterProgramSemantics.resetScratchResult
          captured).scratch
        (TargetEmitterProgramSemantics.resetScratchResult
          captured).registers
        (TargetEmitterProgramSemantics.resetScratchResult
          captured).checks
        marked
        (TargetEmitterProgramSemantics.resetScratchResult
          captured).targetTokens finalTape := by
  let marked :=
    (head :: prefixTail) ++
      TargetEmitterControllerSourceTrace.captureMarkedSourceCells
        .gate index ++ after
  let captured :=
    TargetEmitterControllerGateTrace.capturedRuntime
      runtime .gate index
  have outputMember :
      TargetEmitterCapacity.CircuitSource raw (.gate index) := by
    rw [← outputEq]
    exact .output
  have beforePacked :
      ∀ symbol, symbol ∈ (head :: prefixTail) →
        TargetEmitter.PackedSymbol symbol := by
    intro symbol member
    apply originalPacked
    simp only [List.mem_append, List.mem_cons]
    have member' : symbol = head ∨ symbol ∈ prefixTail := by
      simpa only [List.mem_cons] using member
    exact Or.inl (Or.inl member')
  let workspace : MarkedWorkspace marked :=
    TargetEmitterControllerGateTrace.markedWorkspace
      .gate index head prefixTail after originalPacked
  rcases
      TargetEmitterControllerGateTrace.outputClassifyCapture_path
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        (head :: prefixTail) after (.gate index)
        runtime.targetTokens initialTape captureReserve beforePacked
        represents with
    ⟨capturedTape, capturePath, capturedRepresents⟩
  have capturedLogical :
      TargetEmitterControllerGateTrace.TapeRepresents
        outputGateResetRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        captured.scratch captured.registers captured.checks
        marked captured.targetTokens capturedTape := by
    simpa [marked, captured,
      TargetEmitterControllerGateTrace.capturedRuntime,
      TargetEmitterControllerGateTrace.sourceValue,
      TargetEmitterControllerTrace.sourceKind,
      TargetEmitterControllerSourceTrace.capturedValue,
      TargetEmitterController.outputCaptureContinuation] using
        capturedRepresents
  have capturedScratchBound :
      captured.scratch <
        TargetEmitterLedger.slotCapacity raw := by
    have reserve := captureReserve
    simp only [
      TargetEmitterControllerSourceTrace.capturedValue] at reserve
    simpa [captured,
      TargetEmitterControllerGateTrace.capturedRuntime,
      TargetEmitterControllerSourceTrace.capturedValue] using
        (Nat.lt_of_succ_le reserve)
  rcases
      TargetEmitterControllerNormalizationTrace.outputGateResetBlock_path
        workspace.context captured capturedScratchBound
        capturedTape capturedLogical with
    ⟨blockSteps, finalTape, blockPath, finalRepresents⟩
  refine
    ⟨TargetEmitterControllerGateTrace.sourceCapturePhaseSteps
        (head :: prefixTail) (.gate index) runtime.scratch +
      blockSteps,
      finalTape, ?_, finalRepresents⟩
  exact
    AcceptPath.trans graph (.node outputFirstRef)
      (.node outputGateResetRef) (.node rawInitialPopRef)
      (TargetEmitterControllerGateTrace.sourceCapturePhaseSteps
        (head :: prefixTail) (.gate index) runtime.scratch)
      blockSteps initialTape capturedTape finalTape
      (by simpa [TargetEmitterControllerTrace.sourceKind,
        TargetEmitterController.outputCaptureContinuation] using
          capturePath)
      blockPath

private theorem inputNormalizationResult_scratch_irrel
    (runtime : Runtime) (scratch : Nat) :
    TargetEmitterProgramSemantics.inputNormalizationResult
        { runtime with scratch := scratch } =
      TargetEmitterProgramSemantics.inputNormalizationResult runtime := by
  unfold TargetEmitterProgramSemantics.inputNormalizationResult
  rw [macroResult_scratch_irrel]

private theorem constantNormalizationResult_scratch_irrel
    (value : Bool) (runtime : Runtime) (scratch : Nat) :
    TargetEmitterProgramSemantics.constantNormalizationResult value
        { runtime with scratch := scratch } =
      TargetEmitterProgramSemantics.constantNormalizationResult
        value runtime := by
  unfold TargetEmitterProgramSemantics.constantNormalizationResult
  dsimp only
  rw [macroResult_scratch_irrel runtime scratch]

def physicalCapturedRuntime (raw : RawCircuit) : Runtime :=
  TargetEmitterControllerGateTrace.capturedRuntime
    (TargetEmitterControllerGateListTrace.gateListRuntime raw)
    (TargetEmitterControllerTrace.sourceKind raw.output)
    (TargetEmitterControllerGateTrace.sourceValue raw.output)

def physicalNormalizationRuntime (raw : RawCircuit) : Runtime :=
  match raw.output with
  | .gate _ =>
      TargetEmitterProgramSemantics.resetScratchResult
        (physicalCapturedRuntime raw)
  | .input _ =>
      TargetEmitterProgramSemantics.inputNormalizationResult
        (physicalCapturedRuntime raw)
  | .constant value =>
      TargetEmitterProgramSemantics.constantNormalizationResult
        value (physicalCapturedRuntime raw)

private theorem gateListRuntime_registers_eq_rawPrefixRuntime
    (raw : RawCircuit) :
    (TargetEmitterControllerGateListTrace.gateListRuntime raw).registers =
      (TargetEmitterSemanticNormalization.rawPrefixRuntime raw).registers := by
  cases raw with
  | mk inputs gates output =>
      cases gates with
      | nil =>
          rfl
      | cons gate rest =>
          exact congrArg (fun runtime : Runtime => runtime.registers)
            (gateListRuntime_eq_rawPrefixRuntime_of_nonempty
              { inputCount := inputs
                gates := gate :: rest
                output := output } (by simp))

private theorem gateListRuntime_core_eq_rawPrefixRuntime
    (raw : RawCircuit) :
    (TargetEmitterControllerGateListTrace.gateListRuntime raw).captured =
        (TargetEmitterSemanticNormalization.rawPrefixRuntime raw).captured ∧
      (TargetEmitterControllerGateListTrace.gateListRuntime raw).registers =
        (TargetEmitterSemanticNormalization.rawPrefixRuntime raw).registers ∧
      (TargetEmitterControllerGateListTrace.gateListRuntime raw).checks =
        (TargetEmitterSemanticNormalization.rawPrefixRuntime raw).checks ∧
      (TargetEmitterControllerGateListTrace.gateListRuntime raw).targetTokens =
        (TargetEmitterSemanticNormalization.rawPrefixRuntime raw).targetTokens := by
  cases raw with
  | mk inputs gates output =>
      cases gates with
      | nil =>
          exact ⟨rfl, rfl, rfl, rfl⟩
      | cons gate rest =>
          have equality :=
            gateListRuntime_eq_rawPrefixRuntime_of_nonempty
              { inputCount := inputs
                gates := gate :: rest
                output := output } (by simp)
          rw [equality]
          exact ⟨rfl, rfl, rfl, rfl⟩

private theorem physicalCapturedRuntime_registers
    (raw : RawCircuit) :
    (physicalCapturedRuntime raw).registers =
      (TargetEmitterSemanticNormalization.outputCapturedRuntime
        raw).registers := by
  simpa [physicalCapturedRuntime,
    TargetEmitterControllerGateTrace.capturedRuntime,
    TargetEmitterSemanticNormalization.outputCapturedRuntime] using
    gateListRuntime_registers_eq_rawPrefixRuntime raw

private theorem physicalCapturedRuntime_scratch_shape
    (raw : RawCircuit) :
    physicalCapturedRuntime raw =
      { TargetEmitterSemanticNormalization.outputCapturedRuntime raw with
        scratch := (physicalCapturedRuntime raw).scratch } := by
  rcases gateListRuntime_core_eq_rawPrefixRuntime raw with
    ⟨captured, registers, checks, targetTokens⟩
  apply runtime_ext
  · unfold physicalCapturedRuntime
      TargetEmitterSemanticNormalization.outputCapturedRuntime
      TargetEmitterControllerGateTrace.capturedRuntime
    cases raw.output with
    | input index => rfl
    | gate index => rfl
    | constant value => cases value <;> rfl
  · rfl
  · simpa [physicalCapturedRuntime,
      TargetEmitterSemanticNormalization.outputCapturedRuntime,
      TargetEmitterControllerGateTrace.capturedRuntime] using registers
  · simpa [physicalCapturedRuntime,
      TargetEmitterSemanticNormalization.outputCapturedRuntime,
      TargetEmitterControllerGateTrace.capturedRuntime] using checks
  · simpa [physicalCapturedRuntime,
      TargetEmitterSemanticNormalization.outputCapturedRuntime,
      TargetEmitterControllerGateTrace.capturedRuntime] using targetTokens

private theorem physicalNormalizationRuntime_eq
    (raw : RawCircuit) :
    physicalNormalizationRuntime raw =
      TargetEmitterSemanticNormalization.normalizationRuntime raw := by
  cases raw with
  | mk inputs gates output =>
      cases gates with
      | nil =>
          cases output with
          | gate index =>
              rfl
          | input index =>
              change
                TargetEmitterProgramSemantics.inputNormalizationResult
                    { TargetEmitterSemanticNormalization.outputCapturedRuntime
                        { inputCount := inputs
                          gates := []
                          output := .input index } with
                      scratch :=
                        TargetEmitterLedger.baselineValue
                          { inputCount := inputs
                            gates := []
                            output := .input index } +
                          1 + index } =
                  TargetEmitterProgramSemantics.inputNormalizationResult
                    (TargetEmitterSemanticNormalization.outputCapturedRuntime
                      { inputCount := inputs
                        gates := []
                        output := .input index })
              exact inputNormalizationResult_scratch_irrel _ _
          | constant value =>
              cases value with
              | false =>
                  change
                    TargetEmitterProgramSemantics.constantNormalizationResult
                        false
                        { TargetEmitterSemanticNormalization.outputCapturedRuntime
                            { inputCount := inputs
                              gates := []
                              output := .constant false } with
                          scratch :=
                            TargetEmitterLedger.baselineValue
                              { inputCount := inputs
                                gates := []
                                output := .constant false } + 1 } =
                      TargetEmitterProgramSemantics.constantNormalizationResult
                        false
                        (TargetEmitterSemanticNormalization.outputCapturedRuntime
                          { inputCount := inputs
                            gates := []
                            output := .constant false })
                  exact
                    constantNormalizationResult_scratch_irrel false _ _
              | true =>
                  change
                    TargetEmitterProgramSemantics.constantNormalizationResult
                        true
                        { TargetEmitterSemanticNormalization.outputCapturedRuntime
                            { inputCount := inputs
                              gates := []
                              output := .constant true } with
                          scratch :=
                            TargetEmitterLedger.baselineValue
                              { inputCount := inputs
                                gates := []
                                output := .constant true } + 1 } =
                      TargetEmitterProgramSemantics.constantNormalizationResult
                        true
                        (TargetEmitterSemanticNormalization.outputCapturedRuntime
                          { inputCount := inputs
                            gates := []
                            output := .constant true })
                  exact
                    constantNormalizationResult_scratch_irrel true _ _
      | cons gate rest =>
          have runtimeEq :=
            gateListRuntime_eq_rawPrefixRuntime_of_nonempty
              { inputCount := inputs
                gates := gate :: rest
                output := output } (by simp)
          cases output with
          | gate index =>
              simp [physicalNormalizationRuntime,
                physicalCapturedRuntime,
                TargetEmitterSemanticNormalization.normalizationRuntime,
                TargetEmitterSemanticNormalization.outputCapturedRuntime,
                TargetEmitterControllerTrace.sourceKind,
                TargetEmitterControllerGateTrace.sourceValue,
                TargetEmitterSemanticSchedule.capturedValue,
                TargetEmitterControllerGateTrace.capturedRuntime,
                TargetEmitterControllerSourceTrace.capturedValue,
                runtimeEq]
          | input index =>
              simp [physicalNormalizationRuntime,
                physicalCapturedRuntime,
                TargetEmitterSemanticNormalization.normalizationRuntime,
                TargetEmitterSemanticNormalization.outputCapturedRuntime,
                TargetEmitterControllerTrace.sourceKind,
                TargetEmitterControllerGateTrace.sourceValue,
                TargetEmitterSemanticSchedule.capturedValue,
                TargetEmitterControllerGateTrace.capturedRuntime,
                TargetEmitterControllerSourceTrace.capturedValue,
                runtimeEq]
          | constant value =>
              cases value <;>
                simp [physicalNormalizationRuntime,
                  physicalCapturedRuntime,
                  TargetEmitterSemanticNormalization.normalizationRuntime,
                  TargetEmitterSemanticNormalization.outputCapturedRuntime,
                  TargetEmitterControllerTrace.sourceKind,
                  TargetEmitterControllerGateTrace.sourceValue,
                  TargetEmitterSemanticSchedule.capturedValue,
                  TargetEmitterControllerGateTrace.capturedRuntime,
                  TargetEmitterControllerSourceTrace.capturedValue,
                  runtimeEq]

private theorem inputNormalizationRanges_scratch_irrel
    {raw : RawCircuit} (runtime : Runtime) (scratch : Nat)
    (ranges :
      TargetEmitterRuntimeProgramSafety.InputNormalizationRanges
        raw runtime) :
    TargetEmitterRuntimeProgramSafety.InputNormalizationRanges
      raw { runtime with scratch := scratch } := by
  refine
    { initial := by simpa using ranges.initial
      afterFirstLeft := by
        simpa only [
          TargetEmitterProgramSemantics.macroResult_registers] using
          ranges.afterFirstLeft
      afterFirstRight := by
        simpa only [
          TargetEmitterProgramSemantics.macroResult_registers] using
          ranges.afterFirstRight
      afterFirstTrace := by
        simpa only [
          TargetEmitterProgramSemantics.macroResult_registers] using
          ranges.afterFirstTrace
      afterSecondLeft := by
        simpa only [
          TargetEmitterProgramSemantics.macroResult_registers] using
          ranges.afterSecondLeft
      afterSecondRight := by
        simpa only [
          TargetEmitterProgramSemantics.macroResult_registers] using
          ranges.afterSecondRight
      afterSecondTrace := by
        simpa only [
          TargetEmitterProgramSemantics.macroResult_registers] using
          ranges.afterSecondTrace
      nextGate := by
        simpa only [
          TargetEmitterProgramSemantics.macroResult_registers] using
          ranges.nextGate }

private theorem constantNormalizationRanges_scratch_irrel
    {raw : RawCircuit} {value : Bool}
    (runtime : Runtime) (scratch : Nat)
    (ranges :
      TargetEmitterRuntimeProgramSafety.ConstantNormalizationRanges
        raw value runtime) :
    TargetEmitterRuntimeProgramSafety.ConstantNormalizationRanges
      raw value { runtime with scratch := scratch } := by
  refine
    { initial := by simpa using ranges.initial
      afterLeft := by
        simpa only [
          TargetEmitterProgramSemantics.macroResult_registers] using
          ranges.afterLeft
      afterRight := by
        simpa only [
          TargetEmitterProgramSemantics.macroResult_registers] using
          ranges.afterRight }

/-! ### Closed prefix witnesses -/

private def AssemblyChecksBound
    (assembly : RawBuilder.MacroAssembly) : Prop :=
  ∀ source, source ∈ assembly.checks →
    RawBuilder.outputGateIndex source < assembly.gates.length

private theorem appendSourceMacro_checksBound
    (inputs totalGates gate side : Nat)
    (assembly : RawBuilder.MacroAssembly)
    (source : RawSource)
    (bound : AssemblyChecksBound assembly) :
    AssemblyChecksBound
      (RawBuilder.appendSourceMacro inputs totalGates gate side
        assembly source) := by
  intro check member
  have gateLength :=
    RawBuilder.appendSourceMacro_gates_length
      inputs totalGates gate side assembly source
  cases source with
  | input index =>
      have shape :
          check ∈ assembly.checks ∨
            check = .gate (assembly.gates.length + 7) := by
        simpa [RawBuilder.appendSourceMacro] using member
      rcases shape with old | rfl
      · have oldBound := bound check old
        rw [gateLength]
        simp [RawBuilder.sourceMacroGateCount]
        omega
      · rw [gateLength]
        simp [RawBuilder.outputGateIndex,
          RawBuilder.sourceMacroGateCount]
  | gate index =>
      have shape :
          check ∈ assembly.checks ∨
            check = .gate (assembly.gates.length + 7) := by
        simpa [RawBuilder.appendSourceMacro] using member
      rcases shape with old | rfl
      · have oldBound := bound check old
        rw [gateLength]
        simp [RawBuilder.sourceMacroGateCount]
        omega
      · rw [gateLength]
        simp [RawBuilder.outputGateIndex,
          RawBuilder.sourceMacroGateCount]
  | constant value =>
      cases value with
      | false =>
          have shape :
              check ∈ assembly.checks ∨
                check = .gate (assembly.gates.length + 2) := by
            simpa [RawBuilder.appendSourceMacro] using member
          rcases shape with old | rfl
          · have oldBound := bound check old
            rw [gateLength]
            simp [RawBuilder.sourceMacroGateCount]
            omega
          · rw [gateLength]
            simp [RawBuilder.outputGateIndex,
              RawBuilder.sourceMacroGateCount]
      | true =>
          have shape :
              check ∈ assembly.checks ∨
                check = .gate (assembly.gates.length + 1) := by
            simpa [RawBuilder.appendSourceMacro] using member
          rcases shape with old | rfl
          · have oldBound := bound check old
            rw [gateLength]
            simp [RawBuilder.sourceMacroGateCount]
            omega
          · rw [gateLength]
            simp [RawBuilder.outputGateIndex,
              RawBuilder.sourceMacroGateCount]

private theorem appendTraceMacro_checksBound
    (inputs totalGates gate : Nat)
    (assembly : RawBuilder.MacroAssembly)
    (bound : AssemblyChecksBound assembly) :
    AssemblyChecksBound
      (RawBuilder.appendTraceMacro inputs totalGates gate assembly) := by
  intro check member
  have shape :
      check ∈ assembly.checks ∨
        check = .gate (assembly.gates.length + 15) := by
    simpa [RawBuilder.appendTraceMacro] using member
  have gateLength :=
    RawBuilder.appendTraceMacro_gates_length
      inputs totalGates gate assembly
  rcases shape with old | rfl
  · have oldBound := bound check old
    rw [gateLength]
    omega
  · rw [gateLength]
    simp [RawBuilder.outputGateIndex]

private theorem assembleGates_checksBound
    (inputs totalGates gate : Nat)
    (assembly : RawBuilder.MacroAssembly)
    (gates : List RawGate)
    (bound : AssemblyChecksBound assembly) :
    AssemblyChecksBound
      (RawBuilder.assembleGates inputs totalGates gate
        assembly gates) := by
  induction gates generalizing gate assembly with
  | nil =>
      simpa [RawBuilder.assembleGates] using bound
  | cons source rest inductionHypothesis =>
      simp only [RawBuilder.assembleGates]
      let left :=
        RawBuilder.appendSourceMacro inputs totalGates gate 0
          assembly source.left
      let right :=
        RawBuilder.appendSourceMacro inputs totalGates gate 1
          left source.right
      let trace :=
        RawBuilder.appendTraceMacro inputs totalGates gate right
      have leftBound : AssemblyChecksBound left := by
        exact appendSourceMacro_checksBound
          inputs totalGates gate 0 assembly source.left bound
      have rightBound : AssemblyChecksBound right := by
        exact appendSourceMacro_checksBound
          inputs totalGates gate 1 left source.right leftBound
      have traceBound : AssemblyChecksBound trace := by
        exact appendTraceMacro_checksBound
          inputs totalGates gate right rightBound
      exact inductionHypothesis (gate + 1) trace traceBound

private theorem macroAssembly_checksBound
    (circuit : RawCircuit) :
    AssemblyChecksBound (RawBuilder.macroAssembly circuit) := by
  unfold RawBuilder.macroAssembly
  apply assembleGates_checksBound
  intro source member
  simp [RawBuilder.emptyAssembly] at member

private theorem checkCoordinates_bound
    (raw : RawCircuit) :
    ∀ value,
      value ∈
          TargetEmitterSemanticCompletion.checkCoordinates raw →
        value < TargetEmitterLedger.slotCapacity raw := by
  intro value member
  rcases List.mem_map.mp member with
    ⟨source, sourceMember, rfl⟩
  have bound :=
    macroAssembly_checksBound raw.normalize source sourceMember
  have macroLength :
      (RawBuilder.macroAssembly raw.normalize).gates.length ≤
        TargetEmitterLedger.baselineValue raw := by
    rw [RawBuilder.macroAssembly_gates_length,
      TargetEmitterLedger.baselineValue_eq_rawBuilder_formula]
    omega
  exact Nat.lt_of_lt_of_le bound
    (Nat.le_trans macroLength
      (TargetEmitterLedger.baselineValue_le_slotCapacity raw))

private theorem normalizationRuntime_range
    (raw : RawCircuit) :
    ControllerRange raw
      (TargetEmitterSemanticNormalization.normalizationRuntime
        raw).registers := by
  rw [normalizationRuntime_registers_constructive]
  refine
    { inputCount_eq := rfl
      normalizedGateCount_eq := rfl
      carrierWidth_eq := rfl
      baseline_eq := rfl
      currentGate_le := ?_
      outputIndex_le := ?_ }
  · cases raw with
    | mk inputs gates output =>
        cases output with
        | input index =>
            simp [TargetEmitterSemanticNormalization.normalizationCurrentGate,
              TargetEmitterLedger.normalizedGateCount,
              TargetEmitterLedger.normalizationAddedGates]
        | gate index =>
            simp [TargetEmitterSemanticNormalization.normalizationCurrentGate,
              TargetEmitterLedger.normalizedGateCount,
              TargetEmitterLedger.normalizationAddedGates]
        | constant value =>
            cases value <;>
              simp [
                TargetEmitterSemanticNormalization.normalizationCurrentGate,
                TargetEmitterLedger.normalizedGateCount,
                TargetEmitterLedger.normalizationAddedGates]
  · change
      (RawBuilder.macroAssembly raw.normalize).gates.length ≤
        TargetEmitterLedger.baselineValue raw + 4
    rw [RawBuilder.macroAssembly_gates_length,
      TargetEmitterLedger.baselineValue_eq_rawBuilder_formula]
    change
      RawBuilder.gateListMacroGateCount raw.normalize.gates ≤
        RawBuilder.gateListMacroGateCount raw.normalize.gates +
          2 * (3 * raw.normalize.gates.length - 1) + 4
    omega

private theorem inputNormalizationResult_captured
    (runtime : Runtime) :
    (TargetEmitterProgramSemantics.inputNormalizationResult
      runtime).captured = runtime.captured := by
  unfold TargetEmitterProgramSemantics.inputNormalizationResult
  dsimp only
  simp only [TargetEmitterProgramSemantics.incrementCurrentGateResult]
  rw [TargetEmitterControllerGateTrace.macroResult_captured,
    TargetEmitterControllerGateTrace.macroResult_captured,
    TargetEmitterControllerGateTrace.macroResult_captured,
    TargetEmitterControllerGateTrace.macroResult_captured,
    TargetEmitterControllerGateTrace.macroResult_captured,
    TargetEmitterControllerGateTrace.macroResult_captured]

private theorem constantNormalizationResult_captured
    (value : Bool) (runtime : Runtime) :
    (TargetEmitterProgramSemantics.constantNormalizationResult
      value runtime).captured = runtime.captured := by
  unfold TargetEmitterProgramSemantics.constantNormalizationResult
  rw [TargetEmitterControllerGateTrace.macroResult_captured,
    TargetEmitterControllerGateTrace.macroResult_captured,
    TargetEmitterControllerGateTrace.macroResult_captured]

private theorem normalizationRuntime_capturedBound
    (raw : RawCircuit) :
    (TargetEmitterSemanticNormalization.normalizationRuntime raw).captured +
          1 ≤
      (SourceParser.circuitCells raw).length := by
  have member :
      TargetEmitterCapacity.CircuitSource raw raw.output := .output
  have bound :=
    TargetEmitterCapacity.circuitSourceCaptureValue_succ_le_cells member
  cases raw with
  | mk inputs gates output =>
      cases output with
      | input index =>
          rw [TargetEmitterSemanticNormalization.normalizationRuntime,
            inputNormalizationResult_captured]
          simpa [
            TargetEmitterSemanticNormalization.outputCapturedRuntime,
            TargetEmitterSemanticSchedule.capturedValue,
            TargetEmitterCapacity.sourceCaptureValue] using bound
      | gate index =>
          simpa [TargetEmitterSemanticNormalization.normalizationRuntime,
            TargetEmitterSemanticNormalization.outputCapturedRuntime,
            TargetEmitterSemanticSchedule.capturedValue,
            TargetEmitterCapacity.sourceCaptureValue,
            TargetEmitterProgramSemantics.resetScratchResult] using bound
      | constant value =>
          rw [TargetEmitterSemanticNormalization.normalizationRuntime,
            constantNormalizationResult_captured]
          cases value <;>
            simpa [
              TargetEmitterSemanticNormalization.outputCapturedRuntime,
              TargetEmitterSemanticSchedule.capturedValue,
              TargetEmitterCapacity.sourceCaptureValue] using bound

private theorem checkCoordinates_nonempty_has_two
    (raw : RawCircuit)
    (nonempty :
      TargetEmitterSemanticCompletion.checkCoordinates raw ≠ []) :
    ∃ prior second newest,
      TargetEmitterSemanticCompletion.checkCoordinates raw =
        prior ++ [second, newest] := by
  have lengthEq :
      (TargetEmitterSemanticCompletion.checkCoordinates raw).length =
        3 * raw.normalize.gates.length := by
    exact
      TargetEmitterSemanticPrefix.macroAssembly_checkCoordinates_length
        raw.normalize
  have two :
      2 ≤
        (TargetEmitterSemanticCompletion.checkCoordinates raw).length := by
    rw [lengthEq]
    have positive : 0 < raw.normalize.gates.length := by
      apply Nat.pos_of_ne_zero
      intro zero
      apply nonempty
      apply List.eq_nil_of_length_eq_zero
      rw [lengthEq, zero]
    omega
  have reverseTwo :
      2 ≤
        (TargetEmitterSemanticCompletion.checkCoordinates raw).reverse.length := by
    simpa using two
  cases reversedEq :
      (TargetEmitterSemanticCompletion.checkCoordinates raw).reverse with
  | nil =>
      rw [reversedEq] at reverseTwo
      simp at reverseTwo
  | cons newest tail =>
      cases tail with
      | nil =>
          rw [reversedEq] at reverseTwo
          simp at reverseTwo
      | cons second priorReversed =>
          refine ⟨priorReversed.reverse, second, newest, ?_⟩
          have recovered := congrArg List.reverse reversedEq
          simpa [List.reverse_reverse, List.reverse_cons,
            List.append_assoc] using recovered

private theorem prefix_outputRoom
    (raw : RawCircuit) (prior : List Nat)
    (second newest : Nat)
    (shape :
      TargetEmitterSemanticCompletion.checkCoordinates raw =
        prior ++ [second, newest]) :
    (TargetEmitterSemanticNormalization.normalizationRuntime
          raw).registers.outputIndex +
          1 + 2 * prior.length ≤
      TargetEmitterLedger.baselineValue raw + 4 := by
  have registers := normalizationRuntime_registers_constructive raw
  have outputIndex :=
    congrArg
      (fun value : TargetEmitter.UnaryRegisters => value.outputIndex)
      registers
  have checksLength :
      (TargetEmitterSemanticCompletion.checkCoordinates raw).length =
        3 * raw.normalize.gates.length := by
    exact
      TargetEmitterSemanticPrefix.macroAssembly_checkCoordinates_length
        raw.normalize
  rw [shape, List.length_append] at checksLength
  rw [outputIndex, RawBuilder.macroAssembly_gates_length,
    TargetEmitterLedger.baselineValue_eq_rawBuilder_formula]
  simp only
  omega

private def rawGate_capturedReady
    (raw : RawCircuit) (index : Nat)
    (outputEq : raw.output = .gate index) :
    TargetEmitterRuntimeProgramSafety.CapturedReady raw
      (markedSource raw)
      (TargetEmitterSemanticNormalization.normalizationRuntime
        raw).captured := by
  have beforePacked :
      ∀ symbol,
        symbol ∈
            TargetEmitterControllerGateListTrace.outputCrossedCells raw →
          TargetEmitter.PackedSymbol symbol := by
    intro symbol member
    apply originalOutputWord_packed raw symbol
    exact List.mem_append.mpr
      (Or.inl (List.mem_append.mpr (Or.inl member)))
  have outputMember :
      TargetEmitterCapacity.CircuitSource raw (.gate index) := by
    rw [← outputEq]
    exact .output
  have capacity :
      index + 1 ≤ TargetEmitterLedger.slotCapacity raw := by
    simpa [TargetEmitterCapacity.sourceCaptureValue] using
      (TargetEmitterCapacity.focusedSourceCaptureReserve outputMember)
  have ready :=
    TargetEmitterControllerGateTrace.sourceReady raw .gate index
      (TargetEmitterControllerGateListTrace.outputCrossedCells raw)
      TargetEmitterControllerTrace.circuitTerminatorCells
      beforePacked capacity
  cases ready with
  | gate captured =>
      simpa [markedSource, outputEq,
        TargetEmitterSemanticNormalization.normalizationRuntime,
        TargetEmitterSemanticNormalization.outputCapturedRuntime,
        TargetEmitterSemanticSchedule.capturedValue,
        TargetEmitterProgramSemantics.resetScratchResult,
        TargetEmitterControllerTrace.sourceKind,
        TargetEmitterControllerGateTrace.sourceValue,
        TargetEmitterControllerSourceTrace.capturedValue] using captured

/-- One literal upper bound for each selected output-normalization program. -/
def normalizationProgramLimit : Nat := 16384

/-- Logical target/check growth reserved for the selected normalization
program after the output coordinate has been captured. -/
def normalizationDataGrowth (raw : RawCircuit) : Nat :=
  normalizationProgramLimit *
    (TargetEmitterLedger.slotCapacity raw + 1)

private theorem programSafe_data_le_normalizationLimit
    {capacity : Nat} {source : List WorkSymbol}
    {context : TargetEmitterRuntimeProgram.SourceContext source}
    {primitives : List TargetEmitterPlan.Primitive}
    {initial final : Runtime}
    (safe :
      TargetEmitterRuntimeProgram.ProgramSafe
        capacity source context primitives initial final)
    (programBound : primitives.length ≤ normalizationProgramLimit) :
    final.targetTokens.length ≤
        initial.targetTokens.length +
          normalizationProgramLimit * (capacity + 1) ∧
      TargetEmitterRuntimeProgramBound.checkCells final.checks ≤
        TargetEmitterRuntimeProgramBound.checkCells initial.checks +
          normalizationProgramLimit * (capacity + 1) := by
  have targetGrowth :=
    TargetEmitterRuntimeProgramBound.ProgramSafe.target_length_le safe
  have checkGrowth :=
    TargetEmitterRuntimeProgramBound.ProgramSafe.checkCells_le safe
  have scaled :=
    Nat.mul_le_mul_right (capacity + 1) programBound
  exact
    ⟨Nat.le_trans targetGrowth
        (Nat.add_le_add_left scaled initial.targetTokens.length),
      Nat.le_trans checkGrowth
        (Nat.add_le_add_left scaled
          (TargetEmitterRuntimeProgramBound.checkCells initial.checks))⟩

private def physicalInput_capturedReady
    (raw : RawCircuit) (index : Nat)
    (outputEq : raw.output = .input index) :
    TargetEmitterRuntimeProgramSafety.CapturedReady raw
      (markedSource raw) (physicalCapturedRuntime raw).captured := by
  have beforePacked :
      ∀ symbol,
        symbol ∈
            TargetEmitterControllerGateListTrace.outputCrossedCells raw →
          TargetEmitter.PackedSymbol symbol := by
    intro symbol member
    apply originalOutputWord_packed raw symbol
    exact List.mem_append.mpr
      (Or.inl (List.mem_append.mpr (Or.inl member)))
  have outputMember :
      TargetEmitterCapacity.CircuitSource raw (.input index) := by
    rw [← outputEq]
    exact .output
  have capacity :
      index + 1 ≤ TargetEmitterLedger.slotCapacity raw := by
    simpa [TargetEmitterCapacity.sourceCaptureValue] using
      (TargetEmitterCapacity.focusedSourceCaptureReserve outputMember)
  have ready :=
    TargetEmitterControllerGateTrace.sourceReady raw .input index
      (TargetEmitterControllerGateListTrace.outputCrossedCells raw)
      TargetEmitterControllerTrace.circuitTerminatorCells
      beforePacked capacity
  cases ready with
  | input captured =>
      simpa [markedSource, outputEq, physicalCapturedRuntime,
        TargetEmitterControllerTrace.sourceKind,
        TargetEmitterControllerGateTrace.sourceValue,
        TargetEmitterControllerGateTrace.capturedRuntime,
        TargetEmitterControllerSourceTrace.capturedValue] using captured

/-- The exact semantic runtime after selected output normalization inherits a
closed data-growth charge from the already bounded gate-list runtime. -/
theorem normalizationRuntime_data_le (raw : RawCircuit) :
    (TargetEmitterSemanticNormalization.normalizationRuntime
          raw).targetTokens.length ≤
        (TargetEmitterControllerGateListTrace.gateListRuntime
          raw).targetTokens.length + normalizationDataGrowth raw ∧
      TargetEmitterRuntimeProgramBound.checkCells
          (TargetEmitterSemanticNormalization.normalizationRuntime
            raw).checks ≤
        TargetEmitterRuntimeProgramBound.checkCells
            (TargetEmitterControllerGateListTrace.gateListRuntime raw).checks +
          normalizationDataGrowth raw := by
  cases raw with
  | mk inputs gates output =>
      let raw : RawCircuit :=
        { inputCount := inputs, gates := gates, output := output }
      let runtime :=
        TargetEmitterControllerGateListTrace.gateListRuntime raw
      let captured := physicalCapturedRuntime raw
      have capturedScratch :
          captured.scratch < TargetEmitterLedger.slotCapacity raw := by
        have reserve := output_capture_reserve raw
        have captureValueEq :
            TargetEmitterControllerSourceTrace.capturedValue
                (TargetEmitterControllerTrace.sourceKind raw.output)
                (TargetEmitterControllerGateTrace.sourceValue raw.output) =
              TargetEmitterCapacity.sourceCaptureValue raw.output := by
          cases output with
          | input index => rfl
          | gate index => rfl
          | constant value => cases value <;> rfl
        apply Nat.lt_of_succ_le
        change
          runtime.scratch +
                TargetEmitterControllerSourceTrace.capturedValue
                  (TargetEmitterControllerTrace.sourceKind raw.output)
                  (TargetEmitterControllerGateTrace.sourceValue raw.output) +
              1 ≤
            TargetEmitterLedger.slotCapacity raw
        rw [captureValueEq]
        simpa [runtime] using reserve
      cases output with
      | input index =>
          have rangesBase :=
            inputNormalizationRanges_constructive inputs gates index
          have ranges :
              TargetEmitterRuntimeProgramSafety.InputNormalizationRanges
                raw captured := by
            change
              TargetEmitterRuntimeProgramSafety.InputNormalizationRanges
                raw (physicalCapturedRuntime raw)
            rw [physicalCapturedRuntime_scratch_shape]
            exact inputNormalizationRanges_scratch_irrel
              (TargetEmitterSemanticNormalization.outputCapturedRuntime raw)
              (physicalCapturedRuntime raw).scratch
              (by simpa [raw] using rangesBase)
          have outputMember :
              TargetEmitterCapacity.CircuitSource raw (.input index) := by
            exact .output
          have capturedBound :
              captured.captured + 1 ≤
                (SourceParser.circuitCells raw).length := by
            simpa [captured, physicalCapturedRuntime,
              TargetEmitterControllerTrace.sourceKind,
              TargetEmitterControllerGateTrace.sourceValue,
              TargetEmitterControllerGateTrace.capturedRuntime,
              TargetEmitterControllerSourceTrace.capturedValue] using
              TargetEmitterCapacity.circuitInputIndex_succ_le_cells
                outputMember
          have safe :=
            TargetEmitterRuntimeProgramSafety.inputNormalization_safe
              (outputWorkspace raw) ranges capturedBound capturedScratch
              (physicalInput_capturedReady raw index rfl)
          have bounds :=
            programSafe_data_le_normalizationLimit safe (by decide)
          have physicalEq := physicalNormalizationRuntime_eq raw
          rw [← physicalEq]
          simpa [raw, runtime, captured, physicalCapturedRuntime,
            physicalNormalizationRuntime,
            TargetEmitterControllerGateTrace.capturedRuntime,
            normalizationDataGrowth] using bounds
      | constant value =>
          have rangesBase :=
            constantNormalizationRanges_constructive inputs gates value
          have ranges :
              TargetEmitterRuntimeProgramSafety.ConstantNormalizationRanges
                raw value captured := by
            change
              TargetEmitterRuntimeProgramSafety.ConstantNormalizationRanges
                raw value (physicalCapturedRuntime raw)
            rw [physicalCapturedRuntime_scratch_shape]
            exact constantNormalizationRanges_scratch_irrel
              (TargetEmitterSemanticNormalization.outputCapturedRuntime raw)
              (physicalCapturedRuntime raw).scratch
              (by simpa [raw] using rangesBase)
          have capturedBound :
              captured.captured + 1 ≤
                (SourceParser.circuitCells raw).length := by
            have cells :=
              TargetEmitterCapacity.fourteen_le_circuitCells_length raw
            have capturedZero : captured.captured = 0 := by
              cases value <;>
                simp [captured, raw, physicalCapturedRuntime,
                  TargetEmitterControllerTrace.sourceKind,
                  TargetEmitterControllerGateTrace.sourceValue,
                  TargetEmitterControllerGateTrace.capturedRuntime,
                  TargetEmitterControllerSourceTrace.capturedValue]
            rw [capturedZero]
            omega
          have safe :=
            TargetEmitterRuntimeProgramSafety.constantNormalization_safe
              value (outputWorkspace raw) ranges capturedBound
              capturedScratch
          have bounds :=
            programSafe_data_le_normalizationLimit safe
              (by cases value <;> decide)
          have physicalEq := physicalNormalizationRuntime_eq raw
          rw [← physicalEq]
          cases value <;>
            simpa [raw, runtime, captured, physicalCapturedRuntime,
              physicalNormalizationRuntime,
              TargetEmitterControllerTrace.sourceKind,
              TargetEmitterControllerGateTrace.sourceValue,
              TargetEmitterControllerGateTrace.capturedRuntime,
              normalizationDataGrowth] using bounds
      | gate index =>
          have safe :=
            TargetEmitterRuntimeProgramSafety.outputGateReset_safe
              (outputWorkspace raw).context capturedScratch
          have bounds :=
            programSafe_data_le_normalizationLimit safe (by decide)
          have physicalEq := physicalNormalizationRuntime_eq raw
          rw [← physicalEq]
          simpa [raw, runtime, captured, physicalCapturedRuntime,
            physicalNormalizationRuntime,
            TargetEmitterControllerTrace.sourceKind,
            TargetEmitterControllerGateTrace.sourceValue,
            TargetEmitterControllerGateTrace.capturedRuntime,
            normalizationDataGrowth] using bounds

private theorem normalizedPrefix_to_beginOutput_path
    (raw : RawCircuit)
    (nonempty :
      TargetEmitterSemanticCompletion.checkCoordinates raw ≠ [])
    (traceEq :
      TargetEmitterSemanticCompletion.outputTraceExpression raw =
        TargetEmitterPlan.traceCoordinate)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents normalizedInitialPopRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterSemanticNormalization.normalizationRuntime raw).scratch
        (TargetEmitterSemanticNormalization.normalizationRuntime raw).registers
        (TargetEmitterSemanticNormalization.normalizationRuntime raw).checks
        (markedSource raw)
        (TargetEmitterSemanticNormalization.normalizationRuntime
          raw).targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node normalizedInitialPopRef)
          (.node beginOutputRef) steps initialTape finalTape ∧
      TapeRepresents beginOutputRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterSemanticCompletion.finalRuntime raw).scratch
        (TargetEmitterSemanticCompletion.finalRuntime raw).registers
        (TargetEmitterSemanticCompletion.finalRuntime raw).checks
        (markedSource raw)
        (TargetEmitterSemanticCompletion.finalRuntime raw).targetTokens
        finalTape ∧
      steps ≤
        TargetEmitterControllerPrefixBound.prefixUniformEnvelope
          (TargetEmitterLedger.slotCapacity raw)
          (markedSource raw)
          (TargetEmitterSemanticNormalization.normalizationRuntime raw)
          (TargetEmitterSemanticCompletion.checkCoordinates raw).length := by
  rcases checkCoordinates_nonempty_has_two raw nonempty with
    ⟨prior, second, newest, shape⟩
  have checksShape :
      (TargetEmitterSemanticNormalization.normalizationRuntime raw).checks =
        prior ++ [second, newest] := by
    rw [normalizationRuntime_checks_constructive,
      ← shape]
    rfl
  have priorBounds :
      ∀ value, value ∈ prior →
        value < TargetEmitterLedger.slotCapacity raw := by
    intro value member
    apply checkCoordinates_bound raw value
    rw [shape]
    exact List.mem_append.mpr (Or.inl member)
  have secondBound :
      second < TargetEmitterLedger.slotCapacity raw := by
    apply checkCoordinates_bound raw second
    rw [shape]
    simp
  have newestBound :
      newest < TargetEmitterLedger.slotCapacity raw := by
    apply checkCoordinates_bound raw newest
    rw [shape]
    simp
  rcases
      TargetEmitterControllerPrefixBound.normalizedInitialPrefix_to_beginOutput_path_bounded
        (outputWorkspace raw)
        (TargetEmitterSemanticNormalization.normalizationRuntime raw)
        prior second newest
        (normalizationRuntime_range raw)
        (normalizationRuntime_capturedBound raw)
        (TargetEmitterSemanticNormalization.normalizationRuntime_scratch raw)
        checksShape priorBounds secondBound newestBound
        (prefix_outputRoom raw prior second newest shape)
        initialTape represents with
    ⟨steps, finalTape, path, finalRepresents, envelopeBound⟩
  have prefixRuntimeEq :
      (TargetEmitterSemanticCompletion.prefixRun raw).runtime =
        TargetEmitterControllerPrefixTrace.normalizedNonemptyPrefixResult
          (TargetEmitterSemanticNormalization.normalizationRuntime raw)
          prior second newest := by
    simp only [
      TargetEmitterSemanticCompletion.prefixRun,
      TargetEmitterControllerPrefixTrace.normalizedNonemptyPrefixResult]
    rw [shape,
      TargetEmitterSemanticPrefixBridge.runPrefix_append_pair_runtime]
  have uniformBound :=
    TargetEmitterControllerPrefixBound.normalizedNonemptyPrefixEnvelope_le_uniform
      (outputWorkspace raw)
      (TargetEmitterSemanticNormalization.normalizationRuntime raw)
      prior second newest
      (normalizationRuntime_range raw)
      (normalizationRuntime_capturedBound raw)
      (TargetEmitterSemanticNormalization.normalizationRuntime_scratch raw)
      checksShape priorBounds secondBound newestBound
      (prefix_outputRoom raw prior second newest shape)
  have countEq :
      prior.length + 2 =
        (TargetEmitterSemanticCompletion.checkCoordinates raw).length := by
    rw [shape]
    simp
  refine ⟨steps, finalTape, path, ?_, ?_⟩
  · simpa only [TargetEmitterSemanticCompletion.finalRuntime,
      if_neg nonempty, traceEq, prefixRuntimeEq] using finalRepresents
  · exact Nat.le_trans envelopeBound
      (by simpa [countEq] using uniformBound)

private theorem rawPrefix_to_beginOutput_path
    (raw : RawCircuit) (index : Nat)
    (outputEq : raw.output = .gate index)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents rawInitialPopRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterSemanticNormalization.normalizationRuntime raw).scratch
        (TargetEmitterSemanticNormalization.normalizationRuntime raw).registers
        (TargetEmitterSemanticNormalization.normalizationRuntime raw).checks
        (markedSource raw)
        (TargetEmitterSemanticNormalization.normalizationRuntime
          raw).targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node rawInitialPopRef)
          (.node beginOutputRef) steps initialTape finalTape ∧
      TapeRepresents beginOutputRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterSemanticCompletion.finalRuntime raw).scratch
        (TargetEmitterSemanticCompletion.finalRuntime raw).registers
        (TargetEmitterSemanticCompletion.finalRuntime raw).checks
        (markedSource raw)
        (TargetEmitterSemanticCompletion.finalRuntime raw).targetTokens
        finalTape ∧
      steps ≤
        TargetEmitterControllerPrefixBound.prefixUniformEnvelope
          (TargetEmitterLedger.slotCapacity raw)
          (markedSource raw)
          (TargetEmitterSemanticNormalization.normalizationRuntime raw)
          (TargetEmitterSemanticCompletion.checkCoordinates raw).length := by
  by_cases nonempty :
      TargetEmitterSemanticCompletion.checkCoordinates raw ≠ []
  · rcases checkCoordinates_nonempty_has_two raw nonempty with
      ⟨prior, second, newest, shape⟩
    have checksShape :
        (TargetEmitterSemanticNormalization.normalizationRuntime raw).checks =
          prior ++ [second, newest] := by
      rw [normalizationRuntime_checks_constructive,
        ← shape]
      rfl
    have priorBounds :
        ∀ value, value ∈ prior →
          value < TargetEmitterLedger.slotCapacity raw := by
      intro value member
      apply checkCoordinates_bound raw value
      rw [shape]
      exact List.mem_append.mpr (Or.inl member)
    have secondBound :
        second < TargetEmitterLedger.slotCapacity raw := by
      apply checkCoordinates_bound raw second
      rw [shape]
      simp
    have newestBound :
        newest < TargetEmitterLedger.slotCapacity raw := by
      apply checkCoordinates_bound raw newest
      rw [shape]
      simp
    rcases
        TargetEmitterControllerPrefixBound.rawInitialPrefix_to_beginOutput_path_bounded
          (outputWorkspace raw)
          (TargetEmitterSemanticNormalization.normalizationRuntime raw)
          prior second newest
          (normalizationRuntime_range raw)
          (normalizationRuntime_capturedBound raw)
          (TargetEmitterSemanticNormalization.normalizationRuntime_scratch raw)
          checksShape priorBounds secondBound newestBound
          (prefix_outputRoom raw prior second newest shape)
          (rawGate_capturedReady raw index outputEq)
          initialTape represents with
      ⟨steps, finalTape, path, finalRepresents, envelopeBound⟩
    have prefixRuntimeEq :
        (TargetEmitterSemanticCompletion.prefixRun raw).runtime =
          TargetEmitterControllerPrefixTrace.rawNonemptyPrefixResult
            (TargetEmitterSemanticNormalization.normalizationRuntime raw)
            prior second newest := by
      simp only [TargetEmitterSemanticCompletion.prefixRun]
      rw [shape,
        TargetEmitterSemanticPrefixBridge.runPrefix_append_pair_runtime]
    have uniformBound :=
      TargetEmitterControllerPrefixBound.rawNonemptyPrefixEnvelope_le_uniform
        (outputWorkspace raw)
        (TargetEmitterSemanticNormalization.normalizationRuntime raw)
        prior second newest
        (normalizationRuntime_range raw)
        (normalizationRuntime_capturedBound raw)
        (TargetEmitterSemanticNormalization.normalizationRuntime_scratch raw)
        checksShape priorBounds secondBound newestBound
        (prefix_outputRoom raw prior second newest shape)
    have countEq :
        prior.length + 2 =
          (TargetEmitterSemanticCompletion.checkCoordinates raw).length := by
      rw [shape]
      simp
    refine ⟨steps, finalTape, path, ?_, ?_⟩
    have traceEq :
        TargetEmitterSemanticCompletion.outputTraceExpression raw =
          TargetEmitterPlan.rawGateTrace := by
      rw [TargetEmitterSemanticCompletion.outputTraceExpression, outputEq]
    · simpa only [TargetEmitterSemanticCompletion.finalRuntime,
        if_neg nonempty, traceEq, prefixRuntimeEq] using finalRepresents
    · exact Nat.le_trans envelopeBound
        (by simpa [countEq] using uniformBound)
  · have empty :
        TargetEmitterSemanticCompletion.checkCoordinates raw = [] :=
      by
        apply Decidable.byContradiction
        intro different
        exact nonempty different
    have checksEmpty :
        (TargetEmitterSemanticNormalization.normalizationRuntime raw).checks =
          [] := by
      rw [normalizationRuntime_checks_constructive]
      simpa [TargetEmitterSemanticCompletion.checkCoordinates] using empty
    rcases
        TargetEmitterControllerPrefixBound.rawInitialPop_empty_to_beginOutput_path_bounded
          (outputWorkspace raw)
          (TargetEmitterSemanticNormalization.normalizationRuntime raw)
          (normalizationRuntime_range raw)
          (normalizationRuntime_capturedBound raw)
          (TargetEmitterSemanticNormalization.normalizationRuntime_scratch raw)
          checksEmpty
          (rawGate_capturedReady raw index outputEq)
          initialTape represents with
      ⟨steps, finalTape, path, finalRepresents, envelopeBound⟩
    have prefixRuntimeEq :
        (TargetEmitterSemanticCompletion.prefixRun raw).runtime =
          TargetEmitterSemanticNormalization.normalizationRuntime raw := by
      simp only [TargetEmitterSemanticCompletion.prefixRun, empty,
        TargetEmitterSemanticPrefix.runPrefix]
    have uniformBound :=
      TargetEmitterControllerPrefixBound.rawInitialEmptyEnvelope_le_uniform
        raw (markedSource raw)
        (TargetEmitterSemanticNormalization.normalizationRuntime raw)
    refine ⟨steps, finalTape, path, ?_, ?_⟩
    · simpa only [TargetEmitterSemanticCompletion.finalRuntime,
        if_pos empty, prefixRuntimeEq] using finalRepresents
    · exact Nat.le_trans envelopeBound
        (by
          simpa [empty] using uniformBound)

/-- Closed normalization charge selected only from the raw output constructor. -/
def outputNormalizationUniformEnvelope (raw : RawCircuit) : Nat :=
  let runtime :=
    TargetEmitterControllerGateListTrace.gateListRuntime raw
  let captured := physicalCapturedRuntime raw
  match raw.output with
  | .input index =>
      TargetEmitterControllerNormalizationBound.sourceCaptureEnvelope
          (TargetEmitterControllerGateListTrace.outputCrossedCells raw).length
          runtime.scratch index +
        TargetEmitterControllerNormalizationBound.inputNormalizationEnvelope
          raw (markedSource raw) captured
  | .constant value =>
      TargetEmitterControllerNormalizationBound.sourceCaptureEnvelope
          (TargetEmitterControllerGateListTrace.outputCrossedCells raw).length
          runtime.scratch 0 +
        TargetEmitterControllerNormalizationBound.constantNormalizationEnvelope
          raw (markedSource raw) captured value
  | .gate index =>
      TargetEmitterControllerNormalizationBound.sourceCaptureEnvelope
          (TargetEmitterControllerGateListTrace.outputCrossedCells raw).length
          runtime.scratch index +
        TargetEmitterControllerNormalizationBound.outputGateResetEnvelope
          raw (markedSource raw) captured

/-- Closed prefix/final charge at the exact semantic normalization boundary. -/
def controllerPrefixUniformEnvelope (raw : RawCircuit) : Nat :=
  TargetEmitterControllerPrefixBound.prefixUniformEnvelope
    (TargetEmitterLedger.slotCapacity raw)
    (markedSource raw)
    (TargetEmitterSemanticNormalization.normalizationRuntime raw)
    (TargetEmitterSemanticCompletion.checkCoordinates raw).length

private theorem gateList_to_beginOutput_path
    (raw : RawCircuit) (initialTape : WorkTape)
    (represents :
      FocusTapeRepresents outputFirstRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterControllerGateListTrace.gateListRuntime raw).scratch
        (TargetEmitterControllerGateListTrace.gateListRuntime raw).registers
        (TargetEmitterControllerGateListTrace.gateListRuntime raw).checks
        (TargetEmitterControllerGateListTrace.outputCrossedCells raw)
        (SourceParser.sourceCells raw.output ++
          TargetEmitterControllerTrace.circuitTerminatorCells)
        (TargetEmitterControllerGateListTrace.gateListRuntime
          raw).targetTokens initialTape) :
    ∃ normalizationSteps prefixSteps finalTape,
      AcceptPath graph (.node outputFirstRef)
          (.node beginOutputRef)
          (normalizationSteps + prefixSteps)
          initialTape finalTape ∧
      TapeRepresents beginOutputRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterSemanticCompletion.finalRuntime raw).scratch
        (TargetEmitterSemanticCompletion.finalRuntime raw).registers
        (TargetEmitterSemanticCompletion.finalRuntime raw).checks
        (markedSource raw)
        (TargetEmitterSemanticCompletion.finalRuntime raw).targetTokens
        finalTape ∧
      normalizationSteps ≤ outputNormalizationUniformEnvelope raw ∧
      prefixSteps ≤ controllerPrefixUniformEnvelope raw := by
  cases raw with
  | mk inputs gates output =>
      let raw : RawCircuit :=
        { inputCount := inputs, gates := gates, output := output }
      let runtime :=
        TargetEmitterControllerGateListTrace.gateListRuntime raw
      have packed :
          ∀ symbol,
            symbol ∈
                (SourceParser.cell00 :: outputPrefixTail raw) ++
                  SourceParser.sourceCells output ++
                  TargetEmitterControllerTrace.circuitTerminatorCells →
              TargetEmitter.PackedSymbol symbol := by
        simpa [raw, outputCrossedCells_eq] using
          originalOutputWord_packed raw
      have focused :
          FocusTapeRepresents outputFirstRef.startState
            (TargetEmitterLedger.slotCapacity raw)
            runtime.scratch runtime.registers runtime.checks
            (SourceParser.cell00 :: outputPrefixTail raw)
            (SourceParser.sourceCells output ++
              TargetEmitterControllerTrace.circuitTerminatorCells)
            runtime.targetTokens initialTape := by
        simpa [raw, runtime, outputCrossedCells_eq] using represents
      cases output with
      | input index =>
          have rangesBase :=
            inputNormalizationRanges_constructive
              inputs gates index
          have ranges :
              TargetEmitterRuntimeProgramSafety.InputNormalizationRanges
                raw
                (TargetEmitterControllerGateTrace.capturedRuntime
                  runtime .input index) := by
            change
              TargetEmitterRuntimeProgramSafety.InputNormalizationRanges
                raw (physicalCapturedRuntime raw)
            rw [physicalCapturedRuntime_scratch_shape]
            exact inputNormalizationRanges_scratch_irrel
              (TargetEmitterSemanticNormalization.outputCapturedRuntime raw)
              (physicalCapturedRuntime raw).scratch
              (by simpa [raw] using rangesBase)
          rcases
              TargetEmitterControllerNormalizationBound.outputInputNormalization_path_bounded
                runtime index
                SourceParser.cell00 (outputPrefixTail raw)
                TargetEmitterControllerTrace.circuitTerminatorCells
                rfl
                (by
                  simpa [raw, runtime,
                    TargetEmitterCapacity.sourceCaptureValue,
                    TargetEmitterControllerSourceTrace.capturedValue] using
                    output_capture_reserve raw)
                ranges packed initialTape focused with
            ⟨normalizationSteps, normalizedTape,
              normalizationPath, normalizedRepresents,
              normalizationBound⟩
          have normalizedRepresents' :
              TapeRepresents normalizedInitialPopRef.startState
                (TargetEmitterLedger.slotCapacity raw)
                (TargetEmitterSemanticNormalization.normalizationRuntime
                  raw).scratch
                (TargetEmitterSemanticNormalization.normalizationRuntime
                  raw).registers
                (TargetEmitterSemanticNormalization.normalizationRuntime
                  raw).checks
                (markedSource raw)
                (TargetEmitterSemanticNormalization.normalizationRuntime
                  raw).targetTokens normalizedTape := by
            have physicalEq := physicalNormalizationRuntime_eq raw
            rw [← physicalEq]
            simpa [raw, runtime, physicalNormalizationRuntime,
              physicalCapturedRuntime, markedSource,
              outputCrossedCells_eq,
              TargetEmitterControllerTrace.sourceKind,
              TargetEmitterControllerGateTrace.sourceValue,
              TargetEmitterControllerPrefixTrace.TapeRepresents,
              TargetEmitterControllerGateTrace.TapeRepresents] using
              normalizedRepresents
          have nonempty :
              TargetEmitterSemanticCompletion.checkCoordinates raw ≠ [] := by
            intro empty
            have lengths :=
              TargetEmitterSemanticPrefix.macroAssembly_checkCoordinates_length
                raw.normalize
            change
              (TargetEmitterSemanticCompletion.checkCoordinates raw).length =
                3 * raw.normalize.gates.length at lengths
            rw [empty] at lengths
            simp [raw, RawCircuit.normalize] at lengths
          rcases
              normalizedPrefix_to_beginOutput_path raw nonempty rfl
                normalizedTape normalizedRepresents' with
            ⟨prefixSteps, finalTape, prefixPath, finalRepresents,
              prefixBound⟩
          refine
            ⟨normalizationSteps, prefixSteps, finalTape, ?_,
              finalRepresents, ?_, prefixBound⟩
          · exact
              AcceptPath.trans graph (.node outputFirstRef)
                (.node normalizedInitialPopRef) (.node beginOutputRef)
                normalizationSteps prefixSteps initialTape normalizedTape
                finalTape normalizationPath prefixPath
          · simpa [outputNormalizationUniformEnvelope, raw, runtime,
              physicalCapturedRuntime, markedSource,
              outputCrossedCells_eq,
              TargetEmitterControllerTrace.sourceKind,
              TargetEmitterControllerGateTrace.sourceValue] using
              normalizationBound
      | constant value =>
          have rangesBase :=
            constantNormalizationRanges_constructive
              inputs gates value
          have ranges :
              TargetEmitterRuntimeProgramSafety.ConstantNormalizationRanges
                raw value
                (TargetEmitterControllerGateTrace.capturedRuntime
                  runtime
                  (if value then .constantTrue else .constantFalse) 0) := by
            have capturedEq :
                TargetEmitterControllerGateTrace.capturedRuntime
                    runtime
                    (if value then .constantTrue else .constantFalse) 0 =
                  physicalCapturedRuntime raw := by
              cases value <;>
                simp [raw, runtime, physicalCapturedRuntime,
                  TargetEmitterControllerTrace.sourceKind,
                  TargetEmitterControllerGateTrace.sourceValue]
            rw [capturedEq, physicalCapturedRuntime_scratch_shape]
            exact constantNormalizationRanges_scratch_irrel
              (TargetEmitterSemanticNormalization.outputCapturedRuntime raw)
              (physicalCapturedRuntime raw).scratch
              (by simpa [raw] using rangesBase)
          rcases
              TargetEmitterControllerNormalizationBound.outputConstantNormalization_path_bounded
                runtime value
                SourceParser.cell00 (outputPrefixTail raw)
                TargetEmitterControllerTrace.circuitTerminatorCells
                rfl
                (by
                  cases value <;>
                    simpa [raw, runtime,
                      TargetEmitterCapacity.sourceCaptureValue,
                      TargetEmitterControllerSourceTrace.capturedValue] using
                      output_capture_reserve raw)
                ranges packed initialTape focused with
            ⟨normalizationSteps, normalizedTape,
              normalizationPath, normalizedRepresents,
              normalizationBound⟩
          have normalizedRepresents' :
              TapeRepresents normalizedInitialPopRef.startState
                (TargetEmitterLedger.slotCapacity raw)
                (TargetEmitterSemanticNormalization.normalizationRuntime
                  raw).scratch
                (TargetEmitterSemanticNormalization.normalizationRuntime
                  raw).registers
                (TargetEmitterSemanticNormalization.normalizationRuntime
                  raw).checks
                (markedSource raw)
                (TargetEmitterSemanticNormalization.normalizationRuntime
                  raw).targetTokens normalizedTape := by
            have physicalEq := physicalNormalizationRuntime_eq raw
            rw [← physicalEq]
            cases value <;>
              simpa [raw, runtime, physicalNormalizationRuntime,
                physicalCapturedRuntime, markedSource,
                outputCrossedCells_eq,
                TargetEmitterControllerTrace.sourceKind,
                TargetEmitterControllerGateTrace.sourceValue,
                TargetEmitterControllerPrefixTrace.TapeRepresents,
                TargetEmitterControllerGateTrace.TapeRepresents] using
                normalizedRepresents
          have nonempty :
              TargetEmitterSemanticCompletion.checkCoordinates raw ≠ [] := by
            intro empty
            have lengths :=
              TargetEmitterSemanticPrefix.macroAssembly_checkCoordinates_length
                raw.normalize
            change
              (TargetEmitterSemanticCompletion.checkCoordinates raw).length =
                3 * raw.normalize.gates.length at lengths
            rw [empty] at lengths
            cases value <;>
              simp [raw, RawCircuit.normalize] at lengths
          have traceEq :
              TargetEmitterSemanticCompletion.outputTraceExpression raw =
                TargetEmitterPlan.traceCoordinate := by
            cases value <;> rfl
          rcases
              normalizedPrefix_to_beginOutput_path raw nonempty traceEq
                normalizedTape normalizedRepresents' with
            ⟨prefixSteps, finalTape, prefixPath, finalRepresents,
              prefixBound⟩
          refine
            ⟨normalizationSteps, prefixSteps, finalTape, ?_,
              finalRepresents, ?_, prefixBound⟩
          · exact
              AcceptPath.trans graph (.node outputFirstRef)
                (.node normalizedInitialPopRef) (.node beginOutputRef)
                normalizationSteps prefixSteps initialTape normalizedTape
                finalTape normalizationPath prefixPath
          · cases value <;>
              simpa [outputNormalizationUniformEnvelope, raw, runtime,
                physicalCapturedRuntime, markedSource,
                outputCrossedCells_eq,
                TargetEmitterControllerTrace.sourceKind,
                TargetEmitterControllerGateTrace.sourceValue] using
                normalizationBound
      | gate index =>
          rcases
              TargetEmitterControllerNormalizationBound.outputGateNormalization_path_bounded
                runtime index
                SourceParser.cell00 (outputPrefixTail raw)
                TargetEmitterControllerTrace.circuitTerminatorCells
                rfl
                (by
                  simpa [raw, runtime,
                    TargetEmitterCapacity.sourceCaptureValue,
                    TargetEmitterControllerSourceTrace.capturedValue] using
                    output_capture_reserve raw)
                packed initialTape focused with
            ⟨normalizationSteps, normalizedTape,
              normalizationPath, normalizedRepresents,
              normalizationBound⟩
          have normalizedRepresents' :
              TapeRepresents rawInitialPopRef.startState
                (TargetEmitterLedger.slotCapacity raw)
                (TargetEmitterSemanticNormalization.normalizationRuntime
                  raw).scratch
                (TargetEmitterSemanticNormalization.normalizationRuntime
                  raw).registers
                (TargetEmitterSemanticNormalization.normalizationRuntime
                  raw).checks
                (markedSource raw)
                (TargetEmitterSemanticNormalization.normalizationRuntime
                  raw).targetTokens normalizedTape := by
            have physicalEq := physicalNormalizationRuntime_eq raw
            rw [← physicalEq]
            simpa [raw, runtime, physicalNormalizationRuntime,
              physicalCapturedRuntime, markedSource,
              outputCrossedCells_eq,
              TargetEmitterControllerTrace.sourceKind,
              TargetEmitterControllerGateTrace.sourceValue,
              TargetEmitterControllerPrefixTrace.TapeRepresents,
              TargetEmitterControllerGateTrace.TapeRepresents] using
              normalizedRepresents
          rcases
              rawPrefix_to_beginOutput_path raw index rfl
                normalizedTape normalizedRepresents' with
            ⟨prefixSteps, finalTape, prefixPath, finalRepresents,
              prefixBound⟩
          refine
            ⟨normalizationSteps, prefixSteps, finalTape, ?_,
              finalRepresents, ?_, prefixBound⟩
          · exact
              AcceptPath.trans graph (.node outputFirstRef)
                (.node rawInitialPopRef) (.node beginOutputRef)
                normalizationSteps prefixSteps initialTape normalizedTape
                finalTape normalizationPath prefixPath
          · simpa [outputNormalizationUniformEnvelope, raw, runtime,
              physicalCapturedRuntime, markedSource,
              outputCrossedCells_eq,
              TargetEmitterControllerTrace.sourceKind,
              TargetEmitterControllerGateTrace.sourceValue] using
              normalizationBound

private structure PrefixRegisterStable
    (initial : Runtime)
    (result : TargetEmitterSemanticPrefix.PrefixRun) : Prop where
  inputCount :
    result.runtime.registers.inputCount =
      initial.registers.inputCount
  normalizedGateCount :
    result.runtime.registers.normalizedGateCount =
      initial.registers.normalizedGateCount
  carrierWidth :
    result.runtime.registers.carrierWidth =
      initial.registers.carrierWidth
  baseline :
    result.runtime.registers.baseline =
      initial.registers.baseline
  currentGate :
    result.runtime.registers.currentGate =
      initial.registers.currentGate

private theorem runPrefix_registerStable
    (coordinates : List Nat) (runtime : Runtime) :
    PrefixRegisterStable runtime
      (TargetEmitterSemanticPrefix.runPrefix coordinates runtime) := by
  induction coordinates generalizing runtime with
  | nil =>
      rw [TargetEmitterSemanticPrefix.runPrefix]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | cons head rest inductionHypothesis =>
      cases rest with
      | nil =>
          rw [TargetEmitterSemanticPrefix.runPrefix]
          exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      | cons next tail =>
          let tailInput : Runtime :=
            { runtime with checks := next :: tail }
          have stableTail :
              PrefixRegisterStable tailInput
                (TargetEmitterSemanticPrefix.runPrefix
                  (next :: tail) tailInput) :=
            inductionHypothesis tailInput
          cases tail with
          | nil =>
              rw [TargetEmitterSemanticPrefix.runPrefix]
              refine
                { inputCount := ?_
                  normalizedGateCount := ?_
                  carrierWidth := ?_
                  baseline := ?_
                  currentGate := ?_ }
              · rw [
                  TargetEmitterProgramSemantics.firstPrefixResult_registers]
                exact stableTail.inputCount
              · rw [
                  TargetEmitterProgramSemantics.firstPrefixResult_registers]
                exact stableTail.normalizedGateCount
              · rw [
                  TargetEmitterProgramSemantics.firstPrefixResult_registers]
                exact stableTail.carrierWidth
              · rw [
                  TargetEmitterProgramSemantics.firstPrefixResult_registers]
                exact stableTail.baseline
              · rw [
                  TargetEmitterProgramSemantics.firstPrefixResult_registers]
                exact stableTail.currentGate
          | cons third more =>
              rw [TargetEmitterSemanticPrefix.runPrefix]
              refine
                { inputCount := ?_
                  normalizedGateCount := ?_
                  carrierWidth := ?_
                  baseline := ?_
                  currentGate := ?_ }
              · rw [
                  TargetEmitterProgramSemantics.nextPrefixResult_registers]
                exact stableTail.inputCount
              · rw [
                  TargetEmitterProgramSemantics.nextPrefixResult_registers]
                exact stableTail.normalizedGateCount
              · rw [
                  TargetEmitterProgramSemantics.nextPrefixResult_registers]
                exact stableTail.carrierWidth
              · rw [
                  TargetEmitterProgramSemantics.nextPrefixResult_registers]
                exact stableTail.baseline
              · rw [
                  TargetEmitterProgramSemantics.nextPrefixResult_registers]
                exact stableTail.currentGate

private theorem runPrefix_outputIndex
    (coordinates : List Nat) (runtime : Runtime) :
    (TargetEmitterSemanticPrefix.runPrefix
          coordinates runtime).runtime.registers.outputIndex =
      runtime.registers.outputIndex +
        (2 * (coordinates.length - 1) - 1) := by
  induction coordinates generalizing runtime with
  | nil =>
      simp [TargetEmitterSemanticPrefix.runPrefix]
  | cons head rest inductionHypothesis =>
      cases rest with
      | nil =>
          simp [TargetEmitterSemanticPrefix.runPrefix]
      | cons next tail =>
          let tailInput : Runtime :=
            { runtime with checks := next :: tail }
          have tailOutput :=
            inductionHypothesis tailInput
          have tailOutput' :
              (TargetEmitterSemanticPrefix.runPrefix
                    (next :: tail) tailInput).runtime.registers.outputIndex =
                runtime.registers.outputIndex +
                  (2 * ((next :: tail).length - 1) - 1) := by
            simpa [tailInput] using tailOutput
          cases tail with
          | nil =>
              rw [TargetEmitterSemanticPrefix.runPrefix,
                TargetEmitterProgramSemantics.firstPrefixResult_registers]
              change
                (TargetEmitterSemanticPrefix.runPrefix
                    [next] tailInput).runtime.registers.outputIndex + 1 =
                  runtime.registers.outputIndex + 1
              rw [tailOutput']
              simp
          | cons third more =>
              rw [TargetEmitterSemanticPrefix.runPrefix,
                TargetEmitterProgramSemantics.nextPrefixResult_registers]
              rw [tailOutput']
              simp only [List.length_cons]
              omega

private theorem prefixRun_outputIndex_le
    (raw : RawCircuit) :
    (TargetEmitterSemanticCompletion.prefixRun
          raw).runtime.registers.outputIndex ≤
      TargetEmitterLedger.baselineValue raw + 4 := by
  have outputIndexEq :=
    runPrefix_outputIndex
      (TargetEmitterSemanticCompletion.checkCoordinates raw)
      (TargetEmitterSemanticNormalization.normalizationRuntime raw)
  have normalizationOutput :
      (TargetEmitterSemanticNormalization.normalizationRuntime
          raw).registers.outputIndex =
        (RawBuilder.macroAssembly raw.normalize).gates.length := by
    simpa using congrArg
        (fun registers : TargetEmitter.UnaryRegisters =>
          registers.outputIndex)
        (normalizationRuntime_registers_constructive raw)
  have coordinatesLength :
      (TargetEmitterSemanticCompletion.checkCoordinates raw).length =
        3 * raw.normalize.gates.length := by
    simpa [TargetEmitterSemanticCompletion.checkCoordinates] using
      (TargetEmitterSemanticPrefix.macroAssembly_checkCoordinates_length
        raw.normalize)
  rw [TargetEmitterSemanticCompletion.prefixRun, outputIndexEq,
    normalizationOutput, coordinatesLength,
    RawBuilder.macroAssembly_gates_length,
    TargetEmitterLedger.baselineValue_eq_rawBuilder_formula]
  omega

private theorem prefixRun_range
    (raw : RawCircuit) :
    ControllerRange raw
      (TargetEmitterSemanticCompletion.prefixRun
        raw).runtime.registers := by
  have initialRange := normalizationRuntime_range raw
  have stable :=
    runPrefix_registerStable
      (TargetEmitterSemanticCompletion.checkCoordinates raw)
      (TargetEmitterSemanticNormalization.normalizationRuntime raw)
  refine
    { inputCount_eq :=
        stable.inputCount.trans initialRange.inputCount_eq
      normalizedGateCount_eq :=
        stable.normalizedGateCount.trans
          initialRange.normalizedGateCount_eq
      carrierWidth_eq :=
        stable.carrierWidth.trans initialRange.carrierWidth_eq
      baseline_eq :=
        stable.baseline.trans initialRange.baseline_eq
      currentGate_le := ?_
      outputIndex_le := prefixRun_outputIndex_le raw }
  rw [show
    (TargetEmitterSemanticCompletion.prefixRun
        raw).runtime.registers.currentGate =
      (TargetEmitterSemanticNormalization.normalizationRuntime
        raw).registers.currentGate by
      simpa [TargetEmitterSemanticCompletion.prefixRun] using
        stable.currentGate]
  exact initialRange.currentGate_le

/-- The semantic prefix/final boundary preserves the source-derived unary
register range needed by the closed output polynomial accounting. -/
theorem finalRuntime_range
    (raw : RawCircuit) :
    ControllerRange raw
      (TargetEmitterSemanticCompletion.finalRuntime raw).registers := by
  by_cases empty :
      TargetEmitterSemanticCompletion.checkCoordinates raw = []
  · simpa [TargetEmitterSemanticCompletion.finalRuntime, empty,
      TargetEmitterProgramSemantics.finalResult_registers] using
      (prefixRun_range raw)
  · simpa [TargetEmitterSemanticCompletion.finalRuntime, empty,
      TargetEmitterProgramSemantics.finalResult_registers] using
      (prefixRun_range raw)

private theorem finalRuntime_scratch
    (raw : RawCircuit) :
    (TargetEmitterSemanticCompletion.finalRuntime raw).scratch = 0 := by
  by_cases empty :
      TargetEmitterSemanticCompletion.checkCoordinates raw = []
  · simp [TargetEmitterSemanticCompletion.finalRuntime, empty,
      TargetEmitterProgramSemantics.finalResult_scratch]
  · simp [TargetEmitterSemanticCompletion.finalRuntime, empty,
      TargetEmitterProgramSemantics.finalResult_scratch]

/-- Closed final-output charge at the exact semantic prefix boundary. -/
def controllerOutputUniformEnvelope (raw : RawCircuit) : Nat :=
  TargetEmitterControllerOutputBound.outputUniformEnvelope
    (TargetEmitterLedger.slotCapacity raw)
    (markedSource raw)
    (TargetEmitterSemanticCompletion.finalRuntime raw)

private theorem beginOutput_to_accept_path
    (raw : RawCircuit) (initialTape : WorkTape)
    (represents :
      TapeRepresents beginOutputRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterSemanticCompletion.finalRuntime raw).scratch
        (TargetEmitterSemanticCompletion.finalRuntime raw).registers
        (TargetEmitterSemanticCompletion.finalRuntime raw).checks
        (markedSource raw)
        (TargetEmitterSemanticCompletion.finalRuntime raw).targetTokens
        initialTape) :
    ∃ outputSteps finalTape,
      AcceptPath graph (.node beginOutputRef) .accept
        outputSteps initialTape finalTape ∧
      TargetEmitterControllerOutputTrace.FinalTapeRepresents
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterSemanticCompletion.completeRuntime raw).scratch
        (TargetEmitterSemanticCompletion.completeRuntime raw).registers
        (TargetEmitterSemanticCompletion.completeRuntime raw).checks
        (markedSource raw)
        (TargetEmitterSemanticCompletion.completeRuntime raw).targetTokens
        finalTape ∧
      outputSteps ≤ controllerOutputUniformEnvelope raw := by
  have range := finalRuntime_range raw
  have reserve :=
    TargetEmitterCapacity.baseline_add_four_lt_slotCapacity raw
  have scratchBound :
      (TargetEmitterSemanticCompletion.finalRuntime raw).scratch <
        TargetEmitterLedger.slotCapacity raw := by
    rw [finalRuntime_scratch]
    omega
  have finishRoom :
      (TargetEmitterSemanticCompletion.finalRuntime
            raw).registers.baseline + 3 <
        TargetEmitterLedger.slotCapacity raw := by
    rw [range.baseline_eq]
    omega
  have baselineBound :
      (TargetEmitterSemanticCompletion.finalRuntime
            raw).registers.baseline ≤
        TargetEmitterLedger.slotCapacity raw := by
    rw [range.baseline_eq]
    omega
  rcases
      TargetEmitterControllerOutputBound.outputPhaseToAccept_path_bounded
        (TargetEmitterLedger.slotCapacity raw)
        (markedSource raw)
        (outputWorkspace raw).context
        (outputWorkspace raw).cursor
        (TargetEmitterSemanticCompletion.finalRuntime raw)
        initialTape range.ledgerFits scratchBound finishRoom represents with
    ⟨outputSteps, finalTape, path, finalRepresents, outputBound⟩
  have uniformBound :=
    TargetEmitterControllerOutputBound.outputPhaseEnvelope_le_uniform
      (TargetEmitterLedger.slotCapacity raw)
      (markedSource raw)
      (TargetEmitterSemanticCompletion.finalRuntime raw)
      baselineBound
  refine ⟨outputSteps, finalTape, path, ?_,
    Nat.le_trans outputBound uniformBound⟩
  simpa [TargetEmitterSemanticCompletion.completeRuntime,
    TargetEmitterSemanticOutput.completeOutputResult] using
    finalRepresents

/-- Closed controller charge obtained by summing the independently uniform
gate-list, normalization, prefix, and final-output envelopes. -/
def controllerUniformEnvelope (raw : RawCircuit) : Nat :=
  TargetEmitterControllerGateListTrace.stackGateListUniformEnvelope raw +
    outputNormalizationUniformEnvelope raw +
    controllerPrefixUniformEnvelope raw +
    controllerOutputUniformEnvelope raw

/-- Exact physical controller completion together with one closed bound whose
statement contains no caller-supplied schedule or certificate. -/
theorem controller_complete_path_bounded
    (raw : RawCircuit) :
    ∃ gateListSteps normalizationSteps prefixSteps outputSteps finalTape,
      AcceptPath graph (.node stackInitializeRef) .accept
        (gateListSteps + normalizationSteps + prefixSteps + outputSteps)
        (TargetEmitterLedger.finalConfiguration raw).tape finalTape ∧
      TargetEmitterControllerOutputTrace.FinalTapeRepresents
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterSemanticCompletion.completeRuntime raw).scratch
        (TargetEmitterSemanticCompletion.completeRuntime raw).registers
        (TargetEmitterSemanticCompletion.completeRuntime raw).checks
        (markedSource raw)
        (TargetEmitterSemanticCompletion.completeRuntime raw).targetTokens
        finalTape ∧
      gateListSteps + normalizationSteps + prefixSteps + outputSteps ≤
        controllerUniformEnvelope raw := by
  rcases
      TargetEmitterControllerGateListTrace.stack_gateList_to_output_path_uniform_bounded
        raw with
    ⟨gateListSteps, outputTape, gateListPath, outputRepresents,
      gateListBound⟩
  rcases
      gateList_to_beginOutput_path raw outputTape outputRepresents with
    ⟨normalizationSteps, prefixSteps, beginTape,
      beginPath, beginRepresents, normalizationBound, prefixBound⟩
  rcases
      beginOutput_to_accept_path raw beginTape beginRepresents with
    ⟨outputSteps, finalTape, outputPath, finalRepresents, outputBound⟩
  refine
    ⟨gateListSteps, normalizationSteps, prefixSteps, outputSteps,
      finalTape, ?_, finalRepresents, ?_⟩
  · have toBegin :=
      AcceptPath.trans graph (.node stackInitializeRef)
        (.node outputFirstRef) (.node beginOutputRef)
        gateListSteps (normalizationSteps + prefixSteps)
        (TargetEmitterLedger.finalConfiguration raw).tape
        outputTape beginTape gateListPath beginPath
    have complete :=
      AcceptPath.trans graph (.node stackInitializeRef)
        (.node beginOutputRef) .accept
        (gateListSteps + (normalizationSteps + prefixSteps)) outputSteps
        (TargetEmitterLedger.finalConfiguration raw).tape
        beginTape finalTape toBegin outputPath
    simpa [Nat.add_assoc] using complete
  · unfold controllerUniformEnvelope
    omega

/-- Exact physical controller completion for every raw circuit.  The four
step components expose the gate-list, output-normalization, prefix/final, and
output-loop portions without requiring a caller-supplied schedule. -/
theorem controller_complete_path
    (raw : RawCircuit) :
    ∃ gateListSteps normalizationSteps prefixSteps outputSteps finalTape,
      AcceptPath graph (.node stackInitializeRef) .accept
        (gateListSteps + normalizationSteps + prefixSteps + outputSteps)
        (TargetEmitterLedger.finalConfiguration raw).tape finalTape ∧
      TargetEmitterControllerOutputTrace.FinalTapeRepresents
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterSemanticCompletion.completeRuntime raw).scratch
        (TargetEmitterSemanticCompletion.completeRuntime raw).registers
        (TargetEmitterSemanticCompletion.completeRuntime raw).checks
        (markedSource raw)
        (TargetEmitterSemanticCompletion.completeRuntime raw).targetTokens
        finalTape := by
  rcases
      TargetEmitterControllerGateListTrace.stack_gateList_to_output_path raw
    with ⟨gateListSteps, outputTape, gateListPath, outputRepresents⟩
  rcases
      gateList_to_beginOutput_path raw outputTape outputRepresents with
    ⟨normalizationSteps, prefixSteps, beginTape,
      beginPath, beginRepresents, _, _⟩
  rcases
      beginOutput_to_accept_path raw beginTape beginRepresents with
    ⟨outputSteps, finalTape, outputPath, finalRepresents, _⟩
  refine
    ⟨gateListSteps, normalizationSteps, prefixSteps, outputSteps,
      finalTape, ?_, finalRepresents⟩
  have toBegin :=
    AcceptPath.trans graph (.node stackInitializeRef)
      (.node outputFirstRef) (.node beginOutputRef)
      gateListSteps (normalizationSteps + prefixSteps)
      (TargetEmitterLedger.finalConfiguration raw).tape
      outputTape beginTape gateListPath beginPath
  have complete :=
    AcceptPath.trans graph (.node stackInitializeRef)
      (.node beginOutputRef) .accept
      (gateListSteps + (normalizationSteps + prefixSteps)) outputSteps
      (TargetEmitterLedger.finalConfiguration raw).tape
      beginTape finalTape toBegin outputPath
  simpa [Nat.add_assoc] using complete

private def workTail : List WorkSymbol → List WorkSymbol
  | [] => []
  | _ :: rest => rest

private theorem workTail_blankCellAt
    (word : List WorkSymbol) (index : Nat) :
    WorkTape.blankCellAt (workTail word) index =
      WorkTape.blankCellAt word (index + 1) := by
  cases word <;> rfl

private theorem encodeWorkRight_blankCellAt_zero
    (word : List WorkSymbol) :
    Tape.blankCellAt (encodeWorkRight word) 0 =
      (WorkTape.blankCellAt word 0).first := by
  cases word <;> rfl

private theorem encodeWorkRight_blankCellAt_one
    (word : List WorkSymbol) :
    Tape.blankCellAt (encodeWorkRight word) 1 =
      (WorkTape.blankCellAt word 0).second := by
  cases word <;> rfl

private theorem encodeWorkRight_blankCellAt_add_two
    (word : List WorkSymbol) (index : Nat) :
    Tape.blankCellAt (encodeWorkRight word) (index + 2) =
      Tape.blankCellAt (encodeWorkRight (workTail word)) index := by
  cases word <;> rfl

private theorem encodeWorkLeft_blankCellAt_zero
    (word : List WorkSymbol) :
    Tape.blankCellAt (encodeWorkLeft word) 0 =
      (WorkTape.blankCellAt word 0).second := by
  cases word <;> rfl

private theorem encodeWorkLeft_blankCellAt_one
    (word : List WorkSymbol) :
    Tape.blankCellAt (encodeWorkLeft word) 1 =
      (WorkTape.blankCellAt word 0).first := by
  cases word <;> rfl

private theorem encodeWorkLeft_blankCellAt_add_two
    (word : List WorkSymbol) (index : Nat) :
    Tape.blankCellAt (encodeWorkLeft word) (index + 2) =
      Tape.blankCellAt (encodeWorkLeft (workTail word)) index := by
  cases word <;> rfl

private theorem encodeWorkRight_blankCellAt_eq
    {first second : List WorkSymbol}
    (equivalent :
      ∀ index,
        WorkTape.blankCellAt first index =
          WorkTape.blankCellAt second index)
    (index : Nat) :
    Tape.blankCellAt (encodeWorkRight first) index =
      Tape.blankCellAt (encodeWorkRight second) index := by
  cases index with
  | zero =>
      rw [encodeWorkRight_blankCellAt_zero,
        encodeWorkRight_blankCellAt_zero, equivalent 0]
  | succ index =>
      cases index with
      | zero =>
          rw [encodeWorkRight_blankCellAt_one,
            encodeWorkRight_blankCellAt_one, equivalent 0]
      | succ index =>
          rw [show index + 1 + 1 = index + 2 by omega,
            encodeWorkRight_blankCellAt_add_two,
            encodeWorkRight_blankCellAt_add_two]
          apply encodeWorkRight_blankCellAt_eq
          intro tailIndex
          rw [workTail_blankCellAt, workTail_blankCellAt]
          exact equivalent (tailIndex + 1)
termination_by index

private theorem encodeWorkLeft_blankCellAt_eq
    {first second : List WorkSymbol}
    (equivalent :
      ∀ index,
        WorkTape.blankCellAt first index =
          WorkTape.blankCellAt second index)
    (index : Nat) :
    Tape.blankCellAt (encodeWorkLeft first) index =
      Tape.blankCellAt (encodeWorkLeft second) index := by
  cases index with
  | zero =>
      rw [encodeWorkLeft_blankCellAt_zero,
        encodeWorkLeft_blankCellAt_zero, equivalent 0]
  | succ index =>
      cases index with
      | zero =>
          rw [encodeWorkLeft_blankCellAt_one,
            encodeWorkLeft_blankCellAt_one, equivalent 0]
      | succ index =>
          rw [show index + 1 + 1 = index + 2 by omega,
            encodeWorkLeft_blankCellAt_add_two,
            encodeWorkLeft_blankCellAt_add_two]
          apply encodeWorkLeft_blankCellAt_eq
          intro tailIndex
          rw [workTail_blankCellAt, workTail_blankCellAt]
          exact equivalent (tailIndex + 1)
termination_by index

private theorem encodeWorkTape_blankEquivalent
    {first second : WorkTape}
    (equivalent : WorkTape.BlankEquivalent first second) :
    Tape.BlankEquivalent
      (encodeWorkTape first) (encodeWorkTape second) := by
  refine ⟨?_, ?_, ?_⟩
  · change first.head.first = second.head.first
    exact congrArg WorkSymbol.first equivalent.head
  · intro index
    change
      Tape.blankCellAt (encodeWorkLeft first.left) index =
        Tape.blankCellAt (encodeWorkLeft second.left) index
    exact encodeWorkLeft_blankCellAt_eq equivalent.left index
  · intro index
    cases index with
    | zero =>
        change first.head.second = second.head.second
        exact congrArg WorkSymbol.second equivalent.head
    | succ index =>
        change
          Tape.blankCellAt (encodeWorkRight first.right) index =
            Tape.blankCellAt (encodeWorkRight second.right) index
        exact encodeWorkRight_blankCellAt_eq equivalent.right index

/-- Blank-equivalent work tapes have the same finite decoded output word. -/
theorem encodeWorkTape_outputBits_eq_of_blankEquivalent
    {first second : WorkTape}
    (equivalent : WorkTape.BlankEquivalent first second) :
    (encodeWorkTape first).outputBits =
      (encodeWorkTape second).outputBits := by
  exact Tape.outputBits_eq_of_blankEquivalent
    (encodeWorkTape_blankEquivalent equivalent)

/-- The exact accepting path exposes the complete semantic runtime's encoded
token word on the actual reached tape, independently of finite exterior blank
materialization. -/
theorem controller_complete_path_output
    (raw : RawCircuit) :
    ∃ gateListSteps normalizationSteps prefixSteps outputSteps finalTape,
      AcceptPath graph (.node stackInitializeRef) .accept
        (gateListSteps + normalizationSteps + prefixSteps + outputSteps)
        (TargetEmitterLedger.finalConfiguration raw).tape finalTape ∧
      TargetEmitterControllerOutputTrace.FinalTapeRepresents
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterSemanticCompletion.completeRuntime raw).scratch
        (TargetEmitterSemanticCompletion.completeRuntime raw).registers
        (TargetEmitterSemanticCompletion.completeRuntime raw).checks
        (markedSource raw)
      (TargetEmitterSemanticCompletion.completeRuntime raw).targetTokens
        finalTape ∧
      (encodeWorkTape finalTape).outputBits =
        encodeTokens
          (TargetEmitterSemanticCompletion.completeRuntime
            raw).targetTokens := by
  rcases controller_complete_path raw with
    ⟨gateListSteps, normalizationSteps, prefixSteps, outputSteps,
      finalTape, path, finalRepresents⟩
  have equivalent :
      WorkTape.BlankEquivalent finalTape
        (TargetEmitterCursorFinalizer.finalTape
          (markedSource raw)
          (SourceParser.packedTokenCells
            (TargetEmitterSemanticCompletion.completeRuntime
              raw).targetTokens)
          (TargetEmitterRuntimePrimitives.fixedWorkspace
            (TargetEmitterLedger.slotCapacity raw)
            (TargetEmitterSemanticCompletion.completeRuntime raw).scratch
            (TargetEmitterSemanticCompletion.completeRuntime raw).registers
            (TargetEmitterSemanticCompletion.completeRuntime raw).checks)
          []) := by
    simpa [TargetEmitterControllerOutputTrace.FinalTapeRepresents] using
      finalRepresents
  have observed :=
    encodeWorkTape_outputBits_eq_of_blankEquivalent equivalent
  have canonical :=
    TargetEmitterControllerOutputTrace.canonicalFinal_output_eq
      (markedSource raw)
      (TargetEmitterSemanticCompletion.completeRuntime raw).targetTokens
      (TargetEmitterLedger.slotCapacity raw)
      (TargetEmitterSemanticCompletion.completeRuntime raw).scratch
      (TargetEmitterSemanticCompletion.completeRuntime raw).registers
      (TargetEmitterSemanticCompletion.completeRuntime raw).checks
  refine
    ⟨gateListSteps, normalizationSteps, prefixSteps, outputSteps,
      finalTape, path, finalRepresents, ?_⟩
  exact observed.trans canonical

end PNP.Concrete.LockedNAND.TargetEmitterControllerCompletionTrace
