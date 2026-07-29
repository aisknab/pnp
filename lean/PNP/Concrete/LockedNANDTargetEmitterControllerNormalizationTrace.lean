/-
Copyright (c) 2026 PNP Labs.

Exact materialized normalization-block paths for the fixed grammar-only
locked-NAND target emitter.
-/

import PNP.Concrete.LockedNANDTargetEmitterControllerGateTrace

namespace PNP.Concrete.LockedNAND.TargetEmitterControllerNormalizationTrace

open PNP.Concrete
open WorkMachineProgramGraph
open WorkMachineProgramPath
open TargetEmitterController
open TargetEmitterPrimitiveCompiler
open TargetEmitterBlockCompiler

set_option maxRecDepth 100000

abbrev Runtime := TargetEmitterProgramSemantics.Runtime
abbrev SourceKind := TargetEmitterPlan.SourceKind
abbrev MarkedWorkspace :=
  TargetEmitterRuntimeProgramSafety.MarkedWorkspace
abbrev CapturedReady :=
  TargetEmitterRuntimeProgramSafety.CapturedReady
abbrev InputNormalizationRanges :=
  TargetEmitterRuntimeProgramSafety.InputNormalizationRanges
abbrev ConstantNormalizationRanges :=
  TargetEmitterRuntimeProgramSafety.ConstantNormalizationRanges
abbrev TapeRepresents :=
  TargetEmitterControllerGateTrace.TapeRepresents
abbrev FocusTapeRepresents :=
  TargetEmitterControllerGateTrace.FocusTapeRepresents

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

private def inputDescriptor : BlockDescriptor :=
  { code := Block.inputNormalization
    primitives := Plan.inputNormalization
    continuation := .node normalizedInitialPopRef }

private def constantDescriptor (value : Bool) : BlockDescriptor :=
  { code :=
      if value then Block.constantTrueNormalization
      else Block.constantFalseNormalization
    primitives := Plan.constantNormalization value
    continuation := .node normalizedInitialPopRef }

private def resetDescriptor : BlockDescriptor :=
  { code := Block.outputGateReset
    primitives := Plan.outputGateReset
    continuation := .node rawInitialPopRef }

private def inputPrograms : List WorkMachine :=
  (compileProgram Plan.inputNormalization).getD []

private def constantPrograms (value : Bool) : List WorkMachine :=
  (compileProgram (Plan.constantNormalization value)).getD []

private def resetPrograms : List WorkMachine :=
  (compileProgram Plan.outputGateReset).getD []

private theorem inputDescriptor_member :
    inputDescriptor ∈ blockDescriptors := by
  simp [inputDescriptor, blockDescriptors, fixedBlockDescriptors]

private theorem constantDescriptor_member (value : Bool) :
    constantDescriptor value ∈ blockDescriptors := by
  cases value <;>
    simp [constantDescriptor, blockDescriptors, fixedBlockDescriptors]

private theorem resetDescriptor_member :
    resetDescriptor ∈ blockDescriptors := by
  simp [resetDescriptor, blockDescriptors, fixedBlockDescriptors]

private theorem input_compiled :
    compileProgram Plan.inputNormalization =
      some inputPrograms := by
  rfl

private theorem constant_compiled (value : Bool) :
    compileProgram (Plan.constantNormalization value) =
      some (constantPrograms value) := by
  cases value <;> rfl

private theorem reset_compiled :
    compileProgram Plan.outputGateReset =
      some resetPrograms := by
  rfl

private theorem input_nonempty : inputPrograms ≠ [] := by
  decide

private theorem constant_nonempty (value : Bool) :
    constantPrograms value ≠ [] := by
  cases value <;> decide

private theorem reset_nonempty : resetPrograms ≠ [] := by
  decide

private theorem input_startState :
    inputNormalizationRef.startState =
      TargetEmitterRuntimeProgram.entryState 0 inputPrograms := by
  rfl

private theorem constant_startState (value : Bool) :
    (if value then constantTrueNormalizationRef
      else constantFalseNormalizationRef).startState =
      TargetEmitterRuntimeProgram.entryState 0
        (constantPrograms value) := by
  cases value <;> rfl

private theorem constant_blockEntry (value : Bool) :
    blockEntry
        (if value then Block.constantTrueNormalization
          else Block.constantFalseNormalization)
        (Plan.constantNormalization value) =
      (if value then constantTrueNormalizationRef
        else constantFalseNormalizationRef) := by
  cases value <;> rfl

private theorem reset_startState :
    outputGateResetRef.startState =
      TargetEmitterRuntimeProgram.entryState 0 resetPrograms := by
  rfl

/-- Execute the fixed six-macro input-output normalization block. -/
theorem inputNormalizationBlock_path
    {raw : RawCircuit} {source : List WorkSymbol}
    (workspace : MarkedWorkspace source)
    (runtime : Runtime)
    (ranges : InputNormalizationRanges raw runtime)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (captured : CapturedReady raw source runtime.captured)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents inputNormalizationRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node inputNormalizationRef)
          (.node normalizedInitialPopRef) steps initialTape finalTape ∧
      TapeRepresents normalizedInitialPopRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterProgramSemantics.inputNormalizationResult
          runtime).scratch
        (TargetEmitterProgramSemantics.inputNormalizationResult
          runtime).registers
        (TargetEmitterProgramSemantics.inputNormalizationResult
          runtime).checks
        source
        (TargetEmitterProgramSemantics.inputNormalizationResult
          runtime).targetTokens finalTape := by
  let initial : WorkConfiguration :=
    { state :=
        TargetEmitterRuntimeProgram.entryState 0 inputPrograms
      tape := initialTape }
  have inputRepresents :
      TargetEmitterRuntime.Represents initial.state
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initial := by
    exact represents_at_state represents
  have safe :=
    TargetEmitterRuntimeProgramSafety.inputNormalization_safe
      workspace ranges capturedBound scratchBound captured
  rcases
      safe.descriptor_acceptPath_exact inputDescriptor
        inputDescriptor_member inputPrograms
        (by simpa [inputDescriptor] using input_compiled)
        input_nonempty 0 initial inputRepresents with
    ⟨steps, actualFinal, path, finalRepresents⟩
  refine ⟨steps, actualFinal.tape, ?_, ?_⟩
  · simpa [inputDescriptor, inputNormalizationRef] using path
  · exact
      represents_at_state
        (newState := normalizedInitialPopRef.startState)
        finalRepresents

/-- Execute either fixed three-macro constant-output normalization block. -/
theorem constantNormalizationBlock_path
    {raw : RawCircuit} {source : List WorkSymbol}
    (value : Bool)
    (workspace : MarkedWorkspace source)
    (runtime : Runtime)
    (ranges : ConstantNormalizationRanges raw value runtime)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents
        (if value then constantTrueNormalizationRef
          else constantFalseNormalizationRef).startState
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph
          (.node
            (if value then constantTrueNormalizationRef
              else constantFalseNormalizationRef))
          (.node normalizedInitialPopRef) steps initialTape finalTape ∧
      TapeRepresents normalizedInitialPopRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterProgramSemantics.constantNormalizationResult
          value runtime).scratch
        (TargetEmitterProgramSemantics.constantNormalizationResult
          value runtime).registers
        (TargetEmitterProgramSemantics.constantNormalizationResult
          value runtime).checks
        source
        (TargetEmitterProgramSemantics.constantNormalizationResult
          value runtime).targetTokens finalTape := by
  let programs := constantPrograms value
  let entry :=
    if value then constantTrueNormalizationRef
    else constantFalseNormalizationRef
  let initial : WorkConfiguration :=
    { state := TargetEmitterRuntimeProgram.entryState 0 programs
      tape := initialTape }
  have inputRepresents :
      TargetEmitterRuntime.Represents initial.state
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initial := by
    exact represents_at_state represents
  have safe :=
    TargetEmitterRuntimeProgramSafety.constantNormalization_safe
      value workspace ranges capturedBound scratchBound
  rcases
      safe.descriptor_acceptPath_exact
        (constantDescriptor value)
        (constantDescriptor_member value) programs
        (by simpa [programs, constantDescriptor] using
          constant_compiled value)
        (by simpa [programs] using constant_nonempty value)
        0 initial inputRepresents with
    ⟨steps, actualFinal, path, finalRepresents⟩
  refine ⟨steps, actualFinal.tape, ?_, ?_⟩
  · simp only [constantDescriptor] at path
    rw [constant_blockEntry value] at path
    simpa [entry, constantDescriptor, initial] using path
  · exact
      represents_at_state
        (newState := normalizedInitialPopRef.startState)
        finalRepresents

/-- Reset scratch after capturing a gate-valued raw output and enter the raw
prefix check-pop branch. -/
theorem outputGateResetBlock_path
    {raw : RawCircuit} {source : List WorkSymbol}
    (context : TargetEmitterRuntimeProgram.SourceContext source)
    (runtime : Runtime)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents outputGateResetRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node outputGateResetRef)
          (.node rawInitialPopRef) steps initialTape finalTape ∧
      TapeRepresents rawInitialPopRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterProgramSemantics.resetScratchResult runtime).scratch
        (TargetEmitterProgramSemantics.resetScratchResult runtime).registers
        (TargetEmitterProgramSemantics.resetScratchResult runtime).checks
        source
        (TargetEmitterProgramSemantics.resetScratchResult runtime).targetTokens
        finalTape := by
  let initial : WorkConfiguration :=
    { state := TargetEmitterRuntimeProgram.entryState 0 resetPrograms
      tape := initialTape }
  have inputRepresents :
      TargetEmitterRuntime.Represents initial.state
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initial := by
    exact represents_at_state represents
  have safe :=
    TargetEmitterRuntimeProgramSafety.outputGateReset_safe
      context scratchBound
  rcases
      safe.descriptor_acceptPath_exact resetDescriptor
        resetDescriptor_member resetPrograms
        (by simpa [resetDescriptor] using reset_compiled)
        reset_nonempty 0 initial inputRepresents with
    ⟨steps, actualFinal, path, finalRepresents⟩
  refine ⟨steps, actualFinal.tape, ?_, ?_⟩
  · simpa [resetDescriptor, outputGateResetRef] using path
  · exact
      represents_at_state
        (newState := rawInitialPopRef.startState)
        finalRepresents

/-! ### Output classification followed by normalization -/

/-- Capture an input-valued circuit output and execute the fixed six-macro
normalization program.  The source cursor is retained in the exact marked
workspace used by the following prefix fold. -/
theorem outputInputNormalization_path
    {raw : RawCircuit}
    (runtime : Runtime) (index : Nat)
    (head : WorkSymbol) (prefixTail after : List WorkSymbol)
    (outputEq : raw.output = .input index)
    (scratchZero : runtime.scratch = 0)
    (ranges :
      InputNormalizationRanges raw
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
  have captureReserve :
      runtime.scratch +
          TargetEmitterControllerSourceTrace.capturedValue
            .input index +
          1 ≤
        TargetEmitterLedger.slotCapacity raw := by
    rw [scratchZero]
    simpa [TargetEmitterCapacity.sourceCaptureValue,
      TargetEmitterControllerSourceTrace.capturedValue] using
      (TargetEmitterCapacity.focusedSourceCaptureReserve
        outputMember)
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
  let workspace :
      MarkedWorkspace marked :=
    TargetEmitterControllerGateTrace.markedWorkspace
      .input index head prefixTail after originalPacked
  have capturedReady :
      CapturedReady raw marked captured.captured := by
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
      TapeRepresents inputNormalizationRef.startState
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
    simp only [
      TargetEmitterControllerSourceTrace.capturedValue] at reserve
    exact Nat.lt_of_succ_le reserve
  have capturedIndexBound :
      captured.captured + 1 ≤
        (SourceParser.circuitCells raw).length := by
    simpa [captured,
      TargetEmitterControllerGateTrace.capturedRuntime,
      TargetEmitterControllerSourceTrace.capturedValue] using
        capturedBound
  rcases
      inputNormalizationBlock_path workspace captured ranges
        capturedIndexBound capturedScratchBound capturedReady
        capturedTape capturedLogical with
    ⟨blockSteps, finalTape, blockPath, finalRepresents⟩
  refine ⟨
    TargetEmitterControllerGateTrace.sourceCapturePhaseSteps
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

/-- Capture a constant-valued circuit output and execute the corresponding
fixed three-macro normalization program. -/
theorem outputConstantNormalization_path
    {raw : RawCircuit}
    (runtime : Runtime) (value : Bool)
    (head : WorkSymbol) (prefixTail after : List WorkSymbol)
    (outputEq : raw.output = .constant value)
    (scratchZero : runtime.scratch = 0)
    (ranges :
      ConstantNormalizationRanges raw value
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
      TargetEmitterControllerGateTrace.capturedRuntime
        runtime kind 0
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
    TargetEmitterControllerGateTrace.capturedRuntime
      runtime kind 0
  have outputMember :
      TargetEmitterCapacity.CircuitSource raw
        (.constant value) := by
    rw [← outputEq]
    exact .output
  have captureReserve :
      runtime.scratch +
          TargetEmitterControllerSourceTrace.capturedValue kind 0 +
          1 ≤
        TargetEmitterLedger.slotCapacity raw := by
    rw [scratchZero]
    have reserve :=
      TargetEmitterCapacity.focusedSourceCaptureReserve
        outputMember
    cases value <;>
      simpa [kind, TargetEmitterCapacity.sourceCaptureValue,
        TargetEmitterControllerSourceTrace.capturedValue] using reserve
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
  let workspace :
      MarkedWorkspace marked :=
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
      TapeRepresents
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
      constantNormalizationBlock_path value workspace captured
        ranges capturedIndexBound capturedScratchBound
        capturedTape capturedLogical with
    ⟨blockSteps, finalTape, blockPath, finalRepresents⟩
  refine ⟨
    TargetEmitterControllerGateTrace.sourceCapturePhaseSteps
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

/-- Capture a gate-valued circuit output, reset the carried unary coordinate,
and enter the raw prefix branch. -/
theorem outputGateNormalization_path
    {raw : RawCircuit}
    (runtime : Runtime) (index : Nat)
    (head : WorkSymbol) (prefixTail after : List WorkSymbol)
    (outputEq : raw.output = .gate index)
    (scratchZero : runtime.scratch = 0)
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
  have captureReserve :
      runtime.scratch +
          TargetEmitterControllerSourceTrace.capturedValue
            .gate index +
          1 ≤
        TargetEmitterLedger.slotCapacity raw := by
    rw [scratchZero]
    simpa [TargetEmitterCapacity.sourceCaptureValue,
      TargetEmitterControllerSourceTrace.capturedValue] using
      (TargetEmitterCapacity.focusedSourceCaptureReserve
        outputMember)
  have beforePacked :
      ∀ symbol, symbol ∈ (head :: prefixTail) →
        TargetEmitter.PackedSymbol symbol := by
    intro symbol member
    apply originalPacked
    simp only [List.mem_append, List.mem_cons]
    have member' : symbol = head ∨ symbol ∈ prefixTail := by
      simpa only [List.mem_cons] using member
    exact Or.inl (Or.inl member')
  let workspace :
      MarkedWorkspace marked :=
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
      TapeRepresents outputGateResetRef.startState
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
      outputGateResetBlock_path workspace.context captured
        capturedScratchBound capturedTape capturedLogical with
    ⟨blockSteps, finalTape, blockPath, finalRepresents⟩
  refine ⟨
    TargetEmitterControllerGateTrace.sourceCapturePhaseSteps
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

end PNP.Concrete.LockedNAND.TargetEmitterControllerNormalizationTrace
