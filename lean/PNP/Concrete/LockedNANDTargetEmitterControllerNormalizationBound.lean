/-
Copyright (c) 2026 PNP Labs.

Constructive work bounds for the three fixed normalization programs of the
grammar-only locked-NAND target emitter.

The bounds reuse the literal primitive-program theorem.  They remain
parametric in the represented runtime so a later controller-wide induction
can supply one common polynomial footprint without exposing a trace schedule.
-/

import PNP.Concrete.LockedNANDTargetEmitterControllerNormalizationTrace
import PNP.Concrete.LockedNANDTargetEmitterRuntimeProgramBound

namespace PNP.Concrete.LockedNAND.TargetEmitterControllerNormalizationBound

open PNP.Concrete
open WorkMachineProgramGraph
open WorkMachineProgramPath
open TargetEmitterController
open TargetEmitterPrimitiveCompiler
open TargetEmitterBlockCompiler
open TargetEmitterPlan

set_option maxRecDepth 100000

abbrev Runtime := TargetEmitterProgramSemantics.Runtime
abbrev MarkedWorkspace :=
  TargetEmitterRuntimeProgramSafety.MarkedWorkspace
abbrev CapturedReady :=
  TargetEmitterRuntimeProgramSafety.CapturedReady
abbrev InputNormalizationRanges :=
  TargetEmitterRuntimeProgramSafety.InputNormalizationRanges
abbrev ConstantNormalizationRanges :=
  TargetEmitterRuntimeProgramSafety.ConstantNormalizationRanges
abbrev TapeRepresents :=
  TargetEmitterControllerNormalizationTrace.TapeRepresents
abbrev FocusTapeRepresents :=
  TargetEmitterControllerNormalizationTrace.FocusTapeRepresents

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

private theorem constant_blockEntry (value : Bool) :
    blockEntry
        (if value then Block.constantTrueNormalization
          else Block.constantFalseNormalization)
        (Plan.constantNormalization value) =
      (if value then constantTrueNormalizationRef
        else constantFalseNormalizationRef) := by
  cases value <;> rfl

/-- Runtime-sensitive primitive envelope for input-output normalization. -/
def inputNormalizationEnvelope (raw : RawCircuit)
    (source : List WorkSymbol) (runtime : Runtime) : Nat :=
  TargetEmitterRuntimeProgramBound.programWorkEnvelope
    (TargetEmitterLedger.slotCapacity raw) source runtime
    Plan.inputNormalization

/-- Runtime-sensitive primitive envelope for either constant-output
normalization branch. -/
def constantNormalizationEnvelope (raw : RawCircuit)
    (source : List WorkSymbol) (runtime : Runtime)
    (value : Bool) : Nat :=
  TargetEmitterRuntimeProgramBound.programWorkEnvelope
    (TargetEmitterLedger.slotCapacity raw) source runtime
    (Plan.constantNormalization value)

/-- Runtime-sensitive primitive envelope for the gate-output scratch reset. -/
def outputGateResetEnvelope (raw : RawCircuit)
    (source : List WorkSymbol) (runtime : Runtime) : Nat :=
  TargetEmitterRuntimeProgramBound.programWorkEnvelope
    (TargetEmitterLedger.slotCapacity raw) source runtime
    Plan.outputGateReset

/-- Closed polynomial expression dominating classification and literal source
capture.  Its three inputs are the retained prefix length, current scratch
value, and classified source coordinate. -/
def sourceCaptureEnvelope
    (beforeLength scratch value : Nat) : Nat :=
  value *
      (2 * (beforeLength + 2) + 2 * scratch + 3 * value + 7) +
    (beforeLength + 2) + 2 * value + 12

/-- Uniform quadratic source-capture polynomial for a common size majorant. -/
def sourceCaptureTimePolynomial : NatPolynomial :=
  let shifted : NatPolynomial :=
    .add .variable (.constant 1)
  .mul (.constant 15) (.mul shifted shifted)

theorem sourceCaptureTimePolynomial_eval (size : Nat) :
    sourceCaptureTimePolynomial.eval size =
      15 * (size + 1) * (size + 1) := by
  simp [sourceCaptureTimePolynomial, Nat.mul_assoc]

private theorem natLoopSteps_evaluated
    (prefixLength count remaining : Nat) :
    TargetEmitterSourceCapture.natLoopSteps
        prefixLength count remaining =
      remaining *
          (2 * prefixLength + 2 * count + 3 * remaining + 7) +
        prefixLength + 2 * remaining + 4 := by
  induction remaining generalizing prefixLength count with
  | zero =>
      simp [TargetEmitterSourceCapture.natLoopSteps,
        TargetEmitterSourceCapture.natFinishSteps]
  | succ remaining ih =>
      rw [TargetEmitterSourceCapture.natLoopSteps, ih]
      simp only [TargetEmitterSourceCapture.unitIterationSteps]
      simp only [Nat.add_mul, Nat.mul_add]
      omega

/-- Literal classifier-and-capture cost is bounded by the closed polynomial
combinator, with no caller-provided schedule. -/
theorem sourceCapturePhaseSteps_le_envelope
    (before : List WorkSymbol) (source : RawSource)
    (scratch : Nat) :
    TargetEmitterControllerGateTrace.sourceCapturePhaseSteps
        before source scratch ≤
      sourceCaptureEnvelope before.length scratch
        (TargetEmitterControllerGateTrace.sourceValue source) := by
  cases source with
  | input value =>
      simp [TargetEmitterControllerGateTrace.sourceCapturePhaseSteps,
        TargetEmitterControllerTrace.classifierSteps,
        TargetEmitterControllerTrace.sourceKind,
        TargetEmitterControllerGateTrace.sourceValue,
        TargetEmitterControllerSourceTrace.capturePathSteps,
        TargetEmitterControllerSourceTrace.captureWorkSteps,
        TargetEmitterSourceCapture.naturalWorkSteps,
        natLoopSteps_evaluated, sourceCaptureEnvelope]
      omega
  | gate value =>
      simp [TargetEmitterControllerGateTrace.sourceCapturePhaseSteps,
        TargetEmitterControllerTrace.classifierSteps,
        TargetEmitterControllerTrace.sourceKind,
        TargetEmitterControllerGateTrace.sourceValue,
        TargetEmitterControllerSourceTrace.capturePathSteps,
        TargetEmitterControllerSourceTrace.captureWorkSteps,
        TargetEmitterSourceCapture.naturalWorkSteps,
        natLoopSteps_evaluated, sourceCaptureEnvelope]
      omega
  | constant value =>
      cases value <;>
        simp [TargetEmitterControllerGateTrace.sourceCapturePhaseSteps,
          TargetEmitterControllerTrace.classifierSteps,
          TargetEmitterControllerTrace.sourceKind,
          TargetEmitterControllerGateTrace.sourceValue,
          TargetEmitterControllerSourceTrace.capturePathSteps,
          TargetEmitterControllerSourceTrace.captureWorkSteps,
          TargetEmitterSourceCapture.constantWorkSteps,
          sourceCaptureEnvelope]
      all_goals omega

/-- The closed capture envelope is quadratic in any common majorant of its
three runtime inputs. -/
theorem sourceCaptureEnvelope_le_timePolynomial
    {beforeLength scratch value size : Nat}
    (beforeBound : beforeLength ≤ size)
    (scratchBound : scratch ≤ size)
    (valueBound : value ≤ size) :
    sourceCaptureEnvelope beforeLength scratch value ≤
      sourceCaptureTimePolynomial.eval size := by
  have factorBound :
      2 * (beforeLength + 2) + 2 * scratch + 3 * value + 7 ≤
        7 * size + 11 := by
    omega
  have productBound :
      value *
          (2 * (beforeLength + 2) + 2 * scratch +
            3 * value + 7) ≤
        size * (7 * size + 11) :=
    Nat.mul_le_mul valueBound factorBound
  have tailBound :
      (beforeLength + 2) + 2 * value + 12 ≤
        3 * size + 14 := by
    omega
  have factorToShift :
      7 * size + 11 ≤ 15 * (size + 1) := by
    omega
  have productToShift :=
    Nat.mul_le_mul_left size factorToShift
  have tailToShift :
      3 * size + 14 ≤ 15 * (size + 1) := by
    omega
  rw [sourceCaptureTimePolynomial_eval]
  have combined :=
    Nat.add_le_add
      (Nat.le_trans productBound productToShift)
      (Nat.le_trans tailBound tailToShift)
  calc
    sourceCaptureEnvelope beforeLength scratch value ≤
        size * (15 * (size + 1)) + 15 * (size + 1) := by
      unfold sourceCaptureEnvelope
      omega
    _ = (size + 1) * (15 * (size + 1)) := by
      rw [Nat.add_mul]
      simp
    _ = 15 * (size + 1) * (size + 1) := by
      ac_rfl

/-- Direct controller cost corollary for a common size majorant. -/
theorem sourceCapturePhaseSteps_le_timePolynomial
    (before : List WorkSymbol) (source : RawSource)
    (scratch size : Nat)
    (beforeBound : before.length ≤ size)
    (scratchBound : scratch ≤ size)
    (valueBound :
      TargetEmitterControllerGateTrace.sourceValue source ≤ size) :
    TargetEmitterControllerGateTrace.sourceCapturePhaseSteps
        before source scratch ≤
      sourceCaptureTimePolynomial.eval size :=
  Nat.le_trans
    (sourceCapturePhaseSteps_le_envelope before source scratch)
    (sourceCaptureEnvelope_le_timePolynomial
      beforeBound scratchBound valueBound)

/-- Bounded form of the fixed six-macro input-output normalization block. -/
theorem inputNormalizationBlock_path_bounded
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
          runtime).targetTokens finalTape ∧
      steps ≤ inputNormalizationEnvelope raw source runtime := by
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
      TargetEmitterRuntimeProgramBound.ProgramSafe.descriptor_acceptPath_bounded
        inputDescriptor inputDescriptor_member safe
        (Nat.le_of_lt scratchBound) inputPrograms
        (by simpa [inputDescriptor] using input_compiled)
        input_nonempty 0 initial inputRepresents with
    ⟨steps, actualFinal, path, finalRepresents, bound⟩
  refine ⟨steps, actualFinal.tape, ?_, ?_, ?_⟩
  · simpa [inputDescriptor, inputNormalizationRef] using path
  · exact
      represents_at_state
        (newState := normalizedInitialPopRef.startState)
        finalRepresents
  · simpa [inputNormalizationEnvelope, inputDescriptor] using bound

/-- Bounded form of either fixed three-macro constant-output normalization
block. -/
theorem constantNormalizationBlock_path_bounded
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
          value runtime).targetTokens finalTape ∧
      steps ≤
        constantNormalizationEnvelope raw source runtime value := by
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
      TargetEmitterRuntimeProgramBound.ProgramSafe.descriptor_acceptPath_bounded
        (constantDescriptor value)
        (constantDescriptor_member value) safe
        (Nat.le_of_lt scratchBound) programs
        (by simpa [programs, constantDescriptor] using
          constant_compiled value)
        (by simpa [programs] using constant_nonempty value)
        0 initial inputRepresents with
    ⟨steps, actualFinal, path, finalRepresents, bound⟩
  refine ⟨steps, actualFinal.tape, ?_, ?_, ?_⟩
  · simp only [constantDescriptor] at path
    rw [constant_blockEntry value] at path
    simpa [entry, constantDescriptor, initial] using path
  · exact
      represents_at_state
        (newState := normalizedInitialPopRef.startState)
        finalRepresents
  · simpa [constantNormalizationEnvelope, constantDescriptor] using
      bound

/-- Bounded form of the gate-output scratch reset block. -/
theorem outputGateResetBlock_path_bounded
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
        finalTape ∧
      steps ≤ outputGateResetEnvelope raw source runtime := by
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
      TargetEmitterRuntimeProgramBound.ProgramSafe.descriptor_acceptPath_bounded
        resetDescriptor resetDescriptor_member safe
        (Nat.le_of_lt scratchBound) resetPrograms
        (by simpa [resetDescriptor] using reset_compiled)
        reset_nonempty 0 initial inputRepresents with
    ⟨steps, actualFinal, path, finalRepresents, bound⟩
  refine ⟨steps, actualFinal.tape, ?_, ?_, ?_⟩
  · simpa [resetDescriptor, outputGateResetRef] using path
  · exact
      represents_at_state
        (newState := rawInitialPopRef.startState)
        finalRepresents
  · simpa [outputGateResetEnvelope, resetDescriptor] using bound

/-! ### Output classification followed by normalization -/

/-- Capture an input-valued circuit output and execute its complete bounded
normalization block. -/
theorem outputInputNormalization_path_bounded
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
          captured).targetTokens finalTape ∧
      steps ≤
        sourceCaptureEnvelope (head :: prefixTail).length
            runtime.scratch index +
          inputNormalizationEnvelope raw marked captured := by
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
      inputNormalizationBlock_path_bounded workspace captured ranges
        capturedIndexBound capturedScratchBound capturedReady
        capturedTape capturedLogical with
    ⟨blockSteps, finalTape, blockPath, finalRepresents, blockBound⟩
  let steps :=
    TargetEmitterControllerGateTrace.sourceCapturePhaseSteps
        (head :: prefixTail) (.input index) runtime.scratch +
      blockSteps
  refine ⟨steps, finalTape, ?_, finalRepresents, ?_⟩
  · exact
      AcceptPath.trans graph (.node outputFirstRef)
        (.node inputNormalizationRef)
        (.node normalizedInitialPopRef)
        (TargetEmitterControllerGateTrace.sourceCapturePhaseSteps
          (head :: prefixTail) (.input index) runtime.scratch)
        blockSteps initialTape capturedTape finalTape
        capturePath blockPath
  · have captureBound :=
      sourceCapturePhaseSteps_le_envelope
        (head :: prefixTail) (.input index) runtime.scratch
    unfold steps
    simp only [TargetEmitterControllerGateTrace.sourceValue] at captureBound
    exact Nat.add_le_add captureBound blockBound

/-- Capture a constant-valued circuit output and execute the selected
three-macro normalization block with a constructive bound. -/
theorem outputConstantNormalization_path_bounded
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
          value captured).targetTokens finalTape ∧
      steps ≤
        sourceCaptureEnvelope (head :: prefixTail).length
            runtime.scratch 0 +
          constantNormalizationEnvelope raw marked captured value := by
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
      constantNormalizationBlock_path_bounded value workspace captured
        ranges capturedIndexBound capturedScratchBound
        capturedTape capturedLogical with
    ⟨blockSteps, finalTape, blockPath, finalRepresents, blockBound⟩
  let steps :=
    TargetEmitterControllerGateTrace.sourceCapturePhaseSteps
        (head :: prefixTail) (.constant value) runtime.scratch +
      blockSteps
  refine ⟨steps, finalTape, ?_, finalRepresents, ?_⟩
  · have capturePath' :
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
  · have captureBound :=
      sourceCapturePhaseSteps_le_envelope
        (head :: prefixTail) (.constant value) runtime.scratch
    unfold steps
    simp only [TargetEmitterControllerGateTrace.sourceValue] at captureBound
    exact Nat.add_le_add captureBound blockBound

/-- Capture a gate-valued circuit output, reset the carried coordinate, and
enter the raw prefix branch with a constructive bound. -/
theorem outputGateNormalization_path_bounded
    {raw : RawCircuit}
    (runtime : Runtime) (index : Nat)
    (head : WorkSymbol) (prefixTail after : List WorkSymbol)
    (_outputEq : raw.output = .gate index)
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
          captured).targetTokens finalTape ∧
      steps ≤
        sourceCaptureEnvelope (head :: prefixTail).length
            runtime.scratch index +
          outputGateResetEnvelope raw marked captured := by
  let marked :=
    (head :: prefixTail) ++
      TargetEmitterControllerSourceTrace.captureMarkedSourceCells
        .gate index ++ after
  let captured :=
    TargetEmitterControllerGateTrace.capturedRuntime
      runtime .gate index
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
      outputGateResetBlock_path_bounded workspace.context captured
        capturedScratchBound capturedTape capturedLogical with
    ⟨blockSteps, finalTape, blockPath, finalRepresents, blockBound⟩
  let steps :=
    TargetEmitterControllerGateTrace.sourceCapturePhaseSteps
        (head :: prefixTail) (.gate index) runtime.scratch +
      blockSteps
  refine ⟨steps, finalTape, ?_, finalRepresents, ?_⟩
  · exact
      AcceptPath.trans graph (.node outputFirstRef)
        (.node outputGateResetRef) (.node rawInitialPopRef)
        (TargetEmitterControllerGateTrace.sourceCapturePhaseSteps
          (head :: prefixTail) (.gate index) runtime.scratch)
        blockSteps initialTape capturedTape finalTape
        (by simpa [TargetEmitterControllerTrace.sourceKind,
          TargetEmitterController.outputCaptureContinuation] using
            capturePath)
        blockPath
  · have captureBound :=
      sourceCapturePhaseSteps_le_envelope
        (head :: prefixTail) (.gate index) runtime.scratch
    unfold steps
    simp only [TargetEmitterControllerGateTrace.sourceValue] at captureBound
    exact Nat.add_le_add captureBound blockBound

end PNP.Concrete.LockedNAND.TargetEmitterControllerNormalizationBound
