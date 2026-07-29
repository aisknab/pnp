/-
Copyright (c) 2026 PNP Labs.

Exact prefix-fold and final-gate paths for the fixed grammar-only locked-NAND
target emitter.

The executable graph contains only the materialized finite controller and
literal primitive tables.  Runtime values, source layouts, and capacity facts
below are proof-only descriptions of those fixed paths; they are never read by
the machine and do not provide a host-side schedule.
-/

import PNP.Concrete.LockedNANDTargetEmitterControllerCheckTrace
import PNP.Concrete.LockedNANDTargetEmitterRuntimeProgramSafety
import PNP.Concrete.LockedNANDTargetEmitterSemanticPrefix

namespace PNP.Concrete.LockedNAND.TargetEmitterControllerPrefixTrace

open PNP.Concrete
open WorkMachineProgramGraph
open WorkMachineProgramPath
open TargetEmitterController
open TargetEmitterPrimitiveCompiler
open TargetEmitterBlockCompiler

set_option maxRecDepth 100000

abbrev Runtime := TargetEmitterProgramSemantics.Runtime
abbrev ProgramSafe := TargetEmitterRuntimeProgram.ProgramSafe
abbrev SourceContext := TargetEmitterRuntimeProgram.SourceContext
abbrev MarkedWorkspace :=
  TargetEmitterRuntimeProgramSafety.MarkedWorkspace
abbrev CapturedReady :=
  TargetEmitterRuntimeProgramSafety.CapturedReady
abbrev ControllerRange :=
  TargetEmitterCapacity.ControllerRange

def TapeRepresents (state capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (source : List WorkSymbol)
    (target : List Token) (tape : WorkTape) : Prop :=
  TargetEmitterRuntime.Represents state capacity scratch
    registers checks source target
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

/-! ### Fixed materialized descriptors -/

private def outputGateResetDescriptor : BlockDescriptor :=
  { code := Block.outputGateReset
    primitives := Plan.outputGateReset
    continuation := .node rawInitialPopRef }

private def rawFirstPrefixDescriptor : BlockDescriptor :=
  { code := Block.rawFirstPrefix
    primitives := Plan.firstPrefix
    continuation := .node rawLoopPopRef }

private def rawNextPrefixDescriptor : BlockDescriptor :=
  { code := Block.rawNextPrefix
    primitives := Plan.nextPrefix
    continuation := .node rawLoopPopRef }

private def rawFinalDescriptor : BlockDescriptor :=
  { code := Block.rawFinal
    primitives := Plan.finalRaw
    continuation := .node beginOutputRef }

private def rawFinalZeroDescriptor : BlockDescriptor :=
  { code := Block.rawFinalZero
    primitives := Plan.finalZero
    continuation := .node beginOutputRef }

private def normalizedFirstPrefixDescriptor : BlockDescriptor :=
  { code := Block.normalizedFirstPrefix
    primitives := Plan.firstPrefix
    continuation := .node normalizedLoopPopRef }

private def normalizedNextPrefixDescriptor : BlockDescriptor :=
  { code := Block.normalizedNextPrefix
    primitives := Plan.nextPrefix
    continuation := .node normalizedLoopPopRef }

private def normalizedFinalDescriptor : BlockDescriptor :=
  { code := Block.normalizedFinal
    primitives := Plan.finalNormalized
    continuation := .node beginOutputRef }

private def outputGateResetPrograms : List WorkMachine :=
  (compileProgram Plan.outputGateReset).getD []

private def firstPrefixPrograms : List WorkMachine :=
  (compileProgram Plan.firstPrefix).getD []

private def nextPrefixPrograms : List WorkMachine :=
  (compileProgram Plan.nextPrefix).getD []

private def finalRawPrograms : List WorkMachine :=
  (compileProgram Plan.finalRaw).getD []

private def finalZeroPrograms : List WorkMachine :=
  (compileProgram Plan.finalZero).getD []

private def finalNormalizedPrograms : List WorkMachine :=
  (compileProgram Plan.finalNormalized).getD []

private theorem outputGateResetDescriptor_member :
    outputGateResetDescriptor ∈ blockDescriptors := by
  simp [outputGateResetDescriptor, blockDescriptors,
    fixedBlockDescriptors]

private theorem rawFirstPrefixDescriptor_member :
    rawFirstPrefixDescriptor ∈ blockDescriptors := by
  simp [rawFirstPrefixDescriptor, blockDescriptors,
    fixedBlockDescriptors]

private theorem rawNextPrefixDescriptor_member :
    rawNextPrefixDescriptor ∈ blockDescriptors := by
  simp [rawNextPrefixDescriptor, blockDescriptors,
    fixedBlockDescriptors]

private theorem rawFinalDescriptor_member :
    rawFinalDescriptor ∈ blockDescriptors := by
  simp [rawFinalDescriptor, blockDescriptors,
    fixedBlockDescriptors]

private theorem rawFinalZeroDescriptor_member :
    rawFinalZeroDescriptor ∈ blockDescriptors := by
  simp [rawFinalZeroDescriptor, blockDescriptors,
    fixedBlockDescriptors]

private theorem normalizedFirstPrefixDescriptor_member :
    normalizedFirstPrefixDescriptor ∈ blockDescriptors := by
  simp [normalizedFirstPrefixDescriptor, blockDescriptors,
    fixedBlockDescriptors]

private theorem normalizedNextPrefixDescriptor_member :
    normalizedNextPrefixDescriptor ∈ blockDescriptors := by
  simp [normalizedNextPrefixDescriptor, blockDescriptors,
    fixedBlockDescriptors]

private theorem normalizedFinalDescriptor_member :
    normalizedFinalDescriptor ∈ blockDescriptors := by
  simp [normalizedFinalDescriptor, blockDescriptors,
    fixedBlockDescriptors]

private theorem outputGateReset_compiled :
    compileProgram Plan.outputGateReset =
      some outputGateResetPrograms := by
  rfl

private theorem firstPrefix_compiled :
    compileProgram Plan.firstPrefix =
      some firstPrefixPrograms := by
  rfl

private theorem nextPrefix_compiled :
    compileProgram Plan.nextPrefix =
      some nextPrefixPrograms := by
  rfl

private theorem finalRaw_compiled :
    compileProgram Plan.finalRaw =
      some finalRawPrograms := by
  rfl

private theorem finalZero_compiled :
    compileProgram Plan.finalZero =
      some finalZeroPrograms := by
  rfl

private theorem finalNormalized_compiled :
    compileProgram Plan.finalNormalized =
      some finalNormalizedPrograms := by
  rfl

private theorem outputGateResetPrograms_nonempty :
    outputGateResetPrograms ≠ [] := by
  decide

private theorem firstPrefixPrograms_nonempty :
    firstPrefixPrograms ≠ [] := by
  decide

private theorem nextPrefixPrograms_nonempty :
    nextPrefixPrograms ≠ [] := by
  decide

private theorem finalRawPrograms_nonempty :
    finalRawPrograms ≠ [] := by
  decide

private theorem finalZeroPrograms_nonempty :
    finalZeroPrograms ≠ [] := by
  decide

private theorem finalNormalizedPrograms_nonempty :
    finalNormalizedPrograms ≠ [] := by
  decide

private theorem materializedBlock_path
    (descriptor : BlockDescriptor)
    (descriptorMember : descriptor ∈ blockDescriptors)
    (programs : List WorkMachine)
    (compiled :
      compileProgram descriptor.primitives = some programs)
    (programsNonempty : programs ≠ [])
    (reference continuation : NodeRef)
    (referenceEq :
      reference =
        blockEntry descriptor.code descriptor.primitives)
    (continuationEq :
      descriptor.continuation = .node continuation)
    (entryEq :
      reference.startState =
        TargetEmitterRuntimeProgram.entryState 0 programs)
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    {initial final : Runtime}
    (safe :
      ProgramSafe capacity source context
        descriptor.primitives initial final)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents reference.startState
        capacity initial.scratch initial.registers initial.checks
        source initial.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node reference) (.node continuation)
          steps initialTape finalTape ∧
      TapeRepresents continuation.startState
        capacity final.scratch final.registers final.checks
        source final.targetTokens finalTape := by
  let initialActual : WorkConfiguration :=
    { state := TargetEmitterRuntimeProgram.entryState 0 programs
      tape := initialTape }
  have inputRepresents :
      TargetEmitterRuntime.Represents initialActual.state
        capacity initial.scratch initial.registers initial.checks
        source initial.targetTokens initialActual := by
    have atEntry :
        TapeRepresents
          (TargetEmitterRuntimeProgram.entryState 0 programs)
          capacity initial.scratch initial.registers initial.checks
          source initial.targetTokens initialTape := by
      rw [← entryEq]
      exact represents
    exact atEntry
  rcases
      safe.descriptor_acceptPath_exact descriptor descriptorMember
        programs compiled programsNonempty 0 initialActual
        inputRepresents with
    ⟨steps, actualFinal, path, finalRepresents⟩
  refine ⟨steps, actualFinal.tape, ?_, ?_⟩
  · simpa [referenceEq, continuationEq] using path
  · exact
      represents_at_state
        (newState := continuation.startState) finalRepresents

/-! ### Exact individual block paths -/

/-- Reset the output-gate scratch coordinate and enter the raw prefix stack
branch. -/
theorem outputGateReset_path
    {raw : RawCircuit} {source : List WorkSymbol}
    (context : SourceContext source)
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
  exact
    materializedBlock_path
      outputGateResetDescriptor outputGateResetDescriptor_member
      outputGateResetPrograms
      (by simpa [outputGateResetDescriptor] using
        outputGateReset_compiled)
      outputGateResetPrograms_nonempty
      outputGateResetRef rawInitialPopRef rfl rfl rfl
      (capacity := TargetEmitterLedger.slotCapacity raw)
      (source := source) (context := context)
      (initial := runtime)
      (final :=
        TargetEmitterProgramSemantics.resetScratchResult runtime)
      (by
        simpa [outputGateResetDescriptor] using
          (TargetEmitterRuntimeProgramSafety.outputGateReset_safe
            context scratchBound))
      initialTape represents

private theorem firstPrefixBlock_path
    {raw : RawCircuit} {source : List WorkSymbol}
    (descriptor : BlockDescriptor)
    (descriptorMember : descriptor ∈ blockDescriptors)
    (reference continuation : NodeRef)
    (referenceEq :
      reference =
        blockEntry descriptor.code descriptor.primitives)
    (continuationEq :
      descriptor.continuation = .node continuation)
    (primitivesEq : descriptor.primitives = Plan.firstPrefix)
    (workspace : MarkedWorkspace source)
    (runtime : Runtime) (prior : List Nat) (newest : Nat)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (checksShape : runtime.checks = prior ++ [newest])
    (newestBound :
      newest < TargetEmitterLedger.slotCapacity raw)
    (entryEq :
      reference.startState =
        TargetEmitterRuntimeProgram.entryState 0 firstPrefixPrograms)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents reference.startState
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node reference) (.node continuation)
          steps initialTape finalTape ∧
      TapeRepresents continuation.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterProgramSemantics.firstPrefixResult
          runtime prior newest).scratch
        (TargetEmitterProgramSemantics.firstPrefixResult
          runtime prior newest).registers
        (TargetEmitterProgramSemantics.firstPrefixResult
          runtime prior newest).checks
        source
        (TargetEmitterProgramSemantics.firstPrefixResult
          runtime prior newest).targetTokens finalTape := by
  have safe :
      ProgramSafe (TargetEmitterLedger.slotCapacity raw)
        source workspace.context descriptor.primitives runtime
        (TargetEmitterProgramSemantics.firstPrefixResult
          runtime prior newest) := by
    rw [primitivesEq]
    exact
      TargetEmitterRuntimeProgramSafety.firstPrefix_safe
        workspace range capturedBound scratchBound
        checksShape newestBound
  exact
    materializedBlock_path descriptor descriptorMember
      firstPrefixPrograms
      (by simpa [primitivesEq] using firstPrefix_compiled)
      firstPrefixPrograms_nonempty reference continuation
      referenceEq continuationEq entryEq
      (capacity := TargetEmitterLedger.slotCapacity raw)
      (source := source) (context := workspace.context)
      (initial := runtime)
      (final :=
        TargetEmitterProgramSemantics.firstPrefixResult
          runtime prior newest)
      safe initialTape represents

/-- Execute the raw first-link block and return to the raw pop loop. -/
theorem rawFirstPrefix_path
    {raw : RawCircuit} {source : List WorkSymbol}
    (workspace : MarkedWorkspace source)
    (runtime : Runtime) (prior : List Nat) (newest : Nat)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (checksShape : runtime.checks = prior ++ [newest])
    (newestBound :
      newest < TargetEmitterLedger.slotCapacity raw)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents rawFirstPrefixRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node rawFirstPrefixRef)
          (.node rawLoopPopRef) steps initialTape finalTape ∧
      TapeRepresents rawLoopPopRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterProgramSemantics.firstPrefixResult
          runtime prior newest).scratch
        (TargetEmitterProgramSemantics.firstPrefixResult
          runtime prior newest).registers
        (TargetEmitterProgramSemantics.firstPrefixResult
          runtime prior newest).checks
        source
        (TargetEmitterProgramSemantics.firstPrefixResult
          runtime prior newest).targetTokens finalTape := by
  exact
    firstPrefixBlock_path rawFirstPrefixDescriptor
      rawFirstPrefixDescriptor_member rawFirstPrefixRef rawLoopPopRef
      rfl rfl rfl workspace runtime prior newest range capturedBound
      scratchBound checksShape newestBound rfl initialTape represents

/-- Execute the normalized first-link block and return to the normalized pop
loop. -/
theorem normalizedFirstPrefix_path
    {raw : RawCircuit} {source : List WorkSymbol}
    (workspace : MarkedWorkspace source)
    (runtime : Runtime) (prior : List Nat) (newest : Nat)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (checksShape : runtime.checks = prior ++ [newest])
    (newestBound :
      newest < TargetEmitterLedger.slotCapacity raw)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents normalizedFirstPrefixRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node normalizedFirstPrefixRef)
          (.node normalizedLoopPopRef) steps initialTape finalTape ∧
      TapeRepresents normalizedLoopPopRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterProgramSemantics.firstPrefixResult
          runtime prior newest).scratch
        (TargetEmitterProgramSemantics.firstPrefixResult
          runtime prior newest).registers
        (TargetEmitterProgramSemantics.firstPrefixResult
          runtime prior newest).checks
        source
        (TargetEmitterProgramSemantics.firstPrefixResult
          runtime prior newest).targetTokens finalTape := by
  exact
    firstPrefixBlock_path normalizedFirstPrefixDescriptor
      normalizedFirstPrefixDescriptor_member normalizedFirstPrefixRef
      normalizedLoopPopRef rfl rfl rfl workspace runtime prior newest
      range capturedBound scratchBound checksShape newestBound rfl
      initialTape represents

private theorem nextPrefixBlock_path
    {raw : RawCircuit} {source : List WorkSymbol}
    (descriptor : BlockDescriptor)
    (descriptorMember : descriptor ∈ blockDescriptors)
    (reference continuation : NodeRef)
    (referenceEq :
      reference =
        blockEntry descriptor.code descriptor.primitives)
    (continuationEq :
      descriptor.continuation = .node continuation)
    (primitivesEq : descriptor.primitives = Plan.nextPrefix)
    (workspace : MarkedWorkspace source)
    (runtime : Runtime)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (entryEq :
      reference.startState =
        TargetEmitterRuntimeProgram.entryState 0 nextPrefixPrograms)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents reference.startState
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node reference) (.node continuation)
          steps initialTape finalTape ∧
      TapeRepresents continuation.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterProgramSemantics.nextPrefixResult runtime).scratch
        (TargetEmitterProgramSemantics.nextPrefixResult runtime).registers
        (TargetEmitterProgramSemantics.nextPrefixResult runtime).checks
        source
        (TargetEmitterProgramSemantics.nextPrefixResult runtime).targetTokens
        finalTape := by
  have safe :
      ProgramSafe (TargetEmitterLedger.slotCapacity raw)
        source workspace.context descriptor.primitives runtime
        (TargetEmitterProgramSemantics.nextPrefixResult runtime) := by
    rw [primitivesEq]
    exact
      TargetEmitterRuntimeProgramSafety.nextPrefix_safe
        workspace range capturedBound scratchBound
  exact
    materializedBlock_path descriptor descriptorMember
      nextPrefixPrograms
      (by simpa [primitivesEq] using nextPrefix_compiled)
      nextPrefixPrograms_nonempty reference continuation
      referenceEq continuationEq entryEq
      (capacity := TargetEmitterLedger.slotCapacity raw)
      (source := source) (context := workspace.context)
      (initial := runtime)
      (final := TargetEmitterProgramSemantics.nextPrefixResult runtime)
      safe initialTape represents

/-- Execute one raw later-link block and return to the raw pop loop. -/
theorem rawNextPrefix_path
    {raw : RawCircuit} {source : List WorkSymbol}
    (workspace : MarkedWorkspace source)
    (runtime : Runtime)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents rawNextPrefixRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node rawNextPrefixRef)
          (.node rawLoopPopRef) steps initialTape finalTape ∧
      TapeRepresents rawLoopPopRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterProgramSemantics.nextPrefixResult runtime).scratch
        (TargetEmitterProgramSemantics.nextPrefixResult runtime).registers
        (TargetEmitterProgramSemantics.nextPrefixResult runtime).checks
        source
        (TargetEmitterProgramSemantics.nextPrefixResult runtime).targetTokens
        finalTape := by
  exact
    nextPrefixBlock_path rawNextPrefixDescriptor
      rawNextPrefixDescriptor_member rawNextPrefixRef rawLoopPopRef
      rfl rfl rfl workspace runtime range capturedBound scratchBound
      rfl initialTape represents

/-- Execute one normalized later-link block and return to the normalized pop
loop. -/
theorem normalizedNextPrefix_path
    {raw : RawCircuit} {source : List WorkSymbol}
    (workspace : MarkedWorkspace source)
    (runtime : Runtime)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents normalizedNextPrefixRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node normalizedNextPrefixRef)
          (.node normalizedLoopPopRef) steps initialTape finalTape ∧
      TapeRepresents normalizedLoopPopRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterProgramSemantics.nextPrefixResult runtime).scratch
        (TargetEmitterProgramSemantics.nextPrefixResult runtime).registers
        (TargetEmitterProgramSemantics.nextPrefixResult runtime).checks
        source
        (TargetEmitterProgramSemantics.nextPrefixResult runtime).targetTokens
        finalTape := by
  exact
    nextPrefixBlock_path normalizedNextPrefixDescriptor
      normalizedNextPrefixDescriptor_member normalizedNextPrefixRef
      normalizedLoopPopRef rfl rfl rfl workspace runtime range
      capturedBound scratchBound rfl initialTape represents

private theorem finalBlock_path
    {raw : RawCircuit} {source : List WorkSymbol}
    (descriptor : BlockDescriptor)
    (descriptorMember : descriptor ∈ blockDescriptors)
    (programs : List WorkMachine)
    (compiled :
      compileProgram descriptor.primitives = some programs)
    (programsNonempty : programs ≠ [])
    (reference : NodeRef)
    (referenceEq :
      reference =
        blockEntry descriptor.code descriptor.primitives)
    (continuationEq :
      descriptor.continuation = .node beginOutputRef)
    (entryEq :
      reference.startState =
        TargetEmitterRuntimeProgram.entryState 0 programs)
    (workspace : MarkedWorkspace source)
    (runtime final : Runtime)
    (safe :
      ProgramSafe (TargetEmitterLedger.slotCapacity raw)
        source workspace.context descriptor.primitives runtime final)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents reference.startState
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node reference) (.node beginOutputRef)
          steps initialTape finalTape ∧
      TapeRepresents beginOutputRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        final.scratch final.registers final.checks source
        final.targetTokens finalTape := by
  exact
    materializedBlock_path descriptor descriptorMember programs
      compiled programsNonempty reference beginOutputRef referenceEq
      continuationEq entryEq
      (capacity := TargetEmitterLedger.slotCapacity raw)
      (source := source) (context := workspace.context)
      (initial := runtime) (final := final)
      safe initialTape represents

/-- Emit the four-gate false-output final suffix. -/
theorem rawFinalZero_path
    {raw : RawCircuit} {source : List WorkSymbol}
    (workspace : MarkedWorkspace source)
    (runtime : Runtime)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (captured : CapturedReady raw source runtime.captured)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents rawFinalZeroRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node rawFinalZeroRef)
          (.node beginOutputRef) steps initialTape finalTape ∧
      TapeRepresents beginOutputRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterProgramSemantics.finalResult runtime
          TargetEmitterPlan.finalZeroPlan).scratch
        (TargetEmitterProgramSemantics.finalResult runtime
          TargetEmitterPlan.finalZeroPlan).registers
        (TargetEmitterProgramSemantics.finalResult runtime
          TargetEmitterPlan.finalZeroPlan).checks
        source
        (TargetEmitterProgramSemantics.finalResult runtime
          TargetEmitterPlan.finalZeroPlan).targetTokens finalTape := by
  exact
    finalBlock_path rawFinalZeroDescriptor
      rawFinalZeroDescriptor_member finalZeroPrograms
      (by simpa [rawFinalZeroDescriptor] using finalZero_compiled)
      finalZeroPrograms_nonempty rawFinalZeroRef rfl rfl rfl
      workspace runtime
      (TargetEmitterProgramSemantics.finalResult runtime
        TargetEmitterPlan.finalZeroPlan)
      (by
        simpa [rawFinalZeroDescriptor] using
          (TargetEmitterRuntimeProgramSafety.finalZero_safe
            workspace range capturedBound scratchBound captured))
      initialTape represents

/-- Emit the four-gate raw positive-output final suffix. -/
theorem rawFinal_path
    {raw : RawCircuit} {source : List WorkSymbol}
    (workspace : MarkedWorkspace source)
    (runtime : Runtime)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (captured : CapturedReady raw source runtime.captured)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents rawFinalRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node rawFinalRef)
          (.node beginOutputRef) steps initialTape finalTape ∧
      TapeRepresents beginOutputRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterProgramSemantics.finalResult runtime
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.rawGateTrace)).scratch
        (TargetEmitterProgramSemantics.finalResult runtime
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.rawGateTrace)).registers
        (TargetEmitterProgramSemantics.finalResult runtime
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.rawGateTrace)).checks
        source
        (TargetEmitterProgramSemantics.finalResult runtime
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.rawGateTrace)).targetTokens finalTape := by
  exact
    finalBlock_path rawFinalDescriptor rawFinalDescriptor_member
      finalRawPrograms
      (by simpa [rawFinalDescriptor] using finalRaw_compiled)
      finalRawPrograms_nonempty rawFinalRef rfl rfl rfl
      workspace runtime
      (TargetEmitterProgramSemantics.finalResult runtime
        (TargetEmitterPlan.finalPositivePlan
          TargetEmitterPlan.rawGateTrace))
      (by
        simpa [rawFinalDescriptor] using
          (TargetEmitterRuntimeProgramSafety.finalRaw_safe
            workspace range capturedBound scratchBound captured))
      initialTape represents

/-- Emit the four-gate normalized positive-output final suffix. -/
theorem normalizedFinal_path
    {raw : RawCircuit} {source : List WorkSymbol}
    (workspace : MarkedWorkspace source)
    (runtime : Runtime)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents normalizedFinalRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node normalizedFinalRef)
          (.node beginOutputRef) steps initialTape finalTape ∧
      TapeRepresents beginOutputRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterProgramSemantics.finalResult runtime
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.traceCoordinate)).scratch
        (TargetEmitterProgramSemantics.finalResult runtime
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.traceCoordinate)).registers
        (TargetEmitterProgramSemantics.finalResult runtime
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.traceCoordinate)).checks
        source
        (TargetEmitterProgramSemantics.finalResult runtime
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.traceCoordinate)).targetTokens finalTape := by
  exact
    finalBlock_path normalizedFinalDescriptor
      normalizedFinalDescriptor_member finalNormalizedPrograms
      (by simpa [normalizedFinalDescriptor] using
        finalNormalized_compiled)
      finalNormalizedPrograms_nonempty normalizedFinalRef rfl rfl rfl
      workspace runtime
      (TargetEmitterProgramSemantics.finalResult runtime
        (TargetEmitterPlan.finalPositivePlan
          TargetEmitterPlan.traceCoordinate))
      (by
        simpa [normalizedFinalDescriptor] using
          (TargetEmitterRuntimeProgramSafety.finalNormalized_safe
            workspace range capturedBound scratchBound))
      initialTape represents

/-! ### Check-pop and block compositions -/

/-- Logical state exposed by one successful physical stack pop. -/
def poppedRuntime
    (runtime : Runtime) (prior : List Nat) (value : Nat) : Runtime :=
  { runtime with
    scratch := value
    checks := prior }

private theorem pop_input_represents
    {source : List WorkSymbol} {runtime : Runtime}
    {state capacity : Nat} {initialTape : WorkTape}
    (context : SourceContext source)
    (scratchZero : runtime.scratch = 0)
    (represents :
      TapeRepresents state capacity runtime.scratch
        runtime.registers runtime.checks source
        runtime.targetTokens initialTape) :
    TargetEmitterRuntime.Represents
      TargetEmitterCheckStack.Pop.startState capacity 0
      runtime.registers runtime.checks
      (context.head :: context.tail) runtime.targetTokens
      { state := TargetEmitterCheckStack.Pop.startState,
        tape := initialTape } := by
  have sourceRepresents :
      TargetEmitterRuntime.Represents state capacity 0
        runtime.registers runtime.checks
        (context.head :: context.tail) runtime.targetTokens
        { state := state, tape := initialTape } := by
    simpa [TapeRepresents, scratchZero, context.source_eq] using
      represents
  exact represents_at_state sourceRepresents

private theorem popped_tape_represents
    {source : List WorkSymbol} {runtime : Runtime}
    {oldState newState capacity value : Nat} {prior : List Nat}
    {actual : WorkConfiguration}
    (context : SourceContext source)
    (represents :
      TargetEmitterRuntime.Represents oldState capacity value
        runtime.registers prior (context.head :: context.tail)
        runtime.targetTokens actual) :
    TapeRepresents newState capacity
      (poppedRuntime runtime prior value).scratch
      (poppedRuntime runtime prior value).registers
      (poppedRuntime runtime prior value).checks source
      (poppedRuntime runtime prior value).targetTokens actual.tape := by
  have transported :=
    represents_at_state (newState := newState) represents
  simpa [TapeRepresents, poppedRuntime, context.source_eq] using
    transported

private theorem context_tape_represents_at_state
    {source : List WorkSymbol}
    {oldState newState capacity scratch : Nat}
    {registers : TargetEmitter.UnaryRegisters}
    {checks : List Nat} {target : List Token}
    {actual : WorkConfiguration}
    (context : SourceContext source)
    (represents :
      TargetEmitterRuntime.Represents oldState capacity scratch
        registers checks (context.head :: context.tail)
        target actual) :
    TapeRepresents newState capacity scratch registers checks
      source target actual.tape := by
  have transported :=
    represents_at_state (newState := newState) represents
  simpa [TapeRepresents, context.source_eq] using transported

/-- An empty raw initial stack selects the literal false-output final block
and reaches the output-section opener. -/
theorem rawInitialPop_empty_to_beginOutput_path
    {raw : RawCircuit} {source : List WorkSymbol}
    (workspace : MarkedWorkspace source)
    (runtime : Runtime)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchZero : runtime.scratch = 0)
    (checksEmpty : runtime.checks = [])
    (captured : CapturedReady raw source runtime.captured)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents rawInitialPopRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node rawInitialPopRef)
          (.node beginOutputRef) steps initialTape finalTape ∧
      TapeRepresents beginOutputRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterProgramSemantics.finalResult runtime
          TargetEmitterPlan.finalZeroPlan).scratch
        (TargetEmitterProgramSemantics.finalResult runtime
          TargetEmitterPlan.finalZeroPlan).registers
        (TargetEmitterProgramSemantics.finalResult runtime
          TargetEmitterPlan.finalZeroPlan).checks
        source
        (TargetEmitterProgramSemantics.finalResult runtime
          TargetEmitterPlan.finalZeroPlan).targetTokens finalTape := by
  let initial : WorkConfiguration :=
    { state := TargetEmitterCheckStack.Pop.startState
      tape := initialTape }
  have popRepresents :
      TargetEmitterRuntime.Represents
        TargetEmitterCheckStack.Pop.startState
        (TargetEmitterLedger.slotCapacity raw) 0
        runtime.registers []
        (workspace.context.head :: workspace.context.tail)
        runtime.targetTokens initial := by
    have base :=
      pop_input_represents workspace.context scratchZero represents
    simpa [initial, checksEmpty] using base
  rcases
      TargetEmitterControllerCheckTrace.rawInitialPop_empty_path
        (TargetEmitterLedger.slotCapacity raw) runtime.registers
        workspace.context.head workspace.context.tail
        runtime.targetTokens initial range.ledgerFits.toCheckStack
        workspace.context.stackAllowed popRepresents with
    ⟨afterPop, popPath, afterPopRepresents⟩
  have finalRepresents :
      TapeRepresents rawFinalZeroRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens afterPop.tape := by
    have transported :
        TapeRepresents rawFinalZeroRef.startState
          (TargetEmitterLedger.slotCapacity raw) 0
          runtime.registers [] source runtime.targetTokens
          afterPop.tape :=
      context_tape_represents_at_state workspace.context
        afterPopRepresents
    simpa [scratchZero, checksEmpty] using transported
  rcases
      rawFinalZero_path workspace runtime range capturedBound
        (by
          rw [scratchZero]
          simp [TargetEmitterLedger.slotCapacity])
        captured afterPop.tape finalRepresents with
    ⟨finalSteps, finalTape, finalPath, outputRepresents⟩
  refine ⟨TargetEmitterControllerCheckTrace.emptyPathSteps
      (TargetEmitterLedger.slotCapacity raw) + finalSteps,
    finalTape, ?_, outputRepresents⟩
  exact
    AcceptPath.trans graph (.node rawInitialPopRef)
      (.node rawFinalZeroRef) (.node beginOutputRef)
      (TargetEmitterControllerCheckTrace.emptyPathSteps
        (TargetEmitterLedger.slotCapacity raw))
      finalSteps initialTape afterPop.tape finalTape
      popPath finalPath

/-- An empty raw loop stack selects the positive raw final block and reaches
the output-section opener. -/
theorem rawLoopPop_empty_to_beginOutput_path
    {raw : RawCircuit} {source : List WorkSymbol}
    (workspace : MarkedWorkspace source)
    (runtime : Runtime)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchZero : runtime.scratch = 0)
    (checksEmpty : runtime.checks = [])
    (captured : CapturedReady raw source runtime.captured)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents rawLoopPopRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node rawLoopPopRef)
          (.node beginOutputRef) steps initialTape finalTape ∧
      TapeRepresents beginOutputRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterProgramSemantics.finalResult runtime
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.rawGateTrace)).scratch
        (TargetEmitterProgramSemantics.finalResult runtime
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.rawGateTrace)).registers
        (TargetEmitterProgramSemantics.finalResult runtime
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.rawGateTrace)).checks
        source
        (TargetEmitterProgramSemantics.finalResult runtime
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.rawGateTrace)).targetTokens finalTape := by
  let initial : WorkConfiguration :=
    { state := TargetEmitterCheckStack.Pop.startState
      tape := initialTape }
  have popRepresents :
      TargetEmitterRuntime.Represents
        TargetEmitterCheckStack.Pop.startState
        (TargetEmitterLedger.slotCapacity raw) 0
        runtime.registers []
        (workspace.context.head :: workspace.context.tail)
        runtime.targetTokens initial := by
    have base :=
      pop_input_represents workspace.context scratchZero represents
    simpa [initial, checksEmpty] using base
  rcases
      TargetEmitterControllerCheckTrace.rawLoopPop_empty_path
        (TargetEmitterLedger.slotCapacity raw) runtime.registers
        workspace.context.head workspace.context.tail
        runtime.targetTokens initial range.ledgerFits.toCheckStack
        workspace.context.stackAllowed popRepresents with
    ⟨afterPop, popPath, afterPopRepresents⟩
  have finalRepresents :
      TapeRepresents rawFinalRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens afterPop.tape := by
    have transported :
        TapeRepresents rawFinalRef.startState
          (TargetEmitterLedger.slotCapacity raw) 0
          runtime.registers [] source runtime.targetTokens
          afterPop.tape :=
      context_tape_represents_at_state workspace.context
        afterPopRepresents
    simpa [scratchZero, checksEmpty] using transported
  rcases
      rawFinal_path workspace runtime range capturedBound
        (by
          rw [scratchZero]
          simp [TargetEmitterLedger.slotCapacity])
        captured afterPop.tape finalRepresents with
    ⟨finalSteps, finalTape, finalPath, outputRepresents⟩
  refine ⟨TargetEmitterControllerCheckTrace.emptyPathSteps
      (TargetEmitterLedger.slotCapacity raw) + finalSteps,
    finalTape, ?_, outputRepresents⟩
  exact
    AcceptPath.trans graph (.node rawLoopPopRef)
      (.node rawFinalRef) (.node beginOutputRef)
      (TargetEmitterControllerCheckTrace.emptyPathSteps
        (TargetEmitterLedger.slotCapacity raw))
      finalSteps initialTape afterPop.tape finalTape
      popPath finalPath

/-- An empty normalized loop stack selects the normalized final block and
reaches the output-section opener. -/
theorem normalizedLoopPop_empty_to_beginOutput_path
    {raw : RawCircuit} {source : List WorkSymbol}
    (workspace : MarkedWorkspace source)
    (runtime : Runtime)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchZero : runtime.scratch = 0)
    (checksEmpty : runtime.checks = [])
    (initialTape : WorkTape)
    (represents :
      TapeRepresents normalizedLoopPopRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node normalizedLoopPopRef)
          (.node beginOutputRef) steps initialTape finalTape ∧
      TapeRepresents beginOutputRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterProgramSemantics.finalResult runtime
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.traceCoordinate)).scratch
        (TargetEmitterProgramSemantics.finalResult runtime
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.traceCoordinate)).registers
        (TargetEmitterProgramSemantics.finalResult runtime
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.traceCoordinate)).checks
        source
        (TargetEmitterProgramSemantics.finalResult runtime
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.traceCoordinate)).targetTokens finalTape := by
  let initial : WorkConfiguration :=
    { state := TargetEmitterCheckStack.Pop.startState
      tape := initialTape }
  have popRepresents :
      TargetEmitterRuntime.Represents
        TargetEmitterCheckStack.Pop.startState
        (TargetEmitterLedger.slotCapacity raw) 0
        runtime.registers []
        (workspace.context.head :: workspace.context.tail)
        runtime.targetTokens initial := by
    have base :=
      pop_input_represents workspace.context scratchZero represents
    simpa [initial, checksEmpty] using base
  rcases
      TargetEmitterControllerCheckTrace.normalizedLoopPop_empty_path
        (TargetEmitterLedger.slotCapacity raw) runtime.registers
        workspace.context.head workspace.context.tail
        runtime.targetTokens initial range.ledgerFits.toCheckStack
        workspace.context.stackAllowed popRepresents with
    ⟨afterPop, popPath, afterPopRepresents⟩
  have finalRepresents :
      TapeRepresents normalizedFinalRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens afterPop.tape := by
    have transported :
        TapeRepresents normalizedFinalRef.startState
          (TargetEmitterLedger.slotCapacity raw) 0
          runtime.registers [] source runtime.targetTokens
          afterPop.tape :=
      context_tape_represents_at_state workspace.context
        afterPopRepresents
    simpa [scratchZero, checksEmpty] using transported
  rcases
      normalizedFinal_path workspace runtime range capturedBound
        (by
          rw [scratchZero]
          simp [TargetEmitterLedger.slotCapacity])
        afterPop.tape finalRepresents with
    ⟨finalSteps, finalTape, finalPath, outputRepresents⟩
  refine ⟨TargetEmitterControllerCheckTrace.emptyPathSteps
      (TargetEmitterLedger.slotCapacity raw) + finalSteps,
    finalTape, ?_, outputRepresents⟩
  exact
    AcceptPath.trans graph (.node normalizedLoopPopRef)
      (.node normalizedFinalRef) (.node beginOutputRef)
      (TargetEmitterControllerCheckTrace.emptyPathSteps
        (TargetEmitterLedger.slotCapacity raw))
      finalSteps initialTape afterPop.tape finalTape
      popPath finalPath

/-- Pop one raw loop check, execute the exact later-link block, and return to
the raw loop branch. -/
theorem rawLoopPop_nonempty_next_path
    {raw : RawCircuit} {source : List WorkSymbol}
    (workspace : MarkedWorkspace source)
    (runtime : Runtime) (prior : List Nat) (value : Nat)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchZero : runtime.scratch = 0)
    (checksShape : runtime.checks = prior ++ [value])
    (valueBound : value < TargetEmitterLedger.slotCapacity raw)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents rawLoopPopRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node rawLoopPopRef)
          (.node rawLoopPopRef) steps initialTape finalTape ∧
      TapeRepresents rawLoopPopRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterProgramSemantics.nextPrefixResult
          (poppedRuntime runtime prior value)).scratch
        (TargetEmitterProgramSemantics.nextPrefixResult
          (poppedRuntime runtime prior value)).registers
        (TargetEmitterProgramSemantics.nextPrefixResult
          (poppedRuntime runtime prior value)).checks
        source
        (TargetEmitterProgramSemantics.nextPrefixResult
          (poppedRuntime runtime prior value)).targetTokens finalTape := by
  let initial : WorkConfiguration :=
    { state := TargetEmitterCheckStack.Pop.startState
      tape := initialTape }
  have popRepresents :
      TargetEmitterRuntime.Represents
        TargetEmitterCheckStack.Pop.startState
        (TargetEmitterLedger.slotCapacity raw) 0
        runtime.registers (prior ++ [value])
        (workspace.context.head :: workspace.context.tail)
        runtime.targetTokens initial := by
    have base :=
      pop_input_represents workspace.context scratchZero represents
    simpa [initial, checksShape] using base
  rcases
      TargetEmitterControllerCheckTrace.rawLoopPop_nonempty_path
        (TargetEmitterLedger.slotCapacity raw) value runtime.registers
        prior workspace.context.head workspace.context.tail
        runtime.targetTokens initial range.ledgerFits.toCheckStack
        (Nat.le_of_lt valueBound) workspace.context.stackAllowed
        popRepresents with
    ⟨afterPop, popPath, afterPopRepresents⟩
  have blockRepresents :
      TapeRepresents rawNextPrefixRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (poppedRuntime runtime prior value).scratch
        (poppedRuntime runtime prior value).registers
        (poppedRuntime runtime prior value).checks source
        (poppedRuntime runtime prior value).targetTokens afterPop.tape :=
    popped_tape_represents workspace.context afterPopRepresents
  rcases
      rawNextPrefix_path workspace
        (poppedRuntime runtime prior value)
        (by simpa [poppedRuntime] using range)
        (by simpa [poppedRuntime] using capturedBound)
        (by simpa [poppedRuntime] using valueBound)
        afterPop.tape blockRepresents with
    ⟨blockSteps, finalTape, blockPath, finalRepresents⟩
  refine
    ⟨TargetEmitterControllerCheckTrace.nonemptyPathSteps
        (TargetEmitterLedger.slotCapacity raw) prior value +
      blockSteps,
      finalTape, ?_, finalRepresents⟩
  exact
    AcceptPath.trans graph (.node rawLoopPopRef)
      (.node rawNextPrefixRef) (.node rawLoopPopRef)
      (TargetEmitterControllerCheckTrace.nonemptyPathSteps
        (TargetEmitterLedger.slotCapacity raw) prior value)
      blockSteps initialTape afterPop.tape finalTape
      popPath blockPath

/-- Pop one normalized loop check, execute the exact later-link block, and
return to the normalized loop branch. -/
theorem normalizedLoopPop_nonempty_next_path
    {raw : RawCircuit} {source : List WorkSymbol}
    (workspace : MarkedWorkspace source)
    (runtime : Runtime) (prior : List Nat) (value : Nat)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchZero : runtime.scratch = 0)
    (checksShape : runtime.checks = prior ++ [value])
    (valueBound : value < TargetEmitterLedger.slotCapacity raw)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents normalizedLoopPopRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node normalizedLoopPopRef)
          (.node normalizedLoopPopRef) steps initialTape finalTape ∧
      TapeRepresents normalizedLoopPopRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterProgramSemantics.nextPrefixResult
          (poppedRuntime runtime prior value)).scratch
        (TargetEmitterProgramSemantics.nextPrefixResult
          (poppedRuntime runtime prior value)).registers
        (TargetEmitterProgramSemantics.nextPrefixResult
          (poppedRuntime runtime prior value)).checks
        source
        (TargetEmitterProgramSemantics.nextPrefixResult
          (poppedRuntime runtime prior value)).targetTokens finalTape := by
  let initial : WorkConfiguration :=
    { state := TargetEmitterCheckStack.Pop.startState
      tape := initialTape }
  have popRepresents :
      TargetEmitterRuntime.Represents
        TargetEmitterCheckStack.Pop.startState
        (TargetEmitterLedger.slotCapacity raw) 0
        runtime.registers (prior ++ [value])
        (workspace.context.head :: workspace.context.tail)
        runtime.targetTokens initial := by
    have base :=
      pop_input_represents workspace.context scratchZero represents
    simpa [initial, checksShape] using base
  rcases
      TargetEmitterControllerCheckTrace.normalizedLoopPop_nonempty_path
        (TargetEmitterLedger.slotCapacity raw) value runtime.registers
        prior workspace.context.head workspace.context.tail
        runtime.targetTokens initial range.ledgerFits.toCheckStack
        (Nat.le_of_lt valueBound) workspace.context.stackAllowed
        popRepresents with
    ⟨afterPop, popPath, afterPopRepresents⟩
  have blockRepresents :
      TapeRepresents normalizedNextPrefixRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (poppedRuntime runtime prior value).scratch
        (poppedRuntime runtime prior value).registers
        (poppedRuntime runtime prior value).checks source
        (poppedRuntime runtime prior value).targetTokens afterPop.tape :=
    popped_tape_represents workspace.context afterPopRepresents
  rcases
      normalizedNextPrefix_path workspace
        (poppedRuntime runtime prior value)
        (by simpa [poppedRuntime] using range)
        (by simpa [poppedRuntime] using capturedBound)
        (by simpa [poppedRuntime] using valueBound)
        afterPop.tape blockRepresents with
    ⟨blockSteps, finalTape, blockPath, finalRepresents⟩
  refine
    ⟨TargetEmitterControllerCheckTrace.nonemptyPathSteps
        (TargetEmitterLedger.slotCapacity raw) prior value +
      blockSteps,
      finalTape, ?_, finalRepresents⟩
  exact
    AcceptPath.trans graph (.node normalizedLoopPopRef)
      (.node normalizedNextPrefixRef) (.node normalizedLoopPopRef)
      (TargetEmitterControllerCheckTrace.nonemptyPathSteps
        (TargetEmitterLedger.slotCapacity raw) prior value)
      blockSteps initialTape afterPop.tape finalTape
      popPath blockPath

/-- Pop the newest raw check, execute the exact first-link block (which pops
the next check internally), and enter the raw loop with the older stack. -/
theorem rawInitialPop_nonempty_first_path
    {raw : RawCircuit} {source : List WorkSymbol}
    (workspace : MarkedWorkspace source)
    (runtime : Runtime) (prior : List Nat)
    (second newest : Nat)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchZero : runtime.scratch = 0)
    (checksShape :
      runtime.checks = prior ++ [second, newest])
    (secondBound :
      second < TargetEmitterLedger.slotCapacity raw)
    (newestBound :
      newest < TargetEmitterLedger.slotCapacity raw)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents rawInitialPopRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node rawInitialPopRef)
          (.node rawLoopPopRef) steps initialTape finalTape ∧
      TapeRepresents rawLoopPopRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterProgramSemantics.firstPrefixResult
          (poppedRuntime runtime (prior ++ [second]) newest)
          prior second).scratch
        (TargetEmitterProgramSemantics.firstPrefixResult
          (poppedRuntime runtime (prior ++ [second]) newest)
          prior second).registers
        (TargetEmitterProgramSemantics.firstPrefixResult
          (poppedRuntime runtime (prior ++ [second]) newest)
          prior second).checks
        source
        (TargetEmitterProgramSemantics.firstPrefixResult
          (poppedRuntime runtime (prior ++ [second]) newest)
          prior second).targetTokens finalTape := by
  let initial : WorkConfiguration :=
    { state := TargetEmitterCheckStack.Pop.startState
      tape := initialTape }
  have popRepresents :
      TargetEmitterRuntime.Represents
        TargetEmitterCheckStack.Pop.startState
        (TargetEmitterLedger.slotCapacity raw) 0 runtime.registers
        ((prior ++ [second]) ++ [newest])
        (workspace.context.head :: workspace.context.tail)
        runtime.targetTokens initial := by
    have base :=
      pop_input_represents workspace.context scratchZero represents
    simpa [initial, checksShape, List.append_assoc] using base
  rcases
      TargetEmitterControllerCheckTrace.rawInitialPop_nonempty_path
        (TargetEmitterLedger.slotCapacity raw) newest runtime.registers
        (prior ++ [second]) workspace.context.head
        workspace.context.tail runtime.targetTokens initial
        range.ledgerFits.toCheckStack (Nat.le_of_lt newestBound)
        workspace.context.stackAllowed popRepresents with
    ⟨afterPop, popPath, afterPopRepresents⟩
  have blockRepresents :
      TapeRepresents rawFirstPrefixRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (poppedRuntime runtime (prior ++ [second]) newest).scratch
        (poppedRuntime runtime (prior ++ [second]) newest).registers
        (poppedRuntime runtime (prior ++ [second]) newest).checks
        source
        (poppedRuntime runtime (prior ++ [second]) newest).targetTokens
        afterPop.tape :=
    popped_tape_represents workspace.context afterPopRepresents
  rcases
      rawFirstPrefix_path workspace
        (poppedRuntime runtime (prior ++ [second]) newest)
        prior second
        (by simpa [poppedRuntime] using range)
        (by simpa [poppedRuntime] using capturedBound)
        (by simpa [poppedRuntime] using newestBound)
        (by simp [poppedRuntime])
        secondBound afterPop.tape blockRepresents with
    ⟨blockSteps, finalTape, blockPath, finalRepresents⟩
  refine
    ⟨TargetEmitterControllerCheckTrace.nonemptyPathSteps
        (TargetEmitterLedger.slotCapacity raw)
        (prior ++ [second]) newest + blockSteps,
      finalTape, ?_, finalRepresents⟩
  exact
    AcceptPath.trans graph (.node rawInitialPopRef)
      (.node rawFirstPrefixRef) (.node rawLoopPopRef)
      (TargetEmitterControllerCheckTrace.nonemptyPathSteps
        (TargetEmitterLedger.slotCapacity raw)
        (prior ++ [second]) newest)
      blockSteps initialTape afterPop.tape finalTape
      popPath blockPath

/-- Normalized counterpart of `rawInitialPop_nonempty_first_path`. -/
theorem normalizedInitialPop_nonempty_first_path
    {raw : RawCircuit} {source : List WorkSymbol}
    (workspace : MarkedWorkspace source)
    (runtime : Runtime) (prior : List Nat)
    (second newest : Nat)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchZero : runtime.scratch = 0)
    (checksShape :
      runtime.checks = prior ++ [second, newest])
    (secondBound :
      second < TargetEmitterLedger.slotCapacity raw)
    (newestBound :
      newest < TargetEmitterLedger.slotCapacity raw)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents normalizedInitialPopRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node normalizedInitialPopRef)
          (.node normalizedLoopPopRef) steps initialTape finalTape ∧
      TapeRepresents normalizedLoopPopRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterProgramSemantics.firstPrefixResult
          (poppedRuntime runtime (prior ++ [second]) newest)
          prior second).scratch
        (TargetEmitterProgramSemantics.firstPrefixResult
          (poppedRuntime runtime (prior ++ [second]) newest)
          prior second).registers
        (TargetEmitterProgramSemantics.firstPrefixResult
          (poppedRuntime runtime (prior ++ [second]) newest)
          prior second).checks
        source
        (TargetEmitterProgramSemantics.firstPrefixResult
          (poppedRuntime runtime (prior ++ [second]) newest)
          prior second).targetTokens finalTape := by
  let initial : WorkConfiguration :=
    { state := TargetEmitterCheckStack.Pop.startState
      tape := initialTape }
  have popRepresents :
      TargetEmitterRuntime.Represents
        TargetEmitterCheckStack.Pop.startState
        (TargetEmitterLedger.slotCapacity raw) 0 runtime.registers
        ((prior ++ [second]) ++ [newest])
        (workspace.context.head :: workspace.context.tail)
        runtime.targetTokens initial := by
    have base :=
      pop_input_represents workspace.context scratchZero represents
    simpa [initial, checksShape, List.append_assoc] using base
  rcases
      TargetEmitterControllerCheckTrace.normalizedInitialPop_nonempty_path
        (TargetEmitterLedger.slotCapacity raw) newest runtime.registers
        (prior ++ [second]) workspace.context.head
        workspace.context.tail runtime.targetTokens initial
        range.ledgerFits.toCheckStack (Nat.le_of_lt newestBound)
        workspace.context.stackAllowed popRepresents with
    ⟨afterPop, popPath, afterPopRepresents⟩
  have blockRepresents :
      TapeRepresents normalizedFirstPrefixRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (poppedRuntime runtime (prior ++ [second]) newest).scratch
        (poppedRuntime runtime (prior ++ [second]) newest).registers
        (poppedRuntime runtime (prior ++ [second]) newest).checks
        source
        (poppedRuntime runtime (prior ++ [second]) newest).targetTokens
        afterPop.tape :=
    popped_tape_represents workspace.context afterPopRepresents
  rcases
      normalizedFirstPrefix_path workspace
        (poppedRuntime runtime (prior ++ [second]) newest)
        prior second
        (by simpa [poppedRuntime] using range)
        (by simpa [poppedRuntime] using capturedBound)
        (by simpa [poppedRuntime] using newestBound)
        (by simp [poppedRuntime])
        secondBound afterPop.tape blockRepresents with
    ⟨blockSteps, finalTape, blockPath, finalRepresents⟩
  refine
    ⟨TargetEmitterControllerCheckTrace.nonemptyPathSteps
        (TargetEmitterLedger.slotCapacity raw)
        (prior ++ [second]) newest + blockSteps,
      finalTape, ?_, finalRepresents⟩
  exact
    AcceptPath.trans graph (.node normalizedInitialPopRef)
      (.node normalizedFirstPrefixRef) (.node normalizedLoopPopRef)
      (TargetEmitterControllerCheckTrace.nonemptyPathSteps
        (TargetEmitterLedger.slotCapacity raw)
        (prior ++ [second]) newest)
      blockSteps initialTape afterPop.tape finalTape
      popPath blockPath

/-! ### Complete fixed-graph prefix loops -/

/-- Logical result of consuming a newest-first list of later prefix checks.
The physical stack corresponding to `popOrder` is `popOrder.reverse`. -/
def nextPrefixLoop : List Nat → Runtime → Runtime
  | [], runtime => runtime
  | value :: rest, runtime =>
      nextPrefixLoop rest
        (TargetEmitterProgramSemantics.nextPrefixResult
          (poppedRuntime runtime rest.reverse value))

private theorem nextPrefix_popped_range
    {raw : RawCircuit} (runtime : Runtime)
    (prior : List Nat) (value : Nat)
    (range : ControllerRange raw runtime.registers)
    (room :
      runtime.registers.outputIndex + 2 ≤
        TargetEmitterLedger.baselineValue raw + 4) :
    ControllerRange raw
      (TargetEmitterProgramSemantics.nextPrefixResult
        (poppedRuntime runtime prior value)).registers := by
  refine
    { inputCount_eq := ?_
      normalizedGateCount_eq := ?_
      carrierWidth_eq := ?_
      baseline_eq := ?_
      currentGate_le := ?_
      outputIndex_le := ?_ }
  · simpa [poppedRuntime,
      TargetEmitterProgramSemantics.nextPrefixResult_registers] using
      range.inputCount_eq
  · simpa [poppedRuntime,
      TargetEmitterProgramSemantics.nextPrefixResult_registers] using
      range.normalizedGateCount_eq
  · simpa [poppedRuntime,
      TargetEmitterProgramSemantics.nextPrefixResult_registers] using
      range.carrierWidth_eq
  · simpa [poppedRuntime,
      TargetEmitterProgramSemantics.nextPrefixResult_registers] using
      range.baseline_eq
  · simpa [poppedRuntime,
      TargetEmitterProgramSemantics.nextPrefixResult_registers] using
      range.currentGate_le
  · simpa [poppedRuntime,
      TargetEmitterProgramSemantics.nextPrefixResult_registers] using room

private theorem firstPrefix_popped_range
    {raw : RawCircuit} (runtime : Runtime)
    (prior : List Nat) (second newest : Nat)
    (range : ControllerRange raw runtime.registers)
    (room :
      runtime.registers.outputIndex + 1 ≤
        TargetEmitterLedger.baselineValue raw + 4) :
    ControllerRange raw
      (TargetEmitterProgramSemantics.firstPrefixResult
        (poppedRuntime runtime (prior ++ [second]) newest)
        prior second).registers := by
  refine
    { inputCount_eq := ?_
      normalizedGateCount_eq := ?_
      carrierWidth_eq := ?_
      baseline_eq := ?_
      currentGate_le := ?_
      outputIndex_le := ?_ }
  · simpa [poppedRuntime,
      TargetEmitterProgramSemantics.firstPrefixResult_registers] using
      range.inputCount_eq
  · simpa [poppedRuntime,
      TargetEmitterProgramSemantics.firstPrefixResult_registers] using
      range.normalizedGateCount_eq
  · simpa [poppedRuntime,
      TargetEmitterProgramSemantics.firstPrefixResult_registers] using
      range.carrierWidth_eq
  · simpa [poppedRuntime,
      TargetEmitterProgramSemantics.firstPrefixResult_registers] using
      range.baseline_eq
  · simpa [poppedRuntime,
      TargetEmitterProgramSemantics.firstPrefixResult_registers] using
      range.currentGate_le
  · simpa [poppedRuntime,
      TargetEmitterProgramSemantics.firstPrefixResult_registers] using room

private theorem nextPrefix_popped_captured
    (runtime : Runtime) (prior : List Nat) (value : Nat) :
    (TargetEmitterProgramSemantics.nextPrefixResult
      (poppedRuntime runtime prior value)).captured =
        runtime.captured := by
  rfl

private theorem firstPrefix_popped_captured
    (runtime : Runtime) (prior : List Nat)
    (second newest : Nat) :
    (TargetEmitterProgramSemantics.firstPrefixResult
      (poppedRuntime runtime (prior ++ [second]) newest)
      prior second).captured = runtime.captured := by
  rfl

/-- Consume every remaining raw prefix check, then execute the raw positive
final block.  `popOrder` is a proof-side description of the values already
present on the physical stack, not an executable schedule. -/
theorem rawLoop_prefixes_to_beginOutput_path
    {raw : RawCircuit} {source : List WorkSymbol}
    (workspace : MarkedWorkspace source)
    (popOrder : List Nat) (runtime : Runtime)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchZero : runtime.scratch = 0)
    (checksShape : runtime.checks = popOrder.reverse)
    (valuesBound :
      ∀ value, value ∈ popOrder →
        value < TargetEmitterLedger.slotCapacity raw)
    (outputRoom :
      runtime.registers.outputIndex + 2 * popOrder.length ≤
        TargetEmitterLedger.baselineValue raw + 4)
    (captured : CapturedReady raw source runtime.captured)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents rawLoopPopRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node rawLoopPopRef)
          (.node beginOutputRef) steps initialTape finalTape ∧
      TapeRepresents beginOutputRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterProgramSemantics.finalResult
          (nextPrefixLoop popOrder runtime)
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.rawGateTrace)).scratch
        (TargetEmitterProgramSemantics.finalResult
          (nextPrefixLoop popOrder runtime)
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.rawGateTrace)).registers
        (TargetEmitterProgramSemantics.finalResult
          (nextPrefixLoop popOrder runtime)
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.rawGateTrace)).checks
        source
        (TargetEmitterProgramSemantics.finalResult
          (nextPrefixLoop popOrder runtime)
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.rawGateTrace)).targetTokens finalTape := by
  induction popOrder generalizing runtime initialTape with
  | nil =>
      have checksEmpty : runtime.checks = [] := by
        simpa using checksShape
      simpa [nextPrefixLoop] using
        (rawLoopPop_empty_to_beginOutput_path workspace runtime range
          capturedBound scratchZero checksEmpty captured initialTape
          represents)
  | cons value rest inductionHypothesis =>
      have valueBound :
          value < TargetEmitterLedger.slotCapacity raw :=
        valuesBound value (List.Mem.head rest)
      have tailBounds :
          ∀ item, item ∈ rest →
            item < TargetEmitterLedger.slotCapacity raw := by
        intro item member
        exact valuesBound item (List.Mem.tail value member)
      have currentRoom :
          runtime.registers.outputIndex + 2 ≤
            TargetEmitterLedger.baselineValue raw + 4 := by
        simp only [List.length_cons] at outputRoom
        omega
      let after :=
        TargetEmitterProgramSemantics.nextPrefixResult
          (poppedRuntime runtime rest.reverse value)
      have afterRange : ControllerRange raw after.registers := by
        exact nextPrefix_popped_range runtime rest.reverse value
          range currentRoom
      have afterCapturedBound :
          after.captured + 1 ≤
            (SourceParser.circuitCells raw).length := by
        rw [show after.captured = runtime.captured by
          exact nextPrefix_popped_captured
            runtime rest.reverse value]
        exact capturedBound
      have afterCaptured :
          CapturedReady raw source after.captured := by
        rw [show after.captured = runtime.captured by
          exact nextPrefix_popped_captured
            runtime rest.reverse value]
        exact captured
      have afterRoom :
          after.registers.outputIndex + 2 * rest.length ≤
            TargetEmitterLedger.baselineValue raw + 4 := by
        simp only [List.length_cons] at outputRoom
        simp only [after, poppedRuntime,
          TargetEmitterProgramSemantics.nextPrefixResult_registers]
        omega
      have nonemptyChecks :
          runtime.checks = rest.reverse ++ [value] := by
        simpa using checksShape
      rcases
          rawLoopPop_nonempty_next_path workspace runtime
            rest.reverse value range capturedBound scratchZero
            nonemptyChecks valueBound initialTape represents with
        ⟨linkSteps, linkTape, linkPath, linkRepresents⟩
      have afterScratch :
          after.scratch = 0 := by
        exact
          TargetEmitterProgramSemantics.nextPrefixResult_scratch
            (poppedRuntime runtime rest.reverse value)
      have afterChecks :
          after.checks = rest.reverse := by
        simpa [after, poppedRuntime] using
          (TargetEmitterProgramSemantics.nextPrefixResult_checks
            (poppedRuntime runtime rest.reverse value))
      rcases
          inductionHypothesis after afterRange afterCapturedBound
            afterScratch afterChecks tailBounds afterRoom afterCaptured
            linkTape (by simpa [after] using linkRepresents) with
        ⟨tailSteps, finalTape, tailPath, finalRepresents⟩
      refine ⟨linkSteps + tailSteps, finalTape, ?_, ?_⟩
      · exact
          AcceptPath.trans graph (.node rawLoopPopRef)
            (.node rawLoopPopRef) (.node beginOutputRef)
            linkSteps tailSteps initialTape linkTape finalTape
            linkPath tailPath
      · simpa [nextPrefixLoop, after] using finalRepresents

/-- Normalized counterpart of `rawLoop_prefixes_to_beginOutput_path`. -/
theorem normalizedLoop_prefixes_to_beginOutput_path
    {raw : RawCircuit} {source : List WorkSymbol}
    (workspace : MarkedWorkspace source)
    (popOrder : List Nat) (runtime : Runtime)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchZero : runtime.scratch = 0)
    (checksShape : runtime.checks = popOrder.reverse)
    (valuesBound :
      ∀ value, value ∈ popOrder →
        value < TargetEmitterLedger.slotCapacity raw)
    (outputRoom :
      runtime.registers.outputIndex + 2 * popOrder.length ≤
        TargetEmitterLedger.baselineValue raw + 4)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents normalizedLoopPopRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node normalizedLoopPopRef)
          (.node beginOutputRef) steps initialTape finalTape ∧
      TapeRepresents beginOutputRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterProgramSemantics.finalResult
          (nextPrefixLoop popOrder runtime)
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.traceCoordinate)).scratch
        (TargetEmitterProgramSemantics.finalResult
          (nextPrefixLoop popOrder runtime)
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.traceCoordinate)).registers
        (TargetEmitterProgramSemantics.finalResult
          (nextPrefixLoop popOrder runtime)
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.traceCoordinate)).checks
        source
        (TargetEmitterProgramSemantics.finalResult
          (nextPrefixLoop popOrder runtime)
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.traceCoordinate)).targetTokens finalTape := by
  induction popOrder generalizing runtime initialTape with
  | nil =>
      have checksEmpty : runtime.checks = [] := by
        simpa using checksShape
      simpa [nextPrefixLoop] using
        (normalizedLoopPop_empty_to_beginOutput_path workspace runtime
          range capturedBound scratchZero checksEmpty initialTape
          represents)
  | cons value rest inductionHypothesis =>
      have valueBound :
          value < TargetEmitterLedger.slotCapacity raw :=
        valuesBound value (List.Mem.head rest)
      have tailBounds :
          ∀ item, item ∈ rest →
            item < TargetEmitterLedger.slotCapacity raw := by
        intro item member
        exact valuesBound item (List.Mem.tail value member)
      have currentRoom :
          runtime.registers.outputIndex + 2 ≤
            TargetEmitterLedger.baselineValue raw + 4 := by
        simp only [List.length_cons] at outputRoom
        omega
      let after :=
        TargetEmitterProgramSemantics.nextPrefixResult
          (poppedRuntime runtime rest.reverse value)
      have afterRange : ControllerRange raw after.registers := by
        exact nextPrefix_popped_range runtime rest.reverse value
          range currentRoom
      have afterCapturedBound :
          after.captured + 1 ≤
            (SourceParser.circuitCells raw).length := by
        rw [show after.captured = runtime.captured by
          exact nextPrefix_popped_captured
            runtime rest.reverse value]
        exact capturedBound
      have afterRoom :
          after.registers.outputIndex + 2 * rest.length ≤
            TargetEmitterLedger.baselineValue raw + 4 := by
        simp only [List.length_cons] at outputRoom
        simp only [after, poppedRuntime,
          TargetEmitterProgramSemantics.nextPrefixResult_registers]
        omega
      have nonemptyChecks :
          runtime.checks = rest.reverse ++ [value] := by
        simpa using checksShape
      rcases
          normalizedLoopPop_nonempty_next_path workspace runtime
            rest.reverse value range capturedBound scratchZero
            nonemptyChecks valueBound initialTape represents with
        ⟨linkSteps, linkTape, linkPath, linkRepresents⟩
      have afterScratch :
          after.scratch = 0 := by
        exact
          TargetEmitterProgramSemantics.nextPrefixResult_scratch
            (poppedRuntime runtime rest.reverse value)
      have afterChecks :
          after.checks = rest.reverse := by
        simpa [after, poppedRuntime] using
          (TargetEmitterProgramSemantics.nextPrefixResult_checks
            (poppedRuntime runtime rest.reverse value))
      rcases
          inductionHypothesis after afterRange afterCapturedBound
            afterScratch afterChecks tailBounds afterRoom
            linkTape (by simpa [after] using linkRepresents) with
        ⟨tailSteps, finalTape, tailPath, finalRepresents⟩
      refine ⟨linkSteps + tailSteps, finalTape, ?_, ?_⟩
      · exact
          AcceptPath.trans graph (.node normalizedLoopPopRef)
            (.node normalizedLoopPopRef) (.node beginOutputRef)
            linkSteps tailSteps initialTape linkTape finalTape
            linkPath tailPath
      · simpa [nextPrefixLoop, after] using finalRepresents

/-- Complete raw nonempty prefix result: first link followed by every older
check in newest-first order. -/
def rawNonemptyPrefixResult
    (runtime : Runtime) (prior : List Nat)
    (second newest : Nat) : Runtime :=
  nextPrefixLoop prior.reverse
    (TargetEmitterProgramSemantics.firstPrefixResult
      (poppedRuntime runtime (prior ++ [second]) newest)
      prior second)

/-- Complete normalized nonempty prefix result.  It is the same pure fold;
only the graph branch and final trace coordinate differ. -/
def normalizedNonemptyPrefixResult
    (runtime : Runtime) (prior : List Nat)
    (second newest : Nat) : Runtime :=
  rawNonemptyPrefixResult runtime prior second newest

/-- Execute every raw nonempty prefix link and the raw positive final block. -/
theorem rawInitialPrefix_to_beginOutput_path
    {raw : RawCircuit} {source : List WorkSymbol}
    (workspace : MarkedWorkspace source)
    (runtime : Runtime) (prior : List Nat)
    (second newest : Nat)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchZero : runtime.scratch = 0)
    (checksShape :
      runtime.checks = prior ++ [second, newest])
    (priorBounds :
      ∀ value, value ∈ prior →
        value < TargetEmitterLedger.slotCapacity raw)
    (secondBound :
      second < TargetEmitterLedger.slotCapacity raw)
    (newestBound :
      newest < TargetEmitterLedger.slotCapacity raw)
    (outputRoom :
      runtime.registers.outputIndex + 1 + 2 * prior.length ≤
        TargetEmitterLedger.baselineValue raw + 4)
    (captured : CapturedReady raw source runtime.captured)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents rawInitialPopRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node rawInitialPopRef)
          (.node beginOutputRef) steps initialTape finalTape ∧
      TapeRepresents beginOutputRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterProgramSemantics.finalResult
          (rawNonemptyPrefixResult runtime prior second newest)
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.rawGateTrace)).scratch
        (TargetEmitterProgramSemantics.finalResult
          (rawNonemptyPrefixResult runtime prior second newest)
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.rawGateTrace)).registers
        (TargetEmitterProgramSemantics.finalResult
          (rawNonemptyPrefixResult runtime prior second newest)
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.rawGateTrace)).checks
        source
        (TargetEmitterProgramSemantics.finalResult
          (rawNonemptyPrefixResult runtime prior second newest)
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.rawGateTrace)).targetTokens finalTape := by
  rcases
      rawInitialPop_nonempty_first_path workspace runtime prior
        second newest range capturedBound scratchZero checksShape
        secondBound newestBound initialTape represents with
    ⟨firstSteps, firstTape, firstPath, firstRepresents⟩
  let after :=
    TargetEmitterProgramSemantics.firstPrefixResult
      (poppedRuntime runtime (prior ++ [second]) newest)
      prior second
  have firstRoom :
      runtime.registers.outputIndex + 1 ≤
        TargetEmitterLedger.baselineValue raw + 4 := by
    omega
  have afterRange : ControllerRange raw after.registers :=
    firstPrefix_popped_range runtime prior second newest range firstRoom
  have afterCapturedBound :
      after.captured + 1 ≤
        (SourceParser.circuitCells raw).length := by
    rw [show after.captured = runtime.captured by
      exact firstPrefix_popped_captured runtime prior second newest]
    exact capturedBound
  have afterCaptured :
      CapturedReady raw source after.captured := by
    rw [show after.captured = runtime.captured by
      exact firstPrefix_popped_captured runtime prior second newest]
    exact captured
  have afterScratch : after.scratch = 0 :=
    TargetEmitterProgramSemantics.firstPrefixResult_scratch
      (poppedRuntime runtime (prior ++ [second]) newest)
      prior second
  have afterChecks : after.checks = (prior.reverse).reverse := by
    rw [List.reverse_reverse]
    simpa [after, poppedRuntime] using
      (TargetEmitterProgramSemantics.firstPrefixResult_checks
        (poppedRuntime runtime (prior ++ [second]) newest)
        prior second)
  have reversedBounds :
      ∀ value, value ∈ prior.reverse →
        value < TargetEmitterLedger.slotCapacity raw := by
    intro value member
    exact priorBounds value (List.mem_reverse.mp member)
  have afterRoom :
      after.registers.outputIndex +
          2 * prior.reverse.length ≤
        TargetEmitterLedger.baselineValue raw + 4 := by
    simp only [after, poppedRuntime,
      TargetEmitterProgramSemantics.firstPrefixResult_registers,
      List.length_reverse]
    omega
  rcases
      rawLoop_prefixes_to_beginOutput_path workspace prior.reverse
        after afterRange afterCapturedBound afterScratch afterChecks
        reversedBounds afterRoom afterCaptured firstTape
        (by simpa [after] using firstRepresents) with
    ⟨tailSteps, finalTape, tailPath, finalRepresents⟩
  refine ⟨firstSteps + tailSteps, finalTape, ?_, ?_⟩
  · exact
      AcceptPath.trans graph (.node rawInitialPopRef)
        (.node rawLoopPopRef) (.node beginOutputRef)
        firstSteps tailSteps initialTape firstTape finalTape
        firstPath tailPath
  · simpa [rawNonemptyPrefixResult, after] using finalRepresents

/-- Execute every normalized nonempty prefix link and its normalized final
block. -/
theorem normalizedInitialPrefix_to_beginOutput_path
    {raw : RawCircuit} {source : List WorkSymbol}
    (workspace : MarkedWorkspace source)
    (runtime : Runtime) (prior : List Nat)
    (second newest : Nat)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchZero : runtime.scratch = 0)
    (checksShape :
      runtime.checks = prior ++ [second, newest])
    (priorBounds :
      ∀ value, value ∈ prior →
        value < TargetEmitterLedger.slotCapacity raw)
    (secondBound :
      second < TargetEmitterLedger.slotCapacity raw)
    (newestBound :
      newest < TargetEmitterLedger.slotCapacity raw)
    (outputRoom :
      runtime.registers.outputIndex + 1 + 2 * prior.length ≤
        TargetEmitterLedger.baselineValue raw + 4)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents normalizedInitialPopRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node normalizedInitialPopRef)
          (.node beginOutputRef) steps initialTape finalTape ∧
      TapeRepresents beginOutputRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterProgramSemantics.finalResult
          (normalizedNonemptyPrefixResult runtime prior second newest)
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.traceCoordinate)).scratch
        (TargetEmitterProgramSemantics.finalResult
          (normalizedNonemptyPrefixResult runtime prior second newest)
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.traceCoordinate)).registers
        (TargetEmitterProgramSemantics.finalResult
          (normalizedNonemptyPrefixResult runtime prior second newest)
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.traceCoordinate)).checks
        source
        (TargetEmitterProgramSemantics.finalResult
          (normalizedNonemptyPrefixResult runtime prior second newest)
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.traceCoordinate)).targetTokens finalTape := by
  rcases
      normalizedInitialPop_nonempty_first_path workspace runtime prior
        second newest range capturedBound scratchZero checksShape
        secondBound newestBound initialTape represents with
    ⟨firstSteps, firstTape, firstPath, firstRepresents⟩
  let after :=
    TargetEmitterProgramSemantics.firstPrefixResult
      (poppedRuntime runtime (prior ++ [second]) newest)
      prior second
  have firstRoom :
      runtime.registers.outputIndex + 1 ≤
        TargetEmitterLedger.baselineValue raw + 4 := by
    omega
  have afterRange : ControllerRange raw after.registers :=
    firstPrefix_popped_range runtime prior second newest range firstRoom
  have afterCapturedBound :
      after.captured + 1 ≤
        (SourceParser.circuitCells raw).length := by
    rw [show after.captured = runtime.captured by
      exact firstPrefix_popped_captured runtime prior second newest]
    exact capturedBound
  have afterScratch : after.scratch = 0 :=
    TargetEmitterProgramSemantics.firstPrefixResult_scratch
      (poppedRuntime runtime (prior ++ [second]) newest)
      prior second
  have afterChecks : after.checks = (prior.reverse).reverse := by
    rw [List.reverse_reverse]
    simpa [after, poppedRuntime] using
      (TargetEmitterProgramSemantics.firstPrefixResult_checks
        (poppedRuntime runtime (prior ++ [second]) newest)
        prior second)
  have reversedBounds :
      ∀ value, value ∈ prior.reverse →
        value < TargetEmitterLedger.slotCapacity raw := by
    intro value member
    exact priorBounds value (List.mem_reverse.mp member)
  have afterRoom :
      after.registers.outputIndex +
          2 * prior.reverse.length ≤
        TargetEmitterLedger.baselineValue raw + 4 := by
    simp only [after, poppedRuntime,
      TargetEmitterProgramSemantics.firstPrefixResult_registers,
      List.length_reverse]
    omega
  rcases
      normalizedLoop_prefixes_to_beginOutput_path workspace
        prior.reverse after afterRange afterCapturedBound
        afterScratch afterChecks reversedBounds afterRoom firstTape
        (by simpa [after] using firstRepresents) with
    ⟨tailSteps, finalTape, tailPath, finalRepresents⟩
  refine ⟨firstSteps + tailSteps, finalTape, ?_, ?_⟩
  · exact
      AcceptPath.trans graph (.node normalizedInitialPopRef)
        (.node normalizedLoopPopRef) (.node beginOutputRef)
        firstSteps tailSteps initialTape firstTape finalTape
        firstPath tailPath
  · simpa [normalizedNonemptyPrefixResult,
      rawNonemptyPrefixResult, after] using finalRepresents

/-! ### Raw output-gate reset through the complete prefix -/

/-- Reset scratch, observe an empty raw check stack, and emit the complete
false-output final suffix through `beginOutputRef`. -/
theorem outputGateReset_empty_to_beginOutput_path
    {raw : RawCircuit} {source : List WorkSymbol}
    (workspace : MarkedWorkspace source)
    (runtime : Runtime)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (checksEmpty : runtime.checks = [])
    (captured : CapturedReady raw source runtime.captured)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents outputGateResetRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node outputGateResetRef)
          (.node beginOutputRef) steps initialTape finalTape ∧
      TapeRepresents beginOutputRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterProgramSemantics.finalResult
          (TargetEmitterProgramSemantics.resetScratchResult runtime)
          TargetEmitterPlan.finalZeroPlan).scratch
        (TargetEmitterProgramSemantics.finalResult
          (TargetEmitterProgramSemantics.resetScratchResult runtime)
          TargetEmitterPlan.finalZeroPlan).registers
        (TargetEmitterProgramSemantics.finalResult
          (TargetEmitterProgramSemantics.resetScratchResult runtime)
          TargetEmitterPlan.finalZeroPlan).checks
        source
        (TargetEmitterProgramSemantics.finalResult
          (TargetEmitterProgramSemantics.resetScratchResult runtime)
          TargetEmitterPlan.finalZeroPlan).targetTokens finalTape := by
  rcases
      outputGateReset_path workspace.context runtime scratchBound
        initialTape represents with
    ⟨resetSteps, resetTape, resetPath, resetRepresents⟩
  let resetRuntime :=
    TargetEmitterProgramSemantics.resetScratchResult runtime
  have resetRange : ControllerRange raw resetRuntime.registers := by
    simpa [resetRuntime,
      TargetEmitterProgramSemantics.resetScratchResult] using range
  have resetCapturedBound :
      resetRuntime.captured + 1 ≤
        (SourceParser.circuitCells raw).length := by
    simpa [resetRuntime,
      TargetEmitterProgramSemantics.resetScratchResult] using
      capturedBound
  have resetChecks : resetRuntime.checks = [] := by
    simpa [resetRuntime,
      TargetEmitterProgramSemantics.resetScratchResult] using checksEmpty
  have resetCaptured :
      CapturedReady raw source resetRuntime.captured := by
    simpa [resetRuntime,
      TargetEmitterProgramSemantics.resetScratchResult] using captured
  rcases
      rawInitialPop_empty_to_beginOutput_path workspace resetRuntime
        resetRange resetCapturedBound rfl resetChecks resetCaptured
        resetTape (by simpa [resetRuntime] using resetRepresents) with
    ⟨tailSteps, finalTape, tailPath, finalRepresents⟩
  refine ⟨resetSteps + tailSteps, finalTape, ?_, ?_⟩
  · exact
      AcceptPath.trans graph (.node outputGateResetRef)
        (.node rawInitialPopRef) (.node beginOutputRef)
        resetSteps tailSteps initialTape resetTape finalTape
        resetPath tailPath
  · simpa [resetRuntime] using finalRepresents

/-- Reset scratch and execute the complete nonempty raw prefix and final
suffix through `beginOutputRef`. -/
theorem outputGateReset_nonempty_to_beginOutput_path
    {raw : RawCircuit} {source : List WorkSymbol}
    (workspace : MarkedWorkspace source)
    (runtime : Runtime) (prior : List Nat)
    (second newest : Nat)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
    (checksShape :
      runtime.checks = prior ++ [second, newest])
    (priorBounds :
      ∀ value, value ∈ prior →
        value < TargetEmitterLedger.slotCapacity raw)
    (secondBound :
      second < TargetEmitterLedger.slotCapacity raw)
    (newestBound :
      newest < TargetEmitterLedger.slotCapacity raw)
    (outputRoom :
      runtime.registers.outputIndex + 1 + 2 * prior.length ≤
        TargetEmitterLedger.baselineValue raw + 4)
    (captured : CapturedReady raw source runtime.captured)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents outputGateResetRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node outputGateResetRef)
          (.node beginOutputRef) steps initialTape finalTape ∧
      let resetRuntime :=
        TargetEmitterProgramSemantics.resetScratchResult runtime
      TapeRepresents beginOutputRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterProgramSemantics.finalResult
          (rawNonemptyPrefixResult
            resetRuntime prior second newest)
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.rawGateTrace)).scratch
        (TargetEmitterProgramSemantics.finalResult
          (rawNonemptyPrefixResult
            resetRuntime prior second newest)
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.rawGateTrace)).registers
        (TargetEmitterProgramSemantics.finalResult
          (rawNonemptyPrefixResult
            resetRuntime prior second newest)
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.rawGateTrace)).checks
        source
        (TargetEmitterProgramSemantics.finalResult
          (rawNonemptyPrefixResult
            resetRuntime prior second newest)
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.rawGateTrace)).targetTokens finalTape := by
  rcases
      outputGateReset_path workspace.context runtime scratchBound
        initialTape represents with
    ⟨resetSteps, resetTape, resetPath, resetRepresents⟩
  let resetRuntime :=
    TargetEmitterProgramSemantics.resetScratchResult runtime
  have resetRange : ControllerRange raw resetRuntime.registers := by
    simpa [resetRuntime,
      TargetEmitterProgramSemantics.resetScratchResult] using range
  have resetCapturedBound :
      resetRuntime.captured + 1 ≤
        (SourceParser.circuitCells raw).length := by
    simpa [resetRuntime,
      TargetEmitterProgramSemantics.resetScratchResult] using
      capturedBound
  have resetChecks :
      resetRuntime.checks = prior ++ [second, newest] := by
    simpa [resetRuntime,
      TargetEmitterProgramSemantics.resetScratchResult] using checksShape
  have resetOutputRoom :
      resetRuntime.registers.outputIndex + 1 + 2 * prior.length ≤
        TargetEmitterLedger.baselineValue raw + 4 := by
    simpa [resetRuntime,
      TargetEmitterProgramSemantics.resetScratchResult] using outputRoom
  have resetCaptured :
      CapturedReady raw source resetRuntime.captured := by
    simpa [resetRuntime,
      TargetEmitterProgramSemantics.resetScratchResult] using captured
  rcases
      rawInitialPrefix_to_beginOutput_path workspace resetRuntime prior
        second newest resetRange resetCapturedBound rfl resetChecks
        priorBounds secondBound newestBound resetOutputRoom resetCaptured
        resetTape (by simpa [resetRuntime] using resetRepresents) with
    ⟨tailSteps, finalTape, tailPath, finalRepresents⟩
  refine ⟨resetSteps + tailSteps, finalTape, ?_, ?_⟩
  · exact
      AcceptPath.trans graph (.node outputGateResetRef)
        (.node rawInitialPopRef) (.node beginOutputRef)
        resetSteps tailSteps initialTape resetTape finalTape
        resetPath tailPath
  · simpa [resetRuntime] using finalRepresents

end PNP.Concrete.LockedNAND.TargetEmitterControllerPrefixTrace
