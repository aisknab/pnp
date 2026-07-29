/-
Copyright (c) 2026 PNP Labs.

Constructive work bounds for the check-stack prefix fold and its fixed final
gate block in the grammar-only locked-NAND target emitter.

The controller still follows the literal stack-pop branches and materialized
primitive programs proved by the exact trace.  The quantities below are
proof-side envelopes only: no runtime value, stack entry, or schedule is
consulted by the executable graph.
-/

import PNP.Concrete.LockedNANDTargetEmitterControllerPrefixTrace
import PNP.Concrete.LockedNANDTargetEmitterRuntimeProgramBound

namespace PNP.Concrete.LockedNAND.TargetEmitterControllerPrefixBound

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
abbrev TapeRepresents :=
  TargetEmitterControllerPrefixTrace.TapeRepresents

/-! ### Runtime-sensitive block envelopes -/

/-- Primitive-program envelope for the first two-gate prefix link. -/
def firstPrefixBlockEnvelope (raw : RawCircuit)
    (source : List WorkSymbol) (runtime : Runtime) : Nat :=
  TargetEmitterRuntimeProgramBound.programWorkEnvelope
    (TargetEmitterLedger.slotCapacity raw) source runtime
    TargetEmitterController.Plan.firstPrefix

/-- Primitive-program envelope for every later two-gate prefix link. -/
def nextPrefixBlockEnvelope (raw : RawCircuit)
    (source : List WorkSymbol) (runtime : Runtime) : Nat :=
  TargetEmitterRuntimeProgramBound.programWorkEnvelope
    (TargetEmitterLedger.slotCapacity raw) source runtime
    TargetEmitterController.Plan.nextPrefix

/-- Primitive-program envelope for the raw false-output final block. -/
def finalZeroBlockEnvelope (raw : RawCircuit)
    (source : List WorkSymbol) (runtime : Runtime) : Nat :=
  TargetEmitterRuntimeProgramBound.programWorkEnvelope
    (TargetEmitterLedger.slotCapacity raw) source runtime
    TargetEmitterController.Plan.finalZero

/-- Primitive-program envelope for the raw positive-output final block. -/
def finalRawBlockEnvelope (raw : RawCircuit)
    (source : List WorkSymbol) (runtime : Runtime) : Nat :=
  TargetEmitterRuntimeProgramBound.programWorkEnvelope
    (TargetEmitterLedger.slotCapacity raw) source runtime
    TargetEmitterController.Plan.finalRaw

/-- Primitive-program envelope for the normalized positive-output final
block. -/
def finalNormalizedBlockEnvelope (raw : RawCircuit)
    (source : List WorkSymbol) (runtime : Runtime) : Nat :=
  TargetEmitterRuntimeProgramBound.programWorkEnvelope
    (TargetEmitterLedger.slotCapacity raw) source runtime
    TargetEmitterController.Plan.finalNormalized

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

private theorem firstPrefix_compiled :
    compileProgram Plan.firstPrefix = some firstPrefixPrograms := by
  rfl

private theorem nextPrefix_compiled :
    compileProgram Plan.nextPrefix = some nextPrefixPrograms := by
  rfl

private theorem finalRaw_compiled :
    compileProgram Plan.finalRaw = some finalRawPrograms := by
  rfl

private theorem finalZero_compiled :
    compileProgram Plan.finalZero = some finalZeroPrograms := by
  rfl

private theorem finalNormalized_compiled :
    compileProgram Plan.finalNormalized =
      some finalNormalizedPrograms := by
  rfl

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

private theorem materializedBlock_path_bounded
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
    (initialScratchBound : initial.scratch ≤ capacity)
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
        source final.targetTokens finalTape ∧
      steps ≤
        TargetEmitterRuntimeProgramBound.programWorkEnvelope
          capacity source initial descriptor.primitives := by
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
      TargetEmitterRuntimeProgramBound.ProgramSafe.descriptor_acceptPath_bounded
        descriptor descriptorMember safe initialScratchBound programs
        compiled programsNonempty 0 initialActual inputRepresents with
    ⟨steps, actualFinal, path, finalRepresents, bound⟩
  refine ⟨steps, actualFinal.tape, ?_, ?_, bound⟩
  · simpa [referenceEq, continuationEq] using path
  · exact
      represents_at_state
        (newState := continuation.startState) finalRepresents

private theorem firstPrefixBlock_path_bounded
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
          runtime prior newest).targetTokens finalTape ∧
      steps ≤ firstPrefixBlockEnvelope raw source runtime := by
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
  rcases
      materializedBlock_path_bounded descriptor descriptorMember
        firstPrefixPrograms
        (by simpa [primitivesEq] using firstPrefix_compiled)
        firstPrefixPrograms_nonempty reference continuation
        referenceEq continuationEq entryEq safe
        (Nat.le_of_lt scratchBound) initialTape represents with
    ⟨steps, finalTape, path, finalRepresents, bound⟩
  exact
    ⟨steps, finalTape, path, finalRepresents,
      by
        simpa [firstPrefixBlockEnvelope, primitivesEq] using bound⟩

private theorem rawFirstPrefix_path_bounded
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
          runtime prior newest).targetTokens finalTape ∧
      steps ≤ firstPrefixBlockEnvelope raw source runtime := by
  exact
    firstPrefixBlock_path_bounded rawFirstPrefixDescriptor
      rawFirstPrefixDescriptor_member rawFirstPrefixRef rawLoopPopRef
      rfl rfl rfl workspace runtime prior newest range capturedBound
      scratchBound checksShape newestBound rfl initialTape represents

private theorem normalizedFirstPrefix_path_bounded
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
          runtime prior newest).targetTokens finalTape ∧
      steps ≤ firstPrefixBlockEnvelope raw source runtime := by
  exact
    firstPrefixBlock_path_bounded normalizedFirstPrefixDescriptor
      normalizedFirstPrefixDescriptor_member normalizedFirstPrefixRef
      normalizedLoopPopRef rfl rfl rfl workspace runtime prior newest
      range capturedBound scratchBound checksShape newestBound rfl
      initialTape represents

private theorem nextPrefixBlock_path_bounded
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
        finalTape ∧
      steps ≤ nextPrefixBlockEnvelope raw source runtime := by
  have safe :
      ProgramSafe (TargetEmitterLedger.slotCapacity raw)
        source workspace.context descriptor.primitives runtime
        (TargetEmitterProgramSemantics.nextPrefixResult runtime) := by
    rw [primitivesEq]
    exact
      TargetEmitterRuntimeProgramSafety.nextPrefix_safe
        workspace range capturedBound scratchBound
  rcases
      materializedBlock_path_bounded descriptor descriptorMember
        nextPrefixPrograms
        (by simpa [primitivesEq] using nextPrefix_compiled)
        nextPrefixPrograms_nonempty reference continuation
        referenceEq continuationEq entryEq safe
        (Nat.le_of_lt scratchBound) initialTape represents with
    ⟨steps, finalTape, path, finalRepresents, bound⟩
  exact
    ⟨steps, finalTape, path, finalRepresents,
      by
        simpa [nextPrefixBlockEnvelope, primitivesEq] using bound⟩

private theorem rawNextPrefix_path_bounded
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
        finalTape ∧
      steps ≤ nextPrefixBlockEnvelope raw source runtime := by
  exact
    nextPrefixBlock_path_bounded rawNextPrefixDescriptor
      rawNextPrefixDescriptor_member rawNextPrefixRef rawLoopPopRef
      rfl rfl rfl workspace runtime range capturedBound scratchBound
      rfl initialTape represents

private theorem normalizedNextPrefix_path_bounded
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
        finalTape ∧
      steps ≤ nextPrefixBlockEnvelope raw source runtime := by
  exact
    nextPrefixBlock_path_bounded normalizedNextPrefixDescriptor
      normalizedNextPrefixDescriptor_member normalizedNextPrefixRef
      normalizedLoopPopRef rfl rfl rfl workspace runtime range
      capturedBound scratchBound rfl initialTape represents

private theorem finalBlock_path_bounded
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
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw)
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
        final.targetTokens finalTape ∧
      steps ≤
        TargetEmitterRuntimeProgramBound.programWorkEnvelope
          (TargetEmitterLedger.slotCapacity raw) source runtime
          descriptor.primitives := by
  exact
    materializedBlock_path_bounded descriptor descriptorMember programs
      compiled programsNonempty reference beginOutputRef referenceEq
      continuationEq entryEq safe (Nat.le_of_lt scratchBound)
      initialTape represents

private theorem rawFinalZero_path_bounded
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
          TargetEmitterPlan.finalZeroPlan).targetTokens finalTape ∧
      steps ≤ finalZeroBlockEnvelope raw source runtime := by
  have safe :=
    TargetEmitterRuntimeProgramSafety.finalZero_safe
      workspace range capturedBound scratchBound captured
  rcases
      finalBlock_path_bounded rawFinalZeroDescriptor
        rawFinalZeroDescriptor_member finalZeroPrograms
        (by simpa [rawFinalZeroDescriptor] using finalZero_compiled)
        finalZeroPrograms_nonempty rawFinalZeroRef rfl rfl rfl
        workspace runtime
        (TargetEmitterProgramSemantics.finalResult runtime
          TargetEmitterPlan.finalZeroPlan)
        (by simpa [rawFinalZeroDescriptor] using safe)
        scratchBound initialTape represents with
    ⟨steps, finalTape, path, finalRepresents, bound⟩
  exact
    ⟨steps, finalTape, path, finalRepresents,
      by
        simpa [finalZeroBlockEnvelope, rawFinalZeroDescriptor] using
          bound⟩

private theorem rawFinal_path_bounded
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
            TargetEmitterPlan.rawGateTrace)).targetTokens finalTape ∧
      steps ≤ finalRawBlockEnvelope raw source runtime := by
  have safe :=
    TargetEmitterRuntimeProgramSafety.finalRaw_safe
      workspace range capturedBound scratchBound captured
  rcases
      finalBlock_path_bounded rawFinalDescriptor rawFinalDescriptor_member
        finalRawPrograms
        (by simpa [rawFinalDescriptor] using finalRaw_compiled)
        finalRawPrograms_nonempty rawFinalRef rfl rfl rfl
        workspace runtime
        (TargetEmitterProgramSemantics.finalResult runtime
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.rawGateTrace))
        (by simpa [rawFinalDescriptor] using safe)
        scratchBound initialTape represents with
    ⟨steps, finalTape, path, finalRepresents, bound⟩
  exact
    ⟨steps, finalTape, path, finalRepresents,
      by
        simpa [finalRawBlockEnvelope, rawFinalDescriptor] using bound⟩

private theorem normalizedFinal_path_bounded
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
            TargetEmitterPlan.traceCoordinate)).targetTokens finalTape ∧
      steps ≤ finalNormalizedBlockEnvelope raw source runtime := by
  have safe :=
    TargetEmitterRuntimeProgramSafety.finalNormalized_safe
      workspace range capturedBound scratchBound
  rcases
      finalBlock_path_bounded normalizedFinalDescriptor
        normalizedFinalDescriptor_member finalNormalizedPrograms
        (by simpa [normalizedFinalDescriptor] using
          finalNormalized_compiled)
        finalNormalizedPrograms_nonempty normalizedFinalRef rfl rfl rfl
        workspace runtime
        (TargetEmitterProgramSemantics.finalResult runtime
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.traceCoordinate))
        (by simpa [normalizedFinalDescriptor] using safe)
        scratchBound initialTape represents with
    ⟨steps, finalTape, path, finalRepresents, bound⟩
  exact
    ⟨steps, finalTape, path, finalRepresents,
      by
        simpa [finalNormalizedBlockEnvelope,
          normalizedFinalDescriptor] using bound⟩

/-! ### Literal pop accounting and recursive envelopes -/

private abbrev poppedRuntime :=
  TargetEmitterControllerPrefixTrace.poppedRuntime

/-- Exact work envelope for the empty raw initial-pop branch. -/
def rawInitialEmptyEnvelope (raw : RawCircuit)
    (source : List WorkSymbol) (runtime : Runtime) : Nat :=
  TargetEmitterControllerCheckTrace.emptyPathSteps
      (TargetEmitterLedger.slotCapacity raw) +
    finalZeroBlockEnvelope raw source runtime

/-- Recursive work envelope for the raw later-link loop and positive final
block. -/
def rawLoopEnvelope (raw : RawCircuit) (source : List WorkSymbol) :
    List Nat → Runtime → Nat
  | [], runtime =>
      TargetEmitterControllerCheckTrace.emptyPathSteps
          (TargetEmitterLedger.slotCapacity raw) +
        finalRawBlockEnvelope raw source runtime
  | value :: rest, runtime =>
      let popped := poppedRuntime runtime rest.reverse value
      let after :=
        TargetEmitterProgramSemantics.nextPrefixResult popped
      TargetEmitterControllerCheckTrace.nonemptyPathSteps
          (TargetEmitterLedger.slotCapacity raw) rest.reverse value +
        nextPrefixBlockEnvelope raw source popped +
        rawLoopEnvelope raw source rest after

/-- Recursive work envelope for the normalized later-link loop and positive
final block. -/
def normalizedLoopEnvelope (raw : RawCircuit)
    (source : List WorkSymbol) :
    List Nat → Runtime → Nat
  | [], runtime =>
      TargetEmitterControllerCheckTrace.emptyPathSteps
          (TargetEmitterLedger.slotCapacity raw) +
        finalNormalizedBlockEnvelope raw source runtime
  | value :: rest, runtime =>
      let popped := poppedRuntime runtime rest.reverse value
      let after :=
        TargetEmitterProgramSemantics.nextPrefixResult popped
      TargetEmitterControllerCheckTrace.nonemptyPathSteps
          (TargetEmitterLedger.slotCapacity raw) rest.reverse value +
        nextPrefixBlockEnvelope raw source popped +
        normalizedLoopEnvelope raw source rest after

/-- Exact work envelope for a nonempty raw initial prefix, all older links,
and the raw final block. -/
def rawNonemptyPrefixEnvelope (raw : RawCircuit)
    (source : List WorkSymbol) (runtime : Runtime)
    (prior : List Nat) (second newest : Nat) : Nat :=
  let popped :=
    poppedRuntime runtime (prior ++ [second]) newest
  let after :=
    TargetEmitterProgramSemantics.firstPrefixResult
      popped prior second
  TargetEmitterControllerCheckTrace.nonemptyPathSteps
      (TargetEmitterLedger.slotCapacity raw)
      (prior ++ [second]) newest +
    firstPrefixBlockEnvelope raw source popped +
    rawLoopEnvelope raw source prior.reverse after

/-- Exact work envelope for a nonempty normalized initial prefix, all older
links, and the normalized final block. -/
def normalizedNonemptyPrefixEnvelope (raw : RawCircuit)
    (source : List WorkSymbol) (runtime : Runtime)
    (prior : List Nat) (second newest : Nat) : Nat :=
  let popped :=
    poppedRuntime runtime (prior ++ [second]) newest
  let after :=
    TargetEmitterProgramSemantics.firstPrefixResult
      popped prior second
  TargetEmitterControllerCheckTrace.nonemptyPathSteps
      (TargetEmitterLedger.slotCapacity raw)
      (prior ++ [second]) newest +
    firstPrefixBlockEnvelope raw source popped +
    normalizedLoopEnvelope raw source prior.reverse after

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
    simpa [TargetEmitterControllerPrefixTrace.TapeRepresents,
      scratchZero, context.source_eq] using represents
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
  simpa [TargetEmitterControllerPrefixTrace.TapeRepresents,
    TargetEmitterControllerPrefixTrace.poppedRuntime,
    context.source_eq] using transported

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
  simpa [TargetEmitterControllerPrefixTrace.TapeRepresents,
    context.source_eq] using transported

/-- Empty raw initial stack: literal reject bridge plus bounded false-output
final block. -/
theorem rawInitialPop_empty_to_beginOutput_path_bounded
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
          TargetEmitterPlan.finalZeroPlan).targetTokens finalTape ∧
      steps ≤ rawInitialEmptyEnvelope raw source runtime := by
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
      rawFinalZero_path_bounded workspace runtime range capturedBound
        (by
          rw [scratchZero]
          simp [TargetEmitterLedger.slotCapacity])
        captured afterPop.tape finalRepresents with
    ⟨finalSteps, finalTape, finalPath, outputRepresents, finalBound⟩
  refine
    ⟨TargetEmitterControllerCheckTrace.emptyPathSteps
        (TargetEmitterLedger.slotCapacity raw) + finalSteps,
      finalTape, ?_, outputRepresents, ?_⟩
  · exact
      AcceptPath.trans graph (.node rawInitialPopRef)
        (.node rawFinalZeroRef) (.node beginOutputRef)
        (TargetEmitterControllerCheckTrace.emptyPathSteps
          (TargetEmitterLedger.slotCapacity raw))
        finalSteps initialTape afterPop.tape finalTape
        popPath finalPath
  · unfold rawInitialEmptyEnvelope
    omega

/-- Empty raw loop stack: literal reject bridge plus bounded raw positive
final block. -/
theorem rawLoopPop_empty_to_beginOutput_path_bounded
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
            TargetEmitterPlan.rawGateTrace)).targetTokens finalTape ∧
      steps ≤ rawLoopEnvelope raw source [] runtime := by
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
      rawFinal_path_bounded workspace runtime range capturedBound
        (by
          rw [scratchZero]
          simp [TargetEmitterLedger.slotCapacity])
        captured afterPop.tape finalRepresents with
    ⟨finalSteps, finalTape, finalPath, outputRepresents, finalBound⟩
  refine
    ⟨TargetEmitterControllerCheckTrace.emptyPathSteps
        (TargetEmitterLedger.slotCapacity raw) + finalSteps,
      finalTape, ?_, outputRepresents, ?_⟩
  · exact
      AcceptPath.trans graph (.node rawLoopPopRef)
        (.node rawFinalRef) (.node beginOutputRef)
        (TargetEmitterControllerCheckTrace.emptyPathSteps
          (TargetEmitterLedger.slotCapacity raw))
        finalSteps initialTape afterPop.tape finalTape
        popPath finalPath
  · simp only [rawLoopEnvelope]
    omega

/-- Empty normalized loop stack: literal reject bridge plus bounded
normalized positive final block. -/
theorem normalizedLoopPop_empty_to_beginOutput_path_bounded
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
            TargetEmitterPlan.traceCoordinate)).targetTokens finalTape ∧
      steps ≤ normalizedLoopEnvelope raw source [] runtime := by
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
      normalizedFinal_path_bounded workspace runtime range capturedBound
        (by
          rw [scratchZero]
          simp [TargetEmitterLedger.slotCapacity])
        afterPop.tape finalRepresents with
    ⟨finalSteps, finalTape, finalPath, outputRepresents, finalBound⟩
  refine
    ⟨TargetEmitterControllerCheckTrace.emptyPathSteps
        (TargetEmitterLedger.slotCapacity raw) + finalSteps,
      finalTape, ?_, outputRepresents, ?_⟩
  · exact
      AcceptPath.trans graph (.node normalizedLoopPopRef)
        (.node normalizedFinalRef) (.node beginOutputRef)
        (TargetEmitterControllerCheckTrace.emptyPathSteps
          (TargetEmitterLedger.slotCapacity raw))
        finalSteps initialTape afterPop.tape finalTape
        popPath finalPath
  · simp only [normalizedLoopEnvelope]
    omega

private theorem rawLoopPop_nonempty_next_path_bounded
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
          (poppedRuntime runtime prior value)).targetTokens finalTape ∧
      steps ≤
        TargetEmitterControllerCheckTrace.nonemptyPathSteps
            (TargetEmitterLedger.slotCapacity raw) prior value +
          nextPrefixBlockEnvelope raw source
            (poppedRuntime runtime prior value) := by
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
      rawNextPrefix_path_bounded workspace
        (poppedRuntime runtime prior value)
        (by
          simpa [TargetEmitterControllerPrefixTrace.poppedRuntime] using
            range)
        (by
          simpa [TargetEmitterControllerPrefixTrace.poppedRuntime] using
            capturedBound)
        (by
          simpa [TargetEmitterControllerPrefixTrace.poppedRuntime] using
            valueBound)
        afterPop.tape blockRepresents with
    ⟨blockSteps, finalTape, blockPath, finalRepresents, blockBound⟩
  refine
    ⟨TargetEmitterControllerCheckTrace.nonemptyPathSteps
        (TargetEmitterLedger.slotCapacity raw) prior value +
      blockSteps,
      finalTape, ?_, finalRepresents, ?_⟩
  · exact
      AcceptPath.trans graph (.node rawLoopPopRef)
        (.node rawNextPrefixRef) (.node rawLoopPopRef)
        (TargetEmitterControllerCheckTrace.nonemptyPathSteps
          (TargetEmitterLedger.slotCapacity raw) prior value)
        blockSteps initialTape afterPop.tape finalTape
        popPath blockPath
  · omega

private theorem normalizedLoopPop_nonempty_next_path_bounded
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
          (poppedRuntime runtime prior value)).targetTokens finalTape ∧
      steps ≤
        TargetEmitterControllerCheckTrace.nonemptyPathSteps
            (TargetEmitterLedger.slotCapacity raw) prior value +
          nextPrefixBlockEnvelope raw source
            (poppedRuntime runtime prior value) := by
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
      normalizedNextPrefix_path_bounded workspace
        (poppedRuntime runtime prior value)
        (by
          simpa [TargetEmitterControllerPrefixTrace.poppedRuntime] using
            range)
        (by
          simpa [TargetEmitterControllerPrefixTrace.poppedRuntime] using
            capturedBound)
        (by
          simpa [TargetEmitterControllerPrefixTrace.poppedRuntime] using
            valueBound)
        afterPop.tape blockRepresents with
    ⟨blockSteps, finalTape, blockPath, finalRepresents, blockBound⟩
  refine
    ⟨TargetEmitterControllerCheckTrace.nonemptyPathSteps
        (TargetEmitterLedger.slotCapacity raw) prior value +
      blockSteps,
      finalTape, ?_, finalRepresents, ?_⟩
  · exact
      AcceptPath.trans graph (.node normalizedLoopPopRef)
        (.node normalizedNextPrefixRef) (.node normalizedLoopPopRef)
        (TargetEmitterControllerCheckTrace.nonemptyPathSteps
          (TargetEmitterLedger.slotCapacity raw) prior value)
        blockSteps initialTape afterPop.tape finalTape
        popPath blockPath
  · omega

private theorem rawInitialPop_nonempty_first_path_bounded
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
          prior second).targetTokens finalTape ∧
      steps ≤
        TargetEmitterControllerCheckTrace.nonemptyPathSteps
            (TargetEmitterLedger.slotCapacity raw)
            (prior ++ [second]) newest +
          firstPrefixBlockEnvelope raw source
            (poppedRuntime runtime (prior ++ [second]) newest) := by
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
      rawFirstPrefix_path_bounded workspace
        (poppedRuntime runtime (prior ++ [second]) newest)
        prior second
        (by
          simpa [TargetEmitterControllerPrefixTrace.poppedRuntime] using
            range)
        (by
          simpa [TargetEmitterControllerPrefixTrace.poppedRuntime] using
            capturedBound)
        (by
          simpa [TargetEmitterControllerPrefixTrace.poppedRuntime] using
            newestBound)
        (by
          simp [TargetEmitterControllerPrefixTrace.poppedRuntime])
        secondBound afterPop.tape blockRepresents with
    ⟨blockSteps, finalTape, blockPath, finalRepresents, blockBound⟩
  refine
    ⟨TargetEmitterControllerCheckTrace.nonemptyPathSteps
        (TargetEmitterLedger.slotCapacity raw)
        (prior ++ [second]) newest + blockSteps,
      finalTape, ?_, finalRepresents, ?_⟩
  · exact
      AcceptPath.trans graph (.node rawInitialPopRef)
        (.node rawFirstPrefixRef) (.node rawLoopPopRef)
        (TargetEmitterControllerCheckTrace.nonemptyPathSteps
          (TargetEmitterLedger.slotCapacity raw)
          (prior ++ [second]) newest)
        blockSteps initialTape afterPop.tape finalTape
        popPath blockPath
  · omega

private theorem normalizedInitialPop_nonempty_first_path_bounded
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
          prior second).targetTokens finalTape ∧
      steps ≤
        TargetEmitterControllerCheckTrace.nonemptyPathSteps
            (TargetEmitterLedger.slotCapacity raw)
            (prior ++ [second]) newest +
          firstPrefixBlockEnvelope raw source
            (poppedRuntime runtime (prior ++ [second]) newest) := by
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
      normalizedFirstPrefix_path_bounded workspace
        (poppedRuntime runtime (prior ++ [second]) newest)
        prior second
        (by
          simpa [TargetEmitterControllerPrefixTrace.poppedRuntime] using
            range)
        (by
          simpa [TargetEmitterControllerPrefixTrace.poppedRuntime] using
            capturedBound)
        (by
          simpa [TargetEmitterControllerPrefixTrace.poppedRuntime] using
            newestBound)
        (by
          simp [TargetEmitterControllerPrefixTrace.poppedRuntime])
        secondBound afterPop.tape blockRepresents with
    ⟨blockSteps, finalTape, blockPath, finalRepresents, blockBound⟩
  refine
    ⟨TargetEmitterControllerCheckTrace.nonemptyPathSteps
        (TargetEmitterLedger.slotCapacity raw)
        (prior ++ [second]) newest + blockSteps,
      finalTape, ?_, finalRepresents, ?_⟩
  · exact
      AcceptPath.trans graph (.node normalizedInitialPopRef)
        (.node normalizedFirstPrefixRef) (.node normalizedLoopPopRef)
        (TargetEmitterControllerCheckTrace.nonemptyPathSteps
          (TargetEmitterLedger.slotCapacity raw)
          (prior ++ [second]) newest)
        blockSteps initialTape afterPop.tape finalTape
        popPath blockPath
  · omega

/-! ### Complete bounded prefix folds -/

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
  · simpa [TargetEmitterControllerPrefixTrace.poppedRuntime,
      TargetEmitterProgramSemantics.nextPrefixResult_registers] using
      range.inputCount_eq
  · simpa [TargetEmitterControllerPrefixTrace.poppedRuntime,
      TargetEmitterProgramSemantics.nextPrefixResult_registers] using
      range.normalizedGateCount_eq
  · simpa [TargetEmitterControllerPrefixTrace.poppedRuntime,
      TargetEmitterProgramSemantics.nextPrefixResult_registers] using
      range.carrierWidth_eq
  · simpa [TargetEmitterControllerPrefixTrace.poppedRuntime,
      TargetEmitterProgramSemantics.nextPrefixResult_registers] using
      range.baseline_eq
  · simpa [TargetEmitterControllerPrefixTrace.poppedRuntime,
      TargetEmitterProgramSemantics.nextPrefixResult_registers] using
      range.currentGate_le
  · simpa [TargetEmitterControllerPrefixTrace.poppedRuntime,
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
  · simpa [TargetEmitterControllerPrefixTrace.poppedRuntime,
      TargetEmitterProgramSemantics.firstPrefixResult_registers] using
      range.inputCount_eq
  · simpa [TargetEmitterControllerPrefixTrace.poppedRuntime,
      TargetEmitterProgramSemantics.firstPrefixResult_registers] using
      range.normalizedGateCount_eq
  · simpa [TargetEmitterControllerPrefixTrace.poppedRuntime,
      TargetEmitterProgramSemantics.firstPrefixResult_registers] using
      range.carrierWidth_eq
  · simpa [TargetEmitterControllerPrefixTrace.poppedRuntime,
      TargetEmitterProgramSemantics.firstPrefixResult_registers] using
      range.baseline_eq
  · simpa [TargetEmitterControllerPrefixTrace.poppedRuntime,
      TargetEmitterProgramSemantics.firstPrefixResult_registers] using
      range.currentGate_le
  · simpa [TargetEmitterControllerPrefixTrace.poppedRuntime,
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

/-- Consume every remaining raw check in newest-first order, then execute the
raw positive final block, with the literal recursive work envelope. -/
theorem rawLoop_prefixes_to_beginOutput_path_bounded
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
          (TargetEmitterControllerPrefixTrace.nextPrefixLoop popOrder runtime)
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.rawGateTrace)).scratch
        (TargetEmitterProgramSemantics.finalResult
          (TargetEmitterControllerPrefixTrace.nextPrefixLoop popOrder runtime)
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.rawGateTrace)).registers
        (TargetEmitterProgramSemantics.finalResult
          (TargetEmitterControllerPrefixTrace.nextPrefixLoop popOrder runtime)
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.rawGateTrace)).checks
        source
        (TargetEmitterProgramSemantics.finalResult
          (TargetEmitterControllerPrefixTrace.nextPrefixLoop popOrder runtime)
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.rawGateTrace)).targetTokens finalTape ∧
      steps ≤ rawLoopEnvelope raw source popOrder runtime := by
  induction popOrder generalizing runtime initialTape with
  | nil =>
      have checksEmpty : runtime.checks = [] := by
        simpa using checksShape
      simpa [TargetEmitterControllerPrefixTrace.nextPrefixLoop] using
        (rawLoopPop_empty_to_beginOutput_path_bounded
          workspace runtime range capturedBound scratchZero
          checksEmpty captured initialTape represents)
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
        simp only [after,
          TargetEmitterControllerPrefixTrace.poppedRuntime,
          TargetEmitterProgramSemantics.nextPrefixResult_registers]
        omega
      have nonemptyChecks :
          runtime.checks = rest.reverse ++ [value] := by
        simpa using checksShape
      rcases
          rawLoopPop_nonempty_next_path_bounded workspace runtime
            rest.reverse value range capturedBound scratchZero
            nonemptyChecks valueBound initialTape represents with
        ⟨linkSteps, linkTape, linkPath, linkRepresents, linkBound⟩
      have afterScratch :
          after.scratch = 0 := by
        exact
          TargetEmitterProgramSemantics.nextPrefixResult_scratch
            (poppedRuntime runtime rest.reverse value)
      have afterChecks :
          after.checks = rest.reverse := by
        simpa [after,
          TargetEmitterControllerPrefixTrace.poppedRuntime] using
          (TargetEmitterProgramSemantics.nextPrefixResult_checks
            (poppedRuntime runtime rest.reverse value))
      rcases
          inductionHypothesis after afterRange afterCapturedBound
            afterScratch afterChecks tailBounds afterRoom afterCaptured
            linkTape (by simpa [after] using linkRepresents) with
        ⟨tailSteps, finalTape, tailPath, finalRepresents, tailBound⟩
      refine
        ⟨linkSteps + tailSteps, finalTape, ?_, ?_, ?_⟩
      · exact
          AcceptPath.trans graph (.node rawLoopPopRef)
            (.node rawLoopPopRef) (.node beginOutputRef)
            linkSteps tailSteps initialTape linkTape finalTape
            linkPath tailPath
      · simpa [TargetEmitterControllerPrefixTrace.nextPrefixLoop,
          after] using finalRepresents
      · have tailBound' :
            tailSteps ≤
              rawLoopEnvelope raw source rest
                (TargetEmitterProgramSemantics.nextPrefixResult
                  (poppedRuntime runtime rest.reverse value)) := by
          simpa [after] using tailBound
        change
          linkSteps + tailSteps ≤
            (TargetEmitterControllerCheckTrace.nonemptyPathSteps
                (TargetEmitterLedger.slotCapacity raw)
                rest.reverse value +
              nextPrefixBlockEnvelope raw source
                (poppedRuntime runtime rest.reverse value)) +
              rawLoopEnvelope raw source rest
                (TargetEmitterProgramSemantics.nextPrefixResult
                  (poppedRuntime runtime rest.reverse value))
        exact Nat.add_le_add linkBound tailBound'

/-- Normalized counterpart of
`rawLoop_prefixes_to_beginOutput_path_bounded`. -/
theorem normalizedLoop_prefixes_to_beginOutput_path_bounded
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
          (TargetEmitterControllerPrefixTrace.nextPrefixLoop popOrder runtime)
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.traceCoordinate)).scratch
        (TargetEmitterProgramSemantics.finalResult
          (TargetEmitterControllerPrefixTrace.nextPrefixLoop popOrder runtime)
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.traceCoordinate)).registers
        (TargetEmitterProgramSemantics.finalResult
          (TargetEmitterControllerPrefixTrace.nextPrefixLoop popOrder runtime)
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.traceCoordinate)).checks
        source
        (TargetEmitterProgramSemantics.finalResult
          (TargetEmitterControllerPrefixTrace.nextPrefixLoop popOrder runtime)
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.traceCoordinate)).targetTokens finalTape ∧
      steps ≤ normalizedLoopEnvelope raw source popOrder runtime := by
  induction popOrder generalizing runtime initialTape with
  | nil =>
      have checksEmpty : runtime.checks = [] := by
        simpa using checksShape
      simpa [TargetEmitterControllerPrefixTrace.nextPrefixLoop] using
        (normalizedLoopPop_empty_to_beginOutput_path_bounded
          workspace runtime range capturedBound scratchZero
          checksEmpty initialTape represents)
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
        simp only [after,
          TargetEmitterControllerPrefixTrace.poppedRuntime,
          TargetEmitterProgramSemantics.nextPrefixResult_registers]
        omega
      have nonemptyChecks :
          runtime.checks = rest.reverse ++ [value] := by
        simpa using checksShape
      rcases
          normalizedLoopPop_nonempty_next_path_bounded workspace runtime
            rest.reverse value range capturedBound scratchZero
            nonemptyChecks valueBound initialTape represents with
        ⟨linkSteps, linkTape, linkPath, linkRepresents, linkBound⟩
      have afterScratch :
          after.scratch = 0 := by
        exact
          TargetEmitterProgramSemantics.nextPrefixResult_scratch
            (poppedRuntime runtime rest.reverse value)
      have afterChecks :
          after.checks = rest.reverse := by
        simpa [after,
          TargetEmitterControllerPrefixTrace.poppedRuntime] using
          (TargetEmitterProgramSemantics.nextPrefixResult_checks
            (poppedRuntime runtime rest.reverse value))
      rcases
          inductionHypothesis after afterRange afterCapturedBound
            afterScratch afterChecks tailBounds afterRoom
            linkTape (by simpa [after] using linkRepresents) with
        ⟨tailSteps, finalTape, tailPath, finalRepresents, tailBound⟩
      refine
        ⟨linkSteps + tailSteps, finalTape, ?_, ?_, ?_⟩
      · exact
          AcceptPath.trans graph (.node normalizedLoopPopRef)
            (.node normalizedLoopPopRef) (.node beginOutputRef)
            linkSteps tailSteps initialTape linkTape finalTape
            linkPath tailPath
      · simpa [TargetEmitterControllerPrefixTrace.nextPrefixLoop,
          after] using finalRepresents
      · have tailBound' :
            tailSteps ≤
              normalizedLoopEnvelope raw source rest
                (TargetEmitterProgramSemantics.nextPrefixResult
                  (poppedRuntime runtime rest.reverse value)) := by
          simpa [after] using tailBound
        change
          linkSteps + tailSteps ≤
            (TargetEmitterControllerCheckTrace.nonemptyPathSteps
                (TargetEmitterLedger.slotCapacity raw)
                rest.reverse value +
              nextPrefixBlockEnvelope raw source
                (poppedRuntime runtime rest.reverse value)) +
              normalizedLoopEnvelope raw source rest
                (TargetEmitterProgramSemantics.nextPrefixResult
                  (poppedRuntime runtime rest.reverse value))
        exact Nat.add_le_add linkBound tailBound'

/-- Complete bounded raw nonempty prefix from the initial pop node through
the raw positive final block. -/
theorem rawInitialPrefix_to_beginOutput_path_bounded
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
          (TargetEmitterControllerPrefixTrace.rawNonemptyPrefixResult
            runtime prior second newest)
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.rawGateTrace)).scratch
        (TargetEmitterProgramSemantics.finalResult
          (TargetEmitterControllerPrefixTrace.rawNonemptyPrefixResult
            runtime prior second newest)
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.rawGateTrace)).registers
        (TargetEmitterProgramSemantics.finalResult
          (TargetEmitterControllerPrefixTrace.rawNonemptyPrefixResult
            runtime prior second newest)
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.rawGateTrace)).checks
        source
        (TargetEmitterProgramSemantics.finalResult
          (TargetEmitterControllerPrefixTrace.rawNonemptyPrefixResult
            runtime prior second newest)
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.rawGateTrace)).targetTokens finalTape ∧
      steps ≤
        rawNonemptyPrefixEnvelope raw source runtime
          prior second newest := by
  rcases
      rawInitialPop_nonempty_first_path_bounded workspace runtime prior
        second newest range capturedBound scratchZero checksShape
        secondBound newestBound initialTape represents with
    ⟨firstSteps, firstTape, firstPath, firstRepresents, firstBound⟩
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
    simpa [after,
      TargetEmitterControllerPrefixTrace.poppedRuntime] using
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
    simp only [after,
      TargetEmitterControllerPrefixTrace.poppedRuntime,
      TargetEmitterProgramSemantics.firstPrefixResult_registers,
      List.length_reverse]
    omega
  rcases
      rawLoop_prefixes_to_beginOutput_path_bounded workspace
        prior.reverse after afterRange afterCapturedBound
        afterScratch afterChecks reversedBounds afterRoom afterCaptured
        firstTape (by simpa [after] using firstRepresents) with
    ⟨tailSteps, finalTape, tailPath, finalRepresents, tailBound⟩
  refine
    ⟨firstSteps + tailSteps, finalTape, ?_, ?_, ?_⟩
  · exact
      AcceptPath.trans graph (.node rawInitialPopRef)
        (.node rawLoopPopRef) (.node beginOutputRef)
        firstSteps tailSteps initialTape firstTape finalTape
        firstPath tailPath
  · simpa [TargetEmitterControllerPrefixTrace.rawNonemptyPrefixResult,
      after] using finalRepresents
  · have tailBound' :
        tailSteps ≤
          rawLoopEnvelope raw source prior.reverse
            (TargetEmitterProgramSemantics.firstPrefixResult
              (poppedRuntime runtime (prior ++ [second]) newest)
              prior second) := by
      simpa [after] using tailBound
    change
      firstSteps + tailSteps ≤
        (TargetEmitterControllerCheckTrace.nonemptyPathSteps
            (TargetEmitterLedger.slotCapacity raw)
            (prior ++ [second]) newest +
          firstPrefixBlockEnvelope raw source
            (poppedRuntime runtime (prior ++ [second]) newest)) +
          rawLoopEnvelope raw source prior.reverse
            (TargetEmitterProgramSemantics.firstPrefixResult
              (poppedRuntime runtime (prior ++ [second]) newest)
              prior second)
    exact Nat.add_le_add firstBound tailBound'

/-- Complete bounded normalized nonempty prefix from the initial pop node
through the normalized positive final block. -/
theorem normalizedInitialPrefix_to_beginOutput_path_bounded
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
          (TargetEmitterControllerPrefixTrace.normalizedNonemptyPrefixResult
            runtime prior second newest)
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.traceCoordinate)).scratch
        (TargetEmitterProgramSemantics.finalResult
          (TargetEmitterControllerPrefixTrace.normalizedNonemptyPrefixResult
            runtime prior second newest)
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.traceCoordinate)).registers
        (TargetEmitterProgramSemantics.finalResult
          (TargetEmitterControllerPrefixTrace.normalizedNonemptyPrefixResult
            runtime prior second newest)
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.traceCoordinate)).checks
        source
        (TargetEmitterProgramSemantics.finalResult
          (TargetEmitterControllerPrefixTrace.normalizedNonemptyPrefixResult
            runtime prior second newest)
          (TargetEmitterPlan.finalPositivePlan
            TargetEmitterPlan.traceCoordinate)).targetTokens finalTape ∧
      steps ≤
        normalizedNonemptyPrefixEnvelope raw source runtime
          prior second newest := by
  rcases
      normalizedInitialPop_nonempty_first_path_bounded workspace runtime
        prior second newest range capturedBound scratchZero checksShape
        secondBound newestBound initialTape represents with
    ⟨firstSteps, firstTape, firstPath, firstRepresents, firstBound⟩
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
    simpa [after,
      TargetEmitterControllerPrefixTrace.poppedRuntime] using
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
    simp only [after,
      TargetEmitterControllerPrefixTrace.poppedRuntime,
      TargetEmitterProgramSemantics.firstPrefixResult_registers,
      List.length_reverse]
    omega
  rcases
      normalizedLoop_prefixes_to_beginOutput_path_bounded workspace
        prior.reverse after afterRange afterCapturedBound
        afterScratch afterChecks reversedBounds afterRoom
        firstTape (by simpa [after] using firstRepresents) with
    ⟨tailSteps, finalTape, tailPath, finalRepresents, tailBound⟩
  refine
    ⟨firstSteps + tailSteps, finalTape, ?_, ?_, ?_⟩
  · exact
      AcceptPath.trans graph (.node normalizedInitialPopRef)
        (.node normalizedLoopPopRef) (.node beginOutputRef)
        firstSteps tailSteps initialTape firstTape finalTape
        firstPath tailPath
  · simpa [
      TargetEmitterControllerPrefixTrace.normalizedNonemptyPrefixResult,
      TargetEmitterControllerPrefixTrace.rawNonemptyPrefixResult,
      after] using finalRepresents
  · have tailBound' :
        tailSteps ≤
          normalizedLoopEnvelope raw source prior.reverse
            (TargetEmitterProgramSemantics.firstPrefixResult
              (poppedRuntime runtime (prior ++ [second]) newest)
              prior second) := by
      simpa [after] using tailBound
    change
      firstSteps + tailSteps ≤
        (TargetEmitterControllerCheckTrace.nonemptyPathSteps
            (TargetEmitterLedger.slotCapacity raw)
            (prior ++ [second]) newest +
          firstPrefixBlockEnvelope raw source
            (poppedRuntime runtime (prior ++ [second]) newest)) +
          normalizedLoopEnvelope raw source prior.reverse
            (TargetEmitterProgramSemantics.firstPrefixResult
              (poppedRuntime runtime (prior ++ [second]) newest)
              prior second)
    exact Nat.add_le_add firstBound tailBound'

/-! ### Closed uniform polynomial domination -/

/-- One fixed upper bound for the primitive count of every prefix or final
block used in this module. -/
def prefixProgramLimit : Nat := 64

/-- Maximum logical target/check-cell growth charged to one fixed block. -/
def prefixBlockGrowth (capacity : Nat) : Nat :=
  prefixProgramLimit * (capacity + 1)

/-- Target-token budget for every block reached during a prefix fold. -/
def prefixTargetLimit (capacity : Nat) (origin : Runtime)
    (blockBudget : Nat) : Nat :=
  origin.targetTokens.length +
    blockBudget * prefixBlockGrowth capacity

/-- Check-stack cell budget for every block reached during a prefix fold. -/
def prefixCheckLimit (capacity : Nat) (origin : Runtime)
    (blockBudget : Nat) : Nat :=
  TargetEmitterRuntimeProgramBound.checkCells origin.checks +
    blockBudget * prefixBlockGrowth capacity

/-- One physical footprint dominating every fixed program in a bounded
prefix fold. -/
def prefixMasterSize (capacity : Nat) (source : List WorkSymbol)
    (origin : Runtime) (blockBudget : Nat) : Nat :=
  capacity + source.length +
    2 * prefixTargetLimit capacity origin blockBudget +
    prefixCheckLimit capacity origin blockBudget +
    prefixProgramLimit * (3 * capacity + 3) + 1

/-- Uniform charge for any materialized prefix or final block. -/
def prefixBlockUnit (capacity : Nat) (source : List WorkSymbol)
    (origin : Runtime) (blockBudget : Nat) : Nat :=
  prefixProgramLimit *
    (TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
      (prefixMasterSize capacity source origin blockBudget) + 1)

/-- Uniform charge for either literal pop branch when at most `checkCount`
bounded records remain. -/
def prefixPopUnit (capacity checkCount : Nat) : Nat :=
  14 * capacity + 2 * (checkCount * capacity) + capacity + 39 +
    capacity *
      (14 * capacity + 2 * (checkCount * capacity) +
        2 * capacity + 43)

/-- Closed non-recursive polynomial envelope for a prefix whose represented
stack contains at most `checkCount` entries. -/
def prefixUniformEnvelope (capacity : Nat)
    (source : List WorkSymbol) (origin : Runtime)
    (checkCount : Nat) : Nat :=
  (checkCount + 1) *
    (prefixPopUnit capacity checkCount +
      prefixBlockUnit capacity source origin (checkCount + 1))

private theorem firstPrefix_length_le :
    Plan.firstPrefix.length ≤ prefixProgramLimit := by
  decide

private theorem nextPrefix_length_le :
    Plan.nextPrefix.length ≤ prefixProgramLimit := by
  decide

private theorem finalZero_length_le :
    Plan.finalZero.length ≤ prefixProgramLimit := by
  decide

private theorem finalRaw_length_le :
    Plan.finalRaw.length ≤ prefixProgramLimit := by
  decide

private theorem finalNormalized_length_le :
    Plan.finalNormalized.length ≤ prefixProgramLimit := by
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

private theorem checkCells_prior_le
    (prior : List Nat) (value : Nat) :
    TargetEmitterRuntimeProgramBound.checkCells prior ≤
      TargetEmitterRuntimeProgramBound.checkCells
        (prior ++ [value]) := by
  unfold TargetEmitterRuntimeProgramBound.checkCells
  rw [TargetEmitterCheckStack.recordsWord_push,
    List.length_append, TargetEmitterCheckStack.recordWord_length]
  omega

private theorem checkCells_le_length_mul
    {capacity : Nat} (checks : List Nat)
    (valuesBound :
      ∀ value, value ∈ checks → value < capacity) :
    TargetEmitterRuntimeProgramBound.checkCells checks ≤
      checks.length * capacity := by
  induction checks with
  | nil =>
      simp [TargetEmitterRuntimeProgramBound.checkCells,
        TargetEmitterCheckStack.recordsWord]
  | cons value rest inductionHypothesis =>
      have valueBound : value + 1 ≤ capacity := by
        exact valuesBound value (List.Mem.head rest)
      have tailBounds :
          ∀ item, item ∈ rest → item < capacity := by
        intro item member
        exact valuesBound item (List.Mem.tail value member)
      have tailBound := inductionHypothesis tailBounds
      rw [show
        TargetEmitterRuntimeProgramBound.checkCells (value :: rest) =
          value + 1 +
            TargetEmitterRuntimeProgramBound.checkCells rest by
        simp [TargetEmitterRuntimeProgramBound.checkCells,
          TargetEmitterCheckStack.recordsWord,
          TargetEmitterCheckStack.recordWord_length]]
      simp only [List.length_cons]
      rw [Nat.succ_mul]
      omega

private theorem emptyPathSteps_le_prefixPopUnit
    (capacity checkCount : Nat) :
    TargetEmitterControllerCheckTrace.emptyPathSteps capacity ≤
      prefixPopUnit capacity checkCount := by
  unfold TargetEmitterControllerCheckTrace.emptyPathSteps
    TargetEmitterCheckStack.Pop.emptyWorkSteps prefixPopUnit
  omega

private theorem nonemptyPathSteps_le_prefixPopUnit
    {capacity checkCount : Nat} (prior : List Nat) (value : Nat)
    (lengthBound : prior.length ≤ checkCount)
    (priorBounds :
      ∀ item, item ∈ prior → item < capacity)
    (valueBound : value ≤ capacity) :
    TargetEmitterControllerCheckTrace.nonemptyPathSteps
        capacity prior value ≤
      prefixPopUnit capacity checkCount := by
  have cellsBound :
      (TargetEmitterCheckStack.recordsWord prior).length ≤
        checkCount * capacity := by
    have localBound :=
      checkCells_le_length_mul prior priorBounds
    unfold TargetEmitterRuntimeProgramBound.checkCells at localBound
    exact Nat.le_trans localBound
      (Nat.mul_le_mul_right capacity lengthBound)
  have factorBound :
      14 * capacity +
          2 * (TargetEmitterCheckStack.recordsWord prior).length +
          2 * value + 43 ≤
        14 * capacity + 2 * (checkCount * capacity) +
          2 * capacity + 43 := by
    omega
  have productBound :
      value *
          (14 * capacity +
            2 * (TargetEmitterCheckStack.recordsWord prior).length +
            2 * value + 43) ≤
        capacity *
          (14 * capacity + 2 * (checkCount * capacity) +
            2 * capacity + 43) :=
    Nat.mul_le_mul valueBound factorBound
  unfold TargetEmitterControllerCheckTrace.nonemptyPathSteps
    TargetEmitterCheckStack.Pop.nonemptyWorkSteps prefixPopUnit
  omega

private theorem programEnvelope_le_prefixBlockUnit
    (capacity : Nat) (source : List WorkSymbol)
    (origin current : Runtime) (blockBudget : Nat)
    (primitives : List TargetEmitterPlan.Primitive)
    (programLength : primitives.length ≤ prefixProgramLimit)
    (targetBound :
      current.targetTokens.length ≤
        prefixTargetLimit capacity origin blockBudget)
    (checksBound :
      TargetEmitterRuntimeProgramBound.checkCells current.checks ≤
        prefixCheckLimit capacity origin blockBudget) :
    TargetEmitterRuntimeProgramBound.programWorkEnvelope
        capacity source current primitives ≤
      prefixBlockUnit capacity source origin blockBudget := by
  have footprintBound :
      TargetEmitterRuntimeProgramBound.runtimeFootprint
          capacity source current primitives.length ≤
        prefixMasterSize capacity source origin blockBudget := by
    unfold TargetEmitterRuntimeProgramBound.runtimeFootprint
      prefixMasterSize
    have reserved :
        primitives.length * (3 * capacity + 3) ≤
          prefixProgramLimit * (3 * capacity + 3) :=
      Nat.mul_le_mul_right (3 * capacity + 3) programLength
    omega
  have squareBound :
      TargetEmitterRuntimeProgramBound.runtimeFootprint
            capacity source current primitives.length *
          TargetEmitterRuntimeProgramBound.runtimeFootprint
            capacity source current primitives.length ≤
        prefixMasterSize capacity source origin blockBudget *
          prefixMasterSize capacity source origin blockBudget :=
    Nat.mul_le_mul footprintBound footprintBound
  have primitiveBound :
      TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
            (TargetEmitterRuntimeProgramBound.runtimeFootprint
              capacity source current primitives.length) + 1 ≤
        TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
            (prefixMasterSize capacity source origin blockBudget) + 1 := by
    unfold TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_left 100 squareBound) 101
  have totalBound :=
    Nat.mul_le_mul programLength primitiveBound
  simpa [TargetEmitterRuntimeProgramBound.programWorkEnvelope,
    prefixBlockUnit] using totalBound

private theorem popped_target_length
    (runtime : Runtime) (prior : List Nat) (value : Nat) :
    (poppedRuntime runtime prior value).targetTokens.length =
      runtime.targetTokens.length := by
  rfl

private theorem popped_checkCells_le
    (runtime : Runtime) (prior : List Nat) (value : Nat)
    (checksShape : runtime.checks = prior ++ [value]) :
    TargetEmitterRuntimeProgramBound.checkCells
        (poppedRuntime runtime prior value).checks ≤
      TargetEmitterRuntimeProgramBound.checkCells runtime.checks := by
  simp only [TargetEmitterControllerPrefixTrace.poppedRuntime]
  rw [checksShape]
  exact checkCells_prior_le prior value

private theorem nextPrefix_target_growth
    {raw : RawCircuit} {source : List WorkSymbol}
    (workspace : MarkedWorkspace source)
    (runtime : Runtime)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw) :
    (TargetEmitterProgramSemantics.nextPrefixResult runtime).targetTokens.length ≤
      runtime.targetTokens.length +
        prefixBlockGrowth (TargetEmitterLedger.slotCapacity raw) := by
  have safe :=
    TargetEmitterRuntimeProgramSafety.nextPrefix_safe
      workspace range capturedBound scratchBound
  have bound := ProgramSafe.target_length_le safe
  have lengthBound := nextPrefix_length_le
  unfold prefixBlockGrowth
  exact Nat.le_trans bound
    (Nat.add_le_add_left
      (Nat.mul_le_mul_right
        (TargetEmitterLedger.slotCapacity raw + 1) lengthBound)
      runtime.targetTokens.length)

private theorem nextPrefix_check_growth
    {raw : RawCircuit} {source : List WorkSymbol}
    (workspace : MarkedWorkspace source)
    (runtime : Runtime)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (scratchBound :
      runtime.scratch < TargetEmitterLedger.slotCapacity raw) :
    TargetEmitterRuntimeProgramBound.checkCells
        (TargetEmitterProgramSemantics.nextPrefixResult runtime).checks ≤
      TargetEmitterRuntimeProgramBound.checkCells runtime.checks +
        prefixBlockGrowth (TargetEmitterLedger.slotCapacity raw) := by
  have safe :=
    TargetEmitterRuntimeProgramSafety.nextPrefix_safe
      workspace range capturedBound scratchBound
  have bound := ProgramSafe.checkCells_le safe
  have lengthBound := nextPrefix_length_le
  unfold prefixBlockGrowth
  exact Nat.le_trans bound
    (Nat.add_le_add_left
      (Nat.mul_le_mul_right
        (TargetEmitterLedger.slotCapacity raw + 1) lengthBound)
      (TargetEmitterRuntimeProgramBound.checkCells runtime.checks))

private theorem firstPrefix_target_growth
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
      newest < TargetEmitterLedger.slotCapacity raw) :
    (TargetEmitterProgramSemantics.firstPrefixResult
        runtime prior newest).targetTokens.length ≤
      runtime.targetTokens.length +
        prefixBlockGrowth (TargetEmitterLedger.slotCapacity raw) := by
  have safe :=
    TargetEmitterRuntimeProgramSafety.firstPrefix_safe workspace range
      capturedBound scratchBound checksShape newestBound
  have bound := ProgramSafe.target_length_le safe
  have lengthBound := firstPrefix_length_le
  unfold prefixBlockGrowth
  exact Nat.le_trans bound
    (Nat.add_le_add_left
      (Nat.mul_le_mul_right
        (TargetEmitterLedger.slotCapacity raw + 1) lengthBound)
      runtime.targetTokens.length)

private theorem firstPrefix_check_growth
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
      newest < TargetEmitterLedger.slotCapacity raw) :
    TargetEmitterRuntimeProgramBound.checkCells
        (TargetEmitterProgramSemantics.firstPrefixResult
          runtime prior newest).checks ≤
      TargetEmitterRuntimeProgramBound.checkCells runtime.checks +
        prefixBlockGrowth (TargetEmitterLedger.slotCapacity raw) := by
  have safe :=
    TargetEmitterRuntimeProgramSafety.firstPrefix_safe workspace range
      capturedBound scratchBound checksShape newestBound
  have bound := ProgramSafe.checkCells_le safe
  have lengthBound := firstPrefix_length_le
  unfold prefixBlockGrowth
  exact Nat.le_trans bound
    (Nat.add_le_add_left
      (Nat.mul_le_mul_right
        (TargetEmitterLedger.slotCapacity raw + 1) lengthBound)
      (TargetEmitterRuntimeProgramBound.checkCells runtime.checks))

private theorem unit_add_succ_mul (count unit : Nat) :
    unit + (count + 1) * unit =
      (count + 1 + 1) * unit := by
  simp only [Nat.add_mul, Nat.one_mul]
  omega

private theorem rawLoopEnvelope_le_uniformAux
    {raw : RawCircuit} {source : List WorkSymbol}
    (workspace : MarkedWorkspace source)
    (origin : Runtime) (totalCount : Nat)
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
    (lengthBound : popOrder.length ≤ totalCount)
    (targetBudget :
      runtime.targetTokens.length +
          (popOrder.length + 1) *
            prefixBlockGrowth
              (TargetEmitterLedger.slotCapacity raw) ≤
        prefixTargetLimit
          (TargetEmitterLedger.slotCapacity raw) origin
          (totalCount + 1))
    (checkBudget :
      TargetEmitterRuntimeProgramBound.checkCells runtime.checks +
          (popOrder.length + 1) *
            prefixBlockGrowth
              (TargetEmitterLedger.slotCapacity raw) ≤
        prefixCheckLimit
          (TargetEmitterLedger.slotCapacity raw) origin
          (totalCount + 1)) :
    rawLoopEnvelope raw source popOrder runtime ≤
      (popOrder.length + 1) *
        (prefixPopUnit
            (TargetEmitterLedger.slotCapacity raw) totalCount +
          prefixBlockUnit
            (TargetEmitterLedger.slotCapacity raw) source origin
            (totalCount + 1)) := by
  induction popOrder generalizing runtime with
  | nil =>
      have currentTarget :
          runtime.targetTokens.length ≤
            prefixTargetLimit
              (TargetEmitterLedger.slotCapacity raw) origin
              (totalCount + 1) := by
        exact Nat.le_trans
          (Nat.le_add_right runtime.targetTokens.length
            (prefixBlockGrowth
              (TargetEmitterLedger.slotCapacity raw)))
          (by simpa using targetBudget)
      have currentChecks :
          TargetEmitterRuntimeProgramBound.checkCells runtime.checks ≤
            prefixCheckLimit
              (TargetEmitterLedger.slotCapacity raw) origin
              (totalCount + 1) := by
        exact Nat.le_trans
          (Nat.le_add_right
            (TargetEmitterRuntimeProgramBound.checkCells runtime.checks)
            (prefixBlockGrowth
              (TargetEmitterLedger.slotCapacity raw)))
          (by simpa using checkBudget)
      have popBound :=
        emptyPathSteps_le_prefixPopUnit
          (TargetEmitterLedger.slotCapacity raw) totalCount
      have blockBound :
          finalRawBlockEnvelope raw source runtime ≤
            prefixBlockUnit
              (TargetEmitterLedger.slotCapacity raw) source origin
              (totalCount + 1) := by
        apply programEnvelope_le_prefixBlockUnit
        · exact finalRaw_length_le
        · exact currentTarget
        · exact currentChecks
      simp only [rawLoopEnvelope, List.length_nil, Nat.zero_add,
        Nat.one_mul]
      exact Nat.add_le_add popBound blockBound
  | cons value rest inductionHypothesis =>
      have valueBound :
          value < TargetEmitterLedger.slotCapacity raw :=
        valuesBound value (List.Mem.head rest)
      have tailBounds :
          ∀ item, item ∈ rest →
            item < TargetEmitterLedger.slotCapacity raw := by
        intro item member
        exact valuesBound item (List.Mem.tail value member)
      have priorBounds :
          ∀ item, item ∈ rest.reverse →
            item < TargetEmitterLedger.slotCapacity raw := by
        intro item member
        exact tailBounds item (List.mem_reverse.mp member)
      have priorLength :
          rest.reverse.length ≤ totalCount := by
        simp only [List.length_reverse]
        exact Nat.le_trans (Nat.le_succ rest.length)
          (by simpa using lengthBound)
      have popBound :=
        nonemptyPathSteps_le_prefixPopUnit rest.reverse value
          priorLength priorBounds (Nat.le_of_lt valueBound)
      have currentTarget :
          runtime.targetTokens.length ≤
            prefixTargetLimit
              (TargetEmitterLedger.slotCapacity raw) origin
              (totalCount + 1) := by
        exact Nat.le_trans
          (Nat.le_add_right runtime.targetTokens.length
            ((List.length (value :: rest) + 1) *
              prefixBlockGrowth
                (TargetEmitterLedger.slotCapacity raw)))
          targetBudget
      have currentChecks :
          TargetEmitterRuntimeProgramBound.checkCells runtime.checks ≤
            prefixCheckLimit
              (TargetEmitterLedger.slotCapacity raw) origin
              (totalCount + 1) := by
        exact Nat.le_trans
          (Nat.le_add_right
            (TargetEmitterRuntimeProgramBound.checkCells runtime.checks)
            ((List.length (value :: rest) + 1) *
              prefixBlockGrowth
                (TargetEmitterLedger.slotCapacity raw)))
          checkBudget
      have nonemptyChecks :
          runtime.checks = rest.reverse ++ [value] := by
        simpa using checksShape
      let popped := poppedRuntime runtime rest.reverse value
      have poppedTarget :
          popped.targetTokens.length ≤
            prefixTargetLimit
              (TargetEmitterLedger.slotCapacity raw) origin
              (totalCount + 1) := by
        simpa [popped, popped_target_length] using currentTarget
      have poppedChecks :
          TargetEmitterRuntimeProgramBound.checkCells popped.checks ≤
            prefixCheckLimit
              (TargetEmitterLedger.slotCapacity raw) origin
              (totalCount + 1) := by
        exact Nat.le_trans
          (by
            simpa [popped] using
              (popped_checkCells_le runtime rest.reverse value
                nonemptyChecks))
          currentChecks
      have blockBound :
          nextPrefixBlockEnvelope raw source popped ≤
            prefixBlockUnit
              (TargetEmitterLedger.slotCapacity raw) source origin
              (totalCount + 1) := by
        apply programEnvelope_le_prefixBlockUnit
        · exact nextPrefix_length_le
        · exact poppedTarget
        · exact poppedChecks
      have currentRoom :
          runtime.registers.outputIndex + 2 ≤
            TargetEmitterLedger.baselineValue raw + 4 := by
        simp only [List.length_cons] at outputRoom
        omega
      let after :=
        TargetEmitterProgramSemantics.nextPrefixResult popped
      have poppedRange : ControllerRange raw popped.registers := by
        simpa [popped,
          TargetEmitterControllerPrefixTrace.poppedRuntime] using range
      have poppedCapturedBound :
          popped.captured + 1 ≤
            (SourceParser.circuitCells raw).length := by
        simpa [popped,
          TargetEmitterControllerPrefixTrace.poppedRuntime] using
          capturedBound
      have poppedScratchBound :
          popped.scratch <
            TargetEmitterLedger.slotCapacity raw := by
        simpa [popped,
          TargetEmitterControllerPrefixTrace.poppedRuntime] using
          valueBound
      have afterTargetGrowth :
          after.targetTokens.length ≤
            popped.targetTokens.length +
              prefixBlockGrowth
                (TargetEmitterLedger.slotCapacity raw) := by
        simpa [after] using
          (nextPrefix_target_growth workspace popped poppedRange
            poppedCapturedBound poppedScratchBound)
      have afterCheckGrowth :
          TargetEmitterRuntimeProgramBound.checkCells after.checks ≤
            TargetEmitterRuntimeProgramBound.checkCells popped.checks +
              prefixBlockGrowth
                (TargetEmitterLedger.slotCapacity raw) := by
        simpa [after] using
          (nextPrefix_check_growth workspace popped poppedRange
            poppedCapturedBound poppedScratchBound)
      have afterTargetFromCurrent :
          after.targetTokens.length ≤
            runtime.targetTokens.length +
              prefixBlockGrowth
                (TargetEmitterLedger.slotCapacity raw) := by
        rw [show popped.targetTokens.length =
          runtime.targetTokens.length by rfl] at afterTargetGrowth
        exact afterTargetGrowth
      have afterChecksFromCurrent :
          TargetEmitterRuntimeProgramBound.checkCells after.checks ≤
            TargetEmitterRuntimeProgramBound.checkCells runtime.checks +
              prefixBlockGrowth
                (TargetEmitterLedger.slotCapacity raw) := by
        exact Nat.le_trans afterCheckGrowth
          (Nat.add_le_add_right
            (popped_checkCells_le runtime rest.reverse value
              nonemptyChecks)
            (prefixBlockGrowth
              (TargetEmitterLedger.slotCapacity raw)))
      have tailTargetBudget :
          after.targetTokens.length +
              (rest.length + 1) *
                prefixBlockGrowth
                  (TargetEmitterLedger.slotCapacity raw) ≤
            prefixTargetLimit
              (TargetEmitterLedger.slotCapacity raw) origin
              (totalCount + 1) := by
        have reserveEq :
            ((List.length (value :: rest) + 1) *
                prefixBlockGrowth
                  (TargetEmitterLedger.slotCapacity raw)) =
              prefixBlockGrowth
                  (TargetEmitterLedger.slotCapacity raw) +
                (rest.length + 1) *
                  prefixBlockGrowth
                    (TargetEmitterLedger.slotCapacity raw) := by
          simp only [List.length_cons]
          rw [Nat.add_mul]
          simp only [Nat.one_mul]
          exact Nat.add_comm _ _
        rw [reserveEq] at targetBudget
        apply Nat.le_trans
          (Nat.add_le_add_right afterTargetFromCurrent
            ((rest.length + 1) *
              prefixBlockGrowth
                (TargetEmitterLedger.slotCapacity raw)))
        simpa only [Nat.add_assoc] using targetBudget
      have tailCheckBudget :
          TargetEmitterRuntimeProgramBound.checkCells after.checks +
              (rest.length + 1) *
                prefixBlockGrowth
                  (TargetEmitterLedger.slotCapacity raw) ≤
            prefixCheckLimit
              (TargetEmitterLedger.slotCapacity raw) origin
              (totalCount + 1) := by
        have reserveEq :
            ((List.length (value :: rest) + 1) *
                prefixBlockGrowth
                  (TargetEmitterLedger.slotCapacity raw)) =
              prefixBlockGrowth
                  (TargetEmitterLedger.slotCapacity raw) +
                (rest.length + 1) *
                  prefixBlockGrowth
                    (TargetEmitterLedger.slotCapacity raw) := by
          simp only [List.length_cons]
          rw [Nat.add_mul]
          simp only [Nat.one_mul]
          exact Nat.add_comm _ _
        rw [reserveEq] at checkBudget
        apply Nat.le_trans
          (Nat.add_le_add_right afterChecksFromCurrent
            ((rest.length + 1) *
              prefixBlockGrowth
                (TargetEmitterLedger.slotCapacity raw)))
        simpa only [Nat.add_assoc] using checkBudget
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
      have afterScratch : after.scratch = 0 := by
        exact
          TargetEmitterProgramSemantics.nextPrefixResult_scratch popped
      have afterChecks :
          after.checks = rest.reverse := by
        simpa [after, popped,
          TargetEmitterControllerPrefixTrace.poppedRuntime] using
          (TargetEmitterProgramSemantics.nextPrefixResult_checks popped)
      have afterRoom :
          after.registers.outputIndex + 2 * rest.length ≤
            TargetEmitterLedger.baselineValue raw + 4 := by
        simp only [List.length_cons] at outputRoom
        simp only [after, popped,
          TargetEmitterControllerPrefixTrace.poppedRuntime,
          TargetEmitterProgramSemantics.nextPrefixResult_registers]
        omega
      have tailLength : rest.length ≤ totalCount :=
        Nat.le_trans (Nat.le_succ rest.length)
          (by simpa using lengthBound)
      have tailBound :=
        inductionHypothesis after afterRange afterCapturedBound
          afterScratch afterChecks tailBounds afterRoom tailLength
          tailTargetBudget tailCheckBudget
      have headBound :
          TargetEmitterControllerCheckTrace.nonemptyPathSteps
                (TargetEmitterLedger.slotCapacity raw)
                rest.reverse value +
              nextPrefixBlockEnvelope raw source popped ≤
            prefixPopUnit
                (TargetEmitterLedger.slotCapacity raw) totalCount +
              prefixBlockUnit
                (TargetEmitterLedger.slotCapacity raw) source origin
                (totalCount + 1) :=
        Nat.add_le_add popBound blockBound
      have totalBound := Nat.add_le_add headBound tailBound
      change
        (TargetEmitterControllerCheckTrace.nonemptyPathSteps
              (TargetEmitterLedger.slotCapacity raw)
              rest.reverse value +
            nextPrefixBlockEnvelope raw source popped) +
            rawLoopEnvelope raw source rest after ≤
          ((rest.length + 1) + 1) *
            (prefixPopUnit
                (TargetEmitterLedger.slotCapacity raw) totalCount +
              prefixBlockUnit
                (TargetEmitterLedger.slotCapacity raw) source origin
                (totalCount + 1))
      calc
        _ ≤
            (prefixPopUnit
                (TargetEmitterLedger.slotCapacity raw) totalCount +
              prefixBlockUnit
                (TargetEmitterLedger.slotCapacity raw) source origin
                (totalCount + 1)) +
              (rest.length + 1) *
                (prefixPopUnit
                    (TargetEmitterLedger.slotCapacity raw) totalCount +
                  prefixBlockUnit
                    (TargetEmitterLedger.slotCapacity raw) source origin
                    (totalCount + 1)) :=
          totalBound
        _ = _ := by
          exact unit_add_succ_mul _ _

/-- The recursive raw loop envelope is dominated by the closed uniform
polynomial expression at its initial represented runtime. -/
theorem rawLoopEnvelope_le_uniform
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
        TargetEmitterLedger.baselineValue raw + 4) :
    rawLoopEnvelope raw source popOrder runtime ≤
      prefixUniformEnvelope
        (TargetEmitterLedger.slotCapacity raw) source runtime
        popOrder.length := by
  have bound :=
    rawLoopEnvelope_le_uniformAux workspace runtime popOrder.length
      popOrder runtime range capturedBound scratchZero checksShape
      valuesBound outputRoom (Nat.le_refl _)
      (by
        simp [prefixTargetLimit])
      (by
        simp [prefixCheckLimit])
  simpa [prefixUniformEnvelope] using bound

private theorem normalizedLoopEnvelope_le_uniformAux
    {raw : RawCircuit} {source : List WorkSymbol}
    (workspace : MarkedWorkspace source)
    (origin : Runtime) (totalCount : Nat)
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
    (lengthBound : popOrder.length ≤ totalCount)
    (targetBudget :
      runtime.targetTokens.length +
          (popOrder.length + 1) *
            prefixBlockGrowth
              (TargetEmitterLedger.slotCapacity raw) ≤
        prefixTargetLimit
          (TargetEmitterLedger.slotCapacity raw) origin
          (totalCount + 1))
    (checkBudget :
      TargetEmitterRuntimeProgramBound.checkCells runtime.checks +
          (popOrder.length + 1) *
            prefixBlockGrowth
              (TargetEmitterLedger.slotCapacity raw) ≤
        prefixCheckLimit
          (TargetEmitterLedger.slotCapacity raw) origin
          (totalCount + 1)) :
    normalizedLoopEnvelope raw source popOrder runtime ≤
      (popOrder.length + 1) *
        (prefixPopUnit
            (TargetEmitterLedger.slotCapacity raw) totalCount +
          prefixBlockUnit
            (TargetEmitterLedger.slotCapacity raw) source origin
            (totalCount + 1)) := by
  induction popOrder generalizing runtime with
  | nil =>
      have currentTarget :
          runtime.targetTokens.length ≤
            prefixTargetLimit
              (TargetEmitterLedger.slotCapacity raw) origin
              (totalCount + 1) := by
        exact Nat.le_trans
          (Nat.le_add_right runtime.targetTokens.length
            (prefixBlockGrowth
              (TargetEmitterLedger.slotCapacity raw)))
          (by simpa using targetBudget)
      have currentChecks :
          TargetEmitterRuntimeProgramBound.checkCells runtime.checks ≤
            prefixCheckLimit
              (TargetEmitterLedger.slotCapacity raw) origin
              (totalCount + 1) := by
        exact Nat.le_trans
          (Nat.le_add_right
            (TargetEmitterRuntimeProgramBound.checkCells runtime.checks)
            (prefixBlockGrowth
              (TargetEmitterLedger.slotCapacity raw)))
          (by simpa using checkBudget)
      have popBound :=
        emptyPathSteps_le_prefixPopUnit
          (TargetEmitterLedger.slotCapacity raw) totalCount
      have blockBound :
          finalNormalizedBlockEnvelope raw source runtime ≤
            prefixBlockUnit
              (TargetEmitterLedger.slotCapacity raw) source origin
              (totalCount + 1) := by
        apply programEnvelope_le_prefixBlockUnit
        · exact finalNormalized_length_le
        · exact currentTarget
        · exact currentChecks
      simp only [normalizedLoopEnvelope, List.length_nil,
        Nat.zero_add, Nat.one_mul]
      exact Nat.add_le_add popBound blockBound
  | cons value rest inductionHypothesis =>
      have valueBound :
          value < TargetEmitterLedger.slotCapacity raw :=
        valuesBound value (List.Mem.head rest)
      have tailBounds :
          ∀ item, item ∈ rest →
            item < TargetEmitterLedger.slotCapacity raw := by
        intro item member
        exact valuesBound item (List.Mem.tail value member)
      have priorBounds :
          ∀ item, item ∈ rest.reverse →
            item < TargetEmitterLedger.slotCapacity raw := by
        intro item member
        exact tailBounds item (List.mem_reverse.mp member)
      have priorLength :
          rest.reverse.length ≤ totalCount := by
        simp only [List.length_reverse]
        exact Nat.le_trans (Nat.le_succ rest.length)
          (by simpa using lengthBound)
      have popBound :=
        nonemptyPathSteps_le_prefixPopUnit rest.reverse value
          priorLength priorBounds (Nat.le_of_lt valueBound)
      have currentTarget :
          runtime.targetTokens.length ≤
            prefixTargetLimit
              (TargetEmitterLedger.slotCapacity raw) origin
              (totalCount + 1) := by
        exact Nat.le_trans
          (Nat.le_add_right runtime.targetTokens.length
            ((List.length (value :: rest) + 1) *
              prefixBlockGrowth
                (TargetEmitterLedger.slotCapacity raw)))
          targetBudget
      have currentChecks :
          TargetEmitterRuntimeProgramBound.checkCells runtime.checks ≤
            prefixCheckLimit
              (TargetEmitterLedger.slotCapacity raw) origin
              (totalCount + 1) := by
        exact Nat.le_trans
          (Nat.le_add_right
            (TargetEmitterRuntimeProgramBound.checkCells runtime.checks)
            ((List.length (value :: rest) + 1) *
              prefixBlockGrowth
                (TargetEmitterLedger.slotCapacity raw)))
          checkBudget
      have nonemptyChecks :
          runtime.checks = rest.reverse ++ [value] := by
        simpa using checksShape
      let popped := poppedRuntime runtime rest.reverse value
      have poppedTarget :
          popped.targetTokens.length ≤
            prefixTargetLimit
              (TargetEmitterLedger.slotCapacity raw) origin
              (totalCount + 1) := by
        simpa [popped, popped_target_length] using currentTarget
      have poppedChecks :
          TargetEmitterRuntimeProgramBound.checkCells popped.checks ≤
            prefixCheckLimit
              (TargetEmitterLedger.slotCapacity raw) origin
              (totalCount + 1) := by
        exact Nat.le_trans
          (by
            simpa [popped] using
              (popped_checkCells_le runtime rest.reverse value
                nonemptyChecks))
          currentChecks
      have blockBound :
          nextPrefixBlockEnvelope raw source popped ≤
            prefixBlockUnit
              (TargetEmitterLedger.slotCapacity raw) source origin
              (totalCount + 1) := by
        apply programEnvelope_le_prefixBlockUnit
        · exact nextPrefix_length_le
        · exact poppedTarget
        · exact poppedChecks
      have currentRoom :
          runtime.registers.outputIndex + 2 ≤
            TargetEmitterLedger.baselineValue raw + 4 := by
        simp only [List.length_cons] at outputRoom
        omega
      let after :=
        TargetEmitterProgramSemantics.nextPrefixResult popped
      have poppedRange : ControllerRange raw popped.registers := by
        simpa [popped,
          TargetEmitterControllerPrefixTrace.poppedRuntime] using range
      have poppedCapturedBound :
          popped.captured + 1 ≤
            (SourceParser.circuitCells raw).length := by
        simpa [popped,
          TargetEmitterControllerPrefixTrace.poppedRuntime] using
          capturedBound
      have poppedScratchBound :
          popped.scratch <
            TargetEmitterLedger.slotCapacity raw := by
        simpa [popped,
          TargetEmitterControllerPrefixTrace.poppedRuntime] using
          valueBound
      have afterTargetGrowth :
          after.targetTokens.length ≤
            popped.targetTokens.length +
              prefixBlockGrowth
                (TargetEmitterLedger.slotCapacity raw) := by
        simpa [after] using
          (nextPrefix_target_growth workspace popped poppedRange
            poppedCapturedBound poppedScratchBound)
      have afterCheckGrowth :
          TargetEmitterRuntimeProgramBound.checkCells after.checks ≤
            TargetEmitterRuntimeProgramBound.checkCells popped.checks +
              prefixBlockGrowth
                (TargetEmitterLedger.slotCapacity raw) := by
        simpa [after] using
          (nextPrefix_check_growth workspace popped poppedRange
            poppedCapturedBound poppedScratchBound)
      have afterTargetFromCurrent :
          after.targetTokens.length ≤
            runtime.targetTokens.length +
              prefixBlockGrowth
                (TargetEmitterLedger.slotCapacity raw) := by
        rw [show popped.targetTokens.length =
          runtime.targetTokens.length by rfl] at afterTargetGrowth
        exact afterTargetGrowth
      have afterChecksFromCurrent :
          TargetEmitterRuntimeProgramBound.checkCells after.checks ≤
            TargetEmitterRuntimeProgramBound.checkCells runtime.checks +
              prefixBlockGrowth
                (TargetEmitterLedger.slotCapacity raw) := by
        exact Nat.le_trans afterCheckGrowth
          (Nat.add_le_add_right
            (popped_checkCells_le runtime rest.reverse value
              nonemptyChecks)
            (prefixBlockGrowth
              (TargetEmitterLedger.slotCapacity raw)))
      have tailTargetBudget :
          after.targetTokens.length +
              (rest.length + 1) *
                prefixBlockGrowth
                  (TargetEmitterLedger.slotCapacity raw) ≤
            prefixTargetLimit
              (TargetEmitterLedger.slotCapacity raw) origin
              (totalCount + 1) := by
        have reserveEq :
            ((List.length (value :: rest) + 1) *
                prefixBlockGrowth
                  (TargetEmitterLedger.slotCapacity raw)) =
              prefixBlockGrowth
                  (TargetEmitterLedger.slotCapacity raw) +
                (rest.length + 1) *
                  prefixBlockGrowth
                    (TargetEmitterLedger.slotCapacity raw) := by
          simp only [List.length_cons]
          rw [Nat.add_mul]
          simp only [Nat.one_mul]
          exact Nat.add_comm _ _
        rw [reserveEq] at targetBudget
        apply Nat.le_trans
          (Nat.add_le_add_right afterTargetFromCurrent
            ((rest.length + 1) *
              prefixBlockGrowth
                (TargetEmitterLedger.slotCapacity raw)))
        simpa only [Nat.add_assoc] using targetBudget
      have tailCheckBudget :
          TargetEmitterRuntimeProgramBound.checkCells after.checks +
              (rest.length + 1) *
                prefixBlockGrowth
                  (TargetEmitterLedger.slotCapacity raw) ≤
            prefixCheckLimit
              (TargetEmitterLedger.slotCapacity raw) origin
              (totalCount + 1) := by
        have reserveEq :
            ((List.length (value :: rest) + 1) *
                prefixBlockGrowth
                  (TargetEmitterLedger.slotCapacity raw)) =
              prefixBlockGrowth
                  (TargetEmitterLedger.slotCapacity raw) +
                (rest.length + 1) *
                  prefixBlockGrowth
                    (TargetEmitterLedger.slotCapacity raw) := by
          simp only [List.length_cons]
          rw [Nat.add_mul]
          simp only [Nat.one_mul]
          exact Nat.add_comm _ _
        rw [reserveEq] at checkBudget
        apply Nat.le_trans
          (Nat.add_le_add_right afterChecksFromCurrent
            ((rest.length + 1) *
              prefixBlockGrowth
                (TargetEmitterLedger.slotCapacity raw)))
        simpa only [Nat.add_assoc] using checkBudget
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
      have afterScratch : after.scratch = 0 := by
        exact
          TargetEmitterProgramSemantics.nextPrefixResult_scratch popped
      have afterChecks :
          after.checks = rest.reverse := by
        simpa [after, popped,
          TargetEmitterControllerPrefixTrace.poppedRuntime] using
          (TargetEmitterProgramSemantics.nextPrefixResult_checks popped)
      have afterRoom :
          after.registers.outputIndex + 2 * rest.length ≤
            TargetEmitterLedger.baselineValue raw + 4 := by
        simp only [List.length_cons] at outputRoom
        simp only [after, popped,
          TargetEmitterControllerPrefixTrace.poppedRuntime,
          TargetEmitterProgramSemantics.nextPrefixResult_registers]
        omega
      have tailLength : rest.length ≤ totalCount :=
        Nat.le_trans (Nat.le_succ rest.length)
          (by simpa using lengthBound)
      have tailBound :=
        inductionHypothesis after afterRange afterCapturedBound
          afterScratch afterChecks tailBounds afterRoom tailLength
          tailTargetBudget tailCheckBudget
      have headBound :
          TargetEmitterControllerCheckTrace.nonemptyPathSteps
                (TargetEmitterLedger.slotCapacity raw)
                rest.reverse value +
              nextPrefixBlockEnvelope raw source popped ≤
            prefixPopUnit
                (TargetEmitterLedger.slotCapacity raw) totalCount +
              prefixBlockUnit
                (TargetEmitterLedger.slotCapacity raw) source origin
                (totalCount + 1) :=
        Nat.add_le_add popBound blockBound
      have totalBound := Nat.add_le_add headBound tailBound
      change
        (TargetEmitterControllerCheckTrace.nonemptyPathSteps
              (TargetEmitterLedger.slotCapacity raw)
              rest.reverse value +
            nextPrefixBlockEnvelope raw source popped) +
            normalizedLoopEnvelope raw source rest after ≤
          ((rest.length + 1) + 1) *
            (prefixPopUnit
                (TargetEmitterLedger.slotCapacity raw) totalCount +
              prefixBlockUnit
                (TargetEmitterLedger.slotCapacity raw) source origin
                (totalCount + 1))
      calc
        _ ≤
            (prefixPopUnit
                (TargetEmitterLedger.slotCapacity raw) totalCount +
              prefixBlockUnit
                (TargetEmitterLedger.slotCapacity raw) source origin
                (totalCount + 1)) +
              (rest.length + 1) *
                (prefixPopUnit
                    (TargetEmitterLedger.slotCapacity raw) totalCount +
                  prefixBlockUnit
                    (TargetEmitterLedger.slotCapacity raw) source origin
                    (totalCount + 1)) :=
          totalBound
        _ = _ := by
          exact unit_add_succ_mul _ _

/-- The recursive normalized loop envelope is dominated by the same closed
uniform polynomial expression. -/
theorem normalizedLoopEnvelope_le_uniform
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
        TargetEmitterLedger.baselineValue raw + 4) :
    normalizedLoopEnvelope raw source popOrder runtime ≤
      prefixUniformEnvelope
        (TargetEmitterLedger.slotCapacity raw) source runtime
        popOrder.length := by
  have bound :=
    normalizedLoopEnvelope_le_uniformAux workspace runtime
      popOrder.length popOrder runtime range capturedBound scratchZero
      checksShape valuesBound outputRoom (Nat.le_refl _)
      (by
        simp [prefixTargetLimit])
      (by
        simp [prefixCheckLimit])
  simpa [prefixUniformEnvelope] using bound

/-- The empty raw initial branch is covered by the zero-check specialization
of the closed uniform envelope. -/
theorem rawInitialEmptyEnvelope_le_uniform
    (raw : RawCircuit) (source : List WorkSymbol)
    (runtime : Runtime) :
    rawInitialEmptyEnvelope raw source runtime ≤
      prefixUniformEnvelope
        (TargetEmitterLedger.slotCapacity raw) source runtime 0 := by
  have popBound :=
    emptyPathSteps_le_prefixPopUnit
      (TargetEmitterLedger.slotCapacity raw) 0
  have blockBound :
      finalZeroBlockEnvelope raw source runtime ≤
        prefixBlockUnit
          (TargetEmitterLedger.slotCapacity raw) source runtime 1 := by
    apply programEnvelope_le_prefixBlockUnit
    · exact finalZero_length_le
    · unfold prefixTargetLimit
      omega
    · unfold prefixCheckLimit
      omega
  simpa [rawInitialEmptyEnvelope, prefixUniformEnvelope] using
    (Nat.add_le_add popBound blockBound)

/-- The complete nonempty raw initial-prefix envelope is dominated by the
closed uniform expression at the original represented stack. -/
theorem rawNonemptyPrefixEnvelope_le_uniform
    {raw : RawCircuit} {source : List WorkSymbol}
    (workspace : MarkedWorkspace source)
    (runtime : Runtime) (prior : List Nat)
    (second newest : Nat)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (_scratchZero : runtime.scratch = 0)
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
        TargetEmitterLedger.baselineValue raw + 4) :
    rawNonemptyPrefixEnvelope raw source runtime
        prior second newest ≤
      prefixUniformEnvelope
        (TargetEmitterLedger.slotCapacity raw) source runtime
        (prior.length + 2) := by
  let capacity := TargetEmitterLedger.slotCapacity raw
  let totalCount := prior.length + 2
  let blockBudget := totalCount + 1
  let popped := poppedRuntime runtime (prior ++ [second]) newest
  let after :=
    TargetEmitterProgramSemantics.firstPrefixResult
      popped prior second
  have popPriorBounds :
      ∀ value, value ∈ prior ++ [second] → value < capacity := by
    intro value member
    rcases List.mem_append.mp member with old | last
    · exact priorBounds value old
    · have equal : value = second := by simpa using last
      subst value
      exact secondBound
  have popPriorLength :
      (prior ++ [second]).length ≤ totalCount := by
    simp [totalCount]
  have popBound :
      TargetEmitterControllerCheckTrace.nonemptyPathSteps
          capacity (prior ++ [second]) newest ≤
        prefixPopUnit capacity totalCount :=
    nonemptyPathSteps_le_prefixPopUnit
      (prior ++ [second]) newest popPriorLength popPriorBounds
      (Nat.le_of_lt newestBound)
  have poppedTarget :
      popped.targetTokens.length ≤
        prefixTargetLimit capacity runtime blockBudget := by
    simp [popped, popped_target_length, prefixTargetLimit]
  have popChecksShape :
      runtime.checks = (prior ++ [second]) ++ [newest] := by
    simpa [List.append_assoc] using checksShape
  have poppedChecks :
      TargetEmitterRuntimeProgramBound.checkCells popped.checks ≤
        prefixCheckLimit capacity runtime blockBudget := by
    apply Nat.le_trans
      (by
        simpa [popped] using
          (popped_checkCells_le runtime (prior ++ [second]) newest
            popChecksShape))
    unfold prefixCheckLimit
    omega
  have blockBound :
      firstPrefixBlockEnvelope raw source popped ≤
        prefixBlockUnit capacity source runtime blockBudget := by
    apply programEnvelope_le_prefixBlockUnit
    · exact firstPrefix_length_le
    · exact poppedTarget
    · exact poppedChecks
  have poppedRange : ControllerRange raw popped.registers := by
    simpa [popped, capacity,
      TargetEmitterControllerPrefixTrace.poppedRuntime] using range
  have poppedCapturedBound :
      popped.captured + 1 ≤
        (SourceParser.circuitCells raw).length := by
    simpa [popped,
      TargetEmitterControllerPrefixTrace.poppedRuntime] using
      capturedBound
  have poppedScratchBound : popped.scratch < capacity := by
    simpa [popped, capacity,
      TargetEmitterControllerPrefixTrace.poppedRuntime] using newestBound
  have poppedChecksShape :
      popped.checks = prior ++ [second] := by
    simp [popped, TargetEmitterControllerPrefixTrace.poppedRuntime]
  have afterTargetGrowth :
      after.targetTokens.length ≤
        popped.targetTokens.length + prefixBlockGrowth capacity := by
    simpa [after, capacity] using
      (firstPrefix_target_growth workspace popped prior second
        poppedRange poppedCapturedBound poppedScratchBound
        poppedChecksShape secondBound)
  have afterCheckGrowth :
      TargetEmitterRuntimeProgramBound.checkCells after.checks ≤
        TargetEmitterRuntimeProgramBound.checkCells popped.checks +
          prefixBlockGrowth capacity := by
    simpa [after, capacity] using
      (firstPrefix_check_growth workspace popped prior second
        poppedRange poppedCapturedBound poppedScratchBound
        poppedChecksShape secondBound)
  have afterTargetFromOrigin :
      after.targetTokens.length ≤
        runtime.targetTokens.length + prefixBlockGrowth capacity := by
    rw [show popped.targetTokens.length =
      runtime.targetTokens.length by rfl] at afterTargetGrowth
    exact afterTargetGrowth
  have afterChecksFromOrigin :
      TargetEmitterRuntimeProgramBound.checkCells after.checks ≤
        TargetEmitterRuntimeProgramBound.checkCells runtime.checks +
          prefixBlockGrowth capacity := by
    exact Nat.le_trans afterCheckGrowth
      (Nat.add_le_add_right
        (by
          simpa [popped] using
            (popped_checkCells_le runtime (prior ++ [second]) newest
              popChecksShape))
        (prefixBlockGrowth capacity))
  have firstRoom :
      runtime.registers.outputIndex + 1 ≤
        TargetEmitterLedger.baselineValue raw + 4 := by
    omega
  have afterRange : ControllerRange raw after.registers := by
    exact firstPrefix_popped_range runtime prior second newest
      range firstRoom
  have afterCapturedBound :
      after.captured + 1 ≤
        (SourceParser.circuitCells raw).length := by
    rw [show after.captured = runtime.captured by
      exact firstPrefix_popped_captured runtime prior second newest]
    exact capturedBound
  have afterScratch : after.scratch = 0 := by
    exact
      TargetEmitterProgramSemantics.firstPrefixResult_scratch
        popped prior second
  have afterChecks :
      after.checks = prior := by
    simpa [after] using
      (TargetEmitterProgramSemantics.firstPrefixResult_checks
        popped prior second)
  have loopChecks :
      after.checks = prior.reverse.reverse := by
    simpa using afterChecks
  have reversedBounds :
      ∀ value, value ∈ prior.reverse → value < capacity := by
    intro value member
    exact priorBounds value (List.mem_reverse.mp member)
  have afterRoom :
      after.registers.outputIndex + 2 * prior.reverse.length ≤
        TargetEmitterLedger.baselineValue raw + 4 := by
    simp only [after, popped,
      TargetEmitterControllerPrefixTrace.poppedRuntime,
      TargetEmitterProgramSemantics.firstPrefixResult_registers,
      List.length_reverse]
    omega
  have reserveBound :
      prefixBlockGrowth capacity +
          (prior.length + 1) * prefixBlockGrowth capacity ≤
        blockBudget * prefixBlockGrowth capacity := by
    rw [unit_add_succ_mul]
    apply Nat.mul_le_mul_right
    simp [blockBudget, totalCount]
  have tailTargetBudget :
      after.targetTokens.length +
          (prior.reverse.length + 1) *
            prefixBlockGrowth capacity ≤
        prefixTargetLimit capacity runtime blockBudget := by
    simp only [List.length_reverse]
    calc
      _ ≤
          (runtime.targetTokens.length +
              prefixBlockGrowth capacity) +
            (prior.length + 1) *
              prefixBlockGrowth capacity :=
        Nat.add_le_add_right afterTargetFromOrigin _
      _ = runtime.targetTokens.length +
          (prefixBlockGrowth capacity +
            (prior.length + 1) * prefixBlockGrowth capacity) := by
        rw [Nat.add_assoc]
      _ ≤
          runtime.targetTokens.length +
            blockBudget * prefixBlockGrowth capacity :=
        Nat.add_le_add_left reserveBound _
      _ = prefixTargetLimit capacity runtime blockBudget := by
        rfl
  have tailCheckBudget :
      TargetEmitterRuntimeProgramBound.checkCells after.checks +
          (prior.reverse.length + 1) *
            prefixBlockGrowth capacity ≤
        prefixCheckLimit capacity runtime blockBudget := by
    simp only [List.length_reverse]
    calc
      _ ≤
          (TargetEmitterRuntimeProgramBound.checkCells runtime.checks +
              prefixBlockGrowth capacity) +
            (prior.length + 1) *
              prefixBlockGrowth capacity :=
        Nat.add_le_add_right afterChecksFromOrigin _
      _ =
          TargetEmitterRuntimeProgramBound.checkCells runtime.checks +
            (prefixBlockGrowth capacity +
              (prior.length + 1) * prefixBlockGrowth capacity) := by
        rw [Nat.add_assoc]
      _ ≤
          TargetEmitterRuntimeProgramBound.checkCells runtime.checks +
            blockBudget * prefixBlockGrowth capacity :=
        Nat.add_le_add_left reserveBound _
      _ = prefixCheckLimit capacity runtime blockBudget := by
        rfl
  have tailLength : prior.reverse.length ≤ totalCount := by
    simp [totalCount]
  have tailBound :=
    rawLoopEnvelope_le_uniformAux workspace runtime totalCount
      prior.reverse after afterRange afterCapturedBound afterScratch
      loopChecks reversedBounds afterRoom tailLength
      tailTargetBudget tailCheckBudget
  have headBound :
      TargetEmitterControllerCheckTrace.nonemptyPathSteps
            capacity (prior ++ [second]) newest +
          firstPrefixBlockEnvelope raw source popped ≤
        prefixPopUnit capacity totalCount +
          prefixBlockUnit capacity source runtime blockBudget :=
    Nat.add_le_add popBound blockBound
  have totalBound := Nat.add_le_add headBound tailBound
  let unit :=
    prefixPopUnit capacity totalCount +
      prefixBlockUnit capacity source runtime blockBudget
  change
    (TargetEmitterControllerCheckTrace.nonemptyPathSteps
          capacity (prior ++ [second]) newest +
        firstPrefixBlockEnvelope raw source popped) +
        rawLoopEnvelope raw source prior.reverse after ≤
      prefixUniformEnvelope capacity source runtime totalCount
  calc
    _ ≤ unit + (prior.reverse.length + 1) * unit := by
      simpa [unit] using totalBound
    _ = (prior.length + 1 + 1) * unit := by
      rw [List.length_reverse]
      exact unit_add_succ_mul _ _
    _ ≤ (totalCount + 1) * unit := by
      apply Nat.mul_le_mul_right
      simp [totalCount]
    _ = prefixUniformEnvelope capacity source runtime totalCount := by
      rfl

/-- The complete nonempty normalized initial-prefix envelope has the same
closed uniform polynomial domination. -/
theorem normalizedNonemptyPrefixEnvelope_le_uniform
    {raw : RawCircuit} {source : List WorkSymbol}
    (workspace : MarkedWorkspace source)
    (runtime : Runtime) (prior : List Nat)
    (second newest : Nat)
    (range : ControllerRange raw runtime.registers)
    (capturedBound :
      runtime.captured + 1 ≤
        (SourceParser.circuitCells raw).length)
    (_scratchZero : runtime.scratch = 0)
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
        TargetEmitterLedger.baselineValue raw + 4) :
    normalizedNonemptyPrefixEnvelope raw source runtime
        prior second newest ≤
      prefixUniformEnvelope
        (TargetEmitterLedger.slotCapacity raw) source runtime
        (prior.length + 2) := by
  let capacity := TargetEmitterLedger.slotCapacity raw
  let totalCount := prior.length + 2
  let blockBudget := totalCount + 1
  let popped := poppedRuntime runtime (prior ++ [second]) newest
  let after :=
    TargetEmitterProgramSemantics.firstPrefixResult
      popped prior second
  have popPriorBounds :
      ∀ value, value ∈ prior ++ [second] → value < capacity := by
    intro value member
    rcases List.mem_append.mp member with old | last
    · exact priorBounds value old
    · have equal : value = second := by simpa using last
      subst value
      exact secondBound
  have popPriorLength :
      (prior ++ [second]).length ≤ totalCount := by
    simp [totalCount]
  have popBound :
      TargetEmitterControllerCheckTrace.nonemptyPathSteps
          capacity (prior ++ [second]) newest ≤
        prefixPopUnit capacity totalCount :=
    nonemptyPathSteps_le_prefixPopUnit
      (prior ++ [second]) newest popPriorLength popPriorBounds
      (Nat.le_of_lt newestBound)
  have poppedTarget :
      popped.targetTokens.length ≤
        prefixTargetLimit capacity runtime blockBudget := by
    simp [popped, popped_target_length, prefixTargetLimit]
  have popChecksShape :
      runtime.checks = (prior ++ [second]) ++ [newest] := by
    simpa [List.append_assoc] using checksShape
  have poppedChecks :
      TargetEmitterRuntimeProgramBound.checkCells popped.checks ≤
        prefixCheckLimit capacity runtime blockBudget := by
    apply Nat.le_trans
      (by
        simpa [popped] using
          (popped_checkCells_le runtime (prior ++ [second]) newest
            popChecksShape))
    unfold prefixCheckLimit
    omega
  have blockBound :
      firstPrefixBlockEnvelope raw source popped ≤
        prefixBlockUnit capacity source runtime blockBudget := by
    apply programEnvelope_le_prefixBlockUnit
    · exact firstPrefix_length_le
    · exact poppedTarget
    · exact poppedChecks
  have poppedRange : ControllerRange raw popped.registers := by
    simpa [popped, capacity,
      TargetEmitterControllerPrefixTrace.poppedRuntime] using range
  have poppedCapturedBound :
      popped.captured + 1 ≤
        (SourceParser.circuitCells raw).length := by
    simpa [popped,
      TargetEmitterControllerPrefixTrace.poppedRuntime] using
      capturedBound
  have poppedScratchBound : popped.scratch < capacity := by
    simpa [popped, capacity,
      TargetEmitterControllerPrefixTrace.poppedRuntime] using newestBound
  have poppedChecksShape :
      popped.checks = prior ++ [second] := by
    simp [popped, TargetEmitterControllerPrefixTrace.poppedRuntime]
  have afterTargetGrowth :
      after.targetTokens.length ≤
        popped.targetTokens.length + prefixBlockGrowth capacity := by
    simpa [after, capacity] using
      (firstPrefix_target_growth workspace popped prior second
        poppedRange poppedCapturedBound poppedScratchBound
        poppedChecksShape secondBound)
  have afterCheckGrowth :
      TargetEmitterRuntimeProgramBound.checkCells after.checks ≤
        TargetEmitterRuntimeProgramBound.checkCells popped.checks +
          prefixBlockGrowth capacity := by
    simpa [after, capacity] using
      (firstPrefix_check_growth workspace popped prior second
        poppedRange poppedCapturedBound poppedScratchBound
        poppedChecksShape secondBound)
  have afterTargetFromOrigin :
      after.targetTokens.length ≤
        runtime.targetTokens.length + prefixBlockGrowth capacity := by
    rw [show popped.targetTokens.length =
      runtime.targetTokens.length by rfl] at afterTargetGrowth
    exact afterTargetGrowth
  have afterChecksFromOrigin :
      TargetEmitterRuntimeProgramBound.checkCells after.checks ≤
        TargetEmitterRuntimeProgramBound.checkCells runtime.checks +
          prefixBlockGrowth capacity := by
    exact Nat.le_trans afterCheckGrowth
      (Nat.add_le_add_right
        (by
          simpa [popped] using
            (popped_checkCells_le runtime (prior ++ [second]) newest
              popChecksShape))
        (prefixBlockGrowth capacity))
  have firstRoom :
      runtime.registers.outputIndex + 1 ≤
        TargetEmitterLedger.baselineValue raw + 4 := by
    omega
  have afterRange : ControllerRange raw after.registers := by
    exact firstPrefix_popped_range runtime prior second newest
      range firstRoom
  have afterCapturedBound :
      after.captured + 1 ≤
        (SourceParser.circuitCells raw).length := by
    rw [show after.captured = runtime.captured by
      exact firstPrefix_popped_captured runtime prior second newest]
    exact capturedBound
  have afterScratch : after.scratch = 0 := by
    exact
      TargetEmitterProgramSemantics.firstPrefixResult_scratch
        popped prior second
  have afterChecks :
      after.checks = prior := by
    simpa [after] using
      (TargetEmitterProgramSemantics.firstPrefixResult_checks
        popped prior second)
  have loopChecks :
      after.checks = prior.reverse.reverse := by
    simpa using afterChecks
  have reversedBounds :
      ∀ value, value ∈ prior.reverse → value < capacity := by
    intro value member
    exact priorBounds value (List.mem_reverse.mp member)
  have afterRoom :
      after.registers.outputIndex + 2 * prior.reverse.length ≤
        TargetEmitterLedger.baselineValue raw + 4 := by
    simp only [after, popped,
      TargetEmitterControllerPrefixTrace.poppedRuntime,
      TargetEmitterProgramSemantics.firstPrefixResult_registers,
      List.length_reverse]
    omega
  have reserveBound :
      prefixBlockGrowth capacity +
          (prior.length + 1) * prefixBlockGrowth capacity ≤
        blockBudget * prefixBlockGrowth capacity := by
    rw [unit_add_succ_mul]
    apply Nat.mul_le_mul_right
    simp [blockBudget, totalCount]
  have tailTargetBudget :
      after.targetTokens.length +
          (prior.reverse.length + 1) *
            prefixBlockGrowth capacity ≤
        prefixTargetLimit capacity runtime blockBudget := by
    simp only [List.length_reverse]
    calc
      _ ≤
          (runtime.targetTokens.length +
              prefixBlockGrowth capacity) +
            (prior.length + 1) *
              prefixBlockGrowth capacity :=
        Nat.add_le_add_right afterTargetFromOrigin _
      _ = runtime.targetTokens.length +
          (prefixBlockGrowth capacity +
            (prior.length + 1) * prefixBlockGrowth capacity) := by
        rw [Nat.add_assoc]
      _ ≤
          runtime.targetTokens.length +
            blockBudget * prefixBlockGrowth capacity :=
        Nat.add_le_add_left reserveBound _
      _ = prefixTargetLimit capacity runtime blockBudget := by
        rfl
  have tailCheckBudget :
      TargetEmitterRuntimeProgramBound.checkCells after.checks +
          (prior.reverse.length + 1) *
            prefixBlockGrowth capacity ≤
        prefixCheckLimit capacity runtime blockBudget := by
    simp only [List.length_reverse]
    calc
      _ ≤
          (TargetEmitterRuntimeProgramBound.checkCells runtime.checks +
              prefixBlockGrowth capacity) +
            (prior.length + 1) *
              prefixBlockGrowth capacity :=
        Nat.add_le_add_right afterChecksFromOrigin _
      _ =
          TargetEmitterRuntimeProgramBound.checkCells runtime.checks +
            (prefixBlockGrowth capacity +
              (prior.length + 1) * prefixBlockGrowth capacity) := by
        rw [Nat.add_assoc]
      _ ≤
          TargetEmitterRuntimeProgramBound.checkCells runtime.checks +
            blockBudget * prefixBlockGrowth capacity :=
        Nat.add_le_add_left reserveBound _
      _ = prefixCheckLimit capacity runtime blockBudget := by
        rfl
  have tailLength : prior.reverse.length ≤ totalCount := by
    simp [totalCount]
  have tailBound :=
    normalizedLoopEnvelope_le_uniformAux workspace runtime totalCount
      prior.reverse after afterRange afterCapturedBound afterScratch
      loopChecks reversedBounds afterRoom tailLength
      tailTargetBudget tailCheckBudget
  have headBound :
      TargetEmitterControllerCheckTrace.nonemptyPathSteps
            capacity (prior ++ [second]) newest +
          firstPrefixBlockEnvelope raw source popped ≤
        prefixPopUnit capacity totalCount +
          prefixBlockUnit capacity source runtime blockBudget :=
    Nat.add_le_add popBound blockBound
  have totalBound := Nat.add_le_add headBound tailBound
  let unit :=
    prefixPopUnit capacity totalCount +
      prefixBlockUnit capacity source runtime blockBudget
  change
    (TargetEmitterControllerCheckTrace.nonemptyPathSteps
          capacity (prior ++ [second]) newest +
        firstPrefixBlockEnvelope raw source popped) +
        normalizedLoopEnvelope raw source prior.reverse after ≤
      prefixUniformEnvelope capacity source runtime totalCount
  calc
    _ ≤ unit + (prior.reverse.length + 1) * unit := by
      simpa [unit] using totalBound
    _ = (prior.length + 1 + 1) * unit := by
      rw [List.length_reverse]
      exact unit_add_succ_mul _ _
    _ ≤ (totalCount + 1) * unit := by
      apply Nat.mul_le_mul_right
      simp [totalCount]
    _ = prefixUniformEnvelope capacity source runtime totalCount := by
      rfl

end PNP.Concrete.LockedNAND.TargetEmitterControllerPrefixBound
