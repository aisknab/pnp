/-
Copyright (c) 2026 PNP Labs.

Constructive work bounds for the output loop and terminal cleanup of the
grammar-only locked-NAND target emitter.

The exact trace module already fixes every comparison branch and graph bridge.
This layer rebuilds only the three small safe-program witnesses so their exact
paths can be paired with the uniform primitive-program envelope.  The loop
counter below is proof-side accounting derived from the represented baseline;
it is not an input to the executable graph.
-/

import PNP.Concrete.LockedNANDTargetEmitterControllerOutputTrace
import PNP.Concrete.LockedNANDTargetEmitterRuntimeProgramBound

namespace PNP.Concrete.LockedNAND.TargetEmitterControllerOutputBound

open PNP.Concrete
open WorkMachineProgramGraph
open WorkMachineProgramPath
open TargetEmitterController
open TargetEmitterPrimitiveCompiler
open TargetEmitterBlockCompiler
open TargetEmitterPlan
open TargetEmitterProgramSemantics
open TargetEmitterRuntimeProgram

abbrev Runtime := TargetEmitterProgramSemantics.Runtime
abbrev CursorLayout := TargetEmitterRuntimeProgram.CursorLayout
abbrev LedgerFits := TargetEmitterRuntimeProgram.LedgerFits
abbrev TapeRepresents :=
  TargetEmitterControllerOutputTrace.TapeRepresents
abbrev FinalTapeRepresents :=
  TargetEmitterControllerOutputTrace.FinalTapeRepresents

private def beginDescriptor : BlockDescriptor :=
  { code := Block.beginOutput
    primitives := Plan.beginOutput
    continuation := .node outputCompareRef }

private def itemDescriptor : BlockDescriptor :=
  { code := Block.outputItem
    primitives := Plan.outputItem
    continuation := .node outputCompareRef }

private def finishDescriptor : BlockDescriptor :=
  { code := Block.outputFinish
    primitives := Plan.outputFinish
    continuation := .node finalizerRef }

private def beginPrograms : List WorkMachine :=
  (compileProgram Plan.beginOutput).getD []

private def itemPrograms : List WorkMachine :=
  (compileProgram Plan.outputItem).getD []

private def finishPrograms : List WorkMachine :=
  (compileProgram Plan.outputFinish).getD []

private theorem beginDescriptor_member :
    beginDescriptor ∈ blockDescriptors := by
  simp [beginDescriptor, blockDescriptors, fixedBlockDescriptors]

private theorem itemDescriptor_member :
    itemDescriptor ∈ blockDescriptors := by
  simp [itemDescriptor, blockDescriptors, fixedBlockDescriptors]

private theorem finishDescriptor_member :
    finishDescriptor ∈ blockDescriptors := by
  simp [finishDescriptor, blockDescriptors, fixedBlockDescriptors]

private theorem begin_compiled :
    compileProgram Plan.beginOutput = some beginPrograms := by
  rfl

private theorem item_compiled :
    compileProgram Plan.outputItem = some itemPrograms := by
  rfl

private theorem finish_compiled :
    compileProgram Plan.outputFinish = some finishPrograms := by
  rfl

private theorem beginPrograms_nonempty : beginPrograms ≠ [] := by
  decide

private theorem itemPrograms_nonempty : itemPrograms ≠ [] := by
  decide

private theorem finishPrograms_nonempty : finishPrograms ≠ [] := by
  decide

private theorem begin_startState :
    beginOutputRef.startState =
      TargetEmitterRuntimeProgram.entryState 0 beginPrograms := by
  rfl

private theorem item_startState :
    outputItemRef.startState =
      TargetEmitterRuntimeProgram.entryState 0 itemPrograms := by
  rfl

private theorem finish_startState :
    outputFinishRef.startState =
      TargetEmitterRuntimeProgram.entryState 0 finishPrograms := by
  rfl

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

private theorem begin_safe
    {capacity : Nat} {source : List WorkSymbol}
    (context : SourceContext source)
    (layout : CursorLayout source)
    (runtime : Runtime)
    (scratchBound : runtime.scratch < capacity) :
    ProgramSafe capacity source context Plan.beginOutput
      runtime (beginOutputResult runtime) := by
  unfold Plan.beginOutput TargetEmitterPlan.beginOutputProgram
  refine ProgramSafe.cons _ _ _ _ _
    (PrimitiveSafe.appendMarked runtime .programEnd layout) ?_
  refine ProgramSafe.cons _ _ _ _ _
    (PrimitiveSafe.resetScratch _ scratchBound) ?_
  simpa [beginOutputResult] using
    (ProgramSafe.nil
      ({ runtime with
        scratch := 0
        targetTokens := runtime.targetTokens ++ [.programEnd] }))

private theorem item_safe
    {capacity : Nat} {source : List WorkSymbol}
    (context : SourceContext source)
    (layout : CursorLayout source)
    (runtime : Runtime)
    (scratchBound : runtime.scratch < capacity) :
    ProgramSafe capacity source context Plan.outputItem
      runtime (outputLoopItemResult runtime) := by
  unfold Plan.outputItem TargetEmitterPlan.outputLoopItemProgram
  refine ProgramSafe.cons _ _ _ _ _
    (PrimitiveSafe.appendMarked runtime .gate layout) ?_
  refine ProgramSafe.cons _ _ _ _ _
    (PrimitiveSafe.emitScratchNatMarked _
      (Nat.le_of_lt scratchBound) layout) ?_
  refine ProgramSafe.cons _ _ _ _ _
    (PrimitiveSafe.incrementScratch _ scratchBound) ?_
  simpa [outputLoopItemResult, encodeSourceTokens,
    List.append_assoc] using
    (ProgramSafe.nil
      ({ runtime with
        scratch := runtime.scratch + 1
        targetTokens :=
          (runtime.targetTokens ++ [.gate]) ++
            encodeNatTokens runtime.scratch }))

private theorem finish_safe
    {capacity : Nat} {source : List WorkSymbol}
    (context : SourceContext source)
    (layout : CursorLayout source)
    (runtime : Runtime)
    (fits : LedgerFits capacity runtime.registers)
    (room : runtime.scratch + 3 < capacity) :
    ProgramSafe capacity source context Plan.outputFinish
      runtime (outputLoopFinishResult runtime) := by
  unfold Plan.outputFinish TargetEmitterPlan.outputLoopFinishProgram
  refine ProgramSafe.cons _ _ _ _ _
    (PrimitiveSafe.incrementScratch runtime (by omega)) ?_
  refine ProgramSafe.cons _ _ _ _ _
    (PrimitiveSafe.incrementScratch _ (by simp; omega)) ?_
  refine ProgramSafe.cons _ _ _ _ _
    (PrimitiveSafe.incrementScratch _ (by simp; omega)) ?_
  refine ProgramSafe.cons _ _ _ _ _
    (PrimitiveSafe.appendMarked _ .gate layout) ?_
  refine ProgramSafe.cons _ _ _ _ _
    (PrimitiveSafe.emitScratchNatMarked _ (by simp; omega) layout) ?_
  refine ProgramSafe.cons _ _ _ _ _
    (PrimitiveSafe.appendMarked _ .outputsEnd layout) ?_
  refine ProgramSafe.cons _ _ _ _ _
    (PrimitiveSafe.resetScratch _ room) ?_
  refine ProgramSafe.cons _ _ _ _ _
    (PrimitiveSafe.addRegister _ .baseline .baseline rfl fits
      (by simpa [TargetEmitterLedger.slotValue] using fits.baseline)) ?_
  refine ProgramSafe.cons _ _ _ _ _
    (PrimitiveSafe.appendMarked _ .threshold layout) ?_
  refine ProgramSafe.cons _ _ _ _ _
    (PrimitiveSafe.emitScratchNatMarked _
      (by simpa [TargetEmitterLedger.slotValue] using fits.baseline)
      layout) ?_
  refine ProgramSafe.cons _ _ _ _ _
    (PrimitiveSafe.appendMarked _ .instanceEnd layout) ?_
  simpa [outputLoopFinishResult, encodeSourceTokens,
    TargetEmitterLedger.slotValue, List.append_assoc] using
    (ProgramSafe.nil
      ({ runtime with
        scratch := runtime.registers.baseline
        targetTokens :=
          (((((runtime.targetTokens ++ [.gate]) ++
              encodeNatTokens (runtime.scratch + 3)) ++
            [.outputsEnd]) ++ [.threshold]) ++
            encodeNatTokens runtime.registers.baseline) ++
            [.instanceEnd] }))

/-- Uniform primitive-program envelope for the begin-output block. -/
def beginBlockEnvelope (capacity : Nat) (source : List WorkSymbol)
    (runtime : Runtime) : Nat :=
  TargetEmitterRuntimeProgramBound.programWorkEnvelope
    capacity source runtime Plan.beginOutput

/-- Uniform primitive-program envelope for one output-item block. -/
def itemBlockEnvelope (capacity : Nat) (source : List WorkSymbol)
    (runtime : Runtime) : Nat :=
  TargetEmitterRuntimeProgramBound.programWorkEnvelope
    capacity source runtime Plan.outputItem

/-- Uniform primitive-program envelope for the output-finish block. -/
def finishBlockEnvelope (capacity : Nat) (source : List WorkSymbol)
    (runtime : Runtime) : Nat :=
  TargetEmitterRuntimeProgramBound.programWorkEnvelope
    capacity source runtime Plan.outputFinish

/-- Exact recursive work envelope for the represented output loop. -/
def outputLoopEnvelope (capacity : Nat) (source : List WorkSymbol) :
    Nat → Runtime → Nat
  | 0, runtime =>
      TargetEmitterControllerOutputTrace.comparePathSteps
          capacity runtime.scratch +
        finishBlockEnvelope capacity source runtime +
        TargetEmitterControllerOutputTrace.finalizerPathSteps source
  | remaining + 1, runtime =>
      TargetEmitterControllerOutputTrace.comparePathSteps
          capacity runtime.scratch +
        itemBlockEnvelope capacity source runtime +
        outputLoopEnvelope capacity source remaining
          (outputLoopItemResult runtime)

/-- Exact recursive envelope for the full begin-output suffix. -/
def outputPhaseEnvelope (capacity : Nat) (source : List WorkSymbol)
    (runtime : Runtime) : Nat :=
  beginBlockEnvelope capacity source runtime +
    outputLoopEnvelope capacity source runtime.registers.baseline
      (beginOutputResult runtime)

/-- Target-token budget covering `programEnd` and every possible output item
before the finish block. -/
def outputTargetLimit (capacity : Nat) (runtime : Runtime) : Nat :=
  runtime.targetTokens.length + 1 +
    capacity * (capacity + 2)

/-- One physical footprint large enough for every fixed block in the output
suffix.  Eleven is the literal length of the largest output block. -/
def outputMasterSize (capacity : Nat) (source : List WorkSymbol)
    (runtime : Runtime) : Nat :=
  capacity + source.length +
    2 * outputTargetLimit capacity runtime +
    TargetEmitterRuntimeProgramBound.checkCells runtime.checks +
    11 * (3 * capacity + 3) + 1

/-- Uniform work charge for any one of the three output blocks. -/
def outputBlockUnit (capacity : Nat) (source : List WorkSymbol)
    (runtime : Runtime) : Nat :=
  11 *
    (TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
      (outputMasterSize capacity source runtime) + 1)

/-- Uniform charge for one literal baseline comparison and its graph bridge. -/
def outputCompareUnit (capacity : Nat) : Nat :=
  50 * (capacity + 1) * (capacity + 1)

/-- Closed non-recursive envelope for the full output suffix. -/
def outputUniformEnvelope (capacity : Nat) (source : List WorkSymbol)
    (runtime : Runtime) : Nat :=
  outputBlockUnit capacity source runtime +
    (runtime.registers.baseline + 1) *
      (outputCompareUnit capacity +
        outputBlockUnit capacity source runtime) +
    TargetEmitterControllerOutputTrace.finalizerPathSteps source

/-- Bounded begin-output block from any represented entry tape. -/
theorem beginBlock_path_bounded
    (capacity : Nat) (source : List WorkSymbol)
    (context : SourceContext source)
    (layout : CursorLayout source)
    (runtime : Runtime) (initialTape : WorkTape)
    (scratchBound : runtime.scratch < capacity)
    (represents :
      TapeRepresents beginOutputRef.startState
        capacity runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node beginOutputRef)
          (.node outputCompareRef) steps initialTape finalTape ∧
      TapeRepresents outputCompareRef.startState
        capacity (beginOutputResult runtime).scratch
        (beginOutputResult runtime).registers
        (beginOutputResult runtime).checks source
        (beginOutputResult runtime).targetTokens finalTape ∧
      steps ≤ beginBlockEnvelope capacity source runtime := by
  let initial : WorkConfiguration :=
    { state := TargetEmitterRuntimeProgram.entryState 0 beginPrograms
      tape := initialTape }
  have inputRepresents :
      TargetEmitterRuntime.Represents initial.state
        capacity runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initial := by
    have atEntry :
        TapeRepresents
          (TargetEmitterRuntimeProgram.entryState 0 beginPrograms)
          capacity runtime.scratch runtime.registers runtime.checks
          source runtime.targetTokens initialTape := by
      rw [← begin_startState]
      exact represents
    exact atEntry
  have scratchLe : runtime.scratch ≤ capacity :=
    Nat.le_of_lt scratchBound
  rcases
      TargetEmitterRuntimeProgramBound.ProgramSafe.descriptor_acceptPath_bounded
        beginDescriptor beginDescriptor_member
        (begin_safe context layout runtime scratchBound)
        scratchLe beginPrograms
        (by simpa [beginDescriptor] using begin_compiled)
        beginPrograms_nonempty 0 initial inputRepresents with
    ⟨steps, actualFinal, path, finalRepresents, bound⟩
  refine ⟨steps, actualFinal.tape, ?_, ?_, ?_⟩
  · simpa [beginDescriptor, beginOutputRef] using path
  · exact
      represents_at_state
        (newState := outputCompareRef.startState)
        finalRepresents
  · simpa [beginBlockEnvelope, beginDescriptor] using bound

/-- Bounded one-item block from any represented item entry tape. -/
theorem itemBlock_path_bounded
    (capacity : Nat) (source : List WorkSymbol)
    (context : SourceContext source)
    (layout : CursorLayout source)
    (runtime : Runtime) (initialTape : WorkTape)
    (scratchBound : runtime.scratch < capacity)
    (represents :
      TapeRepresents outputItemRef.startState
        capacity runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node outputItemRef)
          (.node outputCompareRef) steps initialTape finalTape ∧
      TapeRepresents outputCompareRef.startState
        capacity (outputLoopItemResult runtime).scratch
        (outputLoopItemResult runtime).registers
        (outputLoopItemResult runtime).checks source
        (outputLoopItemResult runtime).targetTokens finalTape ∧
      steps ≤ itemBlockEnvelope capacity source runtime := by
  let initial : WorkConfiguration :=
    { state := TargetEmitterRuntimeProgram.entryState 0 itemPrograms
      tape := initialTape }
  have inputRepresents :
      TargetEmitterRuntime.Represents initial.state
        capacity runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initial := by
    have atEntry :
        TapeRepresents
          (TargetEmitterRuntimeProgram.entryState 0 itemPrograms)
          capacity runtime.scratch runtime.registers runtime.checks
          source runtime.targetTokens initialTape := by
      rw [← item_startState]
      exact represents
    exact atEntry
  have scratchLe : runtime.scratch ≤ capacity :=
    Nat.le_of_lt scratchBound
  rcases
      TargetEmitterRuntimeProgramBound.ProgramSafe.descriptor_acceptPath_bounded
        itemDescriptor itemDescriptor_member
        (item_safe context layout runtime scratchBound)
        scratchLe itemPrograms
        (by simpa [itemDescriptor] using item_compiled)
        itemPrograms_nonempty 0 initial inputRepresents with
    ⟨steps, actualFinal, path, finalRepresents, bound⟩
  refine ⟨steps, actualFinal.tape, ?_, ?_, ?_⟩
  · simpa [itemDescriptor, outputItemRef] using path
  · exact
      represents_at_state
        (newState := outputCompareRef.startState)
        finalRepresents
  · simpa [itemBlockEnvelope, itemDescriptor] using bound

/-- Bounded output-finish block from any represented finish entry tape. -/
theorem finishBlock_path_bounded
    (capacity : Nat) (source : List WorkSymbol)
    (context : SourceContext source)
    (layout : CursorLayout source)
    (runtime : Runtime) (initialTape : WorkTape)
    (fits : LedgerFits capacity runtime.registers)
    (room : runtime.scratch + 3 < capacity)
    (represents :
      TapeRepresents outputFinishRef.startState
        capacity runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node outputFinishRef)
          (.node finalizerRef) steps initialTape finalTape ∧
      TapeRepresents finalizerRef.startState
        capacity (outputLoopFinishResult runtime).scratch
        (outputLoopFinishResult runtime).registers
        (outputLoopFinishResult runtime).checks source
        (outputLoopFinishResult runtime).targetTokens finalTape ∧
      steps ≤ finishBlockEnvelope capacity source runtime := by
  let initial : WorkConfiguration :=
    { state := TargetEmitterRuntimeProgram.entryState 0 finishPrograms
      tape := initialTape }
  have inputRepresents :
      TargetEmitterRuntime.Represents initial.state
        capacity runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initial := by
    have atEntry :
        TapeRepresents
          (TargetEmitterRuntimeProgram.entryState 0 finishPrograms)
          capacity runtime.scratch runtime.registers runtime.checks
          source runtime.targetTokens initialTape := by
      rw [← finish_startState]
      exact represents
    exact atEntry
  have scratchLe : runtime.scratch ≤ capacity := by
    have := fits.baseline
    omega
  rcases
      TargetEmitterRuntimeProgramBound.ProgramSafe.descriptor_acceptPath_bounded
        finishDescriptor finishDescriptor_member
        (finish_safe context layout runtime fits room)
        scratchLe finishPrograms
        (by simpa [finishDescriptor] using finish_compiled)
        finishPrograms_nonempty 0 initial inputRepresents with
    ⟨steps, actualFinal, path, finalRepresents, bound⟩
  refine ⟨steps, actualFinal.tape, ?_, ?_, ?_⟩
  · simpa [finishDescriptor, outputFinishRef] using path
  · exact
      represents_at_state
        (newState := finalizerRef.startState)
        finalRepresents
  · simpa [finishBlockEnvelope, finishDescriptor] using bound

/-- One comparison match, the bounded finish block, and exact cleanup. -/
theorem compareMatchToAccept_path_bounded
    (capacity : Nat) (source : List WorkSymbol)
    (context : SourceContext source)
    (layout : CursorLayout source)
    (runtime : Runtime) (initialTape : WorkTape)
    (fits : LedgerFits capacity runtime.registers)
    (equal : runtime.scratch = runtime.registers.baseline)
    (room : runtime.scratch + 3 < capacity)
    (represents :
      TapeRepresents outputCompareRef.startState
        capacity runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node outputCompareRef) .accept
        steps initialTape finalTape ∧
      FinalTapeRepresents capacity
        (outputLoopFinishResult runtime).scratch
        (outputLoopFinishResult runtime).registers
        (outputLoopFinishResult runtime).checks source
        (outputLoopFinishResult runtime).targetTokens finalTape ∧
      steps ≤
        TargetEmitterControllerOutputTrace.comparePathSteps
            capacity runtime.scratch +
          finishBlockEnvelope capacity source runtime +
          TargetEmitterControllerOutputTrace.finalizerPathSteps source := by
  rcases
      TargetEmitterControllerOutputTrace.compareMatch_path
        capacity runtime.scratch runtime.registers runtime.checks
        source context runtime.targetTokens initialTape fits equal
        represents with
    ⟨finishTape, comparePath, finishRepresents⟩
  rcases
      finishBlock_path_bounded capacity source context layout runtime
        finishTape fits room finishRepresents with
    ⟨finishSteps, finalizerTape, finishPath,
      finalizerRepresents, finishBound⟩
  rcases
      TargetEmitterControllerOutputTrace.finalizerAccept_path
        capacity (outputLoopFinishResult runtime).scratch
        (outputLoopFinishResult runtime).registers
        (outputLoopFinishResult runtime).checks source
        (outputLoopFinishResult runtime).targetTokens
        finalizerTape
        (TargetEmitterControllerOutputTrace.CursorLayout.finalizerAllowed
          layout)
        finalizerRepresents with
    ⟨finalTape, finalizerPath, finalRepresents⟩
  let throughFinish :=
    AcceptPath.trans graph (.node outputCompareRef)
      (.node outputFinishRef) (.node finalizerRef)
      (TargetEmitterControllerOutputTrace.comparePathSteps
        capacity runtime.scratch)
      finishSteps initialTape finishTape finalizerTape
      comparePath finishPath
  let steps :=
    TargetEmitterControllerOutputTrace.comparePathSteps
        capacity runtime.scratch +
      finishSteps +
      TargetEmitterControllerOutputTrace.finalizerPathSteps source
  refine ⟨steps, finalTape, ?_, finalRepresents, ?_⟩
  · exact
      AcceptPath.trans graph (.node outputCompareRef)
        (.node finalizerRef) .accept
        (TargetEmitterControllerOutputTrace.comparePathSteps
            capacity runtime.scratch + finishSteps)
        (TargetEmitterControllerOutputTrace.finalizerPathSteps source)
        initialTape finalizerTape finalTape
        throughFinish finalizerPath
  · unfold steps
    omega

/-- One comparison mismatch followed by one bounded output-item block. -/
theorem compareMismatchItem_path_bounded
    (capacity : Nat) (source : List WorkSymbol)
    (context : SourceContext source)
    (layout : CursorLayout source)
    (runtime : Runtime) (initialTape : WorkTape)
    (fits : LedgerFits capacity runtime.registers)
    (less : runtime.scratch < runtime.registers.baseline)
    (represents :
      TapeRepresents outputCompareRef.startState
        capacity runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node outputCompareRef)
          (.node outputCompareRef) steps initialTape finalTape ∧
      TapeRepresents outputCompareRef.startState
        capacity (outputLoopItemResult runtime).scratch
        (outputLoopItemResult runtime).registers
        (outputLoopItemResult runtime).checks source
        (outputLoopItemResult runtime).targetTokens finalTape ∧
      steps ≤
        TargetEmitterControllerOutputTrace.comparePathSteps
            capacity runtime.scratch +
          itemBlockEnvelope capacity source runtime := by
  rcases
      TargetEmitterControllerOutputTrace.compareMismatch_path
        capacity runtime.scratch runtime.registers runtime.checks
        source context runtime.targetTokens initialTape fits less
        represents with
    ⟨itemTape, comparePath, itemRepresents⟩
  have scratchBound : runtime.scratch < capacity :=
    Nat.lt_of_lt_of_le less fits.baseline
  rcases
      itemBlock_path_bounded capacity source context layout runtime
        itemTape scratchBound itemRepresents with
    ⟨itemSteps, finalTape, itemPath, finalRepresents, itemBound⟩
  let steps :=
    TargetEmitterControllerOutputTrace.comparePathSteps
        capacity runtime.scratch + itemSteps
  refine ⟨steps, finalTape, ?_, finalRepresents, ?_⟩
  · exact
      AcceptPath.trans graph (.node outputCompareRef)
        (.node outputItemRef) (.node outputCompareRef)
        (TargetEmitterControllerOutputTrace.comparePathSteps
          capacity runtime.scratch)
        itemSteps initialTape itemTape finalTape comparePath itemPath
  · unfold steps
    omega

/-- Bounded form of the complete represented output loop. -/
theorem outputLoopToAccept_path_bounded
    (capacity : Nat) (source : List WorkSymbol)
    (context : SourceContext source)
    (layout : CursorLayout source)
    (remaining : Nat)
    (runtime : Runtime) (initialTape : WorkTape)
    (fits : LedgerFits capacity runtime.registers)
    (baseline :
      runtime.registers.baseline =
        runtime.scratch + remaining)
    (finishRoom : runtime.registers.baseline + 3 < capacity)
    (represents :
      TapeRepresents outputCompareRef.startState
        capacity runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node outputCompareRef) .accept
        steps initialTape finalTape ∧
      FinalTapeRepresents capacity
        (TargetEmitterControllerOutputTrace.outputLoopResult
          remaining runtime).scratch
        (TargetEmitterControllerOutputTrace.outputLoopResult
          remaining runtime).registers
        (TargetEmitterControllerOutputTrace.outputLoopResult
          remaining runtime).checks source
        (TargetEmitterControllerOutputTrace.outputLoopResult
          remaining runtime).targetTokens finalTape ∧
      steps ≤ outputLoopEnvelope capacity source remaining runtime := by
  induction remaining generalizing runtime initialTape with
  | zero =>
      have equal :
          runtime.scratch = runtime.registers.baseline := by
        omega
      have room : runtime.scratch + 3 < capacity := by
        omega
      simpa [outputLoopEnvelope,
        TargetEmitterControllerOutputTrace.outputLoopResult] using
        (compareMatchToAccept_path_bounded capacity source context
          layout runtime initialTape fits equal room represents)
  | succ remaining inductionHypothesis =>
      have less :
          runtime.scratch < runtime.registers.baseline := by
        omega
      rcases
          compareMismatchItem_path_bounded capacity source context
            layout runtime initialTape fits less represents with
        ⟨itemSteps, itemTape, itemPath, itemRepresents, itemBound⟩
      have nextFits :
          LedgerFits capacity
            (outputLoopItemResult runtime).registers := by
        simpa [outputLoopItemResult] using fits
      have nextBaseline :
          (outputLoopItemResult runtime).registers.baseline =
            (outputLoopItemResult runtime).scratch + remaining := by
        simp [outputLoopItemResult]
        omega
      have nextRoom :
          (outputLoopItemResult runtime).registers.baseline + 3 <
            capacity := by
        simpa [outputLoopItemResult] using finishRoom
      rcases
          inductionHypothesis (outputLoopItemResult runtime)
            itemTape nextFits nextBaseline nextRoom itemRepresents with
        ⟨tailSteps, finalTape, tailPath,
          finalRepresents, tailBound⟩
      let steps := itemSteps + tailSteps
      refine ⟨steps, finalTape, ?_, ?_, ?_⟩
      · exact
          AcceptPath.trans graph (.node outputCompareRef)
            (.node outputCompareRef) .accept
            itemSteps tailSteps initialTape itemTape finalTape
            itemPath tailPath
      · simpa [TargetEmitterControllerOutputTrace.outputLoopResult] using
          finalRepresents
      · unfold steps
        simp only [outputLoopEnvelope]
        omega

/-- Complete begin-output suffix with its constructive recursive envelope. -/
theorem outputPhaseToAccept_path_bounded
    (capacity : Nat) (source : List WorkSymbol)
    (context : SourceContext source)
    (layout : CursorLayout source)
    (runtime : Runtime) (initialTape : WorkTape)
    (fits : LedgerFits capacity runtime.registers)
    (scratchBound : runtime.scratch < capacity)
    (finishRoom : runtime.registers.baseline + 3 < capacity)
    (represents :
      TapeRepresents beginOutputRef.startState
        capacity runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node beginOutputRef) .accept
        steps initialTape finalTape ∧
      FinalTapeRepresents capacity
        (TargetEmitterControllerOutputTrace.outputLoopResult
          runtime.registers.baseline
          (beginOutputResult runtime)).scratch
        (TargetEmitterControllerOutputTrace.outputLoopResult
          runtime.registers.baseline
          (beginOutputResult runtime)).registers
        (TargetEmitterControllerOutputTrace.outputLoopResult
          runtime.registers.baseline
          (beginOutputResult runtime)).checks source
        (TargetEmitterControllerOutputTrace.outputLoopResult
          runtime.registers.baseline
          (beginOutputResult runtime)).targetTokens finalTape ∧
      steps ≤ outputPhaseEnvelope capacity source runtime := by
  rcases
      beginBlock_path_bounded capacity source context layout runtime
        initialTape scratchBound represents with
    ⟨beginSteps, compareTape, beginPath,
      compareRepresents, beginBound⟩
  have beginFits :
      LedgerFits capacity (beginOutputResult runtime).registers := by
    simpa [beginOutputResult] using fits
  have baseline :
      (beginOutputResult runtime).registers.baseline =
        (beginOutputResult runtime).scratch +
          runtime.registers.baseline := by
    simp [beginOutputResult]
  have room :
      (beginOutputResult runtime).registers.baseline + 3 <
        capacity := by
    simpa [beginOutputResult] using finishRoom
  rcases
      outputLoopToAccept_path_bounded capacity source context layout
        runtime.registers.baseline (beginOutputResult runtime)
        compareTape beginFits baseline room compareRepresents with
    ⟨loopSteps, finalTape, loopPath,
      finalRepresents, loopBound⟩
  let steps := beginSteps + loopSteps
  refine ⟨steps, finalTape, ?_, finalRepresents, ?_⟩
  · exact
      AcceptPath.trans graph (.node beginOutputRef)
        (.node outputCompareRef) .accept
        beginSteps loopSteps initialTape compareTape finalTape
        beginPath loopPath
  · unfold steps outputPhaseEnvelope
    omega

/-! ### Non-recursive domination -/

private theorem encodeNatTokens_length (value : Nat) :
    (encodeNatTokens value).length = value + 1 := by
  induction value with
  | zero =>
      rfl
  | succ value inductionHypothesis =>
      simp [encodeNatTokens, inductionHypothesis]

private theorem programEnvelope_le_outputBlockUnit
    (capacity : Nat) (source : List WorkSymbol)
    (origin current : Runtime)
    (primitives : List TargetEmitterPlan.Primitive)
    (programLength : primitives.length ≤ 11)
    (targetBound :
      current.targetTokens.length ≤
        outputTargetLimit capacity origin)
    (checksEq : current.checks = origin.checks) :
    TargetEmitterRuntimeProgramBound.programWorkEnvelope
        capacity source current primitives ≤
      outputBlockUnit capacity source origin := by
  have footprintBound :
      TargetEmitterRuntimeProgramBound.runtimeFootprint
          capacity source current primitives.length ≤
        outputMasterSize capacity source origin := by
    unfold TargetEmitterRuntimeProgramBound.runtimeFootprint
      outputMasterSize
    rw [checksEq]
    have reserved :
        primitives.length * (3 * capacity + 3) ≤
          11 * (3 * capacity + 3) :=
      Nat.mul_le_mul_right (3 * capacity + 3) programLength
    omega
  have squareBound :
      TargetEmitterRuntimeProgramBound.runtimeFootprint
            capacity source current primitives.length *
          TargetEmitterRuntimeProgramBound.runtimeFootprint
            capacity source current primitives.length ≤
        outputMasterSize capacity source origin *
          outputMasterSize capacity source origin :=
    Nat.mul_le_mul footprintBound footprintBound
  have primitiveBound :
      TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
            (TargetEmitterRuntimeProgramBound.runtimeFootprint
              capacity source current primitives.length) + 1 ≤
        TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
            (outputMasterSize capacity source origin) + 1 := by
    unfold TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_left 100 squareBound) 101
  have totalBound :=
    Nat.mul_le_mul programLength primitiveBound
  simpa [TargetEmitterRuntimeProgramBound.programWorkEnvelope,
    outputBlockUnit] using totalBound

private theorem beginBlockEnvelope_le_outputBlockUnit
    (capacity : Nat) (source : List WorkSymbol)
    (runtime : Runtime) :
    beginBlockEnvelope capacity source runtime ≤
      outputBlockUnit capacity source runtime := by
  apply programEnvelope_le_outputBlockUnit
  · decide
  · unfold outputTargetLimit
    omega
  · rfl

private theorem itemBlockEnvelope_le_outputBlockUnit
    (capacity : Nat) (source : List WorkSymbol)
    (origin runtime : Runtime)
    (targetBound :
      runtime.targetTokens.length ≤
        outputTargetLimit capacity origin)
    (checksEq : runtime.checks = origin.checks) :
    itemBlockEnvelope capacity source runtime ≤
      outputBlockUnit capacity source origin := by
  apply programEnvelope_le_outputBlockUnit
  · decide
  · exact targetBound
  · exact checksEq

private theorem finishBlockEnvelope_le_outputBlockUnit
    (capacity : Nat) (source : List WorkSymbol)
    (origin runtime : Runtime)
    (targetBound :
      runtime.targetTokens.length ≤
        outputTargetLimit capacity origin)
    (checksEq : runtime.checks = origin.checks) :
    finishBlockEnvelope capacity source runtime ≤
      outputBlockUnit capacity source origin := by
  apply programEnvelope_le_outputBlockUnit
  · decide
  · exact targetBound
  · exact checksEq

private theorem comparePathSteps_le_outputCompareUnit
    (capacity scratch : Nat) (scratchBound : scratch ≤ capacity) :
    TargetEmitterControllerOutputTrace.comparePathSteps
        capacity scratch ≤
      outputCompareUnit capacity := by
  have workBound :=
    TargetEmitterScratchCompareSlot.workSteps_le_polynomialWorkBound
      .baseline capacity scratch
  apply Nat.le_trans (Nat.add_le_add_right workBound 1)
  have factorBound :
      TargetEmitterScratchCompareSlot.polynomialWorkBound
            capacity scratch + 1 ≤
        (scratch + 1) * (14 * capacity + 36) := by
    unfold TargetEmitterScratchCompareSlot.polynomialWorkBound
    simp only [Nat.mul_add, Nat.add_mul]
    omega
  have leftFactor : scratch + 1 ≤ capacity + 1 :=
    Nat.add_le_add_right scratchBound 1
  have rightFactor :
      14 * capacity + 36 ≤ 50 * (capacity + 1) := by
    omega
  calc
    TargetEmitterScratchCompareSlot.polynomialWorkBound
          capacity scratch + 1 ≤
        (scratch + 1) * (14 * capacity + 36) :=
      factorBound
    _ ≤ (capacity + 1) * (50 * (capacity + 1)) :=
      Nat.mul_le_mul leftFactor rightFactor
    _ = outputCompareUnit capacity := by
      simp [outputCompareUnit, Nat.mul_comm]

private theorem outputLoopEnvelope_le_uniformAux
    (capacity : Nat) (source : List WorkSymbol)
    (origin : Runtime) (remaining : Nat) (runtime : Runtime)
    (baselineBound :
      runtime.registers.baseline ≤ capacity)
    (position :
      runtime.scratch + remaining =
        runtime.registers.baseline)
    (checksEq : runtime.checks = origin.checks)
    (targetBudget :
      runtime.targetTokens.length +
          remaining * (capacity + 2) ≤
        outputTargetLimit capacity origin) :
    outputLoopEnvelope capacity source remaining runtime ≤
      (remaining + 1) *
          (outputCompareUnit capacity +
            outputBlockUnit capacity source origin) +
        TargetEmitterControllerOutputTrace.finalizerPathSteps source := by
  induction remaining generalizing runtime with
  | zero =>
      have scratchBound : runtime.scratch ≤ capacity := by
        omega
      have compareBound :=
        comparePathSteps_le_outputCompareUnit
          capacity runtime.scratch scratchBound
      have currentTarget :
          runtime.targetTokens.length ≤
            outputTargetLimit capacity origin := by
        simpa using targetBudget
      have finishBound :=
        finishBlockEnvelope_le_outputBlockUnit
          capacity source origin runtime currentTarget checksEq
      simp only [outputLoopEnvelope]
      omega
  | succ remaining inductionHypothesis =>
      have scratchBound : runtime.scratch ≤ capacity := by
        omega
      have compareBound :=
        comparePathSteps_le_outputCompareUnit
          capacity runtime.scratch scratchBound
      have currentTarget :
          runtime.targetTokens.length ≤
            outputTargetLimit capacity origin := by
        exact Nat.le_trans
          (Nat.le_add_right runtime.targetTokens.length
            ((remaining + 1) * (capacity + 2)))
          targetBudget
      have itemBound :=
        itemBlockEnvelope_le_outputBlockUnit
          capacity source origin runtime currentTarget checksEq
      have nextBaseline :
          (outputLoopItemResult runtime).registers.baseline ≤
            capacity := by
        simpa [outputLoopItemResult] using baselineBound
      have nextPosition :
          (outputLoopItemResult runtime).scratch + remaining =
            (outputLoopItemResult runtime).registers.baseline := by
        simp [outputLoopItemResult]
        omega
      have nextChecks :
          (outputLoopItemResult runtime).checks =
            origin.checks := by
        simpa [outputLoopItemResult] using checksEq
      have itemTargetLength :
          (outputLoopItemResult runtime).targetTokens.length =
            runtime.targetTokens.length + runtime.scratch + 2 := by
        simp [outputLoopItemResult, encodeSourceTokens,
          encodeNatTokens_length]
        omega
      have nextTargetBudget :
          (outputLoopItemResult runtime).targetTokens.length +
                remaining * (capacity + 2) ≤
            outputTargetLimit capacity origin := by
        rw [itemTargetLength]
        rw [Nat.succ_mul] at targetBudget
        omega
      have tailBound :=
        inductionHypothesis
          (outputLoopItemResult runtime)
          nextBaseline nextPosition nextChecks nextTargetBudget
      simp only [outputLoopEnvelope]
      rw [Nat.succ_mul]
      omega

/-- The recursive output envelope is dominated by one closed expression in
the initial runtime, capacity, and retained-source length. -/
theorem outputPhaseEnvelope_le_uniform
    (capacity : Nat) (source : List WorkSymbol)
    (runtime : Runtime)
    (baselineBound : runtime.registers.baseline ≤ capacity) :
    outputPhaseEnvelope capacity source runtime ≤
      outputUniformEnvelope capacity source runtime := by
  have beginBound :=
    beginBlockEnvelope_le_outputBlockUnit
      capacity source runtime
  have loopBaseline :
      (beginOutputResult runtime).registers.baseline ≤ capacity := by
    simpa [beginOutputResult] using baselineBound
  have loopPosition :
      (beginOutputResult runtime).scratch +
          runtime.registers.baseline =
        (beginOutputResult runtime).registers.baseline := by
    simp [beginOutputResult]
  have loopChecks :
      (beginOutputResult runtime).checks = runtime.checks := by
    rfl
  have baselineProduct :
      runtime.registers.baseline * (capacity + 2) ≤
        capacity * (capacity + 2) :=
    Nat.mul_le_mul_right (capacity + 2) baselineBound
  have loopTargetBudget :
      (beginOutputResult runtime).targetTokens.length +
            runtime.registers.baseline * (capacity + 2) ≤
        outputTargetLimit capacity runtime := by
    simp only [beginOutputResult, List.length_append,
      List.length_cons, List.length_nil, outputTargetLimit]
    omega
  have loopBound :=
    outputLoopEnvelope_le_uniformAux
      capacity source runtime runtime.registers.baseline
      (beginOutputResult runtime) loopBaseline loopPosition
      loopChecks loopTargetBudget
  unfold outputPhaseEnvelope outputUniformEnvelope
  omega

end PNP.Concrete.LockedNAND.TargetEmitterControllerOutputBound
