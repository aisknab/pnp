/-
Copyright (c) 2026 PNP Labs.

Exact graph paths for the output comparison loop and terminal cleanup of the
fixed grammar-only locked-NAND target emitter.

The executable controller contains only literal primitive tables and fixed
graph bridges.  The relations in this file are proof-only witnesses that
compose those tables; no runtime schedule, decoded target, or caller-supplied
execution certificate is embedded in the machine.
-/

import PNP.Concrete.LockedNANDTargetEmitterControllerTrace
import PNP.Concrete.LockedNANDTargetEmitterRuntimeProgram

namespace PNP.Concrete.LockedNAND.TargetEmitterControllerOutputTrace

open PNP.Concrete
open WorkMachineProgramGraph
open WorkMachineProgramPath
open TargetEmitterController
open TargetEmitterPrimitiveCompiler
open TargetEmitterBlockCompiler
open TargetEmitterProgramSemantics
open TargetEmitterRuntimeProgram

abbrev Runtime := TargetEmitterProgramSemantics.Runtime
abbrev CursorLayout := TargetEmitterRuntimeProgram.CursorLayout
abbrev LedgerFits := TargetEmitterRuntimeProgram.LedgerFits

def TapeRepresents (state capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (source : List WorkSymbol)
    (target : List Token) (tape : WorkTape) : Prop :=
  TargetEmitterRuntime.Represents state capacity scratch
    registers checks source target
    { state := state, tape := tape }

def FinalTapeRepresents (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (source : List WorkSymbol)
    (target : List Token) (tape : WorkTape) : Prop :=
  WorkTape.BlankEquivalent tape
    (TargetEmitterCursorFinalizer.finalTape source
      (SourceParser.packedTokenCells target)
      (TargetEmitterRuntimePrimitives.fixedWorkspace
        capacity scratch registers checks)
      [])

def compareWorkSteps (capacity scratch : Nat) : Nat :=
  TargetEmitterScratchCompareSlot.workSteps
    .baseline capacity scratch

def comparePathSteps (capacity scratch : Nat) : Nat :=
  compareWorkSteps capacity scratch + 1

def finalizerPathSteps (source : List WorkSymbol) : Nat :=
  TargetEmitterCursorFinalizer.workSteps source + 1

private def programEntryState (fallback : Nat) :
    List WorkMachine → Nat
  | [] => fallback
  | program :: _ => program.startState

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

private theorem configuration_eq_of_state
    {configuration : WorkConfiguration} {state : Nat}
    (stateEq : configuration.state = state) :
    configuration =
      { state := state, tape := configuration.tape } := by
  cases configuration with
  | mk actualState tape =>
      simp only at stateEq
      subst actualState
      rfl

private theorem programSafe_linearAcceptRuns
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    {primitives : List TargetEmitterPlan.Primitive}
    {initial final : Runtime}
    (safe :
      ProgramSafe capacity source context
        primitives initial final) :
    ∀ {programs : List WorkMachine},
      compileProgram primitives = some programs →
      ∀ (fallback : Nat) (actual : WorkConfiguration),
        TargetEmitterRuntime.Represents
            (programEntryState fallback programs)
            capacity initial.scratch initial.registers initial.checks
            source initial.targetTokens actual →
        ∃ steps actualFinal,
          LinearAcceptRuns programs steps
            actual.tape actualFinal.tape ∧
          TargetEmitterRuntime.Represents actualFinal.state
            capacity final.scratch final.registers final.checks
            source final.targetTokens actualFinal := by
  induction safe with
  | nil runtime =>
      intro programs compiled fallback actual represents
      change some [] = some programs at compiled
      have programsEq : programs = [] :=
        (Option.some.inj compiled).symm
      subst programs
      have finalRepresents :
          TargetEmitterRuntime.Represents actual.state
            capacity runtime.scratch runtime.registers runtime.checks
            source runtime.targetTokens actual := by
        have stateEq :
            actual.state = fallback :=
          TargetEmitterRuntime.Represents.state_eq represents
        simpa [programEntryState, stateEq] using represents
      exact
        ⟨0, actual, LinearAcceptRuns.terminal actual.tape,
          finalRepresents⟩
  | cons primitive rest initial middle final head tail ih =>
      intro programs compiled fallback actual represents
      cases machineEq : primitiveMachine primitive with
      | none =>
          simp [compileProgram, machineEq] at compiled
      | some program =>
          cases tailEq : compileProgram rest with
          | none =>
              simp [compileProgram, machineEq, tailEq] at compiled
          | some tailPrograms =>
              simp only [compileProgram_cons, machineEq, tailEq] at compiled
              have programsEq :
                  programs = program :: tailPrograms := by
                exact (Option.some.inj compiled).symm
              subst programs
              have inputRepresents :
                  TargetEmitterRuntime.Represents program.startState
                    capacity initial.scratch initial.registers
                    initial.checks source initial.targetTokens actual := by
                simpa [programEntryState] using represents
              rcases head.exact program machineEq actual
                  inputRepresents with
                ⟨localSteps, actualMiddle, localRun,
                  middleRepresents⟩
              let tailInitial : WorkConfiguration :=
                { state :=
                    programEntryState program.acceptState tailPrograms
                  tape := actualMiddle.tape }
              have tailRepresents :
                  TargetEmitterRuntime.Represents
                    (programEntryState program.acceptState tailPrograms)
                    capacity middle.scratch middle.registers middle.checks
                    source middle.targetTokens tailInitial := by
                exact represents_at_state middleRepresents
              rcases ih tailEq program.acceptState tailInitial
                  tailRepresents with
                ⟨tailSteps, actualFinal, tailRuns,
                  finalRepresents⟩
              have actualState :
                  actual.state = program.startState :=
                TargetEmitterRuntime.Represents.state_eq inputRepresents
              have middleState :
                  actualMiddle.state = program.acceptState :=
                TargetEmitterRuntime.Represents.state_eq middleRepresents
              have localRun' :
                  workRunExact? program localSteps
                      { state := program.startState,
                        tape := actual.tape } =
                    some
                      { state := program.acceptState,
                        tape := actualMiddle.tape } := by
                rw [configuration_eq_of_state actualState] at localRun
                rw [configuration_eq_of_state middleState] at localRun
                exact localRun
              refine
                ⟨localSteps + 1 + tailSteps, actualFinal, ?_,
                  finalRepresents⟩
              exact LinearAcceptRuns.step program tailPrograms
                localSteps tailSteps actual.tape actualMiddle.tape
                actualFinal.tape localRun' tailRuns

private theorem block_path_of_safe
    (descriptor : BlockDescriptor)
    (descriptorMember : descriptor ∈ blockDescriptors)
    (programs : List WorkMachine)
    (compiled :
      compileProgram descriptor.primitives = some programs)
    (programsNonempty : programs ≠ [])
    {capacity : Nat} {source : List WorkSymbol}
    {context : SourceContext source}
    {initial final : Runtime}
    (safe :
      ProgramSafe capacity source context
        descriptor.primitives initial final)
    (continuationState : Nat)
    (initialTape : WorkTape)
    (represents :
      TapeRepresents (programEntryState 0 programs)
        capacity initial.scratch initial.registers initial.checks
        source initial.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph
          (.node
            (blockEntry descriptor.code descriptor.primitives))
          descriptor.continuation steps initialTape finalTape ∧
      TapeRepresents continuationState
        capacity final.scratch final.registers final.checks
        source final.targetTokens finalTape := by
  rcases
      programSafe_linearAcceptRuns safe compiled 0
        { state := programEntryState 0 programs,
          tape := initialTape }
        represents with
    ⟨steps, actualFinal, runs, finalRepresents⟩
  have path :=
    descriptor_acceptPath_of_compiled descriptor descriptorMember
      programs compiled programsNonempty steps initialTape
      actualFinal.tape runs
  refine ⟨steps, actualFinal.tape, path, ?_⟩
  exact represents_at_state finalRepresents

private theorem localAcceptRun_of_exact
    (node : Node) (steps : Nat)
    (initial final : WorkConfiguration)
    (initialState :
      initial.state = node.program.startState)
    (finalState :
      final.state = node.program.acceptState)
    (exactRun :
      workRunExact? node.program steps initial = some final) :
    LocalAcceptRun node steps initial.tape final.tape := by
  rcases initial with ⟨initialStateValue, initialTape⟩
  rcases final with ⟨finalStateValue, finalTape⟩
  change initialStateValue = node.program.startState at initialState
  change finalStateValue = node.program.acceptState at finalState
  subst initialStateValue
  subst finalStateValue
  exact exactRun

private theorem localRejectRun_of_exact
    (node : Node) (steps : Nat)
    (initial final : WorkConfiguration)
    (initialState :
      initial.state = node.program.startState)
    (finalState :
      final.state = node.program.rejectState)
    (exactRun :
      workRunExact? node.program steps initial = some final) :
    LocalRejectRun node steps initial.tape final.tape := by
  rcases initial with ⟨initialStateValue, initialTape⟩
  rcases final with ⟨finalStateValue, finalTape⟩
  change initialStateValue = node.program.startState at initialState
  change finalStateValue = node.program.rejectState at finalState
  subst initialStateValue
  subst finalStateValue
  exact exactRun

private theorem outputCompareNode_member :
    outputCompareNode ∈ graph.nodes := by
  apply controlNode_member_nodes
  simp [controlNodes]

private theorem finalizerNode_member :
    finalizerNode ∈ graph.nodes := by
  apply controlNode_member_nodes
  simp [controlNodes]

/-! ### Safe fixed output blocks -/

private theorem beginOutput_safe
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

private theorem outputItem_safe
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

private theorem outputFinish_safe
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

private def beginOutputDescriptor : BlockDescriptor :=
  { code := Block.beginOutput
    primitives := Plan.beginOutput
    continuation := .node outputCompareRef }

private def outputItemDescriptor : BlockDescriptor :=
  { code := Block.outputItem
    primitives := Plan.outputItem
    continuation := .node outputCompareRef }

private def outputFinishDescriptor : BlockDescriptor :=
  { code := Block.outputFinish
    primitives := Plan.outputFinish
    continuation := .node finalizerRef }

private def beginOutputPrograms : List WorkMachine :=
  [ TargetEmitterCursorAppender.machineFor .programEnd
  , TargetEmitterScratchReset.machine
  ]

private def outputItemPrograms : List WorkMachine :=
  [ TargetEmitterCursorAppender.machineFor .gate
  , TargetEmitterCursorNatLoop.machine
  , TargetEmitterScratchIncrement.machine
  ]

private def outputFinishPrograms : List WorkMachine :=
  [ TargetEmitterScratchIncrement.machine
  , TargetEmitterScratchIncrement.machine
  , TargetEmitterScratchIncrement.machine
  , TargetEmitterCursorAppender.machineFor .gate
  , TargetEmitterCursorNatLoop.machine
  , TargetEmitterCursorAppender.machineFor .outputsEnd
  , TargetEmitterScratchReset.machine
  , TargetEmitterScratchAddSlot.machineFor .baseline
  , TargetEmitterCursorAppender.machineFor .threshold
  , TargetEmitterCursorNatLoop.machine
  , TargetEmitterCursorAppender.machineFor .instanceEnd
  ]

private theorem beginOutputDescriptor_member :
    beginOutputDescriptor ∈ blockDescriptors := by
  simp [beginOutputDescriptor, blockDescriptors,
    fixedBlockDescriptors]

private theorem outputItemDescriptor_member :
    outputItemDescriptor ∈ blockDescriptors := by
  simp [outputItemDescriptor, blockDescriptors,
    fixedBlockDescriptors]

private theorem outputFinishDescriptor_member :
    outputFinishDescriptor ∈ blockDescriptors := by
  simp [outputFinishDescriptor, blockDescriptors,
    fixedBlockDescriptors]

private theorem beginOutput_compiled :
    compileProgram Plan.beginOutput = some beginOutputPrograms := by
  rfl

private theorem outputItem_compiled :
    compileProgram Plan.outputItem = some outputItemPrograms := by
  rfl

private theorem outputFinish_compiled :
    compileProgram Plan.outputFinish = some outputFinishPrograms := by
  rfl

/-- Append `programEnd`, reset scratch, and follow every literal bridge in the
fixed begin-output block to the comparison node. -/
theorem beginOutput_path
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
        (beginOutputResult runtime).targetTokens finalTape := by
  have inputRepresents :
      TapeRepresents (programEntryState 0 beginOutputPrograms)
        capacity runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape := by
    simpa [beginOutputPrograms, programEntryState,
      beginOutputRef, blockEntry, blockEntry?, blockMachines,
      beginOutput_compiled, entryRef?, machineRef] using represents
  rcases
      block_path_of_safe beginOutputDescriptor
        beginOutputDescriptor_member beginOutputPrograms
        (by simpa [beginOutputDescriptor] using beginOutput_compiled)
        (by simp [beginOutputPrograms])
        (beginOutput_safe context layout runtime scratchBound)
        outputCompareRef.startState initialTape inputRepresents with
    ⟨steps, finalTape, path, finalRepresents⟩
  exact
    ⟨steps, finalTape,
      by simpa [beginOutputDescriptor, beginOutputRef],
      finalRepresents⟩

/-- Emit one gate coordinate, increment scratch, and follow every literal
bridge in the fixed output-item block back to the comparison node. -/
theorem outputItem_path
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
        (outputLoopItemResult runtime).targetTokens finalTape := by
  have inputRepresents :
      TapeRepresents (programEntryState 0 outputItemPrograms)
        capacity runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape := by
    simpa [outputItemPrograms, programEntryState,
      outputItemRef, blockEntry, blockEntry?, blockMachines,
      outputItem_compiled, entryRef?, machineRef] using represents
  rcases
      block_path_of_safe outputItemDescriptor
        outputItemDescriptor_member outputItemPrograms
        (by simpa [outputItemDescriptor] using outputItem_compiled)
        (by simp [outputItemPrograms])
        (outputItem_safe context layout runtime scratchBound)
        outputCompareRef.startState initialTape inputRepresents with
    ⟨steps, finalTape, path, finalRepresents⟩
  exact
    ⟨steps, finalTape,
      by simpa [outputItemDescriptor, outputItemRef],
      finalRepresents⟩

/-- Serialize the final output gate, threshold, and instance terminator, then
follow every literal bridge in the fixed finish block to terminal cleanup. -/
theorem outputFinish_path
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
        (outputLoopFinishResult runtime).targetTokens finalTape := by
  have inputRepresents :
      TapeRepresents (programEntryState 0 outputFinishPrograms)
        capacity runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape := by
    simpa [outputFinishPrograms, programEntryState,
      outputFinishRef, blockEntry, blockEntry?, blockMachines,
      outputFinish_compiled, entryRef?, machineRef] using represents
  rcases
      block_path_of_safe outputFinishDescriptor
        outputFinishDescriptor_member outputFinishPrograms
        (by simpa [outputFinishDescriptor] using outputFinish_compiled)
        (by simp [outputFinishPrograms])
        (outputFinish_safe context layout runtime fits room)
        finalizerRef.startState initialTape inputRepresents with
    ⟨steps, finalTape, path, finalRepresents⟩
  exact
    ⟨steps, finalTape,
      by simpa [outputFinishDescriptor, outputFinishRef],
      finalRepresents⟩

/-! ### Literal comparison branches -/

/-- A matching output index follows the comparison node's fixed accept bridge
to the output-finish block.  The complete logical workspace is unchanged. -/
theorem compareMatch_path
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (source : List WorkSymbol)
    (context : SourceContext source)
    (target : List Token) (initialTape : WorkTape)
    (fits : LedgerFits capacity registers)
    (equal : scratch = registers.baseline)
    (represents :
      TapeRepresents outputCompareRef.startState
        capacity scratch registers checks source target initialTape) :
    ∃ finalTape,
      AcceptPath graph (.node outputCompareRef)
          (.node outputFinishRef)
          (comparePathSteps capacity scratch)
          initialTape finalTape ∧
      TapeRepresents outputFinishRef.startState
        capacity scratch registers checks source target finalTape := by
  let initial : WorkConfiguration :=
    { state := outputCompareRef.startState, tape := initialTape }
  have inputRepresents :
      TargetEmitterRuntime.Represents
        (TargetEmitterScratchCompareSlot.startState .baseline)
        capacity scratch registers checks
        (context.head :: context.tail) target initial := by
    simpa [TapeRepresents, initial, outputCompareRef, controlRef,
      TargetEmitterScratchCompareSlot.machineFor,
      context.source_eq] using represents
  rcases
      TargetEmitterRuntimePrimitives.compareRegisterEqual_exact
        .baseline capacity scratch registers checks
        context.head context.tail target initial
        fits.toPrimitive
        (by
          simpa [TargetEmitterLedger.slotValue] using equal)
        context.compareAllowed inputRepresents with
    ⟨actualFinal, exactRun, finalRepresents⟩
  have localRun :
      LocalAcceptRun outputCompareNode
        (compareWorkSteps capacity scratch)
        initialTape actualFinal.tape := by
    apply localAcceptRun_of_exact outputCompareNode
      (compareWorkSteps capacity scratch) initial actualFinal
    · rfl
    · simpa [outputCompareNode, controlNode,
        TargetEmitterScratchCompareSlot.machineFor] using
        TargetEmitterRuntime.Represents.state_eq finalRepresents
    · simpa [outputCompareNode, controlNode,
        TargetEmitterScratchCompareSlot.machineFor,
        compareWorkSteps] using exactRun
  have tail :
      AcceptPath graph (.node outputFinishRef) (.node outputFinishRef)
        0 actualFinal.tape actualFinal.tape :=
    AcceptPath.terminal _ _
  have path :=
    AcceptPath.step outputCompareNode (.node outputFinishRef)
      (compareWorkSteps capacity scratch) 0
      initialTape actualFinal.tape actualFinal.tape
      outputCompareNode_member localRun
      (by simpa [outputCompareNode, controlNode] using tail)
  have finalRepresents' :
      TargetEmitterRuntime.Represents
        TargetEmitterScratchCompareSlot.acceptState
        capacity scratch registers checks source target actualFinal := by
    simpa only [context.source_eq] using finalRepresents
  refine ⟨actualFinal.tape, ?_, ?_⟩
  · simpa [comparePathSteps, outputCompareRef, outputCompareNode,
      controlRef, controlNode, Node.reference] using path
  · exact represents_at_state finalRepresents'

/-- A strictly smaller output index follows the comparison node's fixed reject
bridge to the one-item output block.  The complete logical workspace is
unchanged. -/
theorem compareMismatch_path
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (source : List WorkSymbol)
    (context : SourceContext source)
    (target : List Token) (initialTape : WorkTape)
    (fits : LedgerFits capacity registers)
    (less : scratch < registers.baseline)
    (represents :
      TapeRepresents outputCompareRef.startState
        capacity scratch registers checks source target initialTape) :
    ∃ finalTape,
      AcceptPath graph (.node outputCompareRef)
          (.node outputItemRef)
          (comparePathSteps capacity scratch)
          initialTape finalTape ∧
      TapeRepresents outputItemRef.startState
        capacity scratch registers checks source target finalTape := by
  let initial : WorkConfiguration :=
    { state := outputCompareRef.startState, tape := initialTape }
  have inputRepresents :
      TargetEmitterRuntime.Represents
        (TargetEmitterScratchCompareSlot.startState .baseline)
        capacity scratch registers checks
        (context.head :: context.tail) target initial := by
    simpa [TapeRepresents, initial, outputCompareRef, controlRef,
      TargetEmitterScratchCompareSlot.machineFor,
      context.source_eq] using represents
  rcases
      TargetEmitterRuntimePrimitives.compareRegisterLess_exact
        .baseline capacity scratch registers checks
        context.head context.tail target initial
        fits.toPrimitive
        (by
          simpa [TargetEmitterLedger.slotValue] using less)
        context.compareAllowed inputRepresents with
    ⟨actualFinal, exactRun, finalRepresents⟩
  have localRun :
      LocalRejectRun outputCompareNode
        (compareWorkSteps capacity scratch)
        initialTape actualFinal.tape := by
    apply localRejectRun_of_exact outputCompareNode
      (compareWorkSteps capacity scratch) initial actualFinal
    · rfl
    · simpa [outputCompareNode, controlNode,
        TargetEmitterScratchCompareSlot.machineFor] using
        TargetEmitterRuntime.Represents.state_eq finalRepresents
    · simpa [outputCompareNode, controlNode,
        TargetEmitterScratchCompareSlot.machineFor,
        compareWorkSteps] using exactRun
  have tail :
      AcceptPath graph (.node outputItemRef) (.node outputItemRef)
        0 actualFinal.tape actualFinal.tape :=
    AcceptPath.terminal _ _
  have path :=
    AcceptPath.stepReject outputCompareNode (.node outputItemRef)
      (compareWorkSteps capacity scratch) 0
      initialTape actualFinal.tape actualFinal.tape
      outputCompareNode_member localRun
      (by simpa [outputCompareNode, controlNode] using tail)
  have finalRepresents' :
      TargetEmitterRuntime.Represents
        TargetEmitterScratchCompareSlot.rejectState
        capacity scratch registers checks source target actualFinal := by
    simpa only [context.source_eq] using finalRepresents
  refine ⟨actualFinal.tape, ?_, ?_⟩
  · simpa [comparePathSteps, outputCompareRef, outputCompareNode,
      controlRef, controlNode, Node.reference] using path
  · exact represents_at_state finalRepresents'

theorem outputZeroComparison_path
    (capacity : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (source : List WorkSymbol)
    (context : SourceContext source)
    (target : List Token) (initialTape : WorkTape)
    (fits : LedgerFits capacity registers)
    (outputZero : registers.baseline = 0)
    (represents :
      TapeRepresents outputCompareRef.startState
        capacity 0 registers checks source target initialTape) :
    ∃ finalTape,
      AcceptPath graph (.node outputCompareRef)
          (.node outputFinishRef)
          (comparePathSteps capacity 0)
          initialTape finalTape ∧
      TapeRepresents outputFinishRef.startState
        capacity 0 registers checks source target finalTape := by
  exact compareMatch_path capacity 0 registers checks source
    context target initialTape fits outputZero.symm represents

theorem outputPositiveComparison_path
    (capacity : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (source : List WorkSymbol)
    (context : SourceContext source)
    (target : List Token) (initialTape : WorkTape)
    (fits : LedgerFits capacity registers)
    (outputPositive : 0 < registers.baseline)
    (represents :
      TapeRepresents outputCompareRef.startState
        capacity 0 registers checks source target initialTape) :
    ∃ finalTape,
      AcceptPath graph (.node outputCompareRef)
          (.node outputItemRef)
          (comparePathSteps capacity 0)
          initialTape finalTape ∧
      TapeRepresents outputItemRef.startState
        capacity 0 registers checks source target finalTape := by
  exact compareMismatch_path capacity 0 registers checks source
    context target initialTape fits outputPositive represents

/-! ### Literal terminal cleanup -/

theorem CursorLayout.finalizerAllowed
    {source : List WorkSymbol}
    (layout : CursorLayout source) :
    ∀ symbol, symbol ∈ source →
      TargetEmitterCursorFinalizer.SourceSymbol symbol := by
  intro symbol member
  rw [layout.cursorSource,
    TargetEmitterCursorAppender.sourceWithCursor] at member
  rcases List.mem_append.mp member with beforeMember | tailMember
  · exact Or.inl (layout.beforePacked symbol beforeMember)
  · rcases List.mem_cons.mp tailMember with marker | afterMember
    · exact Or.inr marker
    · exact Or.inl (layout.afterPacked symbol afterMember)

/-- The cursor-aware finalizer erases exactly the retained source and boundary,
then follows its fixed accept bridge to the graph's global accept endpoint. -/
theorem finalizerAccept_path
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (source : List WorkSymbol)
    (target : List Token) (initialTape : WorkTape)
    (allowed :
      ∀ symbol, symbol ∈ source →
        TargetEmitterCursorFinalizer.SourceSymbol symbol)
    (represents :
      TapeRepresents finalizerRef.startState
        capacity scratch registers checks source target initialTape) :
    ∃ finalTape,
      AcceptPath graph (.node finalizerRef) .accept
          (finalizerPathSteps source) initialTape finalTape ∧
      FinalTapeRepresents capacity scratch registers checks
        source target finalTape := by
  let initial : WorkConfiguration :=
    { state := finalizerRef.startState, tape := initialTape }
  let outsideLeft :=
    TargetEmitterRuntimePrimitives.fixedWorkspace
      capacity scratch registers checks
  let canonicalInput :=
    TargetEmitterCursorFinalizer.inputConfiguration source
      (SourceParser.packedTokenCells target) outsideLeft []
  let canonicalFinal :=
    TargetEmitterCursorFinalizer.finalConfiguration source
      (SourceParser.packedTokenCells target) outsideLeft []
  have actualToLogical :
      WorkConfiguration.BlankEquivalent initial
        (TargetEmitterRuntime.logicalConfiguration
          TargetEmitterCursorFinalizer.eraseState
          capacity scratch registers checks source target) := by
    simpa [TapeRepresents, TargetEmitterRuntime.Represents,
      initial, finalizerRef, controlRef,
      TargetEmitterCursorFinalizer.machine] using represents
  have canonicalToLogical :
      WorkConfiguration.BlankEquivalent canonicalInput
        (TargetEmitterRuntime.logicalConfiguration
          TargetEmitterCursorFinalizer.eraseState
          capacity scratch registers checks source target) := by
    cases source with
    | nil =>
        simpa [canonicalInput,
          TargetEmitterCursorFinalizer.inputConfiguration,
          TargetEmitterCursorFinalizer.configurationAtWord,
          TargetEmitterCursorFinalizer.tapeAtWord,
          TargetEmitter.configAtWord,
          TargetEmitterRuntime.logicalLeftWorkspace,
          TargetEmitterRuntimePrimitives.fixedWorkspace,
          TargetEmitterRuntime.logicalWord, outsideLeft,
          List.append_assoc] using
            (TargetEmitterRuntime.padded_blankEquivalent
              TargetEmitterCursorFinalizer.eraseState
              capacity scratch registers checks [] target 0 1)
    | cons head tail =>
        simpa [canonicalInput,
          TargetEmitterCursorFinalizer.inputConfiguration,
          TargetEmitterCursorFinalizer.configurationAtWord,
          TargetEmitterCursorFinalizer.tapeAtWord,
          TargetEmitter.configAtWord,
          TargetEmitterRuntime.logicalLeftWorkspace,
          TargetEmitterRuntimePrimitives.fixedWorkspace,
          TargetEmitterRuntime.logicalWord, outsideLeft,
          List.append_assoc] using
            (TargetEmitterRuntime.padded_blankEquivalent
              TargetEmitterCursorFinalizer.eraseState
              capacity scratch registers checks
              (head :: tail) target 0 1)
  have inputEquivalent :
      WorkConfiguration.BlankEquivalent initial canonicalInput :=
    WorkConfiguration.blankEquivalent_trans actualToLogical
      (WorkConfiguration.blankEquivalent_symm canonicalToLogical)
  have canonicalRun :
      workRunExact? TargetEmitterCursorFinalizer.machine
          (TargetEmitterCursorFinalizer.workSteps source)
          canonicalInput =
        some canonicalFinal := by
    simpa [canonicalInput, canonicalFinal] using
      (TargetEmitterCursorFinalizer.finalize_exact source
        (SourceParser.packedTokenCells target) outsideLeft [] allowed)
  rcases
      workRunExact?_transport TargetEmitterCursorFinalizer.machine
        (TargetEmitterCursorFinalizer.workSteps source)
        inputEquivalent canonicalRun with
    ⟨actualFinal, exactRun, finalEquivalent⟩
  have localRun :
      LocalAcceptRun finalizerNode
        (TargetEmitterCursorFinalizer.workSteps source)
        initialTape actualFinal.tape := by
    apply localAcceptRun_of_exact finalizerNode
      (TargetEmitterCursorFinalizer.workSteps source)
      initial actualFinal
    · rfl
    · simpa [finalizerNode, controlNode,
        TargetEmitterCursorFinalizer.machine, canonicalFinal,
        TargetEmitterCursorFinalizer.finalConfiguration] using
        finalEquivalent.state
    · simpa [finalizerNode, controlNode] using exactRun
  have tail :
      AcceptPath graph .accept .accept 0
        actualFinal.tape actualFinal.tape :=
    AcceptPath.terminal _ _
  have path :=
    AcceptPath.step finalizerNode .accept
      (TargetEmitterCursorFinalizer.workSteps source) 0
      initialTape actualFinal.tape actualFinal.tape
      finalizerNode_member localRun
      (by simpa [finalizerNode, controlNode] using tail)
  refine ⟨actualFinal.tape, ?_, ?_⟩
  · simpa [finalizerPathSteps, finalizerRef, finalizerNode,
      controlRef, controlNode, Node.reference] using path
  · simpa [FinalTapeRepresents, canonicalFinal,
      TargetEmitterCursorFinalizer.finalConfiguration,
      outsideLeft] using finalEquivalent.tape

/-- A matching comparison, the complete fixed finish block, and terminal
cleanup compose to one exact path to global acceptance. -/
theorem compareMatchToAccept_path
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
        (outputLoopFinishResult runtime).targetTokens finalTape := by
  rcases
      compareMatch_path capacity runtime.scratch runtime.registers
        runtime.checks source context runtime.targetTokens initialTape
        fits equal represents with
    ⟨finishTape, comparePath, finishRepresents⟩
  rcases
      outputFinish_path capacity source context layout runtime
        finishTape fits room finishRepresents with
    ⟨finishSteps, finalizerTape, finishPath,
      finalizerRepresents⟩
  rcases
      finalizerAccept_path capacity
        (outputLoopFinishResult runtime).scratch
        (outputLoopFinishResult runtime).registers
        (outputLoopFinishResult runtime).checks source
        (outputLoopFinishResult runtime).targetTokens
        finalizerTape layout.finalizerAllowed finalizerRepresents with
    ⟨finalTape, finalizerPath, finalRepresents⟩
  have throughFinish :=
    AcceptPath.trans graph (.node outputCompareRef)
      (.node outputFinishRef) (.node finalizerRef)
      (comparePathSteps capacity runtime.scratch) finishSteps
      initialTape finishTape finalizerTape
      comparePath finishPath
  have complete :=
    AcceptPath.trans graph (.node outputCompareRef)
      (.node finalizerRef) .accept
      (comparePathSteps capacity runtime.scratch + finishSteps)
      (finalizerPathSteps source)
      initialTape finalizerTape finalTape
      throughFinish finalizerPath
  exact
    ⟨comparePathSteps capacity runtime.scratch + finishSteps +
        finalizerPathSteps source,
      finalTape, complete, finalRepresents⟩

/-- A smaller comparison, the complete one-item block, and its return bridge
compose to one exact output-loop iteration. -/
theorem compareMismatchItem_path
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
        (outputLoopItemResult runtime).targetTokens finalTape := by
  rcases
      compareMismatch_path capacity runtime.scratch runtime.registers
        runtime.checks source context runtime.targetTokens initialTape
        fits less represents with
    ⟨itemTape, comparePath, itemRepresents⟩
  have scratchBound : runtime.scratch < capacity :=
    Nat.lt_of_lt_of_le less fits.baseline
  rcases
      outputItem_path capacity source context layout runtime itemTape
        scratchBound itemRepresents with
    ⟨itemSteps, finalTape, itemPath, finalRepresents⟩
  exact
    ⟨comparePathSteps capacity runtime.scratch + itemSteps,
      finalTape,
      AcceptPath.trans graph (.node outputCompareRef)
        (.node outputItemRef) (.node outputCompareRef)
        (comparePathSteps capacity runtime.scratch) itemSteps
        initialTape itemTape finalTape comparePath itemPath,
      finalRepresents⟩

def outputLoopResult : Nat → Runtime → Runtime
  | 0, runtime => outputLoopFinishResult runtime
  | remaining + 1, runtime =>
      outputLoopResult remaining (outputLoopItemResult runtime)

/-- Iterate only the controller's already-materialized comparison and item
cycle.  `remaining` is proof-side induction data tied to the physical baseline
register; it is not supplied to the executable graph. -/
theorem outputLoopToAccept_path
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
        (outputLoopResult remaining runtime).scratch
        (outputLoopResult remaining runtime).registers
        (outputLoopResult remaining runtime).checks source
        (outputLoopResult remaining runtime).targetTokens finalTape := by
  induction remaining generalizing runtime initialTape with
  | zero =>
      have equal :
          runtime.scratch = runtime.registers.baseline := by
        omega
      have room : runtime.scratch + 3 < capacity := by
        omega
      simpa [outputLoopResult] using
        (compareMatchToAccept_path capacity source context layout
          runtime initialTape fits equal room represents)
  | succ remaining inductionHypothesis =>
      have less :
          runtime.scratch < runtime.registers.baseline := by
        omega
      rcases
          compareMismatchItem_path capacity source context layout
            runtime initialTape fits less represents with
        ⟨itemSteps, itemTape, itemPath, itemRepresents⟩
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
        ⟨tailSteps, finalTape, tailPath, finalRepresents⟩
      refine
        ⟨itemSteps + tailSteps, finalTape, ?_, ?_⟩
      · exact
          AcceptPath.trans graph (.node outputCompareRef)
            (.node outputCompareRef) .accept
            itemSteps tailSteps initialTape itemTape finalTape
            itemPath tailPath
      · simpa [outputLoopResult] using finalRepresents

/-- Complete the output suffix from the begin-output block for every baseline:
zero takes the match branch immediately; a positive baseline performs exactly
that many item cycles before the same finish and cleanup path. -/
theorem outputPhaseToAccept_path
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
        (outputLoopResult runtime.registers.baseline
          (beginOutputResult runtime)).scratch
        (outputLoopResult runtime.registers.baseline
          (beginOutputResult runtime)).registers
        (outputLoopResult runtime.registers.baseline
          (beginOutputResult runtime)).checks source
        (outputLoopResult runtime.registers.baseline
          (beginOutputResult runtime)).targetTokens finalTape := by
  rcases
      beginOutput_path capacity source context layout runtime
        initialTape scratchBound represents with
    ⟨beginSteps, compareTape, beginPath, compareRepresents⟩
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
      outputLoopToAccept_path capacity source context layout
        runtime.registers.baseline (beginOutputResult runtime)
        compareTape beginFits baseline room compareRepresents with
    ⟨loopSteps, finalTape, loopPath, finalRepresents⟩
  exact
    ⟨beginSteps + loopSteps, finalTape,
      AcceptPath.trans graph (.node beginOutputRef)
        (.node outputCompareRef) .accept
        beginSteps loopSteps initialTape compareTape finalTape
        beginPath loopPath,
      finalRepresents⟩

/-- The zero-output branch begins at the fixed begin-output block and reaches
global acceptance without entering the item loop. -/
theorem outputZeroToAccept_path
    (capacity : Nat) (source : List WorkSymbol)
    (context : SourceContext source)
    (layout : CursorLayout source)
    (runtime : Runtime) (initialTape : WorkTape)
    (fits : LedgerFits capacity runtime.registers)
    (scratchBound : runtime.scratch < capacity)
    (outputZero : runtime.registers.baseline = 0)
    (finishRoom : 3 < capacity)
    (represents :
      TapeRepresents beginOutputRef.startState
        capacity runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node beginOutputRef) .accept
        steps initialTape finalTape ∧
      FinalTapeRepresents capacity
        (outputLoopFinishResult
          (beginOutputResult runtime)).scratch
        (outputLoopFinishResult
          (beginOutputResult runtime)).registers
        (outputLoopFinishResult
          (beginOutputResult runtime)).checks source
        (outputLoopFinishResult
          (beginOutputResult runtime)).targetTokens finalTape := by
  rcases
      beginOutput_path capacity source context layout runtime
        initialTape scratchBound represents with
    ⟨beginSteps, compareTape, beginPath, compareRepresents⟩
  have equal :
      (beginOutputResult runtime).scratch =
        (beginOutputResult runtime).registers.baseline := by
    simp [beginOutputResult, outputZero]
  have room :
      (beginOutputResult runtime).scratch + 3 < capacity := by
    simpa [beginOutputResult] using finishRoom
  rcases
      compareMatchToAccept_path capacity source context layout
        (beginOutputResult runtime) compareTape
        (by simpa [beginOutputResult] using fits)
        equal room compareRepresents with
    ⟨suffixSteps, finalTape, suffixPath, finalRepresents⟩
  exact
    ⟨beginSteps + suffixSteps, finalTape,
      AcceptPath.trans graph (.node beginOutputRef)
        (.node outputCompareRef) .accept
        beginSteps suffixSteps initialTape compareTape finalTape
        beginPath suffixPath,
      finalRepresents⟩

/-- The positive-output branch begins at the fixed begin-output block, takes
the comparison's reject bridge, emits coordinate zero, and returns to compare
with scratch equal to one. -/
theorem outputPositiveFirstItem_path
    (capacity : Nat) (source : List WorkSymbol)
    (context : SourceContext source)
    (layout : CursorLayout source)
    (runtime : Runtime) (initialTape : WorkTape)
    (fits : LedgerFits capacity runtime.registers)
    (scratchBound : runtime.scratch < capacity)
    (outputPositive : 0 < runtime.registers.baseline)
    (represents :
      TapeRepresents beginOutputRef.startState
        capacity runtime.scratch runtime.registers runtime.checks
        source runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node beginOutputRef)
          (.node outputCompareRef) steps initialTape finalTape ∧
      TapeRepresents outputCompareRef.startState
        capacity
        (outputLoopItemResult
          (beginOutputResult runtime)).scratch
        (outputLoopItemResult
          (beginOutputResult runtime)).registers
        (outputLoopItemResult
          (beginOutputResult runtime)).checks source
        (outputLoopItemResult
          (beginOutputResult runtime)).targetTokens finalTape := by
  rcases
      beginOutput_path capacity source context layout runtime
        initialTape scratchBound represents with
    ⟨beginSteps, compareTape, beginPath, compareRepresents⟩
  have less :
      (beginOutputResult runtime).scratch <
        (beginOutputResult runtime).registers.baseline := by
    simpa [beginOutputResult] using outputPositive
  rcases
      compareMismatchItem_path capacity source context layout
        (beginOutputResult runtime) compareTape
        (by simpa [beginOutputResult] using fits)
        less compareRepresents with
    ⟨itemSteps, finalTape, itemPath, finalRepresents⟩
  exact
    ⟨beginSteps + itemSteps, finalTape,
      AcceptPath.trans graph (.node beginOutputRef)
        (.node outputCompareRef) (.node outputCompareRef)
        beginSteps itemSteps initialTape compareTape finalTape
        beginPath itemPath,
      finalRepresents⟩

theorem canonicalFinal_output_eq
    (source : List WorkSymbol) (target : List Token)
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) :
    (encodeWorkTape
      (TargetEmitterCursorFinalizer.finalTape source
        (SourceParser.packedTokenCells target)
        (TargetEmitterRuntimePrimitives.fixedWorkspace
          capacity scratch registers checks)
        [])).outputBits =
      encodeTokens target := by
  exact TargetEmitterCursorFinalizer.final_output_eq source target
    (TargetEmitterRuntimePrimitives.fixedWorkspace
      capacity scratch registers checks)
    []

theorem finalAccept_halted (tape : WorkTape) :
    machine.isHalted
        (endpointConfiguration (.accept : Endpoint) tape) = true :=
  accept_halted tape

theorem finalReject_halted (tape : WorkTape) :
    machine.isHalted
        (endpointConfiguration (.reject : Endpoint) tape) = true :=
  reject_halted tape

theorem finalDead_stuck (tape : WorkTape) :
    workStep? machine
        (endpointConfiguration (.dead : Endpoint) tape) = none :=
  dead_stuck tape

end PNP.Concrete.LockedNAND.TargetEmitterControllerOutputTrace
