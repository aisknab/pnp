/-
Copyright (c) 2026 PNP Labs.

Exact materialized header-block paths for the fixed grammar-only locked-NAND
target emitter.

The public paths are closed over the canonical scanner/ledger/stack
initialization.  In particular, callers do not provide compilation, capacity,
source-layout, or representation certificates.  The final header-navigation
paths transport the canonical navigator traces across finite blank padding,
retaining both their graph endpoints and exact step counts.
-/

import PNP.Concrete.LockedNANDTargetEmitterControllerInitialTrace
import PNP.Concrete.LockedNANDTargetEmitterRuntimeProgramSafety
import PNP.Concrete.WorkMachineProgramPathBlankEquivalence

namespace PNP.Concrete.LockedNAND.TargetEmitterControllerHeaderTrace

open PNP.Concrete
open WorkMachineProgramGraph
open WorkMachineProgramPath
open TargetEmitterController
open TargetEmitterPrimitiveCompiler
open TargetEmitterBlockCompiler

set_option maxRecDepth 100000

abbrev Runtime := TargetEmitterProgramSemantics.Runtime

/-- The semantic runtime represented at the canonical header-block entry. -/
def initialRuntime (raw : RawCircuit) : Runtime :=
  { captured := 0
    scratch := 0
    registers := TargetEmitterLedger.ledgerRegisters raw
    checks := []
    targetTokens := [] }

/-- Tape-only form of the runtime representation invariant used at graph
node boundaries. -/
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

private def headerDescriptor : BlockDescriptor :=
  { code := Block.header
    primitives := Plan.header
    continuation := .node headerNavigatorRef }

private def headerPrograms : List WorkMachine :=
  (compileProgram Plan.header).getD []

private theorem headerDescriptor_member :
    headerDescriptor ∈ blockDescriptors := by
  simp [headerDescriptor, blockDescriptors, fixedBlockDescriptors]

private theorem header_compiled :
    compileProgram Plan.header = some headerPrograms := by
  rfl

private theorem headerPrograms_nonempty :
    headerPrograms ≠ [] := by
  decide

private theorem header_startState :
    headerRef.startState =
      TargetEmitterRuntimeProgram.entryState 0 headerPrograms := by
  rfl

private def canonical_source_context
    (raw : RawCircuit) :
    TargetEmitterRuntimeProgram.SourceContext
      (SourceParser.circuitCells raw) := by
  cases sourceEq : SourceParser.circuitCells raw with
  | nil =>
      exact False.elim (SourceParser.circuitCells_ne_empty raw sourceEq)
  | cons head tail =>
      exact
        { head := head
          tail := tail
          source_eq := rfl
          allowed := Or.inl <|
            TargetEmitter.circuitCells_packed raw head <| by
              rw [sourceEq]
              exact List.Mem.head tail }

private theorem initial_captured_bound
    (raw : RawCircuit) :
    (initialRuntime raw).captured + 1 ≤
      (SourceParser.circuitCells raw).length := by
  have cells :=
    TargetEmitterCapacity.fourteen_le_circuitCells_length raw
  simp only [initialRuntime]
  omega

private theorem initial_scratch_bound
    (raw : RawCircuit) :
    (initialRuntime raw).scratch <
      TargetEmitterLedger.slotCapacity raw := by
  have reserve :=
    TargetEmitterCapacity.baseline_add_sixtyFour_le_slotCapacity raw
  simp only [initialRuntime]
  omega

private theorem headerBlock_path_of_represents
    (raw : RawCircuit) (initialTape : WorkTape)
    (represents :
      TapeRepresents headerRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (initialRuntime raw).scratch
        (initialRuntime raw).registers
        (initialRuntime raw).checks
        (SourceParser.circuitCells raw)
        (initialRuntime raw).targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node headerRef)
          (.node headerNavigatorRef) steps initialTape finalTape ∧
      TapeRepresents headerNavigatorRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterProgramSemantics.headerResult
          (initialRuntime raw)).scratch
        (TargetEmitterProgramSemantics.headerResult
          (initialRuntime raw)).registers
        (TargetEmitterProgramSemantics.headerResult
          (initialRuntime raw)).checks
        (SourceParser.circuitCells raw)
        (TargetEmitterProgramSemantics.headerResult
          (initialRuntime raw)).targetTokens finalTape := by
  let initial : WorkConfiguration :=
    { state :=
        TargetEmitterRuntimeProgram.entryState 0 headerPrograms
      tape := initialTape }
  have inputRepresents :
      TargetEmitterRuntime.Represents initial.state
        (TargetEmitterLedger.slotCapacity raw)
        (initialRuntime raw).scratch
        (initialRuntime raw).registers
        (initialRuntime raw).checks
        (SourceParser.circuitCells raw)
        (initialRuntime raw).targetTokens initial := by
    have atEntry :
        TapeRepresents
          (TargetEmitterRuntimeProgram.entryState 0 headerPrograms)
          (TargetEmitterLedger.slotCapacity raw)
          (initialRuntime raw).scratch
          (initialRuntime raw).registers
          (initialRuntime raw).checks
          (SourceParser.circuitCells raw)
          (initialRuntime raw).targetTokens initialTape := by
      rw [← header_startState]
      exact represents
    exact atEntry
  have safe :=
    TargetEmitterRuntimeProgramSafety.header_safe
      (canonical_source_context raw)
      (TargetEmitter.circuitCells_packed raw)
      (TargetEmitterCapacity.initialControllerRange raw)
      (initial_captured_bound raw)
      (initial_scratch_bound raw)
  rcases
      safe.descriptor_acceptPath_exact headerDescriptor
        headerDescriptor_member headerPrograms
        (by simpa [headerDescriptor] using header_compiled)
        headerPrograms_nonempty 0 initial inputRepresents with
    ⟨steps, actualFinal, path, finalRepresents⟩
  refine ⟨steps, actualFinal.tape, ?_, ?_⟩
  · simpa [headerDescriptor, headerRef] using path
  · exact
      represents_at_state
        (newState := headerNavigatorRef.startState)
        finalRepresents

/-- The canonical stack-initialization endpoint supplies an exact entry tape
for the materialized header block, which then reaches the header navigator. -/
theorem header_block_path (raw : RawCircuit) :
    ∃ entryTape blockSteps finalTape,
      AcceptPath graph (.node stackInitializeRef) (.node headerRef)
          (TargetEmitterCheckStack.Initialize.workSteps
            (TargetEmitterLedger.slotCapacity raw) + 1)
          (TargetEmitterLedger.finalConfiguration raw).tape
          entryTape ∧
      AcceptPath graph (.node headerRef) (.node headerNavigatorRef)
          blockSteps entryTape finalTape ∧
      TapeRepresents headerNavigatorRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterProgramSemantics.headerResult
          (initialRuntime raw)).scratch
        (TargetEmitterProgramSemantics.headerResult
          (initialRuntime raw)).registers
        (TargetEmitterProgramSemantics.headerResult
          (initialRuntime raw)).checks
        (SourceParser.circuitCells raw)
        (TargetEmitterProgramSemantics.headerResult
          (initialRuntime raw)).targetTokens finalTape := by
  rcases
      TargetEmitterControllerInitialTrace.stack_initialize_path raw with
    ⟨entryActual, stackPath, entryRepresents⟩
  have atHeader :
      TapeRepresents headerRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (initialRuntime raw).scratch
        (initialRuntime raw).registers
        (initialRuntime raw).checks
        (SourceParser.circuitCells raw)
        (initialRuntime raw).targetTokens entryActual.tape := by
    simpa [TapeRepresents, initialRuntime] using
      (represents_at_state
        (newState := headerRef.startState) entryRepresents)
  rcases headerBlock_path_of_represents raw entryActual.tape atHeader with
    ⟨blockSteps, finalTape, blockPath, finalRepresents⟩
  exact
    ⟨entryActual.tape, blockSteps, finalTape, stackPath,
      blockPath, finalRepresents⟩

/-- Compose stack initialization with the exact materialized header block. -/
theorem stack_header_path (raw : RawCircuit) :
    ∃ blockSteps finalTape,
      AcceptPath graph (.node stackInitializeRef)
          (.node headerNavigatorRef)
          (TargetEmitterCheckStack.Initialize.workSteps
              (TargetEmitterLedger.slotCapacity raw) + 1 +
            blockSteps)
          (TargetEmitterLedger.finalConfiguration raw).tape finalTape ∧
      TapeRepresents headerNavigatorRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterProgramSemantics.headerResult
          (initialRuntime raw)).scratch
        (TargetEmitterProgramSemantics.headerResult
          (initialRuntime raw)).registers
        (TargetEmitterProgramSemantics.headerResult
          (initialRuntime raw)).checks
        (SourceParser.circuitCells raw)
        (TargetEmitterProgramSemantics.headerResult
          (initialRuntime raw)).targetTokens finalTape := by
  rcases header_block_path raw with
    ⟨entryTape, blockSteps, finalTape, stackPath, blockPath,
      finalRepresents⟩
  refine ⟨blockSteps, finalTape, ?_, finalRepresents⟩
  exact
    AcceptPath.trans graph (.node stackInitializeRef)
      (.node headerRef) (.node headerNavigatorRef)
      (TargetEmitterCheckStack.Initialize.workSteps
        (TargetEmitterLedger.slotCapacity raw) + 1)
      blockSteps _ _ _ stackPath blockPath

/-- Compose scanner, ledger, stack initialization, and the exact header
block, stopping at the header navigator. -/
theorem scanner_ledger_stack_header_path (raw : RawCircuit) :
    ∃ blockSteps finalTape,
      AcceptPath graph (.node scannerRef) (.node headerNavigatorRef)
          (TargetEmitterGrammarScanner.canonicalSteps raw + 1 +
            (TargetEmitterLedger.workSteps raw + 1) +
            (TargetEmitterCheckStack.Initialize.workSteps
              (TargetEmitterLedger.slotCapacity raw) + 1) +
            blockSteps)
          (rawInputWorkTape (encodeCircuit raw)) finalTape ∧
      TapeRepresents headerNavigatorRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterProgramSemantics.headerResult
          (initialRuntime raw)).scratch
        (TargetEmitterProgramSemantics.headerResult
          (initialRuntime raw)).registers
        (TargetEmitterProgramSemantics.headerResult
          (initialRuntime raw)).checks
        (SourceParser.circuitCells raw)
        (TargetEmitterProgramSemantics.headerResult
          (initialRuntime raw)).targetTokens finalTape := by
  rcases
      TargetEmitterControllerInitialTrace.scanner_ledger_stack_path raw with
    ⟨entryActual, prefixPath, entryRepresents⟩
  have atHeader :
      TapeRepresents headerRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (initialRuntime raw).scratch
        (initialRuntime raw).registers
        (initialRuntime raw).checks
        (SourceParser.circuitCells raw)
        (initialRuntime raw).targetTokens entryActual.tape := by
    simpa [TapeRepresents, initialRuntime] using
      (represents_at_state
        (newState := headerRef.startState) entryRepresents)
  rcases headerBlock_path_of_represents raw entryActual.tape atHeader with
    ⟨blockSteps, finalTape, blockPath, finalRepresents⟩
  refine ⟨blockSteps, finalTape, ?_, finalRepresents⟩
  exact
    AcceptPath.trans graph (.node scannerRef) (.node headerRef)
      (.node headerNavigatorRef)
      (TargetEmitterGrammarScanner.canonicalSteps raw + 1 +
        (TargetEmitterLedger.workSteps raw + 1) +
        (TargetEmitterCheckStack.Initialize.workSteps
          (TargetEmitterLedger.slotCapacity raw) + 1))
      blockSteps _ _ _ prefixPath blockPath

private theorem represented_tape_blankEquivalent
    {state capacity scratch : Nat}
    {registers : TargetEmitter.UnaryRegisters}
    {checks : List Nat} {source : List WorkSymbol}
    {target : List Token} {tape : WorkTape}
    (represents :
      TapeRepresents state capacity scratch registers checks
        source target tape) :
    WorkTape.BlankEquivalent tape
      (TargetEmitterRuntime.logicalTape capacity scratch registers
        checks source target) := by
  simpa only [TapeRepresents,
    TargetEmitterRuntime.logicalConfiguration_tape] using
    represents.tape

/-- For a nonempty gate list, the canonical initialized controller executes
the header block and exact header navigator, stopping at the first left-source
controller node. -/
theorem stack_header_nonempty_path
    (inputs : Nat) (gate : RawGate)
    (gates : List RawGate) (output : RawSource) :
    let raw : RawCircuit :=
      { inputCount := inputs
        gates := gate :: gates
        output := output }
    let afterHeader :=
      TargetEmitterProgramSemantics.headerResult (initialRuntime raw)
    ∃ blockSteps finalTape,
      AcceptPath graph (.node stackInitializeRef) (.node leftFirstRef)
          (TargetEmitterCheckStack.Initialize.workSteps
              (TargetEmitterLedger.slotCapacity raw) + 1 +
            blockSteps +
            (TargetEmitterNavigator.headerWorkSteps
              inputs (gate :: gates).length + 1))
          (TargetEmitterLedger.finalConfiguration raw).tape finalTape ∧
      WorkTape.BlankEquivalent finalTape
        (TargetEmitterControllerTrace.sourceFocusTape
          ((TargetEmitterControllerTrace.circuitHeaderCells
                inputs (gate :: gates).length).reverse ++
            TargetEmitterRuntime.logicalLeftWorkspace
              (TargetEmitterLedger.slotCapacity raw)
              afterHeader.scratch afterHeader.registers
              afterHeader.checks)
          gate.left
          (SourceParser.sourceCells gate.right ++
            [SourceParser.cell01, SourceParser.cell11] ++
            SourceParser.gateListCells gates ++
            TargetEmitterControllerTrace.circuitFooterCells output ++
            TargetEmitter.sourceTargetBoundary ::
              SourceParser.packedTokenCells
                afterHeader.targetTokens)) := by
  dsimp only
  let raw : RawCircuit :=
    { inputCount := inputs
      gates := gate :: gates
      output := output }
  let afterHeader :=
    TargetEmitterProgramSemantics.headerResult (initialRuntime raw)
  rcases stack_header_path raw with
    ⟨blockSteps, headerTape, blockPath, represents⟩
  have canonicalPath :=
    TargetEmitterControllerTrace.header_nonempty_path
      (TargetEmitterLedger.slotCapacity raw)
      afterHeader.scratch afterHeader.registers afterHeader.checks
      afterHeader.targetTokens inputs gate gates output
  have inputEquivalent :
      WorkTape.BlankEquivalent headerTape
        (TargetEmitterRuntime.logicalTape
          (TargetEmitterLedger.slotCapacity raw)
          afterHeader.scratch afterHeader.registers
          afterHeader.checks
          (SourceParser.circuitCells raw)
          afterHeader.targetTokens) := by
    exact represented_tape_blankEquivalent represents
  rcases canonicalPath.transport inputEquivalent with
    ⟨finalTape, navigationPath, finalEquivalent⟩
  refine ⟨blockSteps, finalTape, ?_, finalEquivalent⟩
  exact
    AcceptPath.trans graph (.node stackInitializeRef)
      (.node headerNavigatorRef) (.node leftFirstRef)
      (TargetEmitterCheckStack.Initialize.workSteps
          (TargetEmitterLedger.slotCapacity raw) + 1 +
        blockSteps)
      (TargetEmitterNavigator.headerWorkSteps
        inputs (gate :: gates).length + 1)
      _ _ _ blockPath navigationPath

/-- For an empty gate list, the canonical initialized controller executes
the header block and exact header navigator, stopping at the program-end
controller node. -/
theorem stack_header_empty_path
    (inputs : Nat) (output : RawSource) :
    let raw : RawCircuit :=
      { inputCount := inputs
        gates := []
        output := output }
    let afterHeader :=
      TargetEmitterProgramSemantics.headerResult (initialRuntime raw)
    ∃ blockSteps finalTape,
      AcceptPath graph (.node stackInitializeRef) (.node programEndRef)
          (TargetEmitterCheckStack.Initialize.workSteps
              (TargetEmitterLedger.slotCapacity raw) + 1 +
            blockSteps +
            (TargetEmitterNavigator.headerWorkSteps inputs 0 + 1))
          (TargetEmitterLedger.finalConfiguration raw).tape finalTape ∧
      WorkTape.BlankEquivalent finalTape
        (TargetEmitterControllerTrace.programEndFocusTape
          ((TargetEmitterControllerTrace.circuitHeaderCells
                inputs 0).reverse ++
            TargetEmitterRuntime.logicalLeftWorkspace
              (TargetEmitterLedger.slotCapacity raw)
              afterHeader.scratch afterHeader.registers
              afterHeader.checks)
          output afterHeader.targetTokens) := by
  dsimp only
  let raw : RawCircuit :=
    { inputCount := inputs
      gates := []
      output := output }
  let afterHeader :=
    TargetEmitterProgramSemantics.headerResult (initialRuntime raw)
  rcases stack_header_path raw with
    ⟨blockSteps, headerTape, blockPath, represents⟩
  have canonicalPath :=
    TargetEmitterControllerTrace.header_empty_path
      (TargetEmitterLedger.slotCapacity raw)
      afterHeader.scratch afterHeader.registers afterHeader.checks
      afterHeader.targetTokens inputs output
  have inputEquivalent :
      WorkTape.BlankEquivalent headerTape
        (TargetEmitterRuntime.logicalTape
          (TargetEmitterLedger.slotCapacity raw)
          afterHeader.scratch afterHeader.registers
          afterHeader.checks
          (SourceParser.circuitCells raw)
          afterHeader.targetTokens) := by
    exact represented_tape_blankEquivalent represents
  rcases canonicalPath.transport inputEquivalent with
    ⟨finalTape, navigationPath, finalEquivalent⟩
  refine ⟨blockSteps, finalTape, ?_, finalEquivalent⟩
  exact
    AcceptPath.trans graph (.node stackInitializeRef)
      (.node headerNavigatorRef) (.node programEndRef)
      (TargetEmitterCheckStack.Initialize.workSteps
          (TargetEmitterLedger.slotCapacity raw) + 1 +
        blockSteps)
      (TargetEmitterNavigator.headerWorkSteps inputs 0 + 1)
      _ _ _ blockPath navigationPath

end PNP.Concrete.LockedNAND.TargetEmitterControllerHeaderTrace
