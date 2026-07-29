/-
Copyright (c) 2026 PNP Labs.

Runtime adapters for the non-stack literal target-emitter primitives.

Each theorem below transports an existing exact local-machine trace to the
canonical `TargetEmitterRuntime.Represents` workspace.  The executable
machines remain the literal tables selected by `TargetEmitterPrimitiveCompiler`;
this layer performs no plan interpretation or host-side schedule lookup.
-/

import PNP.Concrete.LockedNANDTargetEmitterRuntime
import PNP.Concrete.LockedNANDTargetEmitterPrimitiveCompiler
import PNP.Concrete.LockedNANDTargetEmitterScratchCompareSlotExact

namespace PNP.Concrete.LockedNAND.TargetEmitterRuntimePrimitives

open PNP.Concrete

abbrev Slot := TargetEmitterLedger.Slot
abbrev LedgerFits := TargetEmitterScratchAddSlot.LedgerFits

def targetSuffix (target : List Token) : List WorkSymbol :=
  TargetEmitter.sourceTargetBoundary ::
    SourceParser.packedTokenCells target

def fixedWorkspace (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) : List WorkSymbol :=
  TargetEmitterCheckStack.scratchWord capacity scratch ++
    TargetEmitterLedger.ledgerBoundary ::
      (TargetEmitterLedger.slotBank capacity registers ++
        TargetEmitterCheckStack.stackWord checks)

def ledgerAndStack (capacity : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) : List WorkSymbol :=
  TargetEmitterLedger.ledgerBoundary ::
    (TargetEmitterLedger.slotBank capacity registers ++
      TargetEmitterCheckStack.stackWord checks)

def postScratchWorkspace (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) : List WorkSymbol :=
  List.replicate (capacity - scratch) WorkSymbol.blank ++
    ledgerAndStack capacity registers checks

private theorem packedTokenCells_append
    (first second : List Token) :
    SourceParser.packedTokenCells (first ++ second) =
      SourceParser.packedTokenCells first ++
        SourceParser.packedTokenCells second := by
  induction first with
  | nil =>
      rfl
  | cons token rest inductionHypothesis =>
      simp only [List.cons_append,
        SourceParser.packedTokenCells, inductionHypothesis,
        List.append_assoc]

private theorem replicate_add {α : Type} (first second : Nat)
    (value : α) :
    List.replicate (first + second) value =
      List.replicate first value ++
        List.replicate second value := by
  induction first with
  | zero =>
      simp
  | succ first inductionHypothesis =>
      simp only [Nat.succ_add, List.replicate_succ,
        inductionHypothesis, List.cons_append]

def incrementRegisters (slot : Slot)
    (registers : TargetEmitter.UnaryRegisters) :
    TargetEmitter.UnaryRegisters :=
  match slot with
  | .inputCount =>
      { registers with inputCount := registers.inputCount + 1 }
  | .normalizedGateCount =>
      { registers with
        normalizedGateCount := registers.normalizedGateCount + 1 }
  | .carrierWidth =>
      { registers with carrierWidth := registers.carrierWidth + 1 }
  | .baseline =>
      { registers with baseline := registers.baseline + 1 }
  | .currentGate =>
      { registers with currentGate := registers.currentGate + 1 }
  | .outputIndex =>
      { registers with outputIndex := registers.outputIndex + 1 }

def slotCell (capacity value : Nat) :
    TargetEmitterSlotIncrement.SlotCell :=
  { value := value
    remaining := capacity - value }

def slotBankOfRegisters (capacity : Nat)
    (registers : TargetEmitter.UnaryRegisters) :
    TargetEmitterSlotIncrement.SlotBank :=
  { inputCount := slotCell capacity registers.inputCount
    normalizedGateCount :=
      slotCell capacity registers.normalizedGateCount
    carrierWidth := slotCell capacity registers.carrierWidth
    baseline := slotCell capacity registers.baseline
    currentGate := slotCell capacity registers.currentGate
    outputIndex := slotCell capacity registers.outputIndex }

theorem slotBankOfRegisters_selected_value
    (capacity : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (slot : Slot) :
    ((slotBankOfRegisters capacity registers).selected slot).value =
      TargetEmitterLedger.slotValue registers slot := by
  cases slot <;> rfl

theorem slotBankOfRegisters_selected_remaining
    (capacity : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (slot : Slot) :
    ((slotBankOfRegisters capacity registers).selected slot).remaining =
      capacity - TargetEmitterLedger.slotValue registers slot := by
  cases slot <;> rfl

private theorem slotCell_word (capacity value : Nat)
    (valueBound : value ≤ capacity) :
    (slotCell capacity value).word =
      TargetEmitterLedger.slotWord capacity value := by
  rw [TargetEmitterSlotIncrement.SlotCell.word_eq_ledger_slotWord]
  have total : value + (capacity - value) = capacity := by
    omega
  simp [slotCell, total]

theorem slotBankOfRegisters_word (capacity : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (fits : LedgerFits capacity registers) :
    (slotBankOfRegisters capacity registers).word =
      TargetEmitterLedger.slotBank capacity registers := by
  simp [slotBankOfRegisters, TargetEmitterSlotIncrement.SlotBank.word,
    TargetEmitterSlotIncrement.SlotBank.cells,
    TargetEmitterSlotIncrement.cellsWord,
    TargetEmitterLedger.slotBank, TargetEmitterLedger.Slot.all,
    TargetEmitterLedger.slotValue,
    slotCell_word capacity registers.inputCount fits.inputCount,
    slotCell_word capacity registers.normalizedGateCount
      fits.normalizedGateCount,
    slotCell_word capacity registers.carrierWidth fits.carrierWidth,
    slotCell_word capacity registers.baseline fits.baseline,
    slotCell_word capacity registers.currentGate fits.currentGate,
    slotCell_word capacity registers.outputIndex fits.outputIndex]

private theorem slotCell_increment (capacity value : Nat) :
    (slotCell capacity value).increment =
      slotCell capacity (value + 1) := by
  unfold slotCell TargetEmitterSlotIncrement.SlotCell.increment
  have remaining :
      capacity - value - 1 = capacity - (value + 1) := by
    omega
  rw [remaining]

theorem slotBankOfRegisters_increment (capacity : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (slot : Slot)
    (_available :
      TargetEmitterLedger.slotValue registers slot < capacity) :
    (slotBankOfRegisters capacity registers).increment slot =
      slotBankOfRegisters capacity (incrementRegisters slot registers) := by
  cases slot with
  | inputCount =>
      simp only [TargetEmitterSlotIncrement.SlotBank.increment,
        slotBankOfRegisters, incrementRegisters]
      rw [slotCell_increment capacity registers.inputCount]
  | normalizedGateCount =>
      simp only [TargetEmitterSlotIncrement.SlotBank.increment,
        slotBankOfRegisters, incrementRegisters]
      rw [slotCell_increment capacity registers.normalizedGateCount]
  | carrierWidth =>
      simp only [TargetEmitterSlotIncrement.SlotBank.increment,
        slotBankOfRegisters, incrementRegisters]
      rw [slotCell_increment capacity registers.carrierWidth]
  | baseline =>
      simp only [TargetEmitterSlotIncrement.SlotBank.increment,
        slotBankOfRegisters, incrementRegisters]
      rw [slotCell_increment capacity registers.baseline]
  | currentGate =>
      simp only [TargetEmitterSlotIncrement.SlotBank.increment,
        slotBankOfRegisters, incrementRegisters]
      rw [slotCell_increment capacity registers.currentGate]
  | outputIndex =>
      simp only [TargetEmitterSlotIncrement.SlotBank.increment,
        slotBankOfRegisters, incrementRegisters]
      rw [slotCell_increment capacity registers.outputIndex]

theorem incrementRegisters_fits (capacity : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (slot : Slot) (fits : LedgerFits capacity registers)
    (available :
      TargetEmitterLedger.slotValue registers slot < capacity) :
    LedgerFits capacity (incrementRegisters slot registers) := by
  rcases fits with
    ⟨inputFits, normalizedFits, carrierFits, baselineFits,
      currentFits, outputFits⟩
  cases slot <;>
    constructor <;>
    simp_all [incrementRegisters, TargetEmitterLedger.slotValue] <;>
    omega

/-! ### Literal appenders -/

/-- Append one literal token while preserving the canonical unmarked source
and every logical workspace component. -/
theorem appendPlain_exact (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (source : List WorkSymbol)
    (target : List Token) (token : Token)
    (actual : WorkConfiguration)
    (sourcePacked :
      ∀ symbol, symbol ∈ source →
        TargetEmitter.PackedSymbol symbol)
    (represents :
      TargetEmitterRuntime.Represents
        (TargetEmitter.seekSourceState token)
        capacity scratch registers checks source target actual) :
    ∃ actualFinal,
      workRunExact? (TargetEmitter.machineFor token)
          (TargetEmitter.packedAppendWorkSteps source
            (SourceParser.packedTokenCells target))
          actual =
        some actualFinal ∧
      TargetEmitterRuntime.Represents
        TargetEmitter.acceptState capacity scratch registers checks
        source (target ++ [token]) actualFinal := by
  have inputEquivalent :
      WorkConfiguration.BlankEquivalent actual
        (TargetEmitter.appendPackedEntry token source
          (SourceParser.packedTokenCells target)
          (fixedWorkspace capacity scratch registers checks) []) := by
    have logicalToPadded :=
      TargetEmitterRuntime.padded_blankEquivalent_symm
        (TargetEmitter.seekSourceState token)
        capacity scratch registers checks source target 0 3
    exact WorkConfiguration.blankEquivalent_trans represents <| by
      simpa [TargetEmitter.appendPackedEntry,
        TargetEmitterRuntime.logicalLeftWorkspace,
        TargetEmitterRuntime.logicalWord, fixedWorkspace,
        List.append_assoc] using logicalToPadded
  rcases workRunExact?_transport
      (TargetEmitter.machineFor token)
      (TargetEmitter.packedAppendWorkSteps source
        (SourceParser.packedTokenCells target))
      inputEquivalent
      (TargetEmitter.appendPacked_exact token source
        (SourceParser.packedTokenCells target)
        (fixedWorkspace capacity scratch registers checks) []
        sourcePacked
        (TargetEmitterRuntime.targetCells_packed target)) with
    ⟨actualFinal, exactRun, finalEquivalent⟩
  refine ⟨actualFinal, exactRun, ?_⟩
  have paddedToLogical :=
    TargetEmitterRuntime.padded_blankEquivalent
      TargetEmitter.acceptState capacity scratch registers checks
      source (target ++ [token]) 0 1
  exact WorkConfiguration.blankEquivalent_trans finalEquivalent <| by
    simpa [TargetEmitterRuntime.Represents,
      TargetEmitter.appendPackedFinal,
      TargetEmitterRuntime.logicalLeftWorkspace,
      TargetEmitterRuntime.logicalWord, fixedWorkspace,
      packedTokenCells_append,
      SourceParser.packedTokenCells,
      TargetEmitter.tokenSymbols_eq_parser_cells,
      List.append_assoc] using paddedToLogical

/-- Append one literal token while retaining the unique contextual source
cursor at exactly the supplied split. -/
theorem appendMarked_exact (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat)
    (before : List WorkSymbol) (original : WorkSymbol)
    (after : List WorkSymbol) (target : List Token)
    (token : Token) (actual : WorkConfiguration)
    (sourcePacked :
      ∀ symbol,
        symbol ∈
          TargetEmitterCursorAppender.originalSource
            before original after →
          TargetEmitter.PackedSymbol symbol)
    (represents :
      TargetEmitterRuntime.Represents
        (TargetEmitter.seekSourceState token)
        capacity scratch registers checks
        (TargetEmitterCursorAppender.sourceWithCursor
          before original after)
        target actual) :
    ∃ actualFinal,
      workRunExact? (TargetEmitterCursorAppender.machineFor token)
          (TargetEmitterCursorAppender.workSteps before after
            (SourceParser.packedTokenCells target))
          actual =
        some actualFinal ∧
      TargetEmitterRuntime.Represents
        (TargetEmitterCursorAppender.doneState token)
        capacity scratch registers checks
        (TargetEmitterCursorAppender.sourceWithCursor
          before original after)
        (target ++ [token]) actualFinal := by
  let source :=
    TargetEmitterCursorAppender.sourceWithCursor
      before original after
  have inputEquivalent :
      WorkConfiguration.BlankEquivalent actual
        (TargetEmitterCursorAppender.entryConfiguration token
          before original after
          (SourceParser.packedTokenCells target)
          (fixedWorkspace capacity scratch registers checks) []) := by
    have logicalToPadded :=
      TargetEmitterRuntime.padded_blankEquivalent_symm
        (TargetEmitter.seekSourceState token)
        capacity scratch registers checks source target 0 3
    exact WorkConfiguration.blankEquivalent_trans represents <| by
      simpa [source,
        TargetEmitterCursorAppender.entryConfiguration,
        TargetEmitterCursorAppender.appendEntry,
        TargetEmitterRuntime.logicalLeftWorkspace,
        TargetEmitterRuntime.logicalWord, fixedWorkspace,
        TargetEmitterCursorAppender.sourceLeftBoundary,
        TargetEmitterCursorAppender.sourceTargetBoundary,
        List.append_assoc] using logicalToPadded
  rcases workRunExact?_transport
      (TargetEmitterCursorAppender.machineFor token)
      (TargetEmitterCursorAppender.workSteps before after
        (SourceParser.packedTokenCells target))
      inputEquivalent
      (TargetEmitterCursorAppender.append_split_exact token
        before original after
        (SourceParser.packedTokenCells target)
        (fixedWorkspace capacity scratch registers checks) []
        sourcePacked
        (TargetEmitterRuntime.targetCells_packed target)) with
    ⟨actualFinal, exactRun, finalEquivalent⟩
  refine ⟨actualFinal, exactRun, ?_⟩
  have paddedToLogical :=
    TargetEmitterRuntime.padded_blankEquivalent
      (TargetEmitterCursorAppender.doneState token)
      capacity scratch registers checks source
      (target ++ [token]) 0 1
  exact WorkConfiguration.blankEquivalent_trans finalEquivalent <| by
    simpa [TargetEmitterRuntime.Represents, source,
      TargetEmitterCursorAppender.finalConfiguration,
      TargetEmitterCursorAppender.appendFinal,
      TargetEmitterRuntime.logicalLeftWorkspace,
      TargetEmitterRuntime.logicalWord, fixedWorkspace,
      packedTokenCells_append,
      SourceParser.packedTokenCells,
      TargetEmitter.tokenSymbols_eq_parser_cells,
      TargetEmitterCursorAppender.sourceLeftBoundary,
      TargetEmitterCursorAppender.sourceTargetBoundary,
      List.append_assoc] using paddedToLogical

/-! ### Scratch and register primitives -/

/-- Reset scratch to zero.  The strict bound supplies the physical blank
that the literal reset table validates before moving the separator. -/
theorem resetScratch_exact (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat)
    (sourceHead : WorkSymbol) (sourceTail : List WorkSymbol)
    (target : List Token) (actual : WorkConfiguration)
    (scratchBound : scratch < capacity)
    (allowed :
      TargetEmitter.PackedSymbol sourceHead ∨
        sourceHead = TargetEmitterCursorAppender.cursorMarker)
    (represents :
      TargetEmitterRuntime.Represents
        TargetEmitterScratchReset.startState
        capacity scratch registers checks
        (sourceHead :: sourceTail) target actual) :
    ∃ actualFinal,
      workRunExact? TargetEmitterScratchReset.machine
          (TargetEmitterScratchReset.workSteps scratch) actual =
        some actualFinal ∧
      TargetEmitterRuntime.Represents
        TargetEmitterScratchReset.acceptState
        capacity 0 registers checks
        (sourceHead :: sourceTail) target actualFinal := by
  let reserve :=
    List.replicate (capacity - scratch - 1) WorkSymbol.blank
  have remaining :
      capacity - scratch =
        1 + (capacity - scratch - 1) := by
    omega
  have blankSplit :
      List.replicate (capacity - scratch) WorkSymbol.blank =
        WorkSymbol.blank :: reserve := by
    rw [remaining, Nat.one_add, List.replicate_succ]
  have inputEquivalent :
      WorkConfiguration.BlankEquivalent actual
        (TargetEmitterScratchReset.entryConfiguration scratch
          sourceHead sourceTail (targetSuffix target)
          reserve (ledgerAndStack capacity registers checks)) := by
    simpa [TargetEmitterRuntime.Represents,
      TargetEmitterRuntime.logicalConfiguration,
      TargetEmitterRuntime.logicalLeftWorkspace,
      TargetEmitterRuntime.logicalWord,
      TargetEmitterScratchReset.entryConfiguration,
      TargetEmitterScratchReset.configAtWord,
      TargetEmitterScratchReset.sourceLeftBoundary,
      TargetEmitterCheckStack.scratchWord,
      TargetEmitterCheckStack.unaryUnit,
      TargetEmitterCheckStack.unarySeparator,
      TargetEmitterCheckStack.cellBlank,
      TargetEmitterScratchReset.unaryUnit,
      TargetEmitterScratchReset.unarySeparator,
      TargetEmitterLedger.sourceLeftBoundary,
      TargetEmitterLedger.unaryUnit,
      TargetEmitterLedger.unarySeparator,
      TargetEmitterLedger.cellBlank,
      TargetEmitter.sourceLeftBoundary,
      TargetEmitter.unaryUnit,
      TargetEmitter.unarySeparator,
      targetSuffix, ledgerAndStack, reserve, blankSplit,
      List.append_assoc] using represents
  rcases workRunExact?_transport
      TargetEmitterScratchReset.machine
      (TargetEmitterScratchReset.workSteps scratch)
      inputEquivalent
      (TargetEmitterScratchReset.exact scratch
        sourceHead sourceTail (targetSuffix target)
        reserve (ledgerAndStack capacity registers checks)
        allowed) with
    ⟨actualFinal, exactRun, finalEquivalent⟩
  refine ⟨actualFinal, exactRun, ?_⟩
  have total :
      scratch + 1 + (capacity - scratch - 1) = capacity := by
    omega
  have blankJoin :
      List.replicate (scratch + 1) WorkSymbol.blank ++ reserve =
        List.replicate capacity WorkSymbol.blank := by
    rw [← replicate_add, total]
  simpa [TargetEmitterRuntime.Represents,
    TargetEmitterRuntime.logicalConfiguration,
    TargetEmitterRuntime.logicalLeftWorkspace,
    TargetEmitterRuntime.logicalWord,
    TargetEmitterScratchReset.finalConfiguration,
    TargetEmitterScratchReset.configAtWord,
    TargetEmitterScratchReset.sourceLeftBoundary,
    TargetEmitterCheckStack.scratchWord,
    TargetEmitterCheckStack.unarySeparator,
    TargetEmitterCheckStack.cellBlank,
    TargetEmitterScratchReset.unarySeparator,
    TargetEmitterLedger.sourceLeftBoundary,
    TargetEmitterLedger.unarySeparator,
    TargetEmitterLedger.cellBlank,
    TargetEmitter.sourceLeftBoundary,
    TargetEmitter.unarySeparator,
    targetSuffix, ledgerAndStack, blankJoin,
    List.append_assoc] using finalEquivalent

/-- Add one selected unary register to scratch without changing the ledger,
stack, source, or target. -/
theorem addRegister_exact (slot : Slot)
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat)
    (sourceHead : WorkSymbol) (sourceTail : List WorkSymbol)
    (target : List Token) (actual : WorkConfiguration)
    (fits : LedgerFits capacity registers)
    (enough :
      scratch + TargetEmitterLedger.slotValue registers slot ≤
        capacity)
    (allowed :
      TargetEmitterScratchAddSlot.sourceAllowed sourceHead)
    (represents :
      TargetEmitterRuntime.Represents
        (TargetEmitterScratchAddSlot.startState slot)
        capacity scratch registers checks
        (sourceHead :: sourceTail) target actual) :
    ∃ actualFinal,
      workRunExact? (TargetEmitterScratchAddSlot.machineFor slot)
          (TargetEmitterScratchAddSlot.workSteps slot capacity scratch
            (TargetEmitterLedger.slotValue registers slot))
          actual =
        some actualFinal ∧
      TargetEmitterRuntime.Represents
        TargetEmitterScratchAddSlot.acceptState
        capacity
        (scratch + TargetEmitterLedger.slotValue registers slot)
        registers checks (sourceHead :: sourceTail) target
        actualFinal := by
  have inputEquivalent :
      WorkConfiguration.BlankEquivalent actual
        (TargetEmitterScratchAddSlot.entryConfiguration
          slot capacity scratch registers sourceHead sourceTail
          (targetSuffix target)
          (TargetEmitterCheckStack.stackWord checks)) := by
    simpa [TargetEmitterRuntime.Represents,
      TargetEmitterRuntime.logicalConfiguration,
      TargetEmitterRuntime.logicalLeftWorkspace,
      TargetEmitterRuntime.logicalWord,
      TargetEmitterScratchAddSlot.entryConfiguration,
      TargetEmitterScratchAddSlot.configAtWord,
      TargetEmitterScratchAddSlot.scratchWord,
      TargetEmitterCheckStack.scratchWord,
      TargetEmitterCheckStack.unaryUnit,
      TargetEmitterCheckStack.unarySeparator,
      TargetEmitterCheckStack.cellBlank,
      TargetEmitterScratchAddSlot.unaryUnit,
      TargetEmitterScratchAddSlot.unarySeparator,
      TargetEmitterScratchAddSlot.sourceLeftBoundary,
      TargetEmitterScratchAddSlot.ledgerBoundary,
      TargetEmitterLedger.sourceLeftBoundary,
      TargetEmitterLedger.cellBlank,
      TargetEmitter.sourceLeftBoundary,
      targetSuffix, List.append_assoc] using represents
  rcases workRunExact?_transport
      (TargetEmitterScratchAddSlot.machineFor slot)
      (TargetEmitterScratchAddSlot.workSteps slot capacity scratch
        (TargetEmitterLedger.slotValue registers slot))
      inputEquivalent
      (TargetEmitterScratchAddSlot.exact slot capacity scratch
        registers sourceHead sourceTail (targetSuffix target)
        (TargetEmitterCheckStack.stackWord checks)
        fits (by simpa [TargetEmitterScratchAddSlot.selectedValue]
          using enough) allowed) with
    ⟨actualFinal, exactRun, finalEquivalent⟩
  refine ⟨actualFinal, exactRun, ?_⟩
  simpa [TargetEmitterRuntime.Represents,
    TargetEmitterRuntime.logicalConfiguration,
    TargetEmitterRuntime.logicalLeftWorkspace,
    TargetEmitterRuntime.logicalWord,
    TargetEmitterScratchAddSlot.finalConfiguration,
    TargetEmitterScratchAddSlot.configAtWord,
    TargetEmitterScratchAddSlot.scratchWord,
    TargetEmitterScratchAddSlot.selectedValue,
    TargetEmitterCheckStack.scratchWord,
    TargetEmitterCheckStack.unaryUnit,
    TargetEmitterCheckStack.unarySeparator,
    TargetEmitterCheckStack.cellBlank,
    TargetEmitterScratchAddSlot.unaryUnit,
    TargetEmitterScratchAddSlot.unarySeparator,
    TargetEmitterScratchAddSlot.sourceLeftBoundary,
    TargetEmitterScratchAddSlot.ledgerBoundary,
    TargetEmitterLedger.sourceLeftBoundary,
    TargetEmitterLedger.cellBlank,
    TargetEmitter.sourceLeftBoundary,
    targetSuffix, List.append_assoc] using finalEquivalent

/-- Increment scratch by one, consuming exactly one logical reserve blank. -/
theorem incrementScratch_exact (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat)
    (sourceHead : WorkSymbol) (sourceTail : List WorkSymbol)
    (target : List Token) (actual : WorkConfiguration)
    (scratchBound : scratch < capacity)
    (allowed :
      TargetEmitter.PackedSymbol sourceHead ∨
        sourceHead = TargetEmitterCursorAppender.cursorMarker)
    (represents :
      TargetEmitterRuntime.Represents
        TargetEmitterScratchIncrement.startState
        capacity scratch registers checks
        (sourceHead :: sourceTail) target actual) :
    ∃ actualFinal,
      workRunExact? TargetEmitterScratchIncrement.machine
          (TargetEmitterScratchIncrement.workSteps scratch) actual =
        some actualFinal ∧
      TargetEmitterRuntime.Represents
        TargetEmitterScratchIncrement.acceptState
        capacity (scratch + 1) registers checks
        (sourceHead :: sourceTail) target actualFinal := by
  let reserve :=
    List.replicate (capacity - scratch - 1) WorkSymbol.blank
  have remaining :
      capacity - scratch =
        1 + (capacity - scratch - 1) := by
    omega
  have blankSplit :
      List.replicate (capacity - scratch) WorkSymbol.blank =
        WorkSymbol.blank :: reserve := by
    rw [remaining, Nat.one_add, List.replicate_succ]
  have inputEquivalent :
      WorkConfiguration.BlankEquivalent actual
        (TargetEmitterScratchIncrement.entryConfiguration scratch
          sourceHead sourceTail (targetSuffix target)
          reserve (ledgerAndStack capacity registers checks)) := by
    simpa [TargetEmitterRuntime.Represents,
      TargetEmitterRuntime.logicalConfiguration,
      TargetEmitterRuntime.logicalLeftWorkspace,
      TargetEmitterRuntime.logicalWord,
      TargetEmitterScratchIncrement.entryConfiguration,
      TargetEmitterScratchIncrement.configAtWord,
      TargetEmitterScratchIncrement.sourceLeftBoundary,
      TargetEmitterCheckStack.scratchWord,
      TargetEmitterCheckStack.unaryUnit,
      TargetEmitterCheckStack.unarySeparator,
      TargetEmitterCheckStack.cellBlank,
      TargetEmitterScratchIncrement.unaryUnit,
      TargetEmitterScratchIncrement.unarySeparator,
      TargetEmitterLedger.sourceLeftBoundary,
      TargetEmitterLedger.unaryUnit,
      TargetEmitterLedger.unarySeparator,
      TargetEmitterLedger.cellBlank,
      TargetEmitter.sourceLeftBoundary,
      TargetEmitter.unaryUnit,
      TargetEmitter.unarySeparator,
      targetSuffix, ledgerAndStack, reserve, blankSplit,
      List.append_assoc] using represents
  rcases workRunExact?_transport
      TargetEmitterScratchIncrement.machine
      (TargetEmitterScratchIncrement.workSteps scratch)
      inputEquivalent
      (TargetEmitterScratchIncrement.exact scratch
        sourceHead sourceTail (targetSuffix target)
        reserve (ledgerAndStack capacity registers checks)
        allowed) with
    ⟨actualFinal, exactRun, finalEquivalent⟩
  refine ⟨actualFinal, exactRun, ?_⟩
  have remainingAfter :
      capacity - scratch - 1 = capacity - (scratch + 1) := by
    omega
  simpa [TargetEmitterRuntime.Represents,
    TargetEmitterRuntime.logicalConfiguration,
    TargetEmitterRuntime.logicalLeftWorkspace,
    TargetEmitterRuntime.logicalWord,
    TargetEmitterScratchIncrement.finalConfiguration,
    TargetEmitterScratchIncrement.configAtWord,
    TargetEmitterScratchIncrement.sourceLeftBoundary,
    TargetEmitterCheckStack.scratchWord,
    TargetEmitterCheckStack.unaryUnit,
    TargetEmitterCheckStack.unarySeparator,
    TargetEmitterCheckStack.cellBlank,
    TargetEmitterScratchIncrement.unaryUnit,
    TargetEmitterScratchIncrement.unarySeparator,
    TargetEmitterLedger.sourceLeftBoundary,
    TargetEmitterLedger.unaryUnit,
    TargetEmitterLedger.unarySeparator,
    TargetEmitterLedger.cellBlank,
    TargetEmitter.sourceLeftBoundary,
    TargetEmitter.unaryUnit,
    TargetEmitter.unarySeparator,
    targetSuffix, ledgerAndStack, reserve, remainingAfter,
    List.append_assoc] using finalEquivalent

/-! ### Captured-source reload -/

/-- Reload the unary natural encoded by a cursor-marked input or gate source
into zero scratch.  The source kind is read from the retained tape; it is not
host-side schedule advice. -/
theorem reloadCaptured_exact
    (kind : TargetEmitterMarkedSourceReload.NatKind)
    (capacity value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat)
    (before : List TargetEmitterMarkedSourceReload.PackedCell)
    (afterSource : List WorkSymbol)
    (target : List Token) (actual : WorkConfiguration)
    (valueBound : value + 1 ≤ capacity)
    (represents :
      TargetEmitterRuntime.Represents
        TargetEmitterMarkedSourceReload.startState
        capacity 0 registers checks
        (TargetEmitterMarkedSourceReload.packedWord before ++
          TargetEmitterMarkedSourceReload.markedSourceCells kind value ++
          afterSource)
        target actual) :
    ∃ actualFinal,
      workRunExact? TargetEmitterMarkedSourceReload.machine
          (TargetEmitterMarkedSourceReload.workSteps
            before.length value)
          actual =
        some actualFinal ∧
      TargetEmitterRuntime.Represents
        TargetEmitterMarkedSourceReload.acceptState
        capacity value registers checks
        (TargetEmitterMarkedSourceReload.packedWord before ++
          TargetEmitterMarkedSourceReload.markedSourceCells kind value ++
          afterSource)
        target actualFinal := by
  let reserve :=
    List.replicate (capacity - (value + 1)) WorkSymbol.blank
  let ledger :=
    TargetEmitterLedger.ledgerBoundary ::
      TargetEmitterLedger.slotBank capacity registers
  have capacitySplit :
      value + 1 + (capacity - (value + 1)) = capacity := by
    omega
  have inputBlanks :
      List.replicate (value + 1) WorkSymbol.blank ++ reserve =
        List.replicate capacity WorkSymbol.blank := by
    rw [← replicate_add, capacitySplit]
  have outputRemaining :
      1 + (capacity - (value + 1)) =
        capacity - value := by
    omega
  have outputBlanks :
      List.replicate 1 WorkSymbol.blank ++ reserve =
        List.replicate (capacity - value) WorkSymbol.blank := by
    rw [← replicate_add, outputRemaining]
  have outputBlankCons :
      WorkSymbol.blank :: reserve =
        List.replicate (capacity - value) WorkSymbol.blank := by
    simpa using outputBlanks
  have inputEquivalent :
      WorkConfiguration.BlankEquivalent actual
        (TargetEmitterMarkedSourceReload.entryConfiguration
          kind value before afterSource (targetSuffix target)
          reserve ledger
          (TargetEmitterCheckStack.stackWord checks)) := by
    simpa [TargetEmitterRuntime.Represents,
      TargetEmitterRuntime.logicalConfiguration,
      TargetEmitterRuntime.logicalLeftWorkspace,
      TargetEmitterRuntime.logicalWord,
      TargetEmitterMarkedSourceReload.entryConfiguration,
      TargetEmitterMarkedSourceReload.configAtWord,
      TargetEmitterMarkedSourceReload.scratchWord,
      TargetEmitterMarkedSourceReload.sourceLeftBoundary,
      TargetEmitterSourceCapture.sourceLeftBoundary,
      TargetEmitterMarkedSourceReload.unarySeparator,
      TargetEmitterCheckStack.scratchWord,
      TargetEmitterCheckStack.unarySeparator,
      TargetEmitterCheckStack.cellBlank,
      TargetEmitterLedger.sourceLeftBoundary,
      TargetEmitterLedger.unarySeparator,
      TargetEmitterLedger.cellBlank,
      TargetEmitter.sourceLeftBoundary,
      TargetEmitter.unarySeparator,
      targetSuffix, reserve, ledger, inputBlanks,
      List.append_assoc] using represents
  have canonicalRun :
      workRunExact? TargetEmitterMarkedSourceReload.machine
          (TargetEmitterMarkedSourceReload.workSteps
            before.length value)
          (TargetEmitterMarkedSourceReload.entryConfiguration
            kind value before afterSource (targetSuffix target)
            reserve ledger
            (TargetEmitterCheckStack.stackWord checks)) =
        some
          (TargetEmitterMarkedSourceReload.finalConfiguration
            kind value before afterSource (targetSuffix target)
            reserve ledger
            (TargetEmitterCheckStack.stackWord checks)) := by
    cases kind with
    | input =>
        exact TargetEmitterMarkedSourceReload.input_exact value
          before afterSource (targetSuffix target) reserve ledger
          (TargetEmitterCheckStack.stackWord checks)
    | gate =>
        exact TargetEmitterMarkedSourceReload.gate_exact value
          before afterSource (targetSuffix target) reserve ledger
          (TargetEmitterCheckStack.stackWord checks)
  rcases workRunExact?_transport
      TargetEmitterMarkedSourceReload.machine
      (TargetEmitterMarkedSourceReload.workSteps before.length value)
      inputEquivalent canonicalRun with
    ⟨actualFinal, exactRun, finalEquivalent⟩
  refine ⟨actualFinal, exactRun, ?_⟩
  simpa [TargetEmitterRuntime.Represents,
    TargetEmitterRuntime.logicalConfiguration,
    TargetEmitterRuntime.logicalLeftWorkspace,
    TargetEmitterRuntime.logicalWord,
    TargetEmitterMarkedSourceReload.finalConfiguration,
    TargetEmitterMarkedSourceReload.configAtWord,
    TargetEmitterMarkedSourceReload.scratchWord,
    TargetEmitterMarkedSourceReload.sourceLeftBoundary,
    TargetEmitterSourceCapture.sourceLeftBoundary,
    TargetEmitterMarkedSourceReload.unaryUnit,
    TargetEmitterMarkedSourceReload.unarySeparator,
    TargetEmitterCheckStack.scratchWord,
    TargetEmitterCheckStack.unaryUnit,
    TargetEmitterCheckStack.unarySeparator,
    TargetEmitterCheckStack.cellBlank,
    TargetEmitterLedger.sourceLeftBoundary,
    TargetEmitterLedger.unaryUnit,
    TargetEmitterLedger.unarySeparator,
    TargetEmitterLedger.cellBlank,
    TargetEmitter.sourceLeftBoundary,
    TargetEmitter.unaryUnit,
    TargetEmitter.unarySeparator,
    targetSuffix, reserve, ledger, outputBlanks, outputBlankCons,
    List.append_assoc] using finalEquivalent

/-! ### Dynamic natural emitters -/

private theorem natLoop_naturalTokens_eq_encodeNatTokens
    (count : Nat) :
    TargetEmitterNatLoop.naturalTokens count =
      encodeNatTokens count := by
  induction count with
  | zero =>
      rfl
  | succ count inductionHypothesis =>
      change
        List.replicate (count + 1) .unit ++ [.natEnd] =
          .unit :: encodeNatTokens count
      rw [List.replicate_succ]
      change
        .unit ::
            (List.replicate count .unit ++ [.natEnd]) =
          .unit :: encodeNatTokens count
      exact congrArg (List.cons Token.unit) inductionHypothesis

/-- Emit the canonical token encoding of the current scratch natural with an
ordinary packed source, leaving the unary scratch counter unchanged. -/
theorem emitScratchNatPlain_exact (capacity count : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat)
    (sourceHead : WorkSymbol) (sourceTail : List WorkSymbol)
    (target : List Token) (actual : WorkConfiguration)
    (_countBound : count ≤ capacity)
    (sourcePacked :
      ∀ symbol, symbol ∈ sourceHead :: sourceTail →
        TargetEmitter.PackedSymbol symbol)
    (represents :
      TargetEmitterRuntime.Represents
        TargetEmitterNatLoop.startState
        capacity count registers checks
        (sourceHead :: sourceTail) target actual) :
    ∃ actualFinal,
      workRunExact? TargetEmitterNatLoop.machine
          (TargetEmitterNatLoop.loopWorkSteps
            (sourceHead :: sourceTail)
            (SourceParser.packedTokenCells target) 0 count)
          actual =
        some actualFinal ∧
      TargetEmitterRuntime.Represents
        TargetEmitterNatLoop.acceptState
        capacity count registers checks
        (sourceHead :: sourceTail)
        (target ++ encodeNatTokens count) actualFinal := by
  let outsideLeft :=
    postScratchWorkspace capacity count registers checks
  have inputEquivalent :
      WorkConfiguration.BlankEquivalent actual
        (TargetEmitterNatLoop.loopConfiguration 0 count
          (sourceHead :: sourceTail)
          (SourceParser.packedTokenCells target)
          outsideLeft []) := by
    have logicalToPadded :=
      TargetEmitterRuntime.padded_blankEquivalent_symm
        TargetEmitterNatLoop.startState
        capacity count registers checks
        (sourceHead :: sourceTail) target 0
        (TargetEmitterNatLoop.blankReserve count).length
    exact WorkConfiguration.blankEquivalent_trans represents <| by
      simpa [TargetEmitterNatLoop.loopConfiguration,
        TargetEmitterNatLoop.phaseConfiguration,
        TargetEmitterNatLoop.readyState,
        TargetEmitterNatLoop.loopCounterWord,
        TargetEmitterNatLoop.blankReserve,
        TargetEmitterNatLoop.sourceLeftBoundary,
        TargetEmitterNatLoop.sourceTargetBoundary,
        TargetEmitterNatLoop.unaryUnit,
        TargetEmitterNatLoop.unarySeparator,
        TargetEmitterRuntime.logicalLeftWorkspace,
        TargetEmitterRuntime.logicalWord,
        TargetEmitterCheckStack.scratchWord,
        TargetEmitterCheckStack.unaryUnit,
        TargetEmitterCheckStack.unarySeparator,
        TargetEmitterCheckStack.cellBlank,
        TargetEmitterLedger.sourceLeftBoundary,
        TargetEmitterLedger.unaryUnit,
        TargetEmitterLedger.unarySeparator,
        TargetEmitterLedger.cellBlank,
        TargetEmitter.sourceLeftBoundary,
        TargetEmitter.sourceTargetBoundary,
        TargetEmitter.unaryUnit,
        TargetEmitter.unarySeparator,
        outsideLeft, postScratchWorkspace, ledgerAndStack,
        List.append_assoc] using logicalToPadded
  rcases workRunExact?_transport
      TargetEmitterNatLoop.machine
      (TargetEmitterNatLoop.loopWorkSteps
        (sourceHead :: sourceTail)
        (SourceParser.packedTokenCells target) 0 count)
      inputEquivalent
      (TargetEmitterNatLoop.loop_exact 0 count sourceHead sourceTail
        (SourceParser.packedTokenCells target)
        outsideLeft [] sourcePacked
        (TargetEmitterRuntime.targetCells_packed target)) with
    ⟨actualFinal, exactRun, finalEquivalent⟩
  refine ⟨actualFinal, exactRun, ?_⟩
  have paddedToLogical :=
    TargetEmitterRuntime.padded_blankEquivalent
      TargetEmitterNatLoop.acceptState
      capacity count registers checks
      (sourceHead :: sourceTail)
      (target ++ encodeNatTokens count) 0 1
  exact WorkConfiguration.blankEquivalent_trans finalEquivalent <| by
    simpa [TargetEmitterNatLoop.cleanedConfiguration,
      TargetEmitterNatLoop.phaseConfiguration,
      TargetEmitterNatLoop.initialCounterWord,
      TargetEmitterNatLoop.sourceLeftBoundary,
      TargetEmitterNatLoop.sourceTargetBoundary,
      TargetEmitterNatLoop.unaryUnit,
      TargetEmitterNatLoop.unarySeparator,
      TargetEmitterRuntime.logicalLeftWorkspace,
      TargetEmitterRuntime.logicalWord,
      TargetEmitterCheckStack.scratchWord,
      TargetEmitterCheckStack.unaryUnit,
      TargetEmitterCheckStack.unarySeparator,
      TargetEmitterCheckStack.cellBlank,
      TargetEmitterLedger.sourceLeftBoundary,
      TargetEmitterLedger.unaryUnit,
      TargetEmitterLedger.unarySeparator,
      TargetEmitterLedger.cellBlank,
      TargetEmitter.sourceLeftBoundary,
      TargetEmitter.sourceTargetBoundary,
      TargetEmitter.unaryUnit,
      TargetEmitter.unarySeparator,
      outsideLeft, postScratchWorkspace, ledgerAndStack,
      packedTokenCells_append,
      natLoop_naturalTokens_eq_encodeNatTokens,
      List.append_assoc] using paddedToLogical

/-- Emit the current scratch natural while retaining a unique contextual
cursor in the source. -/
theorem emitScratchNatMarked_exact (capacity count : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat)
    (before after : List WorkSymbol)
    (target : List Token) (actual : WorkConfiguration)
    (_countBound : count ≤ capacity)
    (beforePacked :
      ∀ symbol, symbol ∈ before →
        TargetEmitter.PackedSymbol symbol)
    (afterPacked :
      ∀ symbol, symbol ∈ after →
        TargetEmitter.PackedSymbol symbol)
    (represents :
      TargetEmitterRuntime.Represents
        TargetEmitterCursorNatLoop.startState
        capacity count registers checks
        (TargetEmitterCursorNatLoop.markedSource before after)
        target actual) :
    ∃ actualFinal,
      workRunExact? TargetEmitterCursorNatLoop.machine
          (TargetEmitterCursorNatLoop.workSteps
            before after target count)
          actual =
        some actualFinal ∧
      TargetEmitterRuntime.Represents
        TargetEmitterCursorNatLoop.acceptState
        capacity count registers checks
        (TargetEmitterCursorNatLoop.markedSource before after)
        (target ++ encodeNatTokens count) actualFinal := by
  let source :=
    TargetEmitterCursorNatLoop.markedSource before after
  let outsideLeft :=
    postScratchWorkspace capacity count registers checks
  have inputEquivalent :
      WorkConfiguration.BlankEquivalent actual
        (TargetEmitterCursorNatLoop.entryConfiguration
          before after count target outsideLeft []) := by
    have logicalToPadded :=
      TargetEmitterRuntime.padded_blankEquivalent_symm
        TargetEmitterCursorNatLoop.startState
        capacity count registers checks source target 0
        (TargetEmitterCursorNatLoop.blankReserve count).length
    exact WorkConfiguration.blankEquivalent_trans represents <| by
      simpa [source,
        TargetEmitterCursorNatLoop.entryConfiguration,
        TargetEmitterCursorNatLoop.loopConfiguration,
        TargetEmitterCursorNatLoop.phaseConfiguration,
        TargetEmitterCursorNatLoop.readyState,
        TargetEmitterCursorNatLoop.loopCounterWord,
        TargetEmitterCursorNatLoop.blankReserve,
        TargetEmitterCursorNatLoop.sourceLeftBoundary,
        TargetEmitterCursorNatLoop.sourceTargetBoundary,
        TargetEmitterCursorNatLoop.unaryUnit,
        TargetEmitterCursorNatLoop.unarySeparator,
        TargetEmitterCursorAppender.sourceLeftBoundary,
        TargetEmitterCursorAppender.sourceTargetBoundary,
        TargetEmitterRuntime.logicalLeftWorkspace,
        TargetEmitterRuntime.logicalWord,
        TargetEmitterCheckStack.scratchWord,
        TargetEmitterCheckStack.unaryUnit,
        TargetEmitterCheckStack.unarySeparator,
        TargetEmitterCheckStack.cellBlank,
        TargetEmitterLedger.sourceLeftBoundary,
        TargetEmitterLedger.unaryUnit,
        TargetEmitterLedger.unarySeparator,
        TargetEmitterLedger.cellBlank,
        TargetEmitter.sourceLeftBoundary,
        TargetEmitter.sourceTargetBoundary,
        TargetEmitter.unaryUnit,
        TargetEmitter.unarySeparator,
        outsideLeft, postScratchWorkspace, ledgerAndStack,
        List.append_assoc] using logicalToPadded
  rcases workRunExact?_transport
      TargetEmitterCursorNatLoop.machine
      (TargetEmitterCursorNatLoop.workSteps before after target count)
      inputEquivalent
      (TargetEmitterCursorNatLoop.exact before after count target
        outsideLeft [] beforePacked afterPacked) with
    ⟨actualFinal, exactRun, finalEquivalent⟩
  refine ⟨actualFinal, exactRun, ?_⟩
  have paddedToLogical :=
    TargetEmitterRuntime.padded_blankEquivalent
      TargetEmitterCursorNatLoop.acceptState
      capacity count registers checks source
      (target ++ encodeNatTokens count) 0 1
  exact WorkConfiguration.blankEquivalent_trans finalEquivalent <| by
    simpa [source,
      TargetEmitterCursorNatLoop.finalConfiguration,
      TargetEmitterCursorNatLoop.cleanedConfiguration,
      TargetEmitterCursorNatLoop.phaseConfiguration,
      TargetEmitterCursorNatLoop.initialCounterWord,
      TargetEmitterCursorNatLoop.sourceLeftBoundary,
      TargetEmitterCursorNatLoop.sourceTargetBoundary,
      TargetEmitterCursorNatLoop.unaryUnit,
      TargetEmitterCursorNatLoop.unarySeparator,
      TargetEmitterCursorAppender.sourceLeftBoundary,
      TargetEmitterCursorAppender.sourceTargetBoundary,
      TargetEmitterRuntime.logicalLeftWorkspace,
      TargetEmitterRuntime.logicalWord,
      TargetEmitterCheckStack.scratchWord,
      TargetEmitterCheckStack.unaryUnit,
      TargetEmitterCheckStack.unarySeparator,
      TargetEmitterCheckStack.cellBlank,
      TargetEmitterLedger.sourceLeftBoundary,
      TargetEmitterLedger.unaryUnit,
      TargetEmitterLedger.unarySeparator,
      TargetEmitterLedger.cellBlank,
      TargetEmitter.sourceLeftBoundary,
      TargetEmitter.sourceTargetBoundary,
      TargetEmitter.unaryUnit,
      TargetEmitter.unarySeparator,
      outsideLeft, postScratchWorkspace, ledgerAndStack,
      List.append_assoc] using paddedToLogical

/-! ### Register comparison and increment -/

/-- The literal comparison table accepts exactly when scratch equals the
selected register and restores the complete runtime workspace. -/
theorem compareRegisterEqual_exact (slot : Slot)
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat)
    (sourceHead : WorkSymbol) (sourceTail : List WorkSymbol)
    (target : List Token) (actual : WorkConfiguration)
    (fits : LedgerFits capacity registers)
    (equal :
      scratch = TargetEmitterLedger.slotValue registers slot)
    (allowed :
      TargetEmitterScratchCompareSlot.SourceAllowed sourceHead)
    (represents :
      TargetEmitterRuntime.Represents
        (TargetEmitterScratchCompareSlot.startState slot)
        capacity scratch registers checks
        (sourceHead :: sourceTail) target actual) :
    ∃ actualFinal,
      workRunExact?
          (TargetEmitterScratchCompareSlot.machineFor slot)
          (TargetEmitterScratchCompareSlot.workSteps
            slot capacity scratch)
          actual =
        some actualFinal ∧
      TargetEmitterRuntime.Represents
        TargetEmitterScratchCompareSlot.acceptState
        capacity scratch registers checks
        (sourceHead :: sourceTail) target actualFinal := by
  have inputEquivalent :
      WorkConfiguration.BlankEquivalent actual
        (TargetEmitterScratchCompareSlot.entryConfiguration
          slot capacity scratch registers sourceHead sourceTail
          (targetSuffix target)
          (TargetEmitterCheckStack.stackWord checks)) := by
    simpa [TargetEmitterRuntime.Represents,
      TargetEmitterRuntime.logicalConfiguration,
      TargetEmitterRuntime.logicalLeftWorkspace,
      TargetEmitterRuntime.logicalWord,
      TargetEmitterScratchCompareSlot.entryConfiguration,
      TargetEmitterScratchCompareSlot.configAtWord,
      TargetEmitterScratchCompareSlot.scratchWord,
      TargetEmitterScratchAddSlot.scratchWord,
      TargetEmitterCheckStack.scratchWord,
      TargetEmitterCheckStack.unaryUnit,
      TargetEmitterCheckStack.unarySeparator,
      TargetEmitterCheckStack.cellBlank,
      TargetEmitterScratchAddSlot.unaryUnit,
      TargetEmitterScratchAddSlot.unarySeparator,
      TargetEmitterScratchCompareSlot.sourceLeftBoundary,
      TargetEmitterScratchCompareSlot.ledgerBoundary,
      TargetEmitterLedger.sourceLeftBoundary,
      TargetEmitterLedger.cellBlank,
      TargetEmitter.sourceLeftBoundary,
      targetSuffix, List.append_assoc] using represents
  rcases workRunExact?_transport
      (TargetEmitterScratchCompareSlot.machineFor slot)
      (TargetEmitterScratchCompareSlot.workSteps
        slot capacity scratch)
      inputEquivalent
      (TargetEmitterScratchCompareSlot.equal_exact
        slot capacity scratch registers sourceHead sourceTail
        (targetSuffix target)
        (TargetEmitterCheckStack.stackWord checks)
        fits
        (by simpa [TargetEmitterScratchCompareSlot.selectedValue,
          TargetEmitterScratchAddSlot.selectedValue]
          using equal)
        allowed) with
    ⟨actualFinal, exactRun, finalEquivalent⟩
  refine ⟨actualFinal, exactRun, ?_⟩
  simpa [TargetEmitterRuntime.Represents,
    TargetEmitterRuntime.logicalConfiguration,
    TargetEmitterRuntime.logicalLeftWorkspace,
    TargetEmitterRuntime.logicalWord,
    TargetEmitterScratchCompareSlot.equalConfiguration,
    TargetEmitterScratchCompareSlot.configAtWord,
    TargetEmitterScratchCompareSlot.scratchWord,
    TargetEmitterScratchAddSlot.scratchWord,
    TargetEmitterCheckStack.scratchWord,
    TargetEmitterCheckStack.unaryUnit,
    TargetEmitterCheckStack.unarySeparator,
    TargetEmitterCheckStack.cellBlank,
    TargetEmitterScratchAddSlot.unaryUnit,
    TargetEmitterScratchAddSlot.unarySeparator,
    TargetEmitterScratchCompareSlot.sourceLeftBoundary,
    TargetEmitterScratchCompareSlot.ledgerBoundary,
    TargetEmitterLedger.sourceLeftBoundary,
    TargetEmitterLedger.cellBlank,
    TargetEmitter.sourceLeftBoundary,
    targetSuffix, List.append_assoc] using finalEquivalent

/-- The literal comparison table rejects exactly when scratch is below the
selected register and restores the complete runtime workspace. -/
theorem compareRegisterLess_exact (slot : Slot)
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat)
    (sourceHead : WorkSymbol) (sourceTail : List WorkSymbol)
    (target : List Token) (actual : WorkConfiguration)
    (fits : LedgerFits capacity registers)
    (less :
      scratch < TargetEmitterLedger.slotValue registers slot)
    (allowed :
      TargetEmitterScratchCompareSlot.SourceAllowed sourceHead)
    (represents :
      TargetEmitterRuntime.Represents
        (TargetEmitterScratchCompareSlot.startState slot)
        capacity scratch registers checks
        (sourceHead :: sourceTail) target actual) :
    ∃ actualFinal,
      workRunExact?
          (TargetEmitterScratchCompareSlot.machineFor slot)
          (TargetEmitterScratchCompareSlot.workSteps
            slot capacity scratch)
          actual =
        some actualFinal ∧
      TargetEmitterRuntime.Represents
        TargetEmitterScratchCompareSlot.rejectState
        capacity scratch registers checks
        (sourceHead :: sourceTail) target actualFinal := by
  have inputEquivalent :
      WorkConfiguration.BlankEquivalent actual
        (TargetEmitterScratchCompareSlot.entryConfiguration
          slot capacity scratch registers sourceHead sourceTail
          (targetSuffix target)
          (TargetEmitterCheckStack.stackWord checks)) := by
    simpa [TargetEmitterRuntime.Represents,
      TargetEmitterRuntime.logicalConfiguration,
      TargetEmitterRuntime.logicalLeftWorkspace,
      TargetEmitterRuntime.logicalWord,
      TargetEmitterScratchCompareSlot.entryConfiguration,
      TargetEmitterScratchCompareSlot.configAtWord,
      TargetEmitterScratchCompareSlot.scratchWord,
      TargetEmitterScratchAddSlot.scratchWord,
      TargetEmitterCheckStack.scratchWord,
      TargetEmitterCheckStack.unaryUnit,
      TargetEmitterCheckStack.unarySeparator,
      TargetEmitterCheckStack.cellBlank,
      TargetEmitterScratchAddSlot.unaryUnit,
      TargetEmitterScratchAddSlot.unarySeparator,
      TargetEmitterScratchCompareSlot.sourceLeftBoundary,
      TargetEmitterScratchCompareSlot.ledgerBoundary,
      TargetEmitterLedger.sourceLeftBoundary,
      TargetEmitterLedger.cellBlank,
      TargetEmitter.sourceLeftBoundary,
      targetSuffix, List.append_assoc] using represents
  rcases workRunExact?_transport
      (TargetEmitterScratchCompareSlot.machineFor slot)
      (TargetEmitterScratchCompareSlot.workSteps
        slot capacity scratch)
      inputEquivalent
      (TargetEmitterScratchCompareSlot.less_exact
        slot capacity scratch registers sourceHead sourceTail
        (targetSuffix target)
        (TargetEmitterCheckStack.stackWord checks)
        fits
        (by simpa [TargetEmitterScratchCompareSlot.selectedValue,
          TargetEmitterScratchAddSlot.selectedValue]
          using less)
        allowed) with
    ⟨actualFinal, exactRun, finalEquivalent⟩
  refine ⟨actualFinal, exactRun, ?_⟩
  simpa [TargetEmitterRuntime.Represents,
    TargetEmitterRuntime.logicalConfiguration,
    TargetEmitterRuntime.logicalLeftWorkspace,
    TargetEmitterRuntime.logicalWord,
    TargetEmitterScratchCompareSlot.lessConfiguration,
    TargetEmitterScratchCompareSlot.configAtWord,
    TargetEmitterScratchCompareSlot.scratchWord,
    TargetEmitterScratchAddSlot.scratchWord,
    TargetEmitterCheckStack.scratchWord,
    TargetEmitterCheckStack.unaryUnit,
    TargetEmitterCheckStack.unarySeparator,
    TargetEmitterCheckStack.cellBlank,
    TargetEmitterScratchAddSlot.unaryUnit,
    TargetEmitterScratchAddSlot.unarySeparator,
    TargetEmitterScratchCompareSlot.sourceLeftBoundary,
    TargetEmitterScratchCompareSlot.ledgerBoundary,
    TargetEmitterLedger.sourceLeftBoundary,
    TargetEmitterLedger.cellBlank,
    TargetEmitter.sourceLeftBoundary,
    targetSuffix, List.append_assoc] using finalEquivalent

/-- Increment exactly one selected fixed-capacity unary register while
preserving scratch, checks, source, and target. -/
theorem incrementRegister_exact (slot : Slot)
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat)
    (sourceHead : WorkSymbol) (sourceTail : List WorkSymbol)
    (target : List Token) (actual : WorkConfiguration)
    (fits : LedgerFits capacity registers)
    (available :
      TargetEmitterLedger.slotValue registers slot < capacity)
    (allowed :
      TargetEmitter.PackedSymbol sourceHead ∨
        sourceHead = TargetEmitterCursorAppender.cursorMarker)
    (represents :
      TargetEmitterRuntime.Represents
        (TargetEmitterSlotIncrement.startState slot)
        capacity scratch registers checks
        (sourceHead :: sourceTail) target actual) :
    ∃ actualFinal,
      workRunExact? (TargetEmitterSlotIncrement.machineFor slot)
          (TargetEmitterSlotIncrement.workSteps slot scratch
            (capacity - scratch)
            (slotBankOfRegisters capacity registers))
          actual =
        some actualFinal ∧
      TargetEmitterRuntime.Represents
        TargetEmitterSlotIncrement.acceptState
        capacity scratch (incrementRegisters slot registers) checks
        (sourceHead :: sourceTail) target actualFinal := by
  let bank := slotBankOfRegisters capacity registers
  have bankWord :
      bank.word =
        TargetEmitterLedger.slotBank capacity registers := by
    exact slotBankOfRegisters_word capacity registers fits
  have capacityAvailable :
      0 < (bank.selected slot).remaining := by
    rw [slotBankOfRegisters_selected_remaining]
    omega
  have updatedFits :
      LedgerFits capacity (incrementRegisters slot registers) :=
    incrementRegisters_fits capacity registers slot fits available
  have updatedBankWord :
      (bank.increment slot).word =
        TargetEmitterLedger.slotBank capacity
          (incrementRegisters slot registers) := by
    rw [slotBankOfRegisters_increment capacity registers
      slot available]
    exact slotBankOfRegisters_word capacity
      (incrementRegisters slot registers) updatedFits
  have inputEquivalent :
      WorkConfiguration.BlankEquivalent actual
        (TargetEmitterSlotIncrement.entryConfiguration slot scratch
          (capacity - scratch) bank
          (TargetEmitterCheckStack.stackWord checks)
          sourceHead sourceTail (targetSuffix target)) := by
    simpa [TargetEmitterRuntime.Represents,
      TargetEmitterRuntime.logicalConfiguration,
      TargetEmitterRuntime.logicalLeftWorkspace,
      TargetEmitterRuntime.logicalWord,
      TargetEmitterSlotIncrement.entryConfiguration,
      TargetEmitterSlotIncrement.configAtWord,
      TargetEmitterSlotIncrement.scratchWord,
      TargetEmitterCheckStack.scratchWord,
      TargetEmitterCheckStack.unaryUnit,
      TargetEmitterCheckStack.unarySeparator,
      TargetEmitterCheckStack.cellBlank,
      TargetEmitterSlotIncrement.unaryUnit,
      TargetEmitterSlotIncrement.unarySeparator,
      TargetEmitterSlotIncrement.sourceLeftBoundary,
      TargetEmitterSlotIncrement.ledgerBoundary,
      TargetEmitterLedger.sourceLeftBoundary,
      TargetEmitterLedger.unaryUnit,
      TargetEmitterLedger.unarySeparator,
      TargetEmitterLedger.cellBlank,
      TargetEmitter.sourceLeftBoundary,
      TargetEmitter.unaryUnit,
      TargetEmitter.unarySeparator,
      bankWord, targetSuffix, List.append_assoc] using represents
  rcases workRunExact?_transport
      (TargetEmitterSlotIncrement.machineFor slot)
      (TargetEmitterSlotIncrement.workSteps slot scratch
        (capacity - scratch) bank)
      inputEquivalent
      (TargetEmitterSlotIncrement.exact slot scratch
        (capacity - scratch) bank
        (TargetEmitterCheckStack.stackWord checks)
        sourceHead sourceTail (targetSuffix target)
        capacityAvailable allowed) with
    ⟨actualFinal, exactRun, finalEquivalent⟩
  refine ⟨actualFinal, exactRun, ?_⟩
  simpa [TargetEmitterRuntime.Represents,
    TargetEmitterRuntime.logicalConfiguration,
    TargetEmitterRuntime.logicalLeftWorkspace,
    TargetEmitterRuntime.logicalWord,
    TargetEmitterSlotIncrement.finalConfiguration,
    TargetEmitterSlotIncrement.configAtWord,
    TargetEmitterSlotIncrement.scratchWord,
    TargetEmitterCheckStack.scratchWord,
    TargetEmitterCheckStack.unaryUnit,
    TargetEmitterCheckStack.unarySeparator,
    TargetEmitterCheckStack.cellBlank,
    TargetEmitterSlotIncrement.unaryUnit,
    TargetEmitterSlotIncrement.unarySeparator,
    TargetEmitterSlotIncrement.sourceLeftBoundary,
    TargetEmitterSlotIncrement.ledgerBoundary,
    TargetEmitterLedger.sourceLeftBoundary,
    TargetEmitterLedger.unaryUnit,
    TargetEmitterLedger.unarySeparator,
    TargetEmitterLedger.cellBlank,
    TargetEmitter.sourceLeftBoundary,
    TargetEmitter.unaryUnit,
    TargetEmitter.unarySeparator,
    updatedBankWord, targetSuffix,
    List.append_assoc] using finalEquivalent

end PNP.Concrete.LockedNAND.TargetEmitterRuntimePrimitives
