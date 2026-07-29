/-
Copyright (c) 2026 PNP Labs.

Runtime adapters for literal retained-source capture and cursor restoration.

Source capture begins at one canonical field after a packed prefix and
rewinds to the first retained source cell.  Cursor restoration begins at the
first retained source cell and advances to the cell following the restored
cursor.  `SourceFocusRepresents` records exactly those noncanonical head
positions while preserving the same logical scratch, ledger, stack, source,
and target workspace.
-/

import PNP.Concrete.LockedNANDTargetEmitterRuntime
import PNP.Concrete.LockedNANDTargetEmitterSourceCapture
import PNP.Concrete.LockedNANDTargetEmitterCursorControl

namespace PNP.Concrete.LockedNAND.TargetEmitterRuntimeSourceControl

open PNP.Concrete

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

/-- Canonical logical workspace with the head positioned after `crossed` and
before `remainingSource`.  The complete retained source is
`crossed ++ remainingSource`. -/
def sourceFocusConfiguration (state capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (crossed remainingSource : List WorkSymbol)
    (target : List Token) : WorkConfiguration :=
  TargetEmitter.configAtWord state
    (crossed.reverse ++
      TargetEmitterRuntime.logicalLeftWorkspace
        capacity scratch registers checks)
    (remainingSource ++ targetSuffix target)

/-- Blank-insensitive runtime invariant at a retained-source focus. -/
def SourceFocusRepresents (state capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (crossed remainingSource : List WorkSymbol)
    (target : List Token) (actual : WorkConfiguration) : Prop :=
  WorkConfiguration.BlankEquivalent actual
    (sourceFocusConfiguration state capacity scratch registers checks
      crossed remainingSource target)

private theorem targetEmitter_configAtWord_state
    (state : Nat) (left word : List WorkSymbol) :
    (TargetEmitter.configAtWord state left word).state = state := by
  cases word <;> rfl

private theorem sourceCapture_configAtWord_eq
    (state : Nat) (left word : List WorkSymbol) :
    TargetEmitterSourceCapture.configAtWord state left word =
      TargetEmitter.configAtWord state left word := by
  cases word <;> rfl

private theorem cursorControl_configAtWord_eq
    (state : Nat) (left word : List WorkSymbol) :
    TargetEmitterCursorControl.configAtWord state left word =
      TargetEmitter.configAtWord state left word := by
  cases word <;> rfl

theorem SourceFocusRepresents.state_eq
    {state capacity scratch : Nat}
    {registers : TargetEmitter.UnaryRegisters}
    {checks : List Nat}
    {crossed remainingSource : List WorkSymbol}
    {target : List Token} {actual : WorkConfiguration}
    (represents :
      SourceFocusRepresents state capacity scratch registers checks
        crossed remainingSource target actual) :
    actual.state = state := by
  exact represents.state.trans
    (targetEmitter_configAtWord_state state
      (crossed.reverse ++
        TargetEmitterRuntime.logicalLeftWorkspace
          capacity scratch registers checks)
      (remainingSource ++ targetSuffix target))

theorem sourceFocusRepresents_nil_iff
    (state capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (source : List WorkSymbol)
    (target : List Token) (actual : WorkConfiguration) :
    SourceFocusRepresents state capacity scratch registers checks
        [] source target actual ↔
      TargetEmitterRuntime.Represents
        state capacity scratch registers checks source target actual := by
  simp [SourceFocusRepresents, sourceFocusConfiguration,
    TargetEmitterRuntime.Represents,
    TargetEmitterRuntime.logicalConfiguration,
    TargetEmitterRuntime.logicalWord, targetSuffix]

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

/-! ### Source capture -/

/-- Capture an input or gate natural from the focused source field, add its
value to scratch, install the unique contextual cursor, and rewind to the
first retained source cell.

The extra `+ 1` in `capacityBound` is the blank that the literal controller
must observe after the final unary increment. -/
theorem captureNatural_exact
    (kind : TargetEmitterSourceCapture.NatKind)
    (capacity scratch value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat)
    (before afterSource : List WorkSymbol)
    (target : List Token) (actual : WorkConfiguration)
    (capacityBound : scratch + value + 1 ≤ capacity)
    (beforePacked :
      ∀ symbol, symbol ∈ before →
        TargetEmitter.PackedSymbol symbol)
    (represents :
      SourceFocusRepresents
        TargetEmitterSourceCapture.startState
        capacity scratch registers checks before
        (TargetEmitterSourceCapture.sourceCells
            kind.sourceKind value ++ afterSource)
        target actual) :
    ∃ actualFinal,
      workRunExact?
          (TargetEmitterSourceCapture.machine kind.sourceKind)
          (TargetEmitterSourceCapture.naturalWorkSteps
            before.length scratch value)
          actual =
        some actualFinal ∧
      TargetEmitterRuntime.Represents
        TargetEmitterSourceCapture.acceptState
        capacity (scratch + value) registers checks
        (before ++
          TargetEmitterSourceCapture.markedSourceCells
            kind.sourceKind value ++ afterSource)
        target actualFinal := by
  let reserveCount := capacity - (scratch + value + 1)
  let reserve :=
    List.replicate reserveCount WorkSymbol.blank
  have inputCount :
      value + 1 + reserveCount = capacity - scratch := by
    unfold reserveCount
    omega
  have outputCount :
      1 + reserveCount = capacity - (scratch + value) := by
    unfold reserveCount
    omega
  have inputBlanks :
      List.replicate (value + 1) WorkSymbol.blank ++ reserve =
        List.replicate (capacity - scratch) WorkSymbol.blank := by
    rw [← replicate_add, inputCount]
  have outputBlanks :
      List.replicate 1 WorkSymbol.blank ++ reserve =
        List.replicate
          (capacity - (scratch + value)) WorkSymbol.blank := by
    rw [← replicate_add, outputCount]
  have outputBlankCons :
      WorkSymbol.blank :: reserve =
        List.replicate
          (capacity - (scratch + value)) WorkSymbol.blank := by
    simpa using outputBlanks
  have inputEquivalent :
      WorkConfiguration.BlankEquivalent actual
        (TargetEmitterSourceCapture.entryConfiguration
          kind.sourceKind value scratch before
          (afterSource ++ targetSuffix target)
          reserve (ledgerAndStack capacity registers checks)) := by
    simpa [SourceFocusRepresents, sourceFocusConfiguration,
      TargetEmitterRuntime.logicalLeftWorkspace,
      TargetEmitterSourceCapture.entryConfiguration,
      sourceCapture_configAtWord_eq,
      TargetEmitterSourceCapture.scratchWord,
      TargetEmitterSourceCapture.sourceLeftBoundary,
      TargetEmitterSourceCapture.unaryUnit,
      TargetEmitterSourceCapture.unarySeparator,
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
      targetSuffix, reserve, ledgerAndStack, inputBlanks,
      List.append_assoc] using represents
  have canonicalRun :
      workRunExact?
          (TargetEmitterSourceCapture.machine kind.sourceKind)
          (TargetEmitterSourceCapture.naturalWorkSteps
            before.length scratch value)
          (TargetEmitterSourceCapture.entryConfiguration
            kind.sourceKind value scratch before
            (afterSource ++ targetSuffix target)
            reserve (ledgerAndStack capacity registers checks)) =
        some
          (TargetEmitterSourceCapture.finalConfiguration
            kind.sourceKind value scratch before
            (afterSource ++ targetSuffix target)
            reserve (ledgerAndStack capacity registers checks)) := by
    cases kind with
    | input =>
        exact TargetEmitterSourceCapture.input_exact
          value scratch before
          (afterSource ++ targetSuffix target)
          reserve (ledgerAndStack capacity registers checks)
          beforePacked
    | gate =>
        exact TargetEmitterSourceCapture.gate_exact
          value scratch before
          (afterSource ++ targetSuffix target)
          reserve (ledgerAndStack capacity registers checks)
          beforePacked
  rcases workRunExact?_transport
      (TargetEmitterSourceCapture.machine kind.sourceKind)
      (TargetEmitterSourceCapture.naturalWorkSteps
        before.length scratch value)
      inputEquivalent canonicalRun with
    ⟨actualFinal, exactRun, finalEquivalent⟩
  refine ⟨actualFinal, exactRun, ?_⟩
  simpa [TargetEmitterRuntime.Represents,
    TargetEmitterRuntime.logicalConfiguration,
    TargetEmitterRuntime.logicalLeftWorkspace,
    TargetEmitterRuntime.logicalWord,
    TargetEmitterSourceCapture.finalConfiguration,
    sourceCapture_configAtWord_eq,
    TargetEmitterSourceCapture.scratchWord,
    TargetEmitterSourceCapture.sourceLeftBoundary,
    TargetEmitterSourceCapture.unaryUnit,
    TargetEmitterSourceCapture.unarySeparator,
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
    targetSuffix, reserve, ledgerAndStack, outputBlankCons,
    List.append_assoc] using finalEquivalent

private theorem captureConstant_exact
    (kind : TargetEmitterSourceCapture.SourceKind)
    (constantKind :
      kind = .constantFalse ∨ kind = .constantTrue)
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat)
    (before afterSource : List WorkSymbol)
    (target : List Token) (actual : WorkConfiguration)
    (capacityBound : scratch + 1 ≤ capacity)
    (beforePacked :
      ∀ symbol, symbol ∈ before →
        TargetEmitter.PackedSymbol symbol)
    (represents :
      SourceFocusRepresents
        TargetEmitterSourceCapture.startState
        capacity scratch registers checks before
        (TargetEmitterSourceCapture.sourceCells kind 0 ++ afterSource)
        target actual) :
    ∃ actualFinal,
      workRunExact? (TargetEmitterSourceCapture.machine kind)
          (TargetEmitterSourceCapture.constantWorkSteps before.length)
          actual =
        some actualFinal ∧
      TargetEmitterRuntime.Represents
        TargetEmitterSourceCapture.acceptState
        capacity scratch registers checks
        (before ++
          TargetEmitterSourceCapture.markedSourceCells kind 0 ++
          afterSource)
        target actualFinal := by
  let reserveCount := capacity - (scratch + 1)
  let reserve :=
    List.replicate reserveCount WorkSymbol.blank
  have blankCount :
      1 + reserveCount = capacity - scratch := by
    unfold reserveCount
    omega
  have blankJoin :
      WorkSymbol.blank :: reserve =
        List.replicate (capacity - scratch) WorkSymbol.blank := by
    have joined :
        List.replicate 1 WorkSymbol.blank ++ reserve =
          List.replicate (capacity - scratch) WorkSymbol.blank := by
      rw [← replicate_add, blankCount]
    simpa using joined
  have inputEquivalent :
      WorkConfiguration.BlankEquivalent actual
        (TargetEmitterSourceCapture.entryConfiguration
          kind 0 scratch before
          (afterSource ++ targetSuffix target)
          reserve (ledgerAndStack capacity registers checks)) := by
    simpa [SourceFocusRepresents, sourceFocusConfiguration,
      TargetEmitterRuntime.logicalLeftWorkspace,
      TargetEmitterSourceCapture.entryConfiguration,
      sourceCapture_configAtWord_eq,
      TargetEmitterSourceCapture.scratchWord,
      TargetEmitterSourceCapture.sourceLeftBoundary,
      TargetEmitterSourceCapture.unaryUnit,
      TargetEmitterSourceCapture.unarySeparator,
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
      targetSuffix, reserve, ledgerAndStack, blankJoin,
      List.append_assoc] using represents
  have canonicalRun :
      workRunExact? (TargetEmitterSourceCapture.machine kind)
          (TargetEmitterSourceCapture.constantWorkSteps before.length)
          (TargetEmitterSourceCapture.entryConfiguration
            kind 0 scratch before
            (afterSource ++ targetSuffix target)
            reserve (ledgerAndStack capacity registers checks)) =
        some
          (TargetEmitterSourceCapture.finalConfiguration
            kind 0 scratch before
            (afterSource ++ targetSuffix target)
            reserve (ledgerAndStack capacity registers checks)) := by
    rcases constantKind with kindFalse | kindTrue
    · subst kind
      exact TargetEmitterSourceCapture.constantFalse_exact
        scratch before (afterSource ++ targetSuffix target)
        reserve (ledgerAndStack capacity registers checks)
        beforePacked
    · subst kind
      exact TargetEmitterSourceCapture.constantTrue_exact
        scratch before (afterSource ++ targetSuffix target)
        reserve (ledgerAndStack capacity registers checks)
        beforePacked
  rcases workRunExact?_transport
      (TargetEmitterSourceCapture.machine kind)
      (TargetEmitterSourceCapture.constantWorkSteps before.length)
      inputEquivalent canonicalRun with
    ⟨actualFinal, exactRun, finalEquivalent⟩
  refine ⟨actualFinal, exactRun, ?_⟩
  simpa [TargetEmitterRuntime.Represents,
    TargetEmitterRuntime.logicalConfiguration,
    TargetEmitterRuntime.logicalLeftWorkspace,
    TargetEmitterRuntime.logicalWord,
    TargetEmitterSourceCapture.finalConfiguration,
    sourceCapture_configAtWord_eq,
    TargetEmitterSourceCapture.scratchWord,
    TargetEmitterSourceCapture.sourceLeftBoundary,
    TargetEmitterSourceCapture.unaryUnit,
    TargetEmitterSourceCapture.unarySeparator,
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
    targetSuffix, reserve, ledgerAndStack, blankJoin,
    List.append_assoc] using finalEquivalent

theorem captureConstantFalse_exact
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat)
    (before afterSource : List WorkSymbol)
    (target : List Token) (actual : WorkConfiguration)
    (capacityBound : scratch + 1 ≤ capacity)
    (beforePacked :
      ∀ symbol, symbol ∈ before →
        TargetEmitter.PackedSymbol symbol)
    (represents :
      SourceFocusRepresents
        TargetEmitterSourceCapture.startState
        capacity scratch registers checks before
        (TargetEmitterSourceCapture.sourceCells .constantFalse 0 ++
          afterSource)
        target actual) :
    ∃ actualFinal,
      workRunExact?
          (TargetEmitterSourceCapture.machine .constantFalse)
          (TargetEmitterSourceCapture.constantWorkSteps before.length)
          actual =
        some actualFinal ∧
      TargetEmitterRuntime.Represents
        TargetEmitterSourceCapture.acceptState
        capacity scratch registers checks
        (before ++
          TargetEmitterSourceCapture.markedSourceCells
            .constantFalse 0 ++ afterSource)
        target actualFinal := by
  exact captureConstant_exact .constantFalse (Or.inl rfl)
    capacity scratch registers checks before afterSource target actual
    capacityBound beforePacked represents

theorem captureConstantTrue_exact
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat)
    (before afterSource : List WorkSymbol)
    (target : List Token) (actual : WorkConfiguration)
    (capacityBound : scratch + 1 ≤ capacity)
    (beforePacked :
      ∀ symbol, symbol ∈ before →
        TargetEmitter.PackedSymbol symbol)
    (represents :
      SourceFocusRepresents
        TargetEmitterSourceCapture.startState
        capacity scratch registers checks before
        (TargetEmitterSourceCapture.sourceCells .constantTrue 0 ++
          afterSource)
        target actual) :
    ∃ actualFinal,
      workRunExact?
          (TargetEmitterSourceCapture.machine .constantTrue)
          (TargetEmitterSourceCapture.constantWorkSteps before.length)
          actual =
        some actualFinal ∧
      TargetEmitterRuntime.Represents
        TargetEmitterSourceCapture.acceptState
        capacity scratch registers checks
        (before ++
          TargetEmitterSourceCapture.markedSourceCells
            .constantTrue 0 ++ afterSource)
        target actualFinal := by
  exact captureConstant_exact .constantTrue (Or.inr rfl)
    capacity scratch registers checks before afterSource target actual
    capacityBound beforePacked represents

/-! ### Cursor restoration -/

/-- Restore the statically selected packed source cell and advance the head
to the following source position. -/
theorem restoreCursor_exact (original : WorkSymbol)
    (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat)
    (before afterSource : List WorkSymbol)
    (target : List Token) (actual : WorkConfiguration)
    (prefixPacked :
      ∀ symbol, symbol ∈ before →
        TargetEmitter.PackedSymbol symbol)
    (represents :
      TargetEmitterRuntime.Represents
        TargetEmitterCursorControl.restoreState
        capacity scratch registers checks
        (before ++ TargetEmitterCursorControl.cursorMark :: afterSource)
        target actual) :
    ∃ actualFinal,
      workRunExact?
          (TargetEmitterCursorControl.restoreMachine original)
          (before.length + 1) actual =
        some actualFinal ∧
      SourceFocusRepresents
        TargetEmitterCursorControl.restoredState
        capacity scratch registers checks
        (before ++ [original]) afterSource target actualFinal := by
  have inputEquivalent :
      WorkConfiguration.BlankEquivalent actual
        (TargetEmitterCursorControl.configAtWord
          TargetEmitterCursorControl.restoreState
          (TargetEmitter.sourceLeftBoundary ::
            fixedWorkspace capacity scratch registers checks)
          (before ++
            TargetEmitterCursorControl.cursorMark ::
              (afterSource ++ targetSuffix target))) := by
    simpa [TargetEmitterRuntime.Represents,
      TargetEmitterRuntime.logicalConfiguration,
      TargetEmitterRuntime.logicalLeftWorkspace,
      TargetEmitterRuntime.logicalWord,
      cursorControl_configAtWord_eq,
      targetSuffix, fixedWorkspace,
      List.append_assoc] using represents
  rcases workRunExact?_transport
      (TargetEmitterCursorControl.restoreMachine original)
      (before.length + 1)
      inputEquivalent
      (TargetEmitterCursorControl.restore_exact original before
        (afterSource ++ targetSuffix target)
        (fixedWorkspace capacity scratch registers checks)
        prefixPacked) with
    ⟨actualFinal, exactRun, finalEquivalent⟩
  refine ⟨actualFinal, exactRun, ?_⟩
  simpa [SourceFocusRepresents, sourceFocusConfiguration,
    TargetEmitterRuntime.logicalLeftWorkspace,
    cursorControl_configAtWord_eq,
    targetSuffix, fixedWorkspace,
    List.reverse_append, List.append_assoc] using finalEquivalent

end PNP.Concrete.LockedNAND.TargetEmitterRuntimeSourceControl
