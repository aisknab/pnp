/-
Copyright (c) 2026 PNP Labs.

Controller-facing exact adapters for the locked-NAND runtime check stack.

The literal stack machines use finite tape windows, while the surrounding
controller carries `TargetEmitterRuntime.Represents`, which denotes the same
infinite blank tape independently of the materialized exterior.  This module
bridges exactly those two interfaces for stack initialization, push, and the
two pop outcomes.  It does not interpret a plan, select a semantic branch, or
construct the whole controller trace.
-/

import PNP.Concrete.LockedNANDTargetEmitterRuntime
import PNP.Concrete.LockedNANDTargetEmitterController

namespace PNP.Concrete.LockedNAND.TargetEmitterRuntimeCheckStack

open PNP.Concrete
open WorkMachineProgramGraph
open WorkMachineProgramPath

namespace CheckStack

abbrev LedgerFits :=
  TargetEmitterCheckStack.LedgerFits

def targetSuffix (target : List Token) : List WorkSymbol :=
  TargetEmitter.sourceTargetBoundary ::
    SourceParser.packedTokenCells target

/-- Canonical pre-initialization workspace.  Its final stack cell is blank;
after `Initialize` it becomes the logical empty-stack end marker. -/
def initializeLogicalConfiguration (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol) (sourceTail : List WorkSymbol)
    (target : List Token) : WorkConfiguration :=
  TargetEmitterCheckStack.Initialize.entryConfiguration
    capacity scratch registers sourceHead sourceTail
    (targetSuffix target) []

/-- Representation invariant at the one exceptional runtime point before
the empty stack end marker has been installed. -/
def InitializeRepresents (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol) (sourceTail : List WorkSymbol)
    (target : List Token) (actual : WorkConfiguration) : Prop :=
  WorkConfiguration.BlankEquivalent actual
    (initializeLogicalConfiguration capacity scratch registers
      sourceHead sourceTail target)

theorem InitializeRepresents.state_eq
    {capacity scratch : Nat}
    {registers : TargetEmitter.UnaryRegisters}
    {sourceHead : WorkSymbol} {sourceTail : List WorkSymbol}
    {target : List Token} {actual : WorkConfiguration}
    (represents :
      InitializeRepresents capacity scratch registers
        sourceHead sourceTail target actual) :
    actual.state =
      TargetEmitterCheckStack.Initialize.startState := by
  exact represents.state

/-- Initialize the canonical empty dynamic stack and return to the common
runtime representation. -/
theorem initialize_exact (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol) (sourceTail : List WorkSymbol)
    (target : List Token) (actual : WorkConfiguration)
    (fits : LedgerFits capacity registers)
    (scratchBound : scratch ≤ capacity)
    (allowed : TargetEmitterCheckStack.sourceAllowed sourceHead)
    (represents :
      InitializeRepresents capacity scratch registers
        sourceHead sourceTail target actual) :
    ∃ actualFinal,
      workRunExact? TargetEmitterCheckStack.Initialize.machine
          (TargetEmitterCheckStack.Initialize.workSteps capacity)
          actual =
        some actualFinal ∧
      TargetEmitterRuntime.Represents
        TargetEmitterCheckStack.Initialize.acceptState
        capacity scratch registers []
        (sourceHead :: sourceTail) target actualFinal := by
  rcases workRunExact?_transport
      TargetEmitterCheckStack.Initialize.machine
      (TargetEmitterCheckStack.Initialize.workSteps capacity)
      represents
      (TargetEmitterCheckStack.Initialize.exact
        capacity scratch registers sourceHead sourceTail
        (targetSuffix target) [] fits scratchBound allowed) with
    ⟨actualFinal, exactRun, finalEquivalent⟩
  refine ⟨actualFinal, exactRun, ?_⟩
  simpa [TargetEmitterRuntime.Represents,
    TargetEmitterRuntime.logicalConfiguration,
    TargetEmitterRuntime.logicalLeftWorkspace,
    TargetEmitterRuntime.logicalWord,
    TargetEmitterCheckStack.Initialize.finalConfiguration,
    TargetEmitterCheckStack.configAtWord, targetSuffix,
    TargetEmitterCheckStack.sourceLeftBoundary,
    TargetEmitterLedger.sourceLeftBoundary,
    TargetEmitterCheckStack.ledgerBoundary,
    List.append_assoc] using finalEquivalent

/-- Copy the current scratch value onto the far end of the logical check
stack, preserving scratch and all fixed ledger slots. -/
theorem push_exact (capacity value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat)
    (sourceHead : WorkSymbol) (sourceTail : List WorkSymbol)
    (target : List Token) (actual : WorkConfiguration)
    (fits : LedgerFits capacity registers)
    (valueBound : value ≤ capacity)
    (allowed : TargetEmitterCheckStack.sourceAllowed sourceHead)
    (represents :
      TargetEmitterRuntime.Represents
        TargetEmitterCheckStack.Push.startState
        capacity value registers checks
        (sourceHead :: sourceTail) target actual) :
    ∃ actualFinal,
      workRunExact? TargetEmitterCheckStack.Push.machine
          (TargetEmitterCheckStack.Push.workSteps capacity
            (TargetEmitterCheckStack.recordsWord checks).length value)
          actual =
        some actualFinal ∧
      TargetEmitterRuntime.Represents
        TargetEmitterCheckStack.Push.acceptState
        capacity value registers (checks ++ [value])
        (sourceHead :: sourceTail) target actualFinal := by
  have logicalToPadded :
      WorkConfiguration.BlankEquivalent
        (TargetEmitterRuntime.logicalConfiguration
          TargetEmitterCheckStack.Push.startState
          capacity value registers checks
          (sourceHead :: sourceTail) target)
        (TargetEmitterCheckStack.Push.entryConfiguration
          capacity value registers checks sourceHead sourceTail
          (targetSuffix target) []) := by
    simpa [TargetEmitterRuntime.logicalConfiguration,
      TargetEmitterRuntime.logicalLeftWorkspace,
      TargetEmitterRuntime.logicalWord,
      TargetEmitterCheckStack.Push.sparseEntryConfiguration,
      TargetEmitterCheckStack.configAtWord, targetSuffix,
      TargetEmitterCheckStack.sourceLeftBoundary,
      TargetEmitterLedger.sourceLeftBoundary,
      TargetEmitterCheckStack.ledgerBoundary,
      List.append_assoc] using
      (TargetEmitterCheckStack.Push.sparse_entry_blankEquivalent
        capacity value registers checks sourceHead sourceTail
        (targetSuffix target) []
        TargetEmitterCheckStack.blankTail_nil)
  have inputEquivalent :
      WorkConfiguration.BlankEquivalent actual
        (TargetEmitterCheckStack.Push.entryConfiguration
          capacity value registers checks sourceHead sourceTail
          (targetSuffix target) []) :=
    WorkConfiguration.blankEquivalent_trans
      represents logicalToPadded
  rcases
      TargetEmitterCheckStack.Push.exact_of_blankEquivalent_entry
        capacity value registers checks sourceHead sourceTail
        (targetSuffix target) [] fits valueBound allowed
        actual inputEquivalent with
    ⟨actualFinal, exactRun, finalEquivalent⟩
  refine ⟨actualFinal, exactRun, ?_⟩
  simpa [TargetEmitterRuntime.Represents,
    TargetEmitterRuntime.logicalConfiguration,
    TargetEmitterRuntime.logicalLeftWorkspace,
    TargetEmitterRuntime.logicalWord,
    TargetEmitterCheckStack.Push.finalConfiguration,
    TargetEmitterCheckStack.configAtWord, targetSuffix,
    TargetEmitterCheckStack.sourceLeftBoundary,
    TargetEmitterLedger.sourceLeftBoundary,
    TargetEmitterCheckStack.ledgerBoundary,
    List.append_assoc] using finalEquivalent

/-- Reject an empty logical stack without changing scratch, registers,
source, target, or the empty stack. -/
theorem pop_empty_exact (capacity : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol) (sourceTail : List WorkSymbol)
    (target : List Token) (actual : WorkConfiguration)
    (fits : LedgerFits capacity registers)
    (allowed : TargetEmitterCheckStack.sourceAllowed sourceHead)
    (represents :
      TargetEmitterRuntime.Represents
        TargetEmitterCheckStack.Pop.startState
        capacity 0 registers []
        (sourceHead :: sourceTail) target actual) :
    ∃ actualFinal,
      workRunExact? TargetEmitterCheckStack.Pop.machine
          (TargetEmitterCheckStack.Pop.emptyWorkSteps capacity)
          actual =
        some actualFinal ∧
      TargetEmitterRuntime.Represents
        TargetEmitterCheckStack.Pop.rejectState
        capacity 0 registers []
        (sourceHead :: sourceTail) target actualFinal := by
  have inputEquivalent :
      WorkConfiguration.BlankEquivalent actual
        (TargetEmitterCheckStack.Pop.entryConfiguration
          capacity registers [] sourceHead sourceTail
          (targetSuffix target) []) := by
    simpa [TargetEmitterRuntime.Represents,
      TargetEmitterRuntime.logicalConfiguration,
      TargetEmitterRuntime.logicalLeftWorkspace,
      TargetEmitterRuntime.logicalWord,
      TargetEmitterCheckStack.Pop.entryConfiguration,
      TargetEmitterCheckStack.configAtWord, targetSuffix,
      TargetEmitterCheckStack.sourceLeftBoundary,
      TargetEmitterLedger.sourceLeftBoundary,
      TargetEmitterCheckStack.ledgerBoundary,
      List.append_assoc] using represents
  rcases
      TargetEmitterCheckStack.Pop.empty_exact_of_blankEquivalent_entry
        capacity registers sourceHead sourceTail
        (targetSuffix target) [] fits allowed actual inputEquivalent with
    ⟨actualFinal, exactRun, finalEquivalent⟩
  refine ⟨actualFinal, exactRun, ?_⟩
  simpa [TargetEmitterRuntime.Represents,
    TargetEmitterRuntime.logicalConfiguration,
    TargetEmitterRuntime.logicalLeftWorkspace,
    TargetEmitterRuntime.logicalWord,
    TargetEmitterCheckStack.Pop.emptyFinalConfiguration,
    TargetEmitterCheckStack.configAtWord, targetSuffix,
    TargetEmitterCheckStack.sourceLeftBoundary,
    TargetEmitterLedger.sourceLeftBoundary,
    TargetEmitterCheckStack.ledgerBoundary,
    List.append_assoc] using finalEquivalent

/-- Pop the newest logical record into zero scratch.  The reclaimed record
cells remain only as a finite blank window and are hidden by `Represents`. -/
theorem pop_nonempty_exact (capacity value : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (prior : List Nat)
    (sourceHead : WorkSymbol) (sourceTail : List WorkSymbol)
    (target : List Token) (actual : WorkConfiguration)
    (fits : LedgerFits capacity registers)
    (valueBound : value ≤ capacity)
    (allowed : TargetEmitterCheckStack.sourceAllowed sourceHead)
    (represents :
      TargetEmitterRuntime.Represents
        TargetEmitterCheckStack.Pop.startState
        capacity 0 registers (prior ++ [value])
        (sourceHead :: sourceTail) target actual) :
    ∃ actualFinal,
      workRunExact? TargetEmitterCheckStack.Pop.machine
          (TargetEmitterCheckStack.Pop.nonemptyWorkSteps capacity
            (TargetEmitterCheckStack.recordsWord prior).length value)
          actual =
        some actualFinal ∧
      TargetEmitterRuntime.Represents
        TargetEmitterCheckStack.Pop.acceptState
        capacity value registers prior
        (sourceHead :: sourceTail) target actualFinal := by
  have inputEquivalent :
      WorkConfiguration.BlankEquivalent actual
        (TargetEmitterCheckStack.Pop.entryConfiguration
          capacity registers (prior ++ [value])
          sourceHead sourceTail (targetSuffix target) []) := by
    simpa [TargetEmitterRuntime.Represents,
      TargetEmitterRuntime.logicalConfiguration,
      TargetEmitterRuntime.logicalLeftWorkspace,
      TargetEmitterRuntime.logicalWord,
      TargetEmitterCheckStack.Pop.entryConfiguration,
      TargetEmitterCheckStack.configAtWord, targetSuffix,
      TargetEmitterCheckStack.sourceLeftBoundary,
      TargetEmitterLedger.sourceLeftBoundary,
      TargetEmitterCheckStack.ledgerBoundary,
      List.append_assoc] using represents
  rcases
      TargetEmitterCheckStack.Pop.nonempty_exact_of_blankEquivalent_entry
        capacity value registers prior sourceHead sourceTail
        (targetSuffix target) [] fits valueBound allowed
        actual inputEquivalent with
    ⟨actualFinal, exactRun, finalEquivalent⟩
  have paddedToLogical :
      WorkConfiguration.BlankEquivalent
        (TargetEmitterCheckStack.Pop.nonemptyFinalConfiguration
          capacity value registers prior sourceHead sourceTail
          (targetSuffix target) [])
        (TargetEmitterRuntime.logicalConfiguration
          TargetEmitterCheckStack.Pop.acceptState
          capacity value registers prior
          (sourceHead :: sourceTail) target) := by
    simpa [TargetEmitterRuntime.logicalLeftWorkspace,
      TargetEmitterRuntime.logicalWord,
      TargetEmitterCheckStack.Pop.nonemptyFinalConfiguration,
      TargetEmitterCheckStack.configAtWord, targetSuffix,
      TargetEmitterCheckStack.cellBlank,
      TargetEmitterCheckStack.sourceLeftBoundary,
      TargetEmitterLedger.sourceLeftBoundary,
      TargetEmitterCheckStack.ledgerBoundary,
      TargetEmitterLedger.cellBlank, List.append_assoc] using
      (TargetEmitterRuntime.padded_blankEquivalent
        TargetEmitterCheckStack.Pop.acceptState
        capacity value registers prior
        (sourceHead :: sourceTail) target (value + 1) 0)
  exact
    ⟨actualFinal, exactRun,
      WorkConfiguration.blankEquivalent_trans
        finalEquivalent paddedToLogical⟩

end CheckStack

/-! ### One controller edge

The initialization node is a literal control node whose accept successor is
the header block entry.  This theorem lifts only that already-materialized
edge; it does not select or execute the header plan.
-/

private theorem stackInitializeNode_member :
    TargetEmitterController.stackInitializeNode ∈
      TargetEmitterController.graph.nodes := by
  change TargetEmitterController.stackInitializeNode ∈
    TargetEmitterController.controlNodes ++
      TargetEmitterController.allBlockNodes
  simp [TargetEmitterController.controlNodes]

theorem stackInitialize_acceptPath (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (sourceHead : WorkSymbol) (sourceTail : List WorkSymbol)
    (target : List Token) (actual : WorkConfiguration)
    (fits : CheckStack.LedgerFits capacity registers)
    (scratchBound : scratch ≤ capacity)
    (allowed : TargetEmitterCheckStack.sourceAllowed sourceHead)
    (represents :
      CheckStack.InitializeRepresents capacity scratch registers
        sourceHead sourceTail target actual) :
    ∃ actualFinal,
      AcceptPath TargetEmitterController.graph
        (.node TargetEmitterController.stackInitializeRef)
        (.node TargetEmitterController.headerRef)
        (TargetEmitterCheckStack.Initialize.workSteps capacity + 1)
        actual.tape actualFinal.tape ∧
      TargetEmitterRuntime.Represents
        TargetEmitterCheckStack.Initialize.acceptState
        capacity scratch registers []
        (sourceHead :: sourceTail) target actualFinal := by
  rcases CheckStack.initialize_exact capacity scratch registers
      sourceHead sourceTail target actual fits scratchBound allowed
      represents with
    ⟨actualFinal, exactRun, finalRepresents⟩
  have actualShape :
      actual =
        { state := TargetEmitterCheckStack.Initialize.startState
          tape := actual.tape } := by
    cases actual with
    | mk state tape =>
        cases CheckStack.InitializeRepresents.state_eq represents
        rfl
  have finalShape :
      actualFinal =
        { state := TargetEmitterCheckStack.Initialize.acceptState
          tape := actualFinal.tape } := by
    cases actualFinal with
    | mk state tape =>
        cases TargetEmitterRuntime.Represents.state_eq
          finalRepresents
        rfl
  have localRun :
      LocalAcceptRun TargetEmitterController.stackInitializeNode
        (TargetEmitterCheckStack.Initialize.workSteps capacity)
        actual.tape actualFinal.tape := by
    unfold LocalAcceptRun
    change
      workRunExact? TargetEmitterCheckStack.Initialize.machine
          (TargetEmitterCheckStack.Initialize.workSteps capacity)
          { state := TargetEmitterCheckStack.Initialize.startState
            tape := actual.tape } =
        some
          { state := TargetEmitterCheckStack.Initialize.acceptState
            tape := actualFinal.tape }
    rw [← actualShape, ← finalShape]
    exact exactRun
  have tail :
      AcceptPath TargetEmitterController.graph
        (.node TargetEmitterController.headerRef)
        (.node TargetEmitterController.headerRef) 0
        actualFinal.tape actualFinal.tape :=
    AcceptPath.terminal
      (.node TargetEmitterController.headerRef) actualFinal.tape
  have path :=
    AcceptPath.step TargetEmitterController.stackInitializeNode
      (.node TargetEmitterController.headerRef)
      (TargetEmitterCheckStack.Initialize.workSteps capacity) 0
      actual.tape actualFinal.tape actualFinal.tape
      stackInitializeNode_member localRun tail
  refine ⟨actualFinal, ?_, finalRepresents⟩
  simpa [TargetEmitterController.stackInitializeNode,
    TargetEmitterController.stackInitializeRef,
    TargetEmitterController.controlNode,
    TargetEmitterController.controlRef,
    Node.reference] using path

end PNP.Concrete.LockedNAND.TargetEmitterRuntimeCheckStack
