/-
Copyright (c) 2026 PNP Labs.

Exact initialization prefix for the fixed grammar-only locked-NAND target
emitter controller.

The ledger deliberately materializes three exterior target-side blanks.  The
stack initializer needs only the logical boundary cell.  This module relates
those finite windows by blank equivalence and composes the already
materialized scanner, ledger, and stack-initialization graph paths.
-/

import PNP.Concrete.LockedNANDTargetEmitterControllerTrace
import PNP.Concrete.LockedNANDTargetEmitterRuntimeCheckStack

namespace PNP.Concrete.LockedNAND.TargetEmitterControllerInitialTrace

open PNP.Concrete
open WorkMachineProgramPath
open TargetEmitterController

def ledgerHandoffConfiguration
    (raw : RawCircuit) : WorkConfiguration :=
  { state := TargetEmitterCheckStack.Initialize.startState
    tape := (TargetEmitterLedger.finalConfiguration raw).tape }

theorem ledgerHandoff_initializeRepresents
    (raw : RawCircuit) :
    TargetEmitterRuntimeCheckStack.CheckStack.InitializeRepresents
      (TargetEmitterLedger.slotCapacity raw) 0
      (TargetEmitterLedger.ledgerRegisters raw)
      SourceParser.cell00
      (SourceParser.circuitCells raw).tail []
      (ledgerHandoffConfiguration raw) := by
  unfold
    TargetEmitterRuntimeCheckStack.CheckStack.InitializeRepresents
    TargetEmitterRuntimeCheckStack.CheckStack.initializeLogicalConfiguration
  refine ⟨rfl, ?_⟩
  have padded :=
    WorkTape.blankEquivalent_of_padding
      (TargetEmitterCheckStack.Initialize.entryConfiguration
        (TargetEmitterLedger.slotCapacity raw) 0
        (TargetEmitterLedger.ledgerRegisters raw)
        SourceParser.cell00
        (SourceParser.circuitCells raw).tail
        (TargetEmitterRuntimeCheckStack.CheckStack.targetSuffix [])
        []).tape
      0 3
  cases raw with
  | mk inputs gates output =>
      simpa [ledgerHandoffConfiguration,
        TargetEmitterLedger.finalConfiguration,
        TargetEmitterLedger.finalTape,
        TargetEmitterLedger.ledgerLeftWorkspace,
        TargetEmitterLedger.zeroScratchReserve,
        TargetEmitterLedger.ledgerWord,
        TargetEmitterCheckStack.Initialize.entryConfiguration,
        TargetEmitterCheckStack.scratchWord,
        TargetEmitterCheckStack.configAtWord,
        TargetEmitterCheckStack.sourceLeftBoundary,
        TargetEmitterCheckStack.unarySeparator,
        TargetEmitterCheckStack.ledgerBoundary,
        TargetEmitterCheckStack.stackBoundary,
        TargetEmitterCheckStack.cellBlank,
        TargetEmitterLedger.sourceLeftBoundary,
        TargetEmitterLedger.sourceTargetBoundary,
        TargetEmitterLedger.unarySeparator,
        TargetEmitterLedger.ledgerBoundary,
        TargetEmitterLedger.stackBoundary,
        TargetEmitterLedger.cellBlank,
        TargetEmitter.sourceLeftBoundary,
        TargetEmitter.sourceTargetBoundary,
        TargetEmitter.unarySeparator,
        TargetEmitterRuntimeCheckStack.CheckStack.targetSuffix,
        TargetEmitter.configAtWord,
        SourceParser.circuitCells, SourceParser.gateListCells,
        SourceParser.packedTokenCells,
        List.append_assoc] using padded

theorem ledgerHandoff_sourceAllowed :
    TargetEmitterCheckStack.sourceAllowed SourceParser.cell00 := by
  simp [TargetEmitterCheckStack.sourceAllowed, SourceParser.cell00]

theorem ledgerHandoff_fits
    (raw : RawCircuit) :
    TargetEmitterRuntimeCheckStack.CheckStack.LedgerFits
      (TargetEmitterLedger.slotCapacity raw)
      (TargetEmitterLedger.ledgerRegisters raw) := by
  let shape := TargetEmitterLedger.ledgerShape raw
  exact
    { inputCount := shape.inputBound
      normalizedGateCount := shape.normalizedGateBound
      carrierWidth := shape.carrierWidthBound
      baseline := shape.baselineBound
      currentGate := shape.currentGateBound
      outputIndex := shape.outputIndexBound }

theorem stack_initialize_path (raw : RawCircuit) :
    ∃ actualFinal,
      AcceptPath graph (.node stackInitializeRef)
        (.node headerRef)
        (TargetEmitterCheckStack.Initialize.workSteps
          (TargetEmitterLedger.slotCapacity raw) + 1)
        (TargetEmitterLedger.finalConfiguration raw).tape
        actualFinal.tape ∧
      TargetEmitterRuntime.Represents
        TargetEmitterCheckStack.Initialize.acceptState
        (TargetEmitterLedger.slotCapacity raw) 0
        (TargetEmitterLedger.ledgerRegisters raw) []
        (SourceParser.circuitCells raw) []
        actualFinal := by
  rcases
      TargetEmitterRuntimeCheckStack.stackInitialize_acceptPath
        (TargetEmitterLedger.slotCapacity raw) 0
        (TargetEmitterLedger.ledgerRegisters raw)
        SourceParser.cell00
        (SourceParser.circuitCells raw).tail []
        (ledgerHandoffConfiguration raw)
        (ledgerHandoff_fits raw) (by omega)
        ledgerHandoff_sourceAllowed
        (ledgerHandoff_initializeRepresents raw) with
    ⟨actualFinal, path, represents⟩
  refine ⟨actualFinal, ?_, ?_⟩
  · simpa [ledgerHandoffConfiguration] using path
  · have sourceEq :
        SourceParser.cell00 ::
            (SourceParser.circuitCells raw).tail =
          SourceParser.circuitCells raw := by
      cases raw with
      | mk inputs gates output =>
          rfl
    rw [sourceEq] at represents
    exact represents

theorem scanner_ledger_stack_path (raw : RawCircuit) :
    ∃ actualFinal,
      AcceptPath graph (.node scannerRef) (.node headerRef)
        (TargetEmitterGrammarScanner.canonicalSteps raw + 1 +
          (TargetEmitterLedger.workSteps raw + 1) +
          (TargetEmitterCheckStack.Initialize.workSteps
            (TargetEmitterLedger.slotCapacity raw) + 1))
        (rawInputWorkTape (encodeCircuit raw))
        actualFinal.tape ∧
      TargetEmitterRuntime.Represents
        TargetEmitterCheckStack.Initialize.acceptState
        (TargetEmitterLedger.slotCapacity raw) 0
        (TargetEmitterLedger.ledgerRegisters raw) []
        (SourceParser.circuitCells raw) []
        actualFinal := by
  rcases stack_initialize_path raw with
    ⟨actualFinal, stackPath, represents⟩
  have initialPath :=
    TargetEmitterControllerTrace.scanner_ledger_path raw
  refine ⟨actualFinal, ?_, represents⟩
  exact AcceptPath.trans graph (.node scannerRef)
    (.node stackInitializeRef) (.node headerRef)
    (TargetEmitterGrammarScanner.canonicalSteps raw + 1 +
      (TargetEmitterLedger.workSteps raw + 1))
    (TargetEmitterCheckStack.Initialize.workSteps
      (TargetEmitterLedger.slotCapacity raw) + 1)
    _ _ _ initialPath stackPath

end PNP.Concrete.LockedNAND.TargetEmitterControllerInitialTrace
