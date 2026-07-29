/-
Copyright (c) 2026 PNP Labs.

Exact recursive gate-list traversal for the fixed grammar-only locked-NAND
target emitter.

The executable graph follows only the retained source word.  The recursive
schedule and raw-builder assembly below are proof-side invariants used to
identify the exact runtime reached after every literal gate.
-/

import PNP.Concrete.LockedNANDTargetEmitterControllerHeaderBound
import PNP.Concrete.LockedNANDTargetEmitterControllerGateBound
import PNP.Concrete.LockedNANDTargetEmitterSemanticSchedule

namespace PNP.Concrete.LockedNAND.TargetEmitterControllerGateListTrace

open PNP.Concrete
open WorkMachineProgramGraph
open WorkMachineProgramPath
open TargetEmitterController

set_option maxRecDepth 100000

abbrev Runtime := TargetEmitterProgramSemantics.Runtime
abbrev FocusTapeRepresents :=
  TargetEmitterControllerGateTrace.FocusTapeRepresents

private theorem configAtWord_state
    (state : Nat) (left word : List WorkSymbol) :
    (TargetEmitter.configAtWord state left word).state = state := by
  cases word <;> rfl

private theorem configAtWord_tape_irrel
    (firstState secondState : Nat)
    (left word : List WorkSymbol) :
    (TargetEmitter.configAtWord firstState left word).tape =
      (TargetEmitter.configAtWord secondState left word).tape := by
  cases word <;> rfl

private theorem focusRepresents_of_tape_equivalent
    (state capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (crossed remaining : List WorkSymbol)
    (target : List Token) (tape : WorkTape)
    (equivalent :
      WorkTape.BlankEquivalent tape
        (TargetEmitterRuntimeSourceControl.sourceFocusConfiguration
          state capacity scratch registers checks crossed remaining
          target).tape) :
    FocusTapeRepresents state capacity scratch registers checks
      crossed remaining target tape := by
  refine ⟨?_, equivalent⟩
  exact
    (configAtWord_state state
      (crossed.reverse ++
        TargetEmitterRuntime.logicalLeftWorkspace
          capacity scratch registers checks)
      (remaining ++
        TargetEmitterRuntimeSourceControl.targetSuffix target)).symm

/-- Runtime reached after emitting the macro blocks of the literal raw gate
list, before output normalization or prefix construction. -/
def gateListRuntime (raw : RawCircuit) : Runtime :=
  TargetEmitterSemanticSchedule.appendGateListResults raw.gates
    (TargetEmitterProgramSemantics.headerResult
      (TargetEmitterControllerHeaderTrace.initialRuntime raw))

/-- Retained source prefix crossed when the controller first focuses the
raw circuit output. -/
def outputCrossedCells (raw : RawCircuit) : List WorkSymbol :=
  TargetEmitterControllerTrace.circuitHeaderCells
      raw.inputCount raw.gates.length ++
    SourceParser.gateListCells raw.gates ++
    [SourceParser.cell10, SourceParser.cell00]

private def crossedCells
    (raw : RawCircuit) (processed : List RawGate) :
    List WorkSymbol :=
  TargetEmitterControllerTrace.circuitHeaderCells
      raw.inputCount raw.gates.length ++
    SourceParser.gateListCells processed

private theorem sourceCapturedValue_eq
    (source : RawSource) :
    TargetEmitterControllerSourceTrace.capturedValue
        (TargetEmitterControllerTrace.sourceKind source)
        (TargetEmitterControllerGateTrace.sourceValue source) =
      TargetEmitterCapacity.sourceCaptureValue source := by
  cases source with
  | input index => rfl
  | gate index => rfl
  | constant value =>
      cases value <;> rfl

private theorem runtime_ext
    (first second : Runtime)
    (captured : first.captured = second.captured)
    (scratch : first.scratch = second.scratch)
    (registers : first.registers = second.registers)
    (checks : first.checks = second.checks)
    (targetTokens : first.targetTokens = second.targetTokens) :
    first = second := by
  cases first
  cases second
  simp_all

private theorem macroResult_scratch_irrel
    (runtime : Runtime) (scratch : Nat)
    (gates : List TargetEmitterPlan.PlannedGate)
    (relative count : Nat) :
    TargetEmitterProgramSemantics.macroResult
        { runtime with scratch := scratch } gates relative count =
      TargetEmitterProgramSemantics.macroResult
        runtime gates relative count := by
  apply runtime_ext
  · exact
      TargetEmitterControllerGateTrace.macroResult_captured
        _ gates relative count |>.trans
        (TargetEmitterControllerGateTrace.macroResult_captured
          runtime gates relative count).symm
  · rfl
  · simp only [TargetEmitterProgramSemantics.macroResult_registers]
  · simp only [TargetEmitterProgramSemantics.macroResult_checks]
  · simp only [TargetEmitterProgramSemantics.macroResult_targetTokens,
      TargetEmitterProgramSemantics.plannedGateTokens,
      TargetEmitterProgramSemantics.evaluatedGates]

set_option linter.unnecessarySimpa false in
private theorem physicalSourceResult_eq_appendSourceResult
    (runtime : Runtime) (source : RawSource) (side : Nat) :
    TargetEmitterProgramSemantics.macroResult
        (TargetEmitterControllerGateTrace.capturedRuntime runtime
          (TargetEmitterControllerTrace.sourceKind source)
          (TargetEmitterControllerGateTrace.sourceValue source))
        (TargetEmitterPlan.sourcePlan
          (TargetEmitterControllerTrace.sourceKind source) side)
        (TargetEmitterPlan.sourceCheckRelative
          (TargetEmitterControllerTrace.sourceKind source))
        (TargetEmitterPlan.sourceGateCount
          (TargetEmitterControllerTrace.sourceKind source)) =
      TargetEmitterSemanticSchedule.appendSourceResult
        side source runtime := by
  cases source with
  | input index =>
      simpa [TargetEmitterControllerGateTrace.capturedRuntime,
        TargetEmitterControllerGateTrace.sourceValue,
        TargetEmitterControllerTrace.sourceKind,
        TargetEmitterControllerSourceTrace.capturedValue,
        TargetEmitterSemanticSchedule.appendSourceResult,
        TargetEmitterSemanticSchedule.withCaptured,
        TargetEmitterSemanticSchedule.capturedValue,
        TargetEmitterSemanticSchedule.sourceKind] using
        macroResult_scratch_irrel
          { runtime with captured := index }
          (runtime.scratch + index)
          (TargetEmitterPlan.sourcePlan .input side)
          (TargetEmitterPlan.sourceCheckRelative .input)
          (TargetEmitterPlan.sourceGateCount .input)
  | gate index =>
      simpa [TargetEmitterControllerGateTrace.capturedRuntime,
        TargetEmitterControllerGateTrace.sourceValue,
        TargetEmitterControllerTrace.sourceKind,
        TargetEmitterControllerSourceTrace.capturedValue,
        TargetEmitterSemanticSchedule.appendSourceResult,
        TargetEmitterSemanticSchedule.withCaptured,
        TargetEmitterSemanticSchedule.capturedValue,
        TargetEmitterSemanticSchedule.sourceKind] using
        macroResult_scratch_irrel
          { runtime with captured := index }
          (runtime.scratch + index)
          (TargetEmitterPlan.sourcePlan .gate side)
          (TargetEmitterPlan.sourceCheckRelative .gate)
          (TargetEmitterPlan.sourceGateCount .gate)
  | constant value =>
      cases value with
      | false =>
          simpa [TargetEmitterControllerGateTrace.capturedRuntime,
            TargetEmitterControllerGateTrace.sourceValue,
            TargetEmitterControllerTrace.sourceKind,
            TargetEmitterControllerSourceTrace.capturedValue,
            TargetEmitterSemanticSchedule.appendSourceResult,
            TargetEmitterSemanticSchedule.withCaptured,
            TargetEmitterSemanticSchedule.capturedValue,
            TargetEmitterSemanticSchedule.sourceKind] using
            macroResult_scratch_irrel
              { runtime with captured := 0 }
              runtime.scratch
              (TargetEmitterPlan.sourcePlan .constantFalse side)
              (TargetEmitterPlan.sourceCheckRelative .constantFalse)
              (TargetEmitterPlan.sourceGateCount .constantFalse)
      | true =>
          simpa [TargetEmitterControllerGateTrace.capturedRuntime,
            TargetEmitterControllerGateTrace.sourceValue,
            TargetEmitterControllerTrace.sourceKind,
            TargetEmitterControllerSourceTrace.capturedValue,
            TargetEmitterSemanticSchedule.appendSourceResult,
            TargetEmitterSemanticSchedule.withCaptured,
            TargetEmitterSemanticSchedule.capturedValue,
            TargetEmitterSemanticSchedule.sourceKind] using
            macroResult_scratch_irrel
              { runtime with captured := 0 }
              runtime.scratch
              (TargetEmitterPlan.sourcePlan .constantTrue side)
              (TargetEmitterPlan.sourceCheckRelative .constantTrue)
              (TargetEmitterPlan.sourceGateCount .constantTrue)

private theorem physicalGateResult_eq_appendGateResult
    (runtime : Runtime) (gate : RawGate) :
    TargetEmitterRuntimeProgramSafety.rightTraceResult
        (TargetEmitterProgramSemantics.macroResult
          (TargetEmitterControllerGateTrace.capturedRuntime
            (TargetEmitterProgramSemantics.macroResult
              (TargetEmitterControllerGateTrace.capturedRuntime runtime
                (TargetEmitterControllerTrace.sourceKind gate.left)
                (TargetEmitterControllerGateTrace.sourceValue gate.left))
              (TargetEmitterPlan.sourcePlan
                (TargetEmitterControllerTrace.sourceKind gate.left) 0)
              (TargetEmitterPlan.sourceCheckRelative
                (TargetEmitterControllerTrace.sourceKind gate.left))
              (TargetEmitterPlan.sourceGateCount
                (TargetEmitterControllerTrace.sourceKind gate.left)))
            (TargetEmitterControllerTrace.sourceKind gate.right)
            (TargetEmitterControllerGateTrace.sourceValue gate.right))
          (TargetEmitterPlan.sourcePlan
            (TargetEmitterControllerTrace.sourceKind gate.right) 1)
          (TargetEmitterPlan.sourceCheckRelative
            (TargetEmitterControllerTrace.sourceKind gate.right))
          (TargetEmitterPlan.sourceGateCount
            (TargetEmitterControllerTrace.sourceKind gate.right))) =
      TargetEmitterSemanticSchedule.appendGateResult gate runtime := by
  rw [physicalSourceResult_eq_appendSourceResult runtime gate.left 0]
  rw [physicalSourceResult_eq_appendSourceResult
    (TargetEmitterSemanticSchedule.appendSourceResult
      0 gate.left runtime) gate.right 1]
  rfl

private theorem appendSourceResult_scratch
    (side : Nat) (source : RawSource) (runtime : Runtime) :
    (TargetEmitterSemanticSchedule.appendSourceResult
      side source runtime).scratch = 0 := by
  exact TargetEmitterProgramSemantics.macroResult_scratch _ _ _ _

private theorem appendGateResult_scratch
    (gate : RawGate) (runtime : Runtime) :
    (TargetEmitterSemanticSchedule.appendGateResult gate runtime).scratch =
      0 := by
  rfl

private theorem appendGateResult_carrierWidth
    (gate : RawGate) (runtime : Runtime) :
    (TargetEmitterSemanticSchedule.appendGateResult
      gate runtime).registers.carrierWidth =
        runtime.registers.carrierWidth := by
  simp [TargetEmitterSemanticSchedule.appendGateResult,
    TargetEmitterSemanticSchedule.appendSourceResult,
    TargetEmitterSemanticSchedule.withCaptured,
    TargetEmitterProgramSemantics.incrementCurrentGateResult,
    TargetEmitterProgramSemantics.macroResult_registers]

private theorem appendGateResult_baseline
    (gate : RawGate) (runtime : Runtime) :
    (TargetEmitterSemanticSchedule.appendGateResult
      gate runtime).registers.baseline =
        runtime.registers.baseline := by
  simp [TargetEmitterSemanticSchedule.appendGateResult,
    TargetEmitterSemanticSchedule.appendSourceResult,
    TargetEmitterSemanticSchedule.withCaptured,
    TargetEmitterProgramSemantics.incrementCurrentGateResult,
    TargetEmitterProgramSemantics.macroResult_registers]

private theorem gateListMacroGateCount_append
    (first second : List RawGate) :
    RawBuilder.gateListMacroGateCount (first ++ second) =
      RawBuilder.gateListMacroGateCount first +
        RawBuilder.gateListMacroGateCount second := by
  induction first with
  | nil =>
      simp [RawBuilder.gateListMacroGateCount]
  | cons gate rest inductionHypothesis =>
      simp only [List.cons_append,
        RawBuilder.gateListMacroGateCount, inductionHypothesis,
        Nat.add_assoc]

private theorem sourceMacroGateCount_le_gate
    (gate : RawGate) :
    RawBuilder.sourceMacroGateCount gate.left ≤
        RawBuilder.gateMacroGateCount gate ∧
      RawBuilder.sourceMacroGateCount gate.left +
          RawBuilder.sourceMacroGateCount gate.right ≤
        RawBuilder.gateMacroGateCount gate := by
  simp only [RawBuilder.gateMacroGateCount]
  exact
    ⟨Nat.le_trans
        (Nat.le_add_right
          (RawBuilder.sourceMacroGateCount gate.left)
          (RawBuilder.sourceMacroGateCount gate.right))
        (Nat.le_add_right
          (RawBuilder.sourceMacroGateCount gate.left +
            RawBuilder.sourceMacroGateCount gate.right) 18),
      Nat.le_add_right
        (RawBuilder.sourceMacroGateCount gate.left +
          RawBuilder.sourceMacroGateCount gate.right) 18⟩

private theorem appendSourceResult_registers
    (side : Nat) (source : RawSource) (runtime : Runtime) :
    (TargetEmitterSemanticSchedule.appendSourceResult
      side source runtime).registers =
        { runtime.registers with
          outputIndex :=
            runtime.registers.outputIndex +
              RawBuilder.sourceMacroGateCount source } := by
  cases source with
  | input index =>
      simp [TargetEmitterSemanticSchedule.appendSourceResult,
        TargetEmitterSemanticSchedule.withCaptured,
        TargetEmitterSemanticSchedule.sourceKind,
        TargetEmitterProgramSemantics.macroResult_registers,
        TargetEmitterPlan.sourceGateCount,
        RawBuilder.sourceMacroGateCount]
  | gate index =>
      simp [TargetEmitterSemanticSchedule.appendSourceResult,
        TargetEmitterSemanticSchedule.withCaptured,
        TargetEmitterSemanticSchedule.sourceKind,
        TargetEmitterProgramSemantics.macroResult_registers,
        TargetEmitterPlan.sourceGateCount,
        RawBuilder.sourceMacroGateCount]
  | constant value =>
      cases value <;>
        simp [TargetEmitterSemanticSchedule.appendSourceResult,
          TargetEmitterSemanticSchedule.withCaptured,
          TargetEmitterSemanticSchedule.sourceKind,
          TargetEmitterProgramSemantics.macroResult_registers,
          TargetEmitterPlan.sourceGateCount,
          RawBuilder.sourceMacroGateCount]

private theorem appendGateResult_inputCount
    (gate : RawGate) (runtime : Runtime) :
    (TargetEmitterSemanticSchedule.appendGateResult
      gate runtime).registers.inputCount =
        runtime.registers.inputCount := by
  simp [TargetEmitterSemanticSchedule.appendGateResult,
    TargetEmitterProgramSemantics.incrementCurrentGateResult,
    TargetEmitterProgramSemantics.macroResult_registers,
    appendSourceResult_registers]

private theorem appendGateResult_normalizedGateCount
    (gate : RawGate) (runtime : Runtime) :
    (TargetEmitterSemanticSchedule.appendGateResult
      gate runtime).registers.normalizedGateCount =
        runtime.registers.normalizedGateCount := by
  simp [TargetEmitterSemanticSchedule.appendGateResult,
    TargetEmitterProgramSemantics.incrementCurrentGateResult,
    TargetEmitterProgramSemantics.macroResult_registers,
    appendSourceResult_registers]

private theorem appendGateResult_currentGate
    (gate : RawGate) (runtime : Runtime) :
    (TargetEmitterSemanticSchedule.appendGateResult
      gate runtime).registers.currentGate =
        runtime.registers.currentGate + 1 := by
  simp [TargetEmitterSemanticSchedule.appendGateResult,
    TargetEmitterProgramSemantics.incrementCurrentGateResult,
    TargetEmitterProgramSemantics.macroResult_registers,
    appendSourceResult_registers]

private theorem appendGateResult_outputIndex
    (gate : RawGate) (runtime : Runtime) :
    (TargetEmitterSemanticSchedule.appendGateResult
      gate runtime).registers.outputIndex =
        runtime.registers.outputIndex +
          RawBuilder.gateMacroGateCount gate := by
  simp [TargetEmitterSemanticSchedule.appendGateResult,
    TargetEmitterProgramSemantics.incrementCurrentGateResult,
    TargetEmitterProgramSemantics.macroResult_registers,
    appendSourceResult_registers,
    RawBuilder.gateMacroGateCount,
    TargetEmitterPlan.traceGateCount]
  omega

private structure RegisterInvariant
    (raw : RawCircuit) (processed : List RawGate)
    (runtime : Runtime) : Prop where
  inputCount :
    runtime.registers.inputCount = raw.inputCount
  normalizedGateCount :
    runtime.registers.normalizedGateCount =
      TargetEmitterLedger.normalizedGateCount raw
  carrierWidth :
    runtime.registers.carrierWidth =
      TargetEmitterLedger.carrierWidthValue raw
  baseline :
    runtime.registers.baseline =
      TargetEmitterLedger.baselineValue raw
  currentGate :
    runtime.registers.currentGate = processed.length
  outputIndex :
    runtime.registers.outputIndex =
      RawBuilder.gateListMacroGateCount processed

private theorem RegisterInvariant.appendGate
    {raw : RawCircuit} {processed : List RawGate}
    {runtime : Runtime} (invariant :
      RegisterInvariant raw processed runtime)
    (gate : RawGate) :
    RegisterInvariant raw (processed ++ [gate])
      (TargetEmitterSemanticSchedule.appendGateResult gate runtime) := by
  refine
    { inputCount := ?_
      normalizedGateCount := ?_
      carrierWidth := ?_
      baseline := ?_
      currentGate := ?_
      outputIndex := ?_ }
  · rw [appendGateResult_inputCount]
    exact invariant.inputCount
  · rw [appendGateResult_normalizedGateCount]
    exact invariant.normalizedGateCount
  · rw [appendGateResult_carrierWidth]
    exact invariant.carrierWidth
  · rw [appendGateResult_baseline]
    exact invariant.baseline
  · rw [appendGateResult_currentGate, invariant.currentGate,
      List.length_append, List.length_singleton]
  · rw [appendGateResult_outputIndex, invariant.outputIndex,
      gateListMacroGateCount_append]
    rfl

private theorem controllerRange_of_invariant
    (raw : RawCircuit) (processed remaining : List RawGate)
    (runtime : Runtime)
    (gatesEq : raw.gates = processed ++ remaining)
    (invariant : RegisterInvariant raw processed runtime) :
    TargetEmitterCapacity.ControllerRange raw runtime.registers := by
  have allWeights :
      RawBuilder.gateListMacroGateCount raw.gates =
        RawBuilder.gateListMacroGateCount processed +
          RawBuilder.gateListMacroGateCount remaining := by
    rw [gatesEq, gateListMacroGateCount_append]
  have baseline :
      RawBuilder.gateListMacroGateCount raw.gates ≤
        TargetEmitterLedger.baselineValue raw := by
    rw [← TargetEmitterLedger.gateListMacroWeight_eq_rawBuilder]
    unfold TargetEmitterLedger.baselineValue
    omega
  refine
    { inputCount_eq := invariant.inputCount
      normalizedGateCount_eq := invariant.normalizedGateCount
      carrierWidth_eq := invariant.carrierWidth
      baseline_eq := invariant.baseline
      currentGate_le := ?_
      outputIndex_le := ?_ }
  · rw [invariant.currentGate]
    rw [TargetEmitterLedger.normalizedGateCount]
    have lengthEq : raw.gates.length =
        processed.length + remaining.length := by
      rw [gatesEq, List.length_append]
    omega
  · rw [invariant.outputIndex]
    omega

private theorem partialControllerRanges
    (raw : RawCircuit) (processed rest : List RawGate)
    (runtime : Runtime) (gate : RawGate)
    (gatesEq : raw.gates = processed ++ gate :: rest)
    (invariant : RegisterInvariant raw processed runtime) :
    let afterLeft :=
      TargetEmitterSemanticSchedule.appendSourceResult
        0 gate.left runtime
    let afterRight :=
      TargetEmitterSemanticSchedule.appendSourceResult
        1 gate.right afterLeft
    TargetEmitterCapacity.ControllerRange raw afterLeft.registers ∧
      TargetEmitterCapacity.ControllerRange raw afterRight.registers ∧
      afterRight.registers.currentGate + 1 ≤
        TargetEmitterLedger.normalizedGateCount raw := by
  dsimp only
  let afterLeft :=
    TargetEmitterSemanticSchedule.appendSourceResult 0 gate.left runtime
  let afterRight :=
    TargetEmitterSemanticSchedule.appendSourceResult 1 gate.right afterLeft
  have leftRegisters :=
    appendSourceResult_registers 0 gate.left runtime
  have rightRegisters :=
    appendSourceResult_registers 1 gate.right afterLeft
  have weights :=
    sourceMacroGateCount_le_gate gate
  have allWeights :
      RawBuilder.gateListMacroGateCount raw.gates =
        RawBuilder.gateListMacroGateCount processed +
          (RawBuilder.gateMacroGateCount gate +
            RawBuilder.gateListMacroGateCount rest) := by
    rw [gatesEq, gateListMacroGateCount_append]
    rfl
  have baseline :
      RawBuilder.gateListMacroGateCount raw.gates ≤
        TargetEmitterLedger.baselineValue raw := by
    rw [← TargetEmitterLedger.gateListMacroWeight_eq_rawBuilder]
    unfold TargetEmitterLedger.baselineValue
    omega
  have currentBound :
      processed.length + 1 ≤
        TargetEmitterLedger.normalizedGateCount raw := by
    rw [TargetEmitterLedger.normalizedGateCount]
    have lengthEq : raw.gates.length =
        processed.length + (rest.length + 1) := by
      rw [gatesEq, List.length_append]
      simp
    omega
  have leftRange :
      TargetEmitterCapacity.ControllerRange raw afterLeft.registers := by
    refine
      { inputCount_eq := ?_
        normalizedGateCount_eq := ?_
        carrierWidth_eq := ?_
        baseline_eq := ?_
        currentGate_le := ?_
        outputIndex_le := ?_ }
    · rw [leftRegisters]
      exact invariant.inputCount
    · rw [leftRegisters]
      exact invariant.normalizedGateCount
    · rw [leftRegisters]
      exact invariant.carrierWidth
    · rw [leftRegisters]
      exact invariant.baseline
    · rw [leftRegisters, invariant.currentGate]
      omega
    · rw [leftRegisters, invariant.outputIndex]
      change
        RawBuilder.gateListMacroGateCount processed +
            RawBuilder.sourceMacroGateCount gate.left ≤
          TargetEmitterLedger.baselineValue raw + 4
      omega
  have rightRange :
      TargetEmitterCapacity.ControllerRange raw afterRight.registers := by
    refine
      { inputCount_eq := ?_
        normalizedGateCount_eq := ?_
        carrierWidth_eq := ?_
        baseline_eq := ?_
        currentGate_le := ?_
        outputIndex_le := ?_ }
    · rw [rightRegisters, leftRegisters]
      exact invariant.inputCount
    · rw [rightRegisters, leftRegisters]
      exact invariant.normalizedGateCount
    · rw [rightRegisters, leftRegisters]
      exact invariant.carrierWidth
    · rw [rightRegisters, leftRegisters]
      exact invariant.baseline
    · rw [rightRegisters, leftRegisters, invariant.currentGate]
      omega
    · rw [rightRegisters, leftRegisters, invariant.outputIndex]
      change
        (RawBuilder.gateListMacroGateCount processed +
            RawBuilder.sourceMacroGateCount gate.left) +
            RawBuilder.sourceMacroGateCount gate.right ≤
          TargetEmitterLedger.baselineValue raw + 4
      omega
  refine ⟨leftRange, rightRange, ?_⟩
  rw [rightRegisters, leftRegisters, invariant.currentGate]
  exact currentBound

private theorem gateListCells_append
    (first second : List RawGate) :
    SourceParser.gateListCells (first ++ second) =
      SourceParser.gateListCells first ++
        SourceParser.gateListCells second := by
  induction first with
  | nil =>
      rfl
  | cons gate rest inductionHypothesis =>
      simp [SourceParser.gateListCells, inductionHypothesis,
        List.append_assoc]

private theorem traversalWord_packed
    (raw : RawCircuit) (processed rest : List RawGate)
    (gate : RawGate)
    (gatesEq : raw.gates = processed ++ gate :: rest) :
    ∀ symbol,
      symbol ∈
          crossedCells raw processed ++
            SourceParser.sourceCells gate.left ++
            SourceParser.sourceCells gate.right ++
            ([SourceParser.cell01, SourceParser.cell11] ++
              SourceParser.gateListCells rest ++
              TargetEmitterControllerTrace.circuitFooterCells raw.output) →
        TargetEmitter.PackedSymbol symbol := by
  intro symbol member
  apply TargetEmitter.circuitCells_packed raw symbol
  have wordEq :
      crossedCells raw processed ++
          SourceParser.sourceCells gate.left ++
          SourceParser.sourceCells gate.right ++
          ([SourceParser.cell01, SourceParser.cell11] ++
            SourceParser.gateListCells rest ++
            TargetEmitterControllerTrace.circuitFooterCells raw.output) =
        SourceParser.circuitCells raw := by
    have gateCountEq :
        raw.gates.length =
          processed.length + (rest.length + 1) := by
      rw [gatesEq, List.length_append]
      simp
    rw [SourceParser.circuitCells, gatesEq]
    simp [crossedCells,
      TargetEmitterControllerTrace.circuitHeaderCells,
      TargetEmitterControllerTrace.circuitFooterCells,
      gateListCells_append,
      SourceParser.gateListCells, SourceParser.gateCells,
      List.append_assoc]
    exact congrArg SourceParser.natCells gateCountEq
  rw [← wordEq]
  exact member

private theorem traversalWord_eq_circuitCells
    (raw : RawCircuit) (processed rest : List RawGate)
    (gate : RawGate)
    (gatesEq : raw.gates = processed ++ gate :: rest) :
    crossedCells raw processed ++
          SourceParser.sourceCells gate.left ++
          SourceParser.sourceCells gate.right ++
          ([SourceParser.cell01, SourceParser.cell11] ++
            SourceParser.gateListCells rest ++
            TargetEmitterControllerTrace.circuitFooterCells raw.output) =
        SourceParser.circuitCells raw := by
  have gateCountEq :
      raw.gates.length =
        processed.length + (rest.length + 1) := by
    rw [gatesEq, List.length_append]
    simp
  rw [SourceParser.circuitCells, gatesEq]
  simp [crossedCells,
    TargetEmitterControllerTrace.circuitHeaderCells,
    TargetEmitterControllerTrace.circuitFooterCells,
    gateListCells_append,
    SourceParser.gateListCells, SourceParser.gateCells,
    List.append_assoc]
  exact congrArg SourceParser.natCells gateCountEq

private theorem crossedCells_nonempty
    (raw : RawCircuit) (processed : List RawGate) :
    crossedCells raw processed =
      SourceParser.cell00 ::
        (SourceParser.cell00 ::
          (SourceParser.natCells raw.inputCount ++
            SourceParser.natCells raw.gates.length ++
            SourceParser.gateListCells processed)) := by
  simp [crossedCells,
    TargetEmitterControllerTrace.circuitHeaderCells,
    List.append_assoc]

/-- Runtime-sensitive constructive envelope for the remaining literal
gate-list traversal.  The recursive arguments are proof-side descriptions of
the retained source prefix and semantic runtime; they are never consulted by
the executable controller. -/
def gateListTraversalEnvelope
    (raw : RawCircuit) :
    List RawGate → List RawGate → Runtime → Nat
  | _, [], _ => 0
  | processed, gate :: [], runtime =>
      TargetEmitterControllerGateBound.gateSourcesTraceEnvelope
          raw (crossedCells raw processed)
          ([SourceParser.cell01, SourceParser.cell11] ++
            TargetEmitterControllerTrace.circuitFooterCells raw.output)
          gate runtime +
        7
  | processed, gate :: next :: tail, runtime =>
      TargetEmitterControllerGateBound.gateSourcesTraceEnvelope
          raw (crossedCells raw processed)
          ([SourceParser.cell01, SourceParser.cell11] ++
            SourceParser.gateListCells (next :: tail) ++
            TargetEmitterControllerTrace.circuitFooterCells raw.output)
          gate runtime +
        4 +
        gateListTraversalEnvelope raw (processed ++ [gate])
          (next :: tail)
          (TargetEmitterSemanticSchedule.appendGateResult gate runtime)

/-! ### Closed uniform gate-list domination -/

/-- Logical target/check-cell growth charged to one traversed raw gate. -/
def gatePerGateGrowth (raw : RawCircuit) : Nat :=
  3 *
    TargetEmitterControllerGateBound.gateBlockGrowth
      (TargetEmitterLedger.slotCapacity raw)

/-- One closed charge dominating a complete gate phase and either of its
fixed cursor advances. -/
def gateListUniformUnit (raw : RawCircuit) : Nat :=
  TargetEmitterControllerGateBound.gateUniformUnit
      (TargetEmitterLedger.slotCapacity raw)
      (SourceParser.circuitCells raw).length
      (TargetEmitterProgramSemantics.headerResult
        (TargetEmitterControllerHeaderTrace.initialRuntime raw))
      raw.gates.length +
    7

/-- Closed gate-list traversal charge, depending only on the decoded raw
circuit rather than the evolving proof-side runtime. -/
def gateListUniformEnvelope (raw : RawCircuit) : Nat :=
  raw.gates.length * gateListUniformUnit raw

private theorem header_registerInvariant (raw : RawCircuit) :
    RegisterInvariant raw []
      (TargetEmitterProgramSemantics.headerResult
        (TargetEmitterControllerHeaderTrace.initialRuntime raw)) := by
  refine
    { inputCount := ?_
      normalizedGateCount := ?_
      carrierWidth := ?_
      baseline := ?_
      currentGate := ?_
      outputIndex := ?_ } <;>
    rw [TargetEmitterProgramSemantics.headerResult_registers] <;>
    rfl

private theorem header_scratchShape (raw : RawCircuit) :
    (TargetEmitterProgramSemantics.headerResult
        (TargetEmitterControllerHeaderTrace.initialRuntime raw)).scratch =
      TargetEmitterLedger.baselineValue raw + 1 := by
  rw [TargetEmitterProgramSemantics.headerResult_scratch]
  rfl

private theorem currentGateEnvelope_le_uniform
    (raw : RawCircuit) (processed : List RawGate)
    (gate : RawGate) (rest : List RawGate)
    (runtime : Runtime)
    (gatesEq : raw.gates = processed ++ gate :: rest)
    (invariant : RegisterInvariant raw processed runtime)
    (scratchShape :
      runtime.scratch = 0 ∨
        runtime.scratch =
          TargetEmitterLedger.baselineValue raw + 1)
    (targetGrowth :
      runtime.targetTokens.length ≤
        (TargetEmitterProgramSemantics.headerResult
          (TargetEmitterControllerHeaderTrace.initialRuntime raw)).targetTokens.length +
          processed.length * gatePerGateGrowth raw)
    (checkGrowth :
      TargetEmitterRuntimeProgramBound.checkCells runtime.checks ≤
        TargetEmitterRuntimeProgramBound.checkCells
            (TargetEmitterProgramSemantics.headerResult
              (TargetEmitterControllerHeaderTrace.initialRuntime raw)).checks +
          processed.length * gatePerGateGrowth raw) :
    TargetEmitterControllerGateBound.gateSourcesTraceEnvelope raw
          (crossedCells raw processed)
          ([SourceParser.cell01, SourceParser.cell11] ++
            SourceParser.gateListCells rest ++
            TargetEmitterControllerTrace.circuitFooterCells raw.output)
          gate runtime ≤
        TargetEmitterControllerGateBound.gateUniformUnit
          (TargetEmitterLedger.slotCapacity raw)
          (SourceParser.circuitCells raw).length
          (TargetEmitterProgramSemantics.headerResult
            (TargetEmitterControllerHeaderTrace.initialRuntime raw))
          raw.gates.length ∧
      (TargetEmitterSemanticSchedule.appendGateResult
        gate runtime).targetTokens.length ≤
          runtime.targetTokens.length + gatePerGateGrowth raw ∧
      TargetEmitterRuntimeProgramBound.checkCells
          (TargetEmitterSemanticSchedule.appendGateResult
            gate runtime).checks ≤
        TargetEmitterRuntimeProgramBound.checkCells runtime.checks +
          gatePerGateGrowth raw := by
  have gateMember : gate ∈ raw.gates := by
    rw [gatesEq]
    simp
  have leftMember :
      TargetEmitterCapacity.CircuitSource raw gate.left :=
    .gateLeft gateMember
  have rightMember :
      TargetEmitterCapacity.CircuitSource raw gate.right :=
    .gateRight gateMember
  have currentRange :
      TargetEmitterCapacity.ControllerRange raw runtime.registers := by
    exact
      controllerRange_of_invariant raw processed (gate :: rest)
        runtime gatesEq invariant
  have ranges :=
    partialControllerRanges raw processed rest runtime gate
      gatesEq invariant
  rcases ranges with
    ⟨afterLeftRange0, afterRightRange0, nextGate0⟩
  have leftCapturedBound :
      TargetEmitterControllerSourceTrace.capturedValue
          (TargetEmitterControllerTrace.sourceKind gate.left)
          (TargetEmitterControllerGateTrace.sourceValue gate.left) + 1 ≤
        (SourceParser.circuitCells raw).length := by
    simpa [sourceCapturedValue_eq] using
      TargetEmitterCapacity.circuitSourceCaptureValue_succ_le_cells
        leftMember
  have rightCapturedBound :
      TargetEmitterControllerSourceTrace.capturedValue
          (TargetEmitterControllerTrace.sourceKind gate.right)
          (TargetEmitterControllerGateTrace.sourceValue gate.right) + 1 ≤
        (SourceParser.circuitCells raw).length := by
    simpa [sourceCapturedValue_eq] using
      TargetEmitterCapacity.circuitSourceCaptureValue_succ_le_cells
        rightMember
  have leftCaptureReserve :
      runtime.scratch +
          TargetEmitterControllerSourceTrace.capturedValue
            (TargetEmitterControllerTrace.sourceKind gate.left)
            (TargetEmitterControllerGateTrace.sourceValue gate.left) + 1 ≤
        TargetEmitterLedger.slotCapacity raw := by
    rcases scratchShape with scratchZero | scratchHeader
    · rw [scratchZero]
      simpa [sourceCapturedValue_eq] using
        TargetEmitterCapacity.focusedSourceCaptureReserve leftMember
    · rw [scratchHeader]
      simpa [sourceCapturedValue_eq] using
        TargetEmitterCapacity.headerFocusedSourceCaptureReserve leftMember
  let leftPhysical :=
    TargetEmitterProgramSemantics.macroResult
      (TargetEmitterControllerGateTrace.capturedRuntime runtime
        (TargetEmitterControllerTrace.sourceKind gate.left)
        (TargetEmitterControllerGateTrace.sourceValue gate.left))
      (TargetEmitterPlan.sourcePlan
        (TargetEmitterControllerTrace.sourceKind gate.left) 0)
      (TargetEmitterPlan.sourceCheckRelative
        (TargetEmitterControllerTrace.sourceKind gate.left))
      (TargetEmitterPlan.sourceGateCount
        (TargetEmitterControllerTrace.sourceKind gate.left))
  have leftPhysicalEq :
      leftPhysical =
        TargetEmitterSemanticSchedule.appendSourceResult
          0 gate.left runtime := by
    exact physicalSourceResult_eq_appendSourceResult runtime gate.left 0
  have afterLeftRange :
      TargetEmitterCapacity.ControllerRange raw
        leftPhysical.registers := by
    rw [leftPhysicalEq]
    exact afterLeftRange0
  have rightCaptureReserve :
      leftPhysical.scratch +
          TargetEmitterControllerSourceTrace.capturedValue
            (TargetEmitterControllerTrace.sourceKind gate.right)
            (TargetEmitterControllerGateTrace.sourceValue gate.right) + 1 ≤
        TargetEmitterLedger.slotCapacity raw := by
    rw [leftPhysicalEq]
    rw [appendSourceResult_scratch]
    simpa [sourceCapturedValue_eq] using
      TargetEmitterCapacity.focusedSourceCaptureReserve rightMember
  let rightPhysical :=
    TargetEmitterProgramSemantics.macroResult
      (TargetEmitterControllerGateTrace.capturedRuntime leftPhysical
        (TargetEmitterControllerTrace.sourceKind gate.right)
        (TargetEmitterControllerGateTrace.sourceValue gate.right))
      (TargetEmitterPlan.sourcePlan
        (TargetEmitterControllerTrace.sourceKind gate.right) 1)
      (TargetEmitterPlan.sourceCheckRelative
        (TargetEmitterControllerTrace.sourceKind gate.right))
      (TargetEmitterPlan.sourceGateCount
        (TargetEmitterControllerTrace.sourceKind gate.right))
  have rightPhysicalEq :
      rightPhysical =
        TargetEmitterSemanticSchedule.appendSourceResult
          1 gate.right
            (TargetEmitterSemanticSchedule.appendSourceResult
              0 gate.left runtime) := by
    dsimp only [rightPhysical]
    calc
      _ = TargetEmitterSemanticSchedule.appendSourceResult
            1 gate.right leftPhysical :=
        physicalSourceResult_eq_appendSourceResult
          leftPhysical gate.right 1
      _ = _ := by rw [leftPhysicalEq]
  have afterRightRange :
      TargetEmitterCapacity.ControllerRange raw
        rightPhysical.registers := by
    rw [rightPhysicalEq]
    exact afterRightRange0
  have nextGate :
      rightPhysical.registers.currentGate + 1 ≤
        TargetEmitterLedger.normalizedGateCount raw := by
    rw [rightPhysicalEq]
    exact nextGate0
  have countBound :
      processed.length + 1 ≤ raw.gates.length := by
    have lengthEq :
        raw.gates.length =
          processed.length + (rest.length + 1) := by
      rw [gatesEq, List.length_append]
      simp
    omega
  have twoBlocks_le_gateGrowth :
      2 *
          TargetEmitterControllerGateBound.gateBlockGrowth
            (TargetEmitterLedger.slotCapacity raw) ≤
        gatePerGateGrowth raw := by
    unfold gatePerGateGrowth
    omega
  have countGrowth :=
    Nat.mul_le_mul_right (gatePerGateGrowth raw) countBound
  have targetBudget :
      runtime.targetTokens.length +
            2 *
              TargetEmitterControllerGateBound.gateBlockGrowth
                (TargetEmitterLedger.slotCapacity raw) ≤
        TargetEmitterControllerGateBound.gateTargetLimit
          (TargetEmitterLedger.slotCapacity raw)
          (TargetEmitterProgramSemantics.headerResult
            (TargetEmitterControllerHeaderTrace.initialRuntime raw))
          raw.gates.length := by
    calc
      _ ≤ runtime.targetTokens.length + gatePerGateGrowth raw :=
        Nat.add_le_add_left twoBlocks_le_gateGrowth _
      _ ≤
          ((TargetEmitterProgramSemantics.headerResult
              (TargetEmitterControllerHeaderTrace.initialRuntime raw)).targetTokens.length +
            processed.length * gatePerGateGrowth raw) +
              gatePerGateGrowth raw :=
        Nat.add_le_add_right targetGrowth _
      _ =
          (TargetEmitterProgramSemantics.headerResult
              (TargetEmitterControllerHeaderTrace.initialRuntime raw)).targetTokens.length +
            (processed.length + 1) * gatePerGateGrowth raw := by
        simp [Nat.add_mul, Nat.add_assoc]
      _ ≤
          (TargetEmitterProgramSemantics.headerResult
              (TargetEmitterControllerHeaderTrace.initialRuntime raw)).targetTokens.length +
            raw.gates.length * gatePerGateGrowth raw :=
        Nat.add_le_add_left countGrowth _
      _ =
          TargetEmitterControllerGateBound.gateTargetLimit
            (TargetEmitterLedger.slotCapacity raw)
            (TargetEmitterProgramSemantics.headerResult
              (TargetEmitterControllerHeaderTrace.initialRuntime raw))
            raw.gates.length := by
        unfold TargetEmitterControllerGateBound.gateTargetLimit
          gatePerGateGrowth
        ac_rfl
  have checkBudget :
      TargetEmitterRuntimeProgramBound.checkCells runtime.checks +
            2 *
              TargetEmitterControllerGateBound.gateBlockGrowth
                (TargetEmitterLedger.slotCapacity raw) ≤
        TargetEmitterControllerGateBound.gateCheckLimit
          (TargetEmitterLedger.slotCapacity raw)
          (TargetEmitterProgramSemantics.headerResult
            (TargetEmitterControllerHeaderTrace.initialRuntime raw))
          raw.gates.length := by
    calc
      _ ≤
          TargetEmitterRuntimeProgramBound.checkCells runtime.checks +
            gatePerGateGrowth raw :=
        Nat.add_le_add_left twoBlocks_le_gateGrowth _
      _ ≤
          (TargetEmitterRuntimeProgramBound.checkCells
              (TargetEmitterProgramSemantics.headerResult
                (TargetEmitterControllerHeaderTrace.initialRuntime raw)).checks +
            processed.length * gatePerGateGrowth raw) +
              gatePerGateGrowth raw :=
        Nat.add_le_add_right checkGrowth _
      _ =
          TargetEmitterRuntimeProgramBound.checkCells
              (TargetEmitterProgramSemantics.headerResult
                (TargetEmitterControllerHeaderTrace.initialRuntime raw)).checks +
            (processed.length + 1) * gatePerGateGrowth raw := by
        simp [Nat.add_mul, Nat.add_assoc]
      _ ≤
          TargetEmitterRuntimeProgramBound.checkCells
              (TargetEmitterProgramSemantics.headerResult
                (TargetEmitterControllerHeaderTrace.initialRuntime raw)).checks +
            raw.gates.length * gatePerGateGrowth raw :=
        Nat.add_le_add_left countGrowth _
      _ =
          TargetEmitterControllerGateBound.gateCheckLimit
            (TargetEmitterLedger.slotCapacity raw)
            (TargetEmitterProgramSemantics.headerResult
              (TargetEmitterControllerHeaderTrace.initialRuntime raw))
            raw.gates.length := by
        unfold TargetEmitterControllerGateBound.gateCheckLimit
          gatePerGateGrowth
        ac_rfl
  have packed :=
    traversalWord_packed raw processed rest gate gatesEq
  have crossedEq := crossedCells_nonempty raw processed
  have sourceLengthBound :
      ((SourceParser.cell00 ::
          (SourceParser.cell00 ::
            (SourceParser.natCells raw.inputCount ++
              SourceParser.natCells raw.gates.length ++
              SourceParser.gateListCells processed))) ++
            SourceParser.sourceCells gate.left ++
            SourceParser.sourceCells gate.right ++
            ([SourceParser.cell01, SourceParser.cell11] ++
              SourceParser.gateListCells rest ++
              TargetEmitterControllerTrace.circuitFooterCells raw.output)).length ≤
        (SourceParser.circuitCells raw).length := by
    have exactLength :=
      congrArg List.length
        (traversalWord_eq_circuitCells
          raw processed rest gate gatesEq)
    exact Nat.le_of_eq
      (by simpa [crossedEq, List.append_assoc] using exactLength)
  rcases
      TargetEmitterControllerGateBound.gateSourcesTraceEnvelope_le_uniform
        runtime
        (TargetEmitterProgramSemantics.headerResult
          (TargetEmitterControllerHeaderTrace.initialRuntime raw))
        currentRange SourceParser.cell00
        (SourceParser.cell00 ::
          (SourceParser.natCells raw.inputCount ++
            SourceParser.natCells raw.gates.length ++
            SourceParser.gateListCells processed))
        ([SourceParser.cell01, SourceParser.cell11] ++
          SourceParser.gateListCells rest ++
          TargetEmitterControllerTrace.circuitFooterCells raw.output)
        gate leftCaptureReserve leftCapturedBound afterLeftRange
        rightCaptureReserve rightCapturedBound afterRightRange
        nextGate
        (by simpa [crossedEq, List.append_assoc] using packed)
        (SourceParser.circuitCells raw).length raw.gates.length
        sourceLengthBound targetBudget checkBudget with
    ⟨envelopeBound, nextTargetGrowth, nextCheckGrowth⟩
  have physicalEq :=
    physicalGateResult_eq_appendGateResult runtime gate
  refine ⟨?_, ?_, ?_⟩
  · simpa [crossedEq, List.append_assoc] using envelopeBound
  · rw [physicalEq] at nextTargetGrowth
    simpa [gatePerGateGrowth] using nextTargetGrowth
  · rw [physicalEq] at nextCheckGrowth
    simpa [gatePerGateGrowth] using nextCheckGrowth

private theorem gateListTraversalEnvelope_le_uniform_aux
    (raw : RawCircuit) (processed : List RawGate)
    (gate : RawGate) (rest : List RawGate)
    (runtime : Runtime)
    (gatesEq : raw.gates = processed ++ gate :: rest)
    (invariant : RegisterInvariant raw processed runtime)
    (scratchShape :
      runtime.scratch = 0 ∨
        runtime.scratch =
          TargetEmitterLedger.baselineValue raw + 1)
    (targetGrowth :
      runtime.targetTokens.length ≤
        (TargetEmitterProgramSemantics.headerResult
          (TargetEmitterControllerHeaderTrace.initialRuntime raw)).targetTokens.length +
          processed.length * gatePerGateGrowth raw)
    (checkGrowth :
      TargetEmitterRuntimeProgramBound.checkCells runtime.checks ≤
        TargetEmitterRuntimeProgramBound.checkCells
            (TargetEmitterProgramSemantics.headerResult
              (TargetEmitterControllerHeaderTrace.initialRuntime raw)).checks +
          processed.length * gatePerGateGrowth raw) :
    gateListTraversalEnvelope raw processed (gate :: rest) runtime ≤
      (gate :: rest).length * gateListUniformUnit raw := by
  induction rest generalizing processed gate runtime with
  | nil =>
      rcases
          currentGateEnvelope_le_uniform raw processed gate []
            runtime gatesEq invariant scratchShape
            targetGrowth checkGrowth with
        ⟨gateBound, _nextTargetGrowth, _nextCheckGrowth⟩
      have gateBound' :
          TargetEmitterControllerGateBound.gateSourcesTraceEnvelope raw
                (crossedCells raw processed)
                ([SourceParser.cell01, SourceParser.cell11] ++
                  TargetEmitterControllerTrace.circuitFooterCells raw.output)
                gate runtime ≤
            TargetEmitterControllerGateBound.gateUniformUnit
              (TargetEmitterLedger.slotCapacity raw)
              (SourceParser.circuitCells raw).length
              (TargetEmitterProgramSemantics.headerResult
                (TargetEmitterControllerHeaderTrace.initialRuntime raw))
              raw.gates.length := by
        simpa [SourceParser.gateListCells, List.append_assoc] using
          gateBound
      have charged :
          TargetEmitterControllerGateBound.gateSourcesTraceEnvelope raw
                (crossedCells raw processed)
                ([SourceParser.cell01, SourceParser.cell11] ++
                  TargetEmitterControllerTrace.circuitFooterCells raw.output)
                gate runtime + 7 ≤
            gateListUniformUnit raw := by
        unfold gateListUniformUnit
        omega
      simpa [gateListTraversalEnvelope] using charged
  | cons next tail inductionHypothesis =>
      rcases
          currentGateEnvelope_le_uniform raw processed gate
            (next :: tail) runtime gatesEq invariant scratchShape
            targetGrowth checkGrowth with
        ⟨gateBound, nextTargetGrowth, nextCheckGrowth⟩
      have nextGatesEq :
          raw.gates =
            (processed ++ [gate]) ++ next :: tail := by
        simpa [List.append_assoc] using gatesEq
      have advancedInvariant :
          RegisterInvariant raw (processed ++ [gate])
            (TargetEmitterSemanticSchedule.appendGateResult
              gate runtime) :=
        invariant.appendGate gate
      have nextScratch :
          (TargetEmitterSemanticSchedule.appendGateResult
            gate runtime).scratch = 0 :=
        appendGateResult_scratch gate runtime
      have nextTargetBound :
          (TargetEmitterSemanticSchedule.appendGateResult
              gate runtime).targetTokens.length ≤
            (TargetEmitterProgramSemantics.headerResult
                (TargetEmitterControllerHeaderTrace.initialRuntime raw)).targetTokens.length +
              (processed ++ [gate]).length *
                gatePerGateGrowth raw := by
        calc
          _ ≤ runtime.targetTokens.length + gatePerGateGrowth raw :=
            nextTargetGrowth
          _ ≤
              ((TargetEmitterProgramSemantics.headerResult
                  (TargetEmitterControllerHeaderTrace.initialRuntime raw)).targetTokens.length +
                processed.length * gatePerGateGrowth raw) +
                  gatePerGateGrowth raw :=
            Nat.add_le_add_right targetGrowth _
          _ =
              (TargetEmitterProgramSemantics.headerResult
                  (TargetEmitterControllerHeaderTrace.initialRuntime raw)).targetTokens.length +
                (processed ++ [gate]).length *
                  gatePerGateGrowth raw := by
            simp [List.length_append, Nat.add_mul, Nat.add_assoc]
      have nextCheckBound :
          TargetEmitterRuntimeProgramBound.checkCells
              (TargetEmitterSemanticSchedule.appendGateResult
                gate runtime).checks ≤
            TargetEmitterRuntimeProgramBound.checkCells
                (TargetEmitterProgramSemantics.headerResult
                  (TargetEmitterControllerHeaderTrace.initialRuntime raw)).checks +
              (processed ++ [gate]).length *
                gatePerGateGrowth raw := by
        calc
          _ ≤
              TargetEmitterRuntimeProgramBound.checkCells runtime.checks +
                gatePerGateGrowth raw :=
            nextCheckGrowth
          _ ≤
              (TargetEmitterRuntimeProgramBound.checkCells
                  (TargetEmitterProgramSemantics.headerResult
                    (TargetEmitterControllerHeaderTrace.initialRuntime raw)).checks +
                processed.length * gatePerGateGrowth raw) +
                  gatePerGateGrowth raw :=
            Nat.add_le_add_right checkGrowth _
          _ =
              TargetEmitterRuntimeProgramBound.checkCells
                  (TargetEmitterProgramSemantics.headerResult
                    (TargetEmitterControllerHeaderTrace.initialRuntime raw)).checks +
                (processed ++ [gate]).length *
                  gatePerGateGrowth raw := by
            simp [List.length_append, Nat.add_mul, Nat.add_assoc]
      have restBound :=
        inductionHypothesis (processed ++ [gate]) next
          (TargetEmitterSemanticSchedule.appendGateResult gate runtime)
          nextGatesEq advancedInvariant (Or.inl nextScratch)
          nextTargetBound nextCheckBound
      have charged :
          TargetEmitterControllerGateBound.gateSourcesTraceEnvelope raw
                (crossedCells raw processed)
                ([SourceParser.cell01, SourceParser.cell11] ++
                  SourceParser.gateListCells (next :: tail) ++
                  TargetEmitterControllerTrace.circuitFooterCells raw.output)
                gate runtime + 4 ≤
            gateListUniformUnit raw := by
        unfold gateListUniformUnit
        omega
      have combined := Nat.add_le_add charged restBound
      simpa only [gateListTraversalEnvelope, List.length_cons,
        Nat.succ_mul, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using combined

/-- The runtime-sensitive recursive gate-list envelope is dominated by one
closed charge depending only on the decoded raw circuit. -/
theorem gateListTraversalEnvelope_le_uniform (raw : RawCircuit) :
    gateListTraversalEnvelope raw [] raw.gates
          (TargetEmitterProgramSemantics.headerResult
            (TargetEmitterControllerHeaderTrace.initialRuntime raw)) ≤
        gateListUniformEnvelope raw := by
  cases gatesEq : raw.gates with
  | nil =>
      simp [gateListTraversalEnvelope, gateListUniformEnvelope, gatesEq]
  | cons gate rest =>
      have bound :=
        gateListTraversalEnvelope_le_uniform_aux raw [] gate rest
          (TargetEmitterProgramSemantics.headerResult
            (TargetEmitterControllerHeaderTrace.initialRuntime raw))
          gatesEq (header_registerInvariant raw)
          (Or.inr (header_scratchShape raw))
          (by simp) (by simp)
      simpa [gateListUniformEnvelope, gatesEq] using bound

private theorem gateListRuntime_growth_aux
    (raw : RawCircuit) (processed rest : List RawGate)
    (runtime : Runtime)
    (gatesEq : raw.gates = processed ++ rest)
    (invariant : RegisterInvariant raw processed runtime)
    (scratchShape :
      runtime.scratch = 0 ∨
        runtime.scratch =
          TargetEmitterLedger.baselineValue raw + 1)
    (targetGrowth :
      runtime.targetTokens.length ≤
        (TargetEmitterProgramSemantics.headerResult
          (TargetEmitterControllerHeaderTrace.initialRuntime raw)).targetTokens.length +
          processed.length * gatePerGateGrowth raw)
    (checkGrowth :
      TargetEmitterRuntimeProgramBound.checkCells runtime.checks ≤
        TargetEmitterRuntimeProgramBound.checkCells
            (TargetEmitterProgramSemantics.headerResult
              (TargetEmitterControllerHeaderTrace.initialRuntime raw)).checks +
          processed.length * gatePerGateGrowth raw) :
    let final :=
      TargetEmitterSemanticSchedule.appendGateListResults rest runtime
    final.targetTokens.length ≤
        (TargetEmitterProgramSemantics.headerResult
          (TargetEmitterControllerHeaderTrace.initialRuntime raw)).targetTokens.length +
          (processed.length + rest.length) * gatePerGateGrowth raw ∧
      TargetEmitterRuntimeProgramBound.checkCells final.checks ≤
        TargetEmitterRuntimeProgramBound.checkCells
            (TargetEmitterProgramSemantics.headerResult
              (TargetEmitterControllerHeaderTrace.initialRuntime raw)).checks +
          (processed.length + rest.length) * gatePerGateGrowth raw := by
  induction rest generalizing processed runtime with
  | nil =>
      simpa [TargetEmitterSemanticSchedule.appendGateListResults] using
        And.intro targetGrowth checkGrowth
  | cons gate tail inductionHypothesis =>
      have currentGatesEq :
          raw.gates = processed ++ gate :: tail := by
        simpa [List.append_assoc] using gatesEq
      rcases
          currentGateEnvelope_le_uniform raw processed gate tail runtime
            currentGatesEq invariant scratchShape targetGrowth checkGrowth with
        ⟨_, nextTargetGrowth, nextCheckGrowth⟩
      let nextRuntime :=
        TargetEmitterSemanticSchedule.appendGateResult gate runtime
      have nextInvariant :
          RegisterInvariant raw (processed ++ [gate]) nextRuntime := by
        exact invariant.appendGate gate
      have nextScratch : nextRuntime.scratch = 0 := by
        exact appendGateResult_scratch gate runtime
      have nextGatesEq :
          raw.gates = (processed ++ [gate]) ++ tail := by
        simpa [List.append_assoc] using currentGatesEq
      have nextTarget :
          nextRuntime.targetTokens.length ≤
            (TargetEmitterProgramSemantics.headerResult
                (TargetEmitterControllerHeaderTrace.initialRuntime raw)).targetTokens.length +
              (processed ++ [gate]).length *
                gatePerGateGrowth raw := by
        calc
          _ ≤ runtime.targetTokens.length + gatePerGateGrowth raw :=
            nextTargetGrowth
          _ ≤
              ((TargetEmitterProgramSemantics.headerResult
                  (TargetEmitterControllerHeaderTrace.initialRuntime raw)).targetTokens.length +
                processed.length * gatePerGateGrowth raw) +
                  gatePerGateGrowth raw :=
            Nat.add_le_add_right targetGrowth _
          _ = _ := by
            simp [List.length_append, Nat.add_mul, Nat.add_assoc]
      have nextChecks :
          TargetEmitterRuntimeProgramBound.checkCells nextRuntime.checks ≤
            TargetEmitterRuntimeProgramBound.checkCells
                (TargetEmitterProgramSemantics.headerResult
                  (TargetEmitterControllerHeaderTrace.initialRuntime raw)).checks +
              (processed ++ [gate]).length *
                gatePerGateGrowth raw := by
        calc
          _ ≤
              TargetEmitterRuntimeProgramBound.checkCells runtime.checks +
                gatePerGateGrowth raw :=
            nextCheckGrowth
          _ ≤
              (TargetEmitterRuntimeProgramBound.checkCells
                  (TargetEmitterProgramSemantics.headerResult
                    (TargetEmitterControllerHeaderTrace.initialRuntime raw)).checks +
                processed.length * gatePerGateGrowth raw) +
                  gatePerGateGrowth raw :=
            Nat.add_le_add_right checkGrowth _
          _ = _ := by
            simp [List.length_append, Nat.add_mul, Nat.add_assoc]
      have tailGrowth :=
        inductionHypothesis (processed ++ [gate]) nextRuntime nextGatesEq
          nextInvariant (Or.inl nextScratch) nextTarget nextChecks
      simpa [TargetEmitterSemanticSchedule.appendGateListResults,
        nextRuntime, List.length_append, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using tailGrowth

/-- The exact semantic runtime after the gate-list traversal stays within the
same closed target/check growth budget used by the uniform work envelope. -/
theorem gateListRuntime_data_le (raw : RawCircuit) :
    (gateListRuntime raw).targetTokens.length ≤
        (TargetEmitterProgramSemantics.headerResult
          (TargetEmitterControllerHeaderTrace.initialRuntime raw)).targetTokens.length +
          raw.gates.length * gatePerGateGrowth raw ∧
      TargetEmitterRuntimeProgramBound.checkCells
          (gateListRuntime raw).checks ≤
        TargetEmitterRuntimeProgramBound.checkCells
            (TargetEmitterProgramSemantics.headerResult
              (TargetEmitterControllerHeaderTrace.initialRuntime raw)).checks +
          raw.gates.length * gatePerGateGrowth raw := by
  have growth :=
    gateListRuntime_growth_aux raw [] raw.gates
      (TargetEmitterProgramSemantics.headerResult
        (TargetEmitterControllerHeaderTrace.initialRuntime raw))
      (by simp) (header_registerInvariant raw)
      (Or.inr (header_scratchShape raw)) (by simp) (by simp)
  simpa [gateListRuntime] using growth

private theorem gateList_to_output_path
    (raw : RawCircuit) (processed : List RawGate)
    (gate : RawGate) (rest : List RawGate)
    (runtime : Runtime) (initialTape : WorkTape)
    (gatesEq : raw.gates = processed ++ gate :: rest)
    (invariant : RegisterInvariant raw processed runtime)
    (scratchShape :
      runtime.scratch = 0 ∨
        runtime.scratch =
          TargetEmitterLedger.baselineValue raw + 1)
    (represents :
      FocusTapeRepresents leftFirstRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        runtime.scratch runtime.registers runtime.checks
        (crossedCells raw processed)
        (SourceParser.sourceCells gate.left ++
          SourceParser.sourceCells gate.right ++
          [SourceParser.cell01, SourceParser.cell11] ++
          SourceParser.gateListCells rest ++
          TargetEmitterControllerTrace.circuitFooterCells raw.output)
        runtime.targetTokens initialTape) :
    ∃ steps finalTape,
      AcceptPath graph (.node leftFirstRef)
          (.node outputFirstRef) steps initialTape finalTape ∧
      FocusTapeRepresents outputFirstRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterSemanticSchedule.appendGateListResults
          (gate :: rest) runtime).scratch
        (TargetEmitterSemanticSchedule.appendGateListResults
          (gate :: rest) runtime).registers
        (TargetEmitterSemanticSchedule.appendGateListResults
          (gate :: rest) runtime).checks
        (outputCrossedCells raw)
        (SourceParser.sourceCells raw.output ++
          TargetEmitterControllerTrace.circuitTerminatorCells)
        (TargetEmitterSemanticSchedule.appendGateListResults
          (gate :: rest) runtime).targetTokens finalTape ∧
      steps ≤
        gateListTraversalEnvelope raw processed
          (gate :: rest) runtime := by
  induction rest generalizing processed gate runtime initialTape with
  | nil =>
      have gateMember : gate ∈ raw.gates := by
        rw [gatesEq]
        simp
      have leftMember :
          TargetEmitterCapacity.CircuitSource raw gate.left :=
        .gateLeft gateMember
      have rightMember :
          TargetEmitterCapacity.CircuitSource raw gate.right :=
        .gateRight gateMember
      have currentRange :
          TargetEmitterCapacity.ControllerRange raw runtime.registers := by
        exact
          controllerRange_of_invariant raw processed [gate]
            runtime gatesEq invariant
      have ranges :=
        partialControllerRanges raw processed [] runtime
          gate gatesEq invariant
      rcases ranges with
        ⟨afterLeftRange0, afterRightRange0, nextGate0⟩
      have leftCapturedBound :
          TargetEmitterControllerSourceTrace.capturedValue
              (TargetEmitterControllerTrace.sourceKind gate.left)
              (TargetEmitterControllerGateTrace.sourceValue gate.left) + 1 ≤
            (SourceParser.circuitCells raw).length := by
        simpa [sourceCapturedValue_eq] using
          TargetEmitterCapacity.circuitSourceCaptureValue_succ_le_cells
            leftMember
      have rightCapturedBound :
          TargetEmitterControllerSourceTrace.capturedValue
              (TargetEmitterControllerTrace.sourceKind gate.right)
              (TargetEmitterControllerGateTrace.sourceValue gate.right) + 1 ≤
            (SourceParser.circuitCells raw).length := by
        simpa [sourceCapturedValue_eq] using
          TargetEmitterCapacity.circuitSourceCaptureValue_succ_le_cells
            rightMember
      have leftCaptureReserve :
          runtime.scratch +
              TargetEmitterControllerSourceTrace.capturedValue
                (TargetEmitterControllerTrace.sourceKind gate.left)
                (TargetEmitterControllerGateTrace.sourceValue gate.left) + 1 ≤
            TargetEmitterLedger.slotCapacity raw := by
        rcases scratchShape with scratchZero | scratchHeader
        · rw [scratchZero]
          simpa [sourceCapturedValue_eq] using
            TargetEmitterCapacity.focusedSourceCaptureReserve leftMember
        · rw [scratchHeader]
          simpa [sourceCapturedValue_eq] using
            TargetEmitterCapacity.headerFocusedSourceCaptureReserve leftMember
      let leftPhysical :=
        TargetEmitterProgramSemantics.macroResult
          (TargetEmitterControllerGateTrace.capturedRuntime runtime
            (TargetEmitterControllerTrace.sourceKind gate.left)
            (TargetEmitterControllerGateTrace.sourceValue gate.left))
          (TargetEmitterPlan.sourcePlan
            (TargetEmitterControllerTrace.sourceKind gate.left) 0)
          (TargetEmitterPlan.sourceCheckRelative
            (TargetEmitterControllerTrace.sourceKind gate.left))
          (TargetEmitterPlan.sourceGateCount
            (TargetEmitterControllerTrace.sourceKind gate.left))
      have leftPhysicalEq :
          leftPhysical =
            TargetEmitterSemanticSchedule.appendSourceResult
              0 gate.left runtime := by
        exact physicalSourceResult_eq_appendSourceResult runtime gate.left 0
      have afterLeftRange :
          TargetEmitterCapacity.ControllerRange raw
            leftPhysical.registers := by
        rw [leftPhysicalEq]
        exact afterLeftRange0
      have rightCaptureReserve :
          leftPhysical.scratch +
              TargetEmitterControllerSourceTrace.capturedValue
                (TargetEmitterControllerTrace.sourceKind gate.right)
                (TargetEmitterControllerGateTrace.sourceValue gate.right) + 1 ≤
            TargetEmitterLedger.slotCapacity raw := by
        rw [leftPhysicalEq]
        rw [appendSourceResult_scratch]
        simpa [sourceCapturedValue_eq] using
          TargetEmitterCapacity.focusedSourceCaptureReserve rightMember
      let rightPhysical :=
        TargetEmitterProgramSemantics.macroResult
          (TargetEmitterControllerGateTrace.capturedRuntime leftPhysical
            (TargetEmitterControllerTrace.sourceKind gate.right)
            (TargetEmitterControllerGateTrace.sourceValue gate.right))
          (TargetEmitterPlan.sourcePlan
            (TargetEmitterControllerTrace.sourceKind gate.right) 1)
          (TargetEmitterPlan.sourceCheckRelative
            (TargetEmitterControllerTrace.sourceKind gate.right))
          (TargetEmitterPlan.sourceGateCount
            (TargetEmitterControllerTrace.sourceKind gate.right))
      have rightPhysicalEq :
          rightPhysical =
            TargetEmitterSemanticSchedule.appendSourceResult
              1 gate.right
                (TargetEmitterSemanticSchedule.appendSourceResult
                  0 gate.left runtime) := by
        dsimp only [rightPhysical]
        calc
          _ = TargetEmitterSemanticSchedule.appendSourceResult
                1 gate.right leftPhysical :=
            physicalSourceResult_eq_appendSourceResult
              leftPhysical gate.right 1
          _ = _ := by rw [leftPhysicalEq]
      have afterRightRange :
          TargetEmitterCapacity.ControllerRange raw
            rightPhysical.registers := by
        rw [rightPhysicalEq]
        exact afterRightRange0
      have nextGate :
          rightPhysical.registers.currentGate + 1 ≤
            TargetEmitterLedger.normalizedGateCount raw := by
        rw [rightPhysicalEq]
        exact nextGate0
      have packed :=
        traversalWord_packed raw processed [] gate gatesEq
      have crossedEq := crossedCells_nonempty raw processed
      rcases
          TargetEmitterControllerGateBound.gateSourcesTrace_path_bounded
            runtime currentRange SourceParser.cell00
            (SourceParser.cell00 ::
              (SourceParser.natCells raw.inputCount ++
                SourceParser.natCells raw.gates.length ++
                SourceParser.gateListCells processed))
            ([SourceParser.cell01, SourceParser.cell11] ++
              TargetEmitterControllerTrace.circuitFooterCells raw.output)
            gate runtime.targetTokens initialTape
            leftCaptureReserve leftCapturedBound afterLeftRange
            rightCaptureReserve rightCapturedBound afterRightRange
            nextGate (by
              simpa [crossedEq, SourceParser.gateListCells,
                List.append_assoc] using packed)
            rfl (by
              simpa [crossedEq, SourceParser.gateListCells,
                List.append_assoc] using represents) with
        ⟨gateSteps, gateTape, gatePath, finalRuntime,
          finalRuntimeEq, gateRepresents, gateBound⟩
      have semanticRuntimeEq :
          finalRuntime =
            TargetEmitterSemanticSchedule.appendGateResult gate runtime := by
        rw [finalRuntimeEq]
        exact physicalGateResult_eq_appendGateResult runtime gate
      have atAdvance :
          FocusTapeRepresents gateAdvanceRef.startState
            (TargetEmitterLedger.slotCapacity raw)
            (TargetEmitterSemanticSchedule.appendGateResult gate runtime).scratch
            (TargetEmitterSemanticSchedule.appendGateResult gate runtime).registers
            (TargetEmitterSemanticSchedule.appendGateResult gate runtime).checks
            (crossedCells raw processed ++
              SourceParser.sourceCells gate.left ++
              SourceParser.sourceCells gate.right)
            ([SourceParser.cell01, SourceParser.cell11] ++
              TargetEmitterControllerTrace.circuitFooterCells raw.output)
            (TargetEmitterSemanticSchedule.appendGateResult gate runtime).targetTokens
            gateTape := by
        simpa [semanticRuntimeEq, crossedEq, List.append_assoc] using
          gateRepresents
      rcases
          TargetEmitterControllerGateTrace.gateAdvanceOutput_path
            (TargetEmitterLedger.slotCapacity raw)
            (TargetEmitterSemanticSchedule.appendGateResult gate runtime).scratch
            (TargetEmitterSemanticSchedule.appendGateResult gate runtime).registers
            (TargetEmitterSemanticSchedule.appendGateResult gate runtime).checks
            (crossedCells raw processed ++
              SourceParser.sourceCells gate.left ++
              SourceParser.sourceCells gate.right)
            raw.output
            (TargetEmitterSemanticSchedule.appendGateResult gate runtime).targetTokens
            gateTape atAdvance with
        ⟨finalTape, outputPath, outputRepresents⟩
      refine ⟨gateSteps + 7, finalTape, ?_, ?_, ?_⟩
      · exact
          AcceptPath.trans graph (.node leftFirstRef)
            (.node gateAdvanceRef) (.node outputFirstRef)
            gateSteps 7 initialTape gateTape finalTape
            gatePath outputPath
      · simpa [TargetEmitterSemanticSchedule.appendGateListResults,
          outputCrossedCells, crossedCells, gatesEq,
          gateListCells_append,
          SourceParser.gateListCells, SourceParser.gateCells,
          List.append_assoc] using outputRepresents
      · simpa [gateListTraversalEnvelope, crossedEq,
          SourceParser.gateListCells, List.append_assoc] using
          Nat.add_le_add_right gateBound 7
  | cons next tail inductionHypothesis =>
      have gateMember : gate ∈ raw.gates := by
        rw [gatesEq]
        simp
      have leftMember :
          TargetEmitterCapacity.CircuitSource raw gate.left :=
        .gateLeft gateMember
      have rightMember :
          TargetEmitterCapacity.CircuitSource raw gate.right :=
        .gateRight gateMember
      have currentRange :
          TargetEmitterCapacity.ControllerRange raw runtime.registers := by
        exact
          controllerRange_of_invariant raw processed
            (gate :: next :: tail) runtime gatesEq invariant
      have ranges :=
        partialControllerRanges raw processed (next :: tail)
          runtime gate gatesEq invariant
      rcases ranges with
        ⟨afterLeftRange0, afterRightRange0, nextGate0⟩
      have leftCapturedBound :
          TargetEmitterControllerSourceTrace.capturedValue
              (TargetEmitterControllerTrace.sourceKind gate.left)
              (TargetEmitterControllerGateTrace.sourceValue gate.left) + 1 ≤
            (SourceParser.circuitCells raw).length := by
        simpa [sourceCapturedValue_eq] using
          TargetEmitterCapacity.circuitSourceCaptureValue_succ_le_cells
            leftMember
      have rightCapturedBound :
          TargetEmitterControllerSourceTrace.capturedValue
              (TargetEmitterControllerTrace.sourceKind gate.right)
              (TargetEmitterControllerGateTrace.sourceValue gate.right) + 1 ≤
            (SourceParser.circuitCells raw).length := by
        simpa [sourceCapturedValue_eq] using
          TargetEmitterCapacity.circuitSourceCaptureValue_succ_le_cells
            rightMember
      have leftCaptureReserve :
          runtime.scratch +
              TargetEmitterControllerSourceTrace.capturedValue
                (TargetEmitterControllerTrace.sourceKind gate.left)
                (TargetEmitterControllerGateTrace.sourceValue gate.left) + 1 ≤
            TargetEmitterLedger.slotCapacity raw := by
        rcases scratchShape with scratchZero | scratchHeader
        · rw [scratchZero]
          simpa [sourceCapturedValue_eq] using
            TargetEmitterCapacity.focusedSourceCaptureReserve leftMember
        · rw [scratchHeader]
          simpa [sourceCapturedValue_eq] using
            TargetEmitterCapacity.headerFocusedSourceCaptureReserve leftMember
      let leftPhysical :=
        TargetEmitterProgramSemantics.macroResult
          (TargetEmitterControllerGateTrace.capturedRuntime runtime
            (TargetEmitterControllerTrace.sourceKind gate.left)
            (TargetEmitterControllerGateTrace.sourceValue gate.left))
          (TargetEmitterPlan.sourcePlan
            (TargetEmitterControllerTrace.sourceKind gate.left) 0)
          (TargetEmitterPlan.sourceCheckRelative
            (TargetEmitterControllerTrace.sourceKind gate.left))
          (TargetEmitterPlan.sourceGateCount
            (TargetEmitterControllerTrace.sourceKind gate.left))
      have leftPhysicalEq :
          leftPhysical =
            TargetEmitterSemanticSchedule.appendSourceResult
              0 gate.left runtime := by
        exact physicalSourceResult_eq_appendSourceResult runtime gate.left 0
      have afterLeftRange :
          TargetEmitterCapacity.ControllerRange raw
            leftPhysical.registers := by
        rw [leftPhysicalEq]
        exact afterLeftRange0
      have rightCaptureReserve :
          leftPhysical.scratch +
              TargetEmitterControllerSourceTrace.capturedValue
                (TargetEmitterControllerTrace.sourceKind gate.right)
                (TargetEmitterControllerGateTrace.sourceValue gate.right) + 1 ≤
            TargetEmitterLedger.slotCapacity raw := by
        rw [leftPhysicalEq]
        rw [appendSourceResult_scratch]
        simpa [sourceCapturedValue_eq] using
          TargetEmitterCapacity.focusedSourceCaptureReserve rightMember
      let rightPhysical :=
        TargetEmitterProgramSemantics.macroResult
          (TargetEmitterControllerGateTrace.capturedRuntime leftPhysical
            (TargetEmitterControllerTrace.sourceKind gate.right)
            (TargetEmitterControllerGateTrace.sourceValue gate.right))
          (TargetEmitterPlan.sourcePlan
            (TargetEmitterControllerTrace.sourceKind gate.right) 1)
          (TargetEmitterPlan.sourceCheckRelative
            (TargetEmitterControllerTrace.sourceKind gate.right))
          (TargetEmitterPlan.sourceGateCount
            (TargetEmitterControllerTrace.sourceKind gate.right))
      have rightPhysicalEq :
          rightPhysical =
            TargetEmitterSemanticSchedule.appendSourceResult
              1 gate.right
                (TargetEmitterSemanticSchedule.appendSourceResult
                  0 gate.left runtime) := by
        dsimp only [rightPhysical]
        calc
          _ = TargetEmitterSemanticSchedule.appendSourceResult
                1 gate.right leftPhysical :=
            physicalSourceResult_eq_appendSourceResult
              leftPhysical gate.right 1
          _ = _ := by rw [leftPhysicalEq]
      have afterRightRange :
          TargetEmitterCapacity.ControllerRange raw
            rightPhysical.registers := by
        rw [rightPhysicalEq]
        exact afterRightRange0
      have nextGate :
          rightPhysical.registers.currentGate + 1 ≤
            TargetEmitterLedger.normalizedGateCount raw := by
        rw [rightPhysicalEq]
        exact nextGate0
      have packed :=
        traversalWord_packed raw processed (next :: tail) gate gatesEq
      have crossedEq := crossedCells_nonempty raw processed
      rcases
          TargetEmitterControllerGateBound.gateSourcesTrace_path_bounded
            runtime currentRange SourceParser.cell00
            (SourceParser.cell00 ::
              (SourceParser.natCells raw.inputCount ++
                SourceParser.natCells raw.gates.length ++
                SourceParser.gateListCells processed))
            ([SourceParser.cell01, SourceParser.cell11] ++
              SourceParser.gateListCells (next :: tail) ++
              TargetEmitterControllerTrace.circuitFooterCells raw.output)
            gate runtime.targetTokens initialTape
            leftCaptureReserve leftCapturedBound afterLeftRange
            rightCaptureReserve rightCapturedBound afterRightRange
            nextGate (by
              simpa [crossedEq, List.append_assoc] using packed)
            rfl (by simpa [crossedEq, List.append_assoc] using represents) with
        ⟨gateSteps, gateTape, gatePath, finalRuntime,
          finalRuntimeEq, gateRepresents, gateBound⟩
      have semanticRuntimeEq :
          finalRuntime =
            TargetEmitterSemanticSchedule.appendGateResult gate runtime := by
        rw [finalRuntimeEq]
        exact physicalGateResult_eq_appendGateResult runtime gate
      have atAdvance :
          FocusTapeRepresents gateAdvanceRef.startState
            (TargetEmitterLedger.slotCapacity raw)
            (TargetEmitterSemanticSchedule.appendGateResult gate runtime).scratch
            (TargetEmitterSemanticSchedule.appendGateResult gate runtime).registers
            (TargetEmitterSemanticSchedule.appendGateResult gate runtime).checks
            (crossedCells raw processed ++
              SourceParser.sourceCells gate.left ++
              SourceParser.sourceCells gate.right)
            ([SourceParser.cell01, SourceParser.cell11] ++
              SourceParser.gateListCells (next :: tail) ++
              TargetEmitterControllerTrace.circuitFooterCells raw.output)
            (TargetEmitterSemanticSchedule.appendGateResult gate runtime).targetTokens
            gateTape := by
        simpa [semanticRuntimeEq, crossedEq, List.append_assoc] using
          gateRepresents
      rcases
          TargetEmitterControllerGateTrace.gateAdvanceNext_path
            (TargetEmitterLedger.slotCapacity raw)
            (TargetEmitterSemanticSchedule.appendGateResult gate runtime).scratch
            (TargetEmitterSemanticSchedule.appendGateResult gate runtime).registers
            (TargetEmitterSemanticSchedule.appendGateResult gate runtime).checks
            (crossedCells raw processed ++
              SourceParser.sourceCells gate.left ++
              SourceParser.sourceCells gate.right)
            (SourceParser.sourceCells next.right ++
              [SourceParser.cell01, SourceParser.cell11] ++
              SourceParser.gateListCells tail ++
              TargetEmitterControllerTrace.circuitFooterCells raw.output)
            next.left
            (TargetEmitterSemanticSchedule.appendGateResult gate runtime).targetTokens
            gateTape (by
              simpa [SourceParser.gateListCells, SourceParser.gateCells,
                List.append_assoc] using atAdvance) with
        ⟨nextTape, advancePath, nextRepresents⟩
      have nextGatesEq :
          raw.gates =
            (processed ++ [gate]) ++ next :: tail := by
        simpa [List.append_assoc] using gatesEq
      have advancedInvariant :
          RegisterInvariant raw (processed ++ [gate])
            (TargetEmitterSemanticSchedule.appendGateResult gate runtime) :=
        invariant.appendGate gate
      have nextFocus :
          FocusTapeRepresents leftFirstRef.startState
            (TargetEmitterLedger.slotCapacity raw)
            (TargetEmitterSemanticSchedule.appendGateResult gate runtime).scratch
            (TargetEmitterSemanticSchedule.appendGateResult gate runtime).registers
            (TargetEmitterSemanticSchedule.appendGateResult gate runtime).checks
            (crossedCells raw (processed ++ [gate]))
            (SourceParser.sourceCells next.left ++
              SourceParser.sourceCells next.right ++
              [SourceParser.cell01, SourceParser.cell11] ++
              SourceParser.gateListCells tail ++
              TargetEmitterControllerTrace.circuitFooterCells raw.output)
            (TargetEmitterSemanticSchedule.appendGateResult gate runtime).targetTokens
            nextTape := by
        simpa only [crossedCells, gateListCells_append,
          SourceParser.gateListCells, SourceParser.gateCells,
          List.append_assoc, List.append_nil,
          List.nil_append] using nextRepresents
      have nextScratch :
          (TargetEmitterSemanticSchedule.appendGateResult gate runtime).scratch =
            0 := by
        exact appendGateResult_scratch gate runtime
      rcases
          inductionHypothesis (processed ++ [gate]) next
            (TargetEmitterSemanticSchedule.appendGateResult gate runtime)
            nextTape nextGatesEq advancedInvariant
            (Or.inl nextScratch) nextFocus with
        ⟨restSteps, finalTape, restPath,
          finalRepresents, restBound⟩
      refine
        ⟨gateSteps + 4 + restSteps, finalTape, ?_, ?_, ?_⟩
      · have first :=
          AcceptPath.trans graph (.node leftFirstRef)
            (.node gateAdvanceRef) (.node leftFirstRef)
            gateSteps 4 initialTape gateTape nextTape
            gatePath advancePath
        exact
          AcceptPath.trans graph (.node leftFirstRef)
            (.node leftFirstRef) (.node outputFirstRef)
            (gateSteps + 4) restSteps initialTape nextTape finalTape
            first restPath
      · simpa [TargetEmitterSemanticSchedule.appendGateListResults] using
          finalRepresents
      · simp only [gateListTraversalEnvelope]
        have firstBound :=
          Nat.add_le_add_right gateBound 4
        have completeBound :=
          Nat.add_le_add firstBound restBound
        simpa [crossedEq, List.append_assoc] using completeBound

private theorem header_nonempty_represents
    (inputs : Nat) (gate : RawGate) (rest : List RawGate)
    (output : RawSource) (tape : WorkTape)
    (equivalent :
      WorkTape.BlankEquivalent tape
        (TargetEmitterControllerTrace.sourceFocusTape
          ((TargetEmitterControllerTrace.circuitHeaderCells
                inputs (gate :: rest).length).reverse ++
            TargetEmitterRuntime.logicalLeftWorkspace
              (TargetEmitterLedger.slotCapacity
                { inputCount := inputs
                  gates := gate :: rest
                  output := output })
              (TargetEmitterProgramSemantics.headerResult
                (TargetEmitterControllerHeaderTrace.initialRuntime
                  { inputCount := inputs
                    gates := gate :: rest
                    output := output })).scratch
              (TargetEmitterProgramSemantics.headerResult
                (TargetEmitterControllerHeaderTrace.initialRuntime
                  { inputCount := inputs
                    gates := gate :: rest
                    output := output })).registers
              (TargetEmitterProgramSemantics.headerResult
                (TargetEmitterControllerHeaderTrace.initialRuntime
                  { inputCount := inputs
                    gates := gate :: rest
                    output := output })).checks)
          gate.left
          (SourceParser.sourceCells gate.right ++
            [SourceParser.cell01, SourceParser.cell11] ++
            SourceParser.gateListCells rest ++
            TargetEmitterControllerTrace.circuitFooterCells output ++
            TargetEmitter.sourceTargetBoundary ::
              SourceParser.packedTokenCells
                (TargetEmitterProgramSemantics.headerResult
                  (TargetEmitterControllerHeaderTrace.initialRuntime
                    { inputCount := inputs
                      gates := gate :: rest
                      output := output })).targetTokens))) :
    let raw : RawCircuit :=
      { inputCount := inputs
        gates := gate :: rest
        output := output }
    let afterHeader :=
      TargetEmitterProgramSemantics.headerResult
        (TargetEmitterControllerHeaderTrace.initialRuntime raw)
    FocusTapeRepresents leftFirstRef.startState
      (TargetEmitterLedger.slotCapacity raw)
      afterHeader.scratch afterHeader.registers afterHeader.checks
      (crossedCells raw [])
      (SourceParser.sourceCells gate.left ++
        SourceParser.sourceCells gate.right ++
        [SourceParser.cell01, SourceParser.cell11] ++
        SourceParser.gateListCells rest ++
        TargetEmitterControllerTrace.circuitFooterCells output)
      afterHeader.targetTokens tape := by
  dsimp only
  apply focusRepresents_of_tape_equivalent
  simp only [
    TargetEmitterRuntimeSourceControl.sourceFocusConfiguration,
    TargetEmitterRuntimeSourceControl.targetSuffix,
    crossedCells, SourceParser.gateListCells,
    List.reverse_append]
  rw [configAtWord_tape_irrel leftFirstRef.startState 0]
  simpa [TargetEmitterControllerTrace.sourceFocusTape,
    List.append_assoc] using equivalent

/-- Empty literal gate lists advance directly from the program-end navigator
to the first output-source controller, retaining the exact header runtime. -/
theorem stack_gateList_empty_to_output_path
    (inputs : Nat) (output : RawSource) :
    let raw : RawCircuit :=
      { inputCount := inputs, gates := [], output := output }
    let finalRuntime := gateListRuntime raw
    ∃ blockSteps finalTape,
      AcceptPath graph (.node stackInitializeRef)
          (.node outputFirstRef)
          (TargetEmitterCheckStack.Initialize.workSteps
              (TargetEmitterLedger.slotCapacity raw) + 1 +
            blockSteps +
            (TargetEmitterNavigator.headerWorkSteps inputs 0 + 1) + 3)
          (TargetEmitterLedger.finalConfiguration raw).tape finalTape ∧
      FocusTapeRepresents outputFirstRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        finalRuntime.scratch finalRuntime.registers finalRuntime.checks
        (outputCrossedCells raw)
        (SourceParser.sourceCells output ++
          TargetEmitterControllerTrace.circuitTerminatorCells)
        finalRuntime.targetTokens finalTape := by
  dsimp only
  let raw : RawCircuit :=
    { inputCount := inputs, gates := [], output := output }
  let afterHeader :=
    TargetEmitterProgramSemantics.headerResult
      (TargetEmitterControllerHeaderTrace.initialRuntime raw)
  rcases
      TargetEmitterControllerHeaderTrace.stack_header_empty_path
        inputs output with
    ⟨blockSteps, programEndTape, headerPath, programEndEquivalent⟩
  have canonicalPath :=
    TargetEmitterControllerTrace.program_end_path
      ((TargetEmitterControllerTrace.circuitHeaderCells inputs 0).reverse ++
        TargetEmitterRuntime.logicalLeftWorkspace
          (TargetEmitterLedger.slotCapacity raw)
          afterHeader.scratch afterHeader.registers afterHeader.checks)
      output afterHeader.targetTokens
  rcases canonicalPath.transport programEndEquivalent with
    ⟨finalTape, outputPath, outputEquivalent⟩
  refine ⟨blockSteps, finalTape, ?_, ?_⟩
  · exact
      AcceptPath.trans graph (.node stackInitializeRef)
        (.node programEndRef) (.node outputFirstRef)
        (TargetEmitterCheckStack.Initialize.workSteps
            (TargetEmitterLedger.slotCapacity raw) + 1 +
          blockSteps +
          (TargetEmitterNavigator.headerWorkSteps inputs 0 + 1))
        3 _ _ _ headerPath outputPath
  · apply focusRepresents_of_tape_equivalent
    simp only [gateListRuntime,
      TargetEmitterSemanticSchedule.appendGateListResults,
      TargetEmitterRuntimeSourceControl.sourceFocusConfiguration,
      TargetEmitterRuntimeSourceControl.targetSuffix,
      outputCrossedCells,
      TargetEmitterControllerTrace.circuitHeaderCells,
      SourceParser.gateListCells, List.append_nil,
      List.reverse_append]
    rw [configAtWord_tape_irrel outputFirstRef.startState 0]
    simpa [TargetEmitterControllerTrace.sourceFocusTape,
      TargetEmitterControllerTrace.circuitHeaderCells,
      List.append_assoc] using outputEquivalent

/-- A nonempty literal gate list is traversed in source order.  Every source
macro and trace macro is materialized, the last gate takes the program-end
branch, and the retained head advances exactly to the raw output source. -/
theorem stack_gateList_nonempty_to_output_path
    (inputs : Nat) (gate : RawGate)
    (rest : List RawGate) (output : RawSource) :
    let raw : RawCircuit :=
      { inputCount := inputs, gates := gate :: rest, output := output }
    let finalRuntime := gateListRuntime raw
    ∃ blockSteps traversalSteps finalTape,
      AcceptPath graph (.node stackInitializeRef)
          (.node outputFirstRef)
          (TargetEmitterCheckStack.Initialize.workSteps
              (TargetEmitterLedger.slotCapacity raw) + 1 +
            blockSteps +
            (TargetEmitterNavigator.headerWorkSteps
              inputs (gate :: rest).length + 1) +
            traversalSteps)
          (TargetEmitterLedger.finalConfiguration raw).tape finalTape ∧
      FocusTapeRepresents outputFirstRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        finalRuntime.scratch finalRuntime.registers finalRuntime.checks
        (outputCrossedCells raw)
        (SourceParser.sourceCells output ++
          TargetEmitterControllerTrace.circuitTerminatorCells)
        finalRuntime.targetTokens finalTape ∧
      traversalSteps ≤
        gateListTraversalEnvelope raw [] (gate :: rest)
          (TargetEmitterProgramSemantics.headerResult
            (TargetEmitterControllerHeaderTrace.initialRuntime raw)) := by
  dsimp only
  let raw : RawCircuit :=
    { inputCount := inputs, gates := gate :: rest, output := output }
  let afterHeader :=
    TargetEmitterProgramSemantics.headerResult
      (TargetEmitterControllerHeaderTrace.initialRuntime raw)
  rcases
      TargetEmitterControllerHeaderTrace.stack_header_nonempty_path
        inputs gate rest output with
    ⟨blockSteps, headerTape, headerPath, headerEquivalent⟩
  have headerRepresents :
      FocusTapeRepresents leftFirstRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        afterHeader.scratch afterHeader.registers afterHeader.checks
        (crossedCells raw [])
        (SourceParser.sourceCells gate.left ++
          SourceParser.sourceCells gate.right ++
          [SourceParser.cell01, SourceParser.cell11] ++
          SourceParser.gateListCells rest ++
          TargetEmitterControllerTrace.circuitFooterCells output)
        afterHeader.targetTokens headerTape := by
    exact header_nonempty_represents inputs gate rest output
      headerTape headerEquivalent
  have initialInvariant :
      RegisterInvariant raw [] afterHeader := by
    refine
      { inputCount := ?_
        normalizedGateCount := ?_
        carrierWidth := ?_
        baseline := ?_
        currentGate := ?_
        outputIndex := ?_ } <;>
      rw [TargetEmitterProgramSemantics.headerResult_registers] <;>
      rfl
  have scratchShape :
      afterHeader.scratch =
        TargetEmitterLedger.baselineValue raw + 1 := by
    rw [TargetEmitterProgramSemantics.headerResult_scratch]
    rfl
  rcases
      gateList_to_output_path raw [] gate rest afterHeader headerTape
        rfl initialInvariant (Or.inr scratchShape)
        headerRepresents with
    ⟨traversalSteps, finalTape, traversalPath,
      finalRepresents, traversalBound⟩
  refine
    ⟨blockSteps, traversalSteps, finalTape, ?_, ?_,
      by simpa [afterHeader] using traversalBound⟩
  · exact
      AcceptPath.trans graph (.node stackInitializeRef)
        (.node leftFirstRef) (.node outputFirstRef)
        (TargetEmitterCheckStack.Initialize.workSteps
            (TargetEmitterLedger.slotCapacity raw) + 1 +
          blockSteps +
          (TargetEmitterNavigator.headerWorkSteps
            inputs (gate :: rest).length + 1))
        traversalSteps _ _ _ headerPath traversalPath
  · simpa [gateListRuntime, raw, afterHeader] using finalRepresents

/-- Closed gate-list traversal for every raw circuit, including the empty
case.  The theorem exposes no caller schedule, capacity certificate, or
source-membership witness. -/
theorem stack_gateList_to_output_path
    (raw : RawCircuit) :
    ∃ steps finalTape,
      AcceptPath graph (.node stackInitializeRef)
          (.node outputFirstRef) steps
          (TargetEmitterLedger.finalConfiguration raw).tape finalTape ∧
      FocusTapeRepresents outputFirstRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (gateListRuntime raw).scratch
        (gateListRuntime raw).registers
        (gateListRuntime raw).checks
        (outputCrossedCells raw)
        (SourceParser.sourceCells raw.output ++
          TargetEmitterControllerTrace.circuitTerminatorCells)
        (gateListRuntime raw).targetTokens finalTape := by
  cases raw with
  | mk inputs gates output =>
      cases gates with
      | nil =>
          rcases stack_gateList_empty_to_output_path inputs output with
            ⟨blockSteps, finalTape, path, represents⟩
          exact ⟨_, finalTape, path, represents⟩
      | cons gate rest =>
          rcases
              stack_gateList_nonempty_to_output_path
                inputs gate rest output with
            ⟨blockSteps, traversalSteps, finalTape, path,
              represents, _traversalBound⟩
          exact ⟨_, finalTape, path, represents⟩

/-- Closed runtime-sensitive envelope for the initialized header navigation
and the complete literal gate-list traversal. -/
def stackGateListEnvelope (raw : RawCircuit) : Nat :=
  TargetEmitterControllerHeaderBound.stackHeaderNavigatorEnvelope raw +
    match raw.gates with
    | [] => 3
    | _ =>
        gateListTraversalEnvelope raw [] raw.gates
          (TargetEmitterProgramSemantics.headerResult
            (TargetEmitterControllerHeaderTrace.initialRuntime raw))

/-- Closed header-plus-gate-list charge with no evolving runtime argument. -/
def stackGateListUniformEnvelope (raw : RawCircuit) : Nat :=
  TargetEmitterControllerHeaderBound.stackHeaderNavigatorEnvelope raw +
    3 + gateListUniformEnvelope raw

/-- The exact runtime-sensitive stack/gate-list envelope is dominated by the
closed uniform charge. -/
theorem stackGateListEnvelope_le_uniform (raw : RawCircuit) :
    stackGateListEnvelope raw ≤ stackGateListUniformEnvelope raw := by
  unfold stackGateListEnvelope stackGateListUniformEnvelope
  cases gatesEq : raw.gates with
  | nil =>
      simp [gateListUniformEnvelope, gatesEq]
  | cons gate rest =>
      have bound := gateListTraversalEnvelope_le_uniform raw
      simp only [gatesEq] at bound ⊢
      omega

/-- Closed bounded gate-list traversal for every raw circuit. -/
theorem stack_gateList_to_output_path_bounded
    (raw : RawCircuit) :
    ∃ steps finalTape,
      AcceptPath graph (.node stackInitializeRef)
          (.node outputFirstRef) steps
          (TargetEmitterLedger.finalConfiguration raw).tape finalTape ∧
      FocusTapeRepresents outputFirstRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (gateListRuntime raw).scratch
        (gateListRuntime raw).registers
        (gateListRuntime raw).checks
        (outputCrossedCells raw)
        (SourceParser.sourceCells raw.output ++
          TargetEmitterControllerTrace.circuitTerminatorCells)
        (gateListRuntime raw).targetTokens finalTape ∧
      steps ≤ stackGateListEnvelope raw := by
  cases raw with
  | mk inputs gates output =>
      cases gates with
      | nil =>
          let raw : RawCircuit :=
            { inputCount := inputs, gates := [], output := output }
          let afterHeader :=
            TargetEmitterProgramSemantics.headerResult
              (TargetEmitterControllerHeaderTrace.initialRuntime raw)
          rcases
              TargetEmitterControllerHeaderBound.stack_header_empty_path_bounded
                inputs output with
            ⟨headerSteps, programEndTape, headerPath,
              programEndEquivalent, headerBound⟩
          have canonicalPath :=
            TargetEmitterControllerTrace.program_end_path
              ((TargetEmitterControllerTrace.circuitHeaderCells
                    inputs 0).reverse ++
                TargetEmitterRuntime.logicalLeftWorkspace
                  (TargetEmitterLedger.slotCapacity raw)
                  afterHeader.scratch afterHeader.registers
                  afterHeader.checks)
              output afterHeader.targetTokens
          rcases canonicalPath.transport programEndEquivalent with
            ⟨finalTape, outputPath, outputEquivalent⟩
          refine
            ⟨headerSteps + 3, finalTape, ?_, ?_, ?_⟩
          · exact
              AcceptPath.trans graph (.node stackInitializeRef)
                (.node programEndRef) (.node outputFirstRef)
                headerSteps 3 _ _ _ headerPath outputPath
          · apply focusRepresents_of_tape_equivalent
            simp only [gateListRuntime,
              TargetEmitterSemanticSchedule.appendGateListResults,
              TargetEmitterRuntimeSourceControl.sourceFocusConfiguration,
              TargetEmitterRuntimeSourceControl.targetSuffix,
              outputCrossedCells,
              TargetEmitterControllerTrace.circuitHeaderCells,
              SourceParser.gateListCells, List.append_nil,
              List.reverse_append]
            rw [configAtWord_tape_irrel outputFirstRef.startState 0]
            simpa [raw, TargetEmitterControllerTrace.sourceFocusTape,
              TargetEmitterControllerTrace.circuitHeaderCells,
              List.append_assoc] using outputEquivalent
          · simpa [stackGateListEnvelope, raw] using
              Nat.add_le_add_right headerBound 3
      | cons gate rest =>
          let raw : RawCircuit :=
            { inputCount := inputs
              gates := gate :: rest
              output := output }
          let afterHeader :=
            TargetEmitterProgramSemantics.headerResult
              (TargetEmitterControllerHeaderTrace.initialRuntime raw)
          rcases
              TargetEmitterControllerHeaderBound.stack_header_nonempty_path_bounded
                inputs gate rest output with
            ⟨headerSteps, headerTape, headerPath,
              headerEquivalent, headerBound⟩
          have headerRepresents :
              FocusTapeRepresents leftFirstRef.startState
                (TargetEmitterLedger.slotCapacity raw)
                afterHeader.scratch afterHeader.registers
                afterHeader.checks
                (crossedCells raw [])
                (SourceParser.sourceCells gate.left ++
                  SourceParser.sourceCells gate.right ++
                  [SourceParser.cell01, SourceParser.cell11] ++
                  SourceParser.gateListCells rest ++
                  TargetEmitterControllerTrace.circuitFooterCells output)
                afterHeader.targetTokens headerTape := by
            exact header_nonempty_represents inputs gate rest output
              headerTape headerEquivalent
          have initialInvariant :
              RegisterInvariant raw [] afterHeader := by
            refine
              { inputCount := ?_
                normalizedGateCount := ?_
                carrierWidth := ?_
                baseline := ?_
                currentGate := ?_
                outputIndex := ?_ } <;>
              rw [TargetEmitterProgramSemantics.headerResult_registers] <;>
              rfl
          have scratchShape :
              afterHeader.scratch =
                TargetEmitterLedger.baselineValue raw + 1 := by
            rw [TargetEmitterProgramSemantics.headerResult_scratch]
            rfl
          rcases
              gateList_to_output_path raw [] gate rest
                afterHeader headerTape rfl initialInvariant
                (Or.inr scratchShape) headerRepresents with
            ⟨traversalSteps, finalTape, traversalPath,
              finalRepresents, traversalBound⟩
          refine
            ⟨headerSteps + traversalSteps, finalTape, ?_, ?_, ?_⟩
          · exact
              AcceptPath.trans graph (.node stackInitializeRef)
                (.node leftFirstRef) (.node outputFirstRef)
                headerSteps traversalSteps _ _ _
                headerPath traversalPath
          · simpa [gateListRuntime, raw, afterHeader] using
              finalRepresents
          · have combined :=
              Nat.add_le_add headerBound traversalBound
            simpa [stackGateListEnvelope, raw, afterHeader] using combined

/-- Closed bounded gate-list traversal using the uniform envelope consumed by
the final polynomial accounting layer. -/
theorem stack_gateList_to_output_path_uniform_bounded
    (raw : RawCircuit) :
    ∃ steps finalTape,
      AcceptPath graph (.node stackInitializeRef)
          (.node outputFirstRef) steps
          (TargetEmitterLedger.finalConfiguration raw).tape finalTape ∧
      FocusTapeRepresents outputFirstRef.startState
        (TargetEmitterLedger.slotCapacity raw)
        (gateListRuntime raw).scratch
        (gateListRuntime raw).registers
        (gateListRuntime raw).checks
        (outputCrossedCells raw)
        (SourceParser.sourceCells raw.output ++
          TargetEmitterControllerTrace.circuitTerminatorCells)
        (gateListRuntime raw).targetTokens finalTape ∧
      steps ≤ stackGateListUniformEnvelope raw := by
  rcases stack_gateList_to_output_path_bounded raw with
    ⟨steps, finalTape, path, represents, bound⟩
  exact
    ⟨steps, finalTape, path, represents,
      Nat.le_trans bound (stackGateListEnvelope_le_uniform raw)⟩

end PNP.Concrete.LockedNAND.TargetEmitterControllerGateListTrace
