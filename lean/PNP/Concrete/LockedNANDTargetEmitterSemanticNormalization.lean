/-
Copyright (c) 2026 PNP Labs.

Pure semantic bridge for the locked-NAND output-normalization branch.

The fixed controller first emits the macros of the source gate list, captures
the raw output, and then selects one of three closed normalization programs.
This module identifies that branch with the independent normalized raw
builder and canonical semantic schedule.  All range witnesses are derived
from the raw circuit itself; none is supplied by a caller or consulted by the
executable controller.
-/

import PNP.Concrete.LockedNANDTargetEmitterSemanticPrefix
import PNP.Concrete.LockedNANDTargetEmitterRuntimeProgramSafety

namespace PNP.Concrete.LockedNAND.TargetEmitterSemanticNormalization

open PNP.Concrete

abbrev Runtime := TargetEmitterProgramSemantics.Runtime
abbrev MacroAssembly := RawBuilder.MacroAssembly
abbrev MacroInvariant := TargetEmitterSemanticSchedule.MacroInvariant
abbrev ControllerRange := TargetEmitterCapacity.ControllerRange
abbrev InputNormalizationRanges :=
  TargetEmitterRuntimeProgramSafety.InputNormalizationRanges
abbrev ConstantNormalizationRanges :=
  TargetEmitterRuntimeProgramSafety.ConstantNormalizationRanges

/-- The literal suffix appended by legacy output normalization. -/
def normalizationSuffix (raw : RawCircuit) : List RawGate :=
  match raw.output with
  | .gate _ => []
  | .input index =>
      let first := raw.gates.length
      [ { left := .input index, right := .constant true }
      , { left := .gate first, right := .gate first } ]
  | .constant false =>
      [{ left := .constant true, right := .constant true }]
  | .constant true =>
      [{ left := .constant false, right := .constant false }]

theorem gates_append_normalizationSuffix (raw : RawCircuit) :
    raw.gates ++ normalizationSuffix raw =
      raw.normalize.gates := by
  cases raw with
  | mk inputs gates output =>
      cases output with
      | gate index =>
          simp [normalizationSuffix, RawCircuit.normalize]
      | input index =>
          simp [normalizationSuffix, RawCircuit.normalize]
      | constant value =>
          cases value <;>
            simp [normalizationSuffix, RawCircuit.normalize]

/-- Builder state after only the gates present in the source word have been
expanded, but already using the normalized total-gate coordinate system. -/
def rawPrefixAssembly (raw : RawCircuit) : MacroAssembly :=
  RawBuilder.assembleGates raw.normalize.inputCount
    raw.normalize.gates.length 0 RawBuilder.emptyAssembly raw.gates

/-- Builder state after the output-selected normalization suffix. -/
def normalizationAssembly (raw : RawCircuit) : MacroAssembly :=
  RawBuilder.assembleGates raw.normalize.inputCount
    raw.normalize.gates.length raw.gates.length
    (rawPrefixAssembly raw) (normalizationSuffix raw)

theorem normalizationAssembly_eq_macroAssembly
    (raw : RawCircuit) :
    normalizationAssembly raw =
      RawBuilder.macroAssembly raw.normalize := by
  unfold normalizationAssembly rawPrefixAssembly RawBuilder.macroAssembly
  rw [← gates_append_normalizationSuffix raw,
    RawBuilder.assembleGates_append]
  simp

/-- Semantic runtime after the source gate list, before the raw output is
captured and classified. -/
def rawPrefixRuntime (raw : RawCircuit) : Runtime :=
  TargetEmitterSemanticSchedule.appendGateListResults raw.gates
    (TargetEmitterSemanticSchedule.normalizedMacroStartRuntime raw)

/-- Pure counterpart of the source-capture handoff used by the physical
controller. -/
def outputCapturedRuntime (raw : RawCircuit) : Runtime :=
  let runtime := rawPrefixRuntime raw
  let captured :=
    TargetEmitterSemanticSchedule.capturedValue raw.output
  { runtime with
    captured := captured
    scratch := runtime.scratch + captured }

/-- Result of the fixed branch selected by the raw output tag. -/
def normalizationRuntime (raw : RawCircuit) : Runtime :=
  match raw.output with
  | .gate _ =>
      TargetEmitterProgramSemantics.resetScratchResult
        (outputCapturedRuntime raw)
  | .input _ =>
      TargetEmitterProgramSemantics.inputNormalizationResult
        (outputCapturedRuntime raw)
  | .constant value =>
      TargetEmitterProgramSemantics.constantNormalizationResult
        value (outputCapturedRuntime raw)

private theorem appendGateListResults_append
    (first second : List RawGate) (runtime : Runtime) :
    TargetEmitterSemanticSchedule.appendGateListResults
        (first ++ second) runtime =
      TargetEmitterSemanticSchedule.appendGateListResults second
        (TargetEmitterSemanticSchedule.appendGateListResults
          first runtime) := by
  induction first generalizing runtime with
  | nil =>
      rfl
  | cons gate rest inductionHypothesis =>
      simp only [List.cons_append,
        TargetEmitterSemanticSchedule.appendGateListResults]
      exact
        inductionHypothesis
          (TargetEmitterSemanticSchedule.appendGateResult gate runtime)

private theorem runtime_ext
    {left right : Runtime}
    (captured : left.captured = right.captured)
    (scratch : left.scratch = right.scratch)
    (registers : left.registers = right.registers)
    (checks : left.checks = right.checks)
    (targetTokens : left.targetTokens = right.targetTokens) :
    left = right := by
  cases left
  cases right
  simp only at captured scratch registers checks targetTokens
  simp only [TargetEmitterProgramSemantics.Runtime.mk.injEq]
  exact ⟨captured, scratch, registers, checks, targetTokens⟩

private theorem registers_ext
    {left right : TargetEmitter.UnaryRegisters}
    (inputCount : left.inputCount = right.inputCount)
    (normalizedGateCount :
      left.normalizedGateCount = right.normalizedGateCount)
    (carrierWidth : left.carrierWidth = right.carrierWidth)
    (baseline : left.baseline = right.baseline)
    (currentGate : left.currentGate = right.currentGate)
    (outputIndex : left.outputIndex = right.outputIndex) :
    left = right := by
  cases left
  cases right
  simp_all

private theorem appendGateListResults_carrierWidth
    (gates : List RawGate) (runtime : Runtime) :
    (TargetEmitterSemanticSchedule.appendGateListResults
      gates runtime).registers.carrierWidth =
        runtime.registers.carrierWidth := by
  induction gates generalizing runtime with
  | nil =>
      rfl
  | cons gate rest inductionHypothesis =>
      rw [TargetEmitterSemanticSchedule.appendGateListResults,
        inductionHypothesis]
      simp [TargetEmitterSemanticSchedule.appendGateResult,
        TargetEmitterSemanticSchedule.appendSourceResult,
        TargetEmitterSemanticSchedule.withCaptured,
        TargetEmitterProgramSemantics.macroResult_registers,
        TargetEmitterProgramSemantics.incrementCurrentGateResult]

private theorem appendGateListResults_baseline
    (gates : List RawGate) (runtime : Runtime) :
    (TargetEmitterSemanticSchedule.appendGateListResults
      gates runtime).registers.baseline =
        runtime.registers.baseline := by
  induction gates generalizing runtime with
  | nil =>
      rfl
  | cons gate rest inductionHypothesis =>
      rw [TargetEmitterSemanticSchedule.appendGateListResults,
        inductionHypothesis]
      simp [TargetEmitterSemanticSchedule.appendGateResult,
        TargetEmitterSemanticSchedule.appendSourceResult,
        TargetEmitterSemanticSchedule.withCaptured,
        TargetEmitterProgramSemantics.macroResult_registers,
        TargetEmitterProgramSemantics.incrementCurrentGateResult]

/-! The schedule module's original macro invariant proof predates the
choice-free raw builder.  Rebuild the same structural facts here with
literal finite binding cases, so no proof extracts a list position through
classical witness selection. -/

private theorem encodeGateListTokens_append_constructive
    (first second : List RawGate) :
    encodeGateListTokens (first ++ second) =
      encodeGateListTokens first ++ encodeGateListTokens second := by
  induction first with
  | nil =>
      rfl
  | cons gate rest inductionHypothesis =>
      simp only [List.cons_append, encodeGateListTokens,
        inductionHypothesis, List.append_assoc]

private theorem listBinding_two_constructive
    (first second : RawSource) :
    RawBuilder.listBinding [first, second] =
      RawBuilder.rawBinding2 first second := by
  funext index
  cases index with
  | zero => rfl
  | succ firstIndex =>
      cases firstIndex with
      | zero => rfl
      | succ rest => rfl

private theorem listBinding_three_constructive
    (first second third : RawSource) :
    RawBuilder.listBinding [first, second, third] =
      RawBuilder.rawBinding3 first second third := by
  funext index
  cases index with
  | zero => rfl
  | succ firstIndex =>
      cases firstIndex with
      | zero => rfl
      | succ secondIndex =>
          cases secondIndex with
          | zero => rfl
          | succ rest => rfl

private theorem listBinding_four_constructive
    (first second third fourth : RawSource) :
    RawBuilder.listBinding [first, second, third, fourth] =
      RawBuilder.rawBinding4 first second third fourth := by
  funext index
  cases index with
  | zero => rfl
  | succ firstIndex =>
      cases firstIndex with
      | zero => rfl
      | succ secondIndex =>
          cases secondIndex with
          | zero => rfl
          | succ thirdIndex =>
              cases thirdIndex with
              | zero => rfl
              | succ rest => rfl

private theorem sourcePlan_appends_raw_gates_constructive
    (inputs totalGates gate side : Nat)
    (assembly : MacroAssembly) (source : RawSource)
    (runtime : Runtime)
    (inputCount :
      runtime.registers.inputCount = inputs)
    (normalizedGateCount :
      runtime.registers.normalizedGateCount = totalGates)
    (currentGate :
      runtime.registers.currentGate = gate)
    (outputIndex :
      runtime.registers.outputIndex = assembly.gates.length) :
    assembly.gates ++
        TargetEmitterProgramSemantics.evaluatedGates
          (TargetEmitterSemanticSchedule.withCaptured source runtime)
          (TargetEmitterPlan.sourcePlan
            (TargetEmitterSemanticSchedule.sourceKind source) side) =
      (RawBuilder.appendSourceMacro
        inputs totalGates gate side assembly source).gates := by
  subst inputs
  subst totalGates
  subst gate
  cases source with
  | input index =>
      simp only [TargetEmitterSemanticSchedule.withCaptured,
        TargetEmitterSemanticSchedule.capturedValue,
        TargetEmitterSemanticSchedule.sourceKind,
        TargetEmitterProgramSemantics.evaluatedGates,
        TargetEmitterPlan.sourcePlan,
        TargetEmitterPlan.sourceBindings,
        TargetEmitterPlan.instantiateTemplate,
        TargetEmitterPlan.sourceTemplate,
        TargetEmitterPlan.evaluate_instantiateTemplateAt]
      change assembly.gates ++ List.map _ RawBuilder.equalityTemplate = _
      simp [TargetEmitterPlan.PlannedSource.evaluate,
        TargetEmitterPlan.sourceLock_evaluated,
        TargetEmitterPlan.occurrence_evaluated,
        TargetEmitterPlan.capturedIndex,
        TargetEmitterPlan.outputIndex,
        TargetEmitterPlan.NatExpression.evaluate_counter,
        TargetEmitterPlan.NatExpression.evaluateCounter,
        RawBuilder.appendSourceMacro, RawBuilder.appendTemplate,
        listBinding_three_constructive, outputIndex,
        RawBuilder.sourceLockCoordinate,
        RawBuilder.occurrenceCoordinate,
        RawBuilder.sourceValueCoordinate,
        RawBuilder.primaryCoordinate, Nat.add_assoc]
  | constant value =>
      cases value with
      | false =>
          simp only [TargetEmitterSemanticSchedule.withCaptured,
            TargetEmitterSemanticSchedule.capturedValue,
            TargetEmitterSemanticSchedule.sourceKind,
            TargetEmitterProgramSemantics.evaluatedGates,
            TargetEmitterPlan.sourcePlan,
            TargetEmitterPlan.sourceBindings,
            TargetEmitterPlan.instantiateTemplate,
            TargetEmitterPlan.sourceTemplate,
            TargetEmitterPlan.evaluate_instantiateTemplateAt]
          change
            assembly.gates ++
                List.map _ RawBuilder.constantZeroTemplate = _
          simp [TargetEmitterPlan.PlannedSource.evaluate,
            TargetEmitterPlan.sourceLock_evaluated,
            TargetEmitterPlan.occurrence_evaluated,
            TargetEmitterPlan.outputIndex,
            TargetEmitterPlan.NatExpression.evaluate_counter,
            TargetEmitterPlan.NatExpression.evaluateCounter,
            RawBuilder.appendSourceMacro, RawBuilder.appendTemplate,
            listBinding_two_constructive, outputIndex,
            RawBuilder.sourceLockCoordinate,
            RawBuilder.occurrenceCoordinate, Nat.add_assoc]
      | true =>
          simp only [TargetEmitterSemanticSchedule.withCaptured,
            TargetEmitterSemanticSchedule.capturedValue,
            TargetEmitterSemanticSchedule.sourceKind,
            TargetEmitterProgramSemantics.evaluatedGates,
            TargetEmitterPlan.sourcePlan,
            TargetEmitterPlan.sourceBindings,
            TargetEmitterPlan.instantiateTemplate,
            TargetEmitterPlan.sourceTemplate,
            TargetEmitterPlan.evaluate_instantiateTemplateAt]
          change
            assembly.gates ++
                List.map _ RawBuilder.constantOneTemplate = _
          simp [TargetEmitterPlan.PlannedSource.evaluate,
            TargetEmitterPlan.sourceLock_evaluated,
            TargetEmitterPlan.occurrence_evaluated,
            TargetEmitterPlan.outputIndex,
            TargetEmitterPlan.NatExpression.evaluate_counter,
            TargetEmitterPlan.NatExpression.evaluateCounter,
            RawBuilder.appendSourceMacro, RawBuilder.appendTemplate,
            listBinding_two_constructive, outputIndex,
            RawBuilder.sourceLockCoordinate,
            RawBuilder.occurrenceCoordinate, Nat.add_assoc]
  | gate index =>
      simp only [TargetEmitterSemanticSchedule.withCaptured,
        TargetEmitterSemanticSchedule.capturedValue,
        TargetEmitterSemanticSchedule.sourceKind,
        TargetEmitterProgramSemantics.evaluatedGates,
        TargetEmitterPlan.sourcePlan,
        TargetEmitterPlan.sourceBindings,
        TargetEmitterPlan.instantiateTemplate,
        TargetEmitterPlan.sourceTemplate,
        TargetEmitterPlan.evaluate_instantiateTemplateAt]
      change assembly.gates ++ List.map _ RawBuilder.equalityTemplate = _
      simp [TargetEmitterPlan.PlannedSource.evaluate,
        TargetEmitterPlan.sourceLock_evaluated,
        TargetEmitterPlan.occurrence_evaluated,
        TargetEmitterPlan.rawGateTrace_evaluated,
        TargetEmitterPlan.outputIndex,
        TargetEmitterPlan.NatExpression.evaluate_counter,
        TargetEmitterPlan.NatExpression.evaluateCounter,
        RawBuilder.appendSourceMacro, RawBuilder.appendTemplate,
        listBinding_three_constructive, outputIndex,
        RawBuilder.sourceLockCoordinate,
        RawBuilder.occurrenceCoordinate,
        RawBuilder.sourceValueCoordinate,
        RawBuilder.traceCoordinate, Nat.add_assoc]

private theorem tracePlan_appends_raw_gates_constructive
    (inputs totalGates gate : Nat)
    (assembly : MacroAssembly) (runtime : Runtime)
    (inputCount :
      runtime.registers.inputCount = inputs)
    (normalizedGateCount :
      runtime.registers.normalizedGateCount = totalGates)
    (currentGate :
      runtime.registers.currentGate = gate)
    (outputIndex :
      runtime.registers.outputIndex = assembly.gates.length) :
    assembly.gates ++
        TargetEmitterProgramSemantics.evaluatedGates
          runtime TargetEmitterPlan.tracePlan =
      (RawBuilder.appendTraceMacro
        inputs totalGates gate assembly).gates := by
  subst inputs
  subst totalGates
  subst gate
  simp only [TargetEmitterProgramSemantics.evaluatedGates,
    TargetEmitterPlan.tracePlan, TargetEmitterPlan.traceBindings,
    TargetEmitterPlan.instantiateTemplate,
    TargetEmitterPlan.evaluate_instantiateTemplateAt]
  change assembly.gates ++ List.map _ RawBuilder.traceTemplate = _
  simp [TargetEmitterPlan.PlannedSource.evaluate,
    RawBuilder.appendTraceMacro, RawBuilder.appendTemplate,
    listBinding_four_constructive,
    TargetEmitterPlan.traceLock_evaluated,
    TargetEmitterPlan.traceCoordinate_evaluated,
    TargetEmitterPlan.occurrence_evaluated,
    TargetEmitterPlan.outputIndex,
    TargetEmitterPlan.NatExpression.evaluate_counter,
    TargetEmitterPlan.NatExpression.evaluateCounter,
    outputIndex,
    RawBuilder.traceLockCoordinate, RawBuilder.traceCoordinate,
    RawBuilder.occurrenceCoordinate, Nat.add_assoc]

private theorem sourceMacro_preserves_invariant_constructive
    (inputs totalGates gate side : Nat)
    (assembly : MacroAssembly) (source : RawSource)
    (tokenPrefix : List Token) (runtime : Runtime)
    (invariant :
      MacroInvariant inputs totalGates gate assembly
        tokenPrefix runtime) :
    MacroInvariant inputs totalGates gate
      (RawBuilder.appendSourceMacro
        inputs totalGates gate side assembly source)
      tokenPrefix
      (TargetEmitterProgramSemantics.macroResult
        (TargetEmitterSemanticSchedule.withCaptured source runtime)
        (TargetEmitterPlan.sourcePlan
          (TargetEmitterSemanticSchedule.sourceKind source) side)
        (TargetEmitterPlan.sourceCheckRelative
          (TargetEmitterSemanticSchedule.sourceKind source))
        (TargetEmitterPlan.sourceGateCount
          (TargetEmitterSemanticSchedule.sourceKind source))) := by
  let gates :=
    TargetEmitterPlan.sourcePlan
      (TargetEmitterSemanticSchedule.sourceKind source) side
  let relative :=
    TargetEmitterPlan.sourceCheckRelative
      (TargetEmitterSemanticSchedule.sourceKind source)
  let count :=
    TargetEmitterPlan.sourceGateCount
      (TargetEmitterSemanticSchedule.sourceKind source)
  let capturedRuntime :=
    TargetEmitterSemanticSchedule.withCaptured source runtime
  let final :=
    TargetEmitterProgramSemantics.macroResult
      capturedRuntime gates relative count
  have gatesEq :
      assembly.gates ++
          TargetEmitterProgramSemantics.evaluatedGates
            capturedRuntime gates =
        (RawBuilder.appendSourceMacro
          inputs totalGates gate side assembly source).gates := by
    exact sourcePlan_appends_raw_gates_constructive
      inputs totalGates gate side assembly source runtime
      invariant.inputCount invariant.normalizedGateCount
      invariant.currentGate invariant.outputIndex
  refine
    { inputCount := ?_
      normalizedGateCount := ?_
      currentGate := ?_
      outputIndex := ?_
      scratch := ?_
      checks := ?_
      targetTokens := ?_ }
  · simpa [final, capturedRuntime,
      TargetEmitterSemanticSchedule.withCaptured, gates, relative, count,
      TargetEmitterProgramSemantics.macroResult,
      TargetEmitterProgramSemantics.resetScratchResult,
      TargetEmitterProgramSemantics.incrementOutputResult,
      TargetEmitterProgramSemantics.checkPushResult,
      TargetEmitterProgramSemantics.gatesResult_registers] using
      invariant.inputCount
  · simpa [final, capturedRuntime,
      TargetEmitterSemanticSchedule.withCaptured, gates, relative, count,
      TargetEmitterProgramSemantics.macroResult,
      TargetEmitterProgramSemantics.resetScratchResult,
      TargetEmitterProgramSemantics.incrementOutputResult,
      TargetEmitterProgramSemantics.checkPushResult,
      TargetEmitterProgramSemantics.gatesResult_registers] using
      invariant.normalizedGateCount
  · simpa [final, capturedRuntime,
      TargetEmitterSemanticSchedule.withCaptured, gates, relative, count,
      TargetEmitterProgramSemantics.macroResult,
      TargetEmitterProgramSemantics.resetScratchResult,
      TargetEmitterProgramSemantics.incrementOutputResult,
      TargetEmitterProgramSemantics.checkPushResult,
      TargetEmitterProgramSemantics.gatesResult_registers] using
      invariant.currentGate
  · rw [TargetEmitterProgramSemantics.macroResult_registers]
    simp only
    change
      runtime.registers.outputIndex +
          TargetEmitterPlan.sourceGateCount
            (TargetEmitterSemanticSchedule.sourceKind source) =
        (RawBuilder.appendSourceMacro
          inputs totalGates gate side assembly source).gates.length
    rw [invariant.outputIndex,
      RawBuilder.appendSourceMacro_gates_length]
    cases source with
    | input index => rfl
    | constant value => cases value <;> rfl
    | gate index => rfl
  · exact
      TargetEmitterProgramSemantics.macroResult_scratch
        capturedRuntime gates relative count
  · rw [TargetEmitterProgramSemantics.macroResult_checks]
    simp only [TargetEmitterSemanticSchedule.withCaptured]
    rw [invariant.checks, invariant.outputIndex]
    cases source with
    | input index =>
        simp [TargetEmitterSemanticSchedule.checkCoordinates,
          RawBuilder.appendSourceMacro,
          TargetEmitterSemanticSchedule.sourceKind,
          TargetEmitterPlan.sourceCheckRelative,
          RawBuilder.outputGateIndex]
    | constant value =>
        cases value <;>
          simp [TargetEmitterSemanticSchedule.checkCoordinates,
            RawBuilder.appendSourceMacro,
            TargetEmitterSemanticSchedule.sourceKind,
            TargetEmitterPlan.sourceCheckRelative,
            RawBuilder.outputGateIndex]
    | gate index =>
        simp [TargetEmitterSemanticSchedule.checkCoordinates,
          RawBuilder.appendSourceMacro,
          TargetEmitterSemanticSchedule.sourceKind,
          TargetEmitterPlan.sourceCheckRelative,
          RawBuilder.outputGateIndex]
  · calc
      final.targetTokens =
          capturedRuntime.targetTokens ++
            TargetEmitterProgramSemantics.plannedGateTokens
              capturedRuntime gates :=
        TargetEmitterProgramSemantics.macroResult_targetTokens
          capturedRuntime gates relative count
      _ =
          tokenPrefix ++
            (encodeGateListTokens assembly.gates ++
              encodeGateListTokens
                (TargetEmitterProgramSemantics.evaluatedGates
                  capturedRuntime gates)) := by
        simp [capturedRuntime,
          TargetEmitterSemanticSchedule.withCaptured,
          TargetEmitterProgramSemantics.plannedGateTokens,
          invariant.targetTokens, List.append_assoc]
      _ =
          tokenPrefix ++
            encodeGateListTokens
              (assembly.gates ++
                TargetEmitterProgramSemantics.evaluatedGates
                  capturedRuntime gates) := by
        rw [encodeGateListTokens_append_constructive]
      _ =
          tokenPrefix ++
            encodeGateListTokens
              (RawBuilder.appendSourceMacro
                inputs totalGates gate side assembly source).gates := by
        rw [gatesEq]

private theorem traceMacro_advances_invariant_constructive
    (inputs totalGates gate : Nat)
    (assembly : MacroAssembly)
    (tokenPrefix : List Token) (runtime : Runtime)
    (invariant :
      MacroInvariant inputs totalGates gate assembly
        tokenPrefix runtime) :
    MacroInvariant inputs totalGates (gate + 1)
      (RawBuilder.appendTraceMacro inputs totalGates gate assembly)
      tokenPrefix
      (TargetEmitterProgramSemantics.incrementCurrentGateResult
        (TargetEmitterProgramSemantics.macroResult runtime
          TargetEmitterPlan.tracePlan
          TargetEmitterPlan.traceCheckRelative
          TargetEmitterPlan.traceGateCount)) := by
  let traced :=
    TargetEmitterProgramSemantics.macroResult runtime
      TargetEmitterPlan.tracePlan
      TargetEmitterPlan.traceCheckRelative
      TargetEmitterPlan.traceGateCount
  have gatesEq :
      assembly.gates ++
          TargetEmitterProgramSemantics.evaluatedGates
            runtime TargetEmitterPlan.tracePlan =
        (RawBuilder.appendTraceMacro
          inputs totalGates gate assembly).gates := by
    exact tracePlan_appends_raw_gates_constructive
      inputs totalGates gate assembly runtime
      invariant.inputCount invariant.normalizedGateCount
      invariant.currentGate invariant.outputIndex
  refine
    { inputCount := ?_
      normalizedGateCount := ?_
      currentGate := ?_
      outputIndex := ?_
      scratch := ?_
      checks := ?_
      targetTokens := ?_ }
  · simpa [TargetEmitterProgramSemantics.incrementCurrentGateResult,
      traced, TargetEmitterProgramSemantics.macroResult,
      TargetEmitterProgramSemantics.resetScratchResult,
      TargetEmitterProgramSemantics.incrementOutputResult,
      TargetEmitterProgramSemantics.checkPushResult,
      TargetEmitterProgramSemantics.gatesResult_registers] using
      invariant.inputCount
  · simpa [TargetEmitterProgramSemantics.incrementCurrentGateResult,
      traced, TargetEmitterProgramSemantics.macroResult,
      TargetEmitterProgramSemantics.resetScratchResult,
      TargetEmitterProgramSemantics.incrementOutputResult,
      TargetEmitterProgramSemantics.checkPushResult,
      TargetEmitterProgramSemantics.gatesResult_registers] using
      invariant.normalizedGateCount
  · simpa [TargetEmitterProgramSemantics.incrementCurrentGateResult,
      traced, TargetEmitterProgramSemantics.macroResult,
      TargetEmitterProgramSemantics.resetScratchResult,
      TargetEmitterProgramSemantics.incrementOutputResult,
      TargetEmitterProgramSemantics.checkPushResult,
      TargetEmitterProgramSemantics.gatesResult_registers] using
      invariant.currentGate
  · simp only [TargetEmitterProgramSemantics.incrementCurrentGateResult]
    rw [TargetEmitterProgramSemantics.macroResult_registers]
    simp only
    rw [invariant.outputIndex,
      RawBuilder.appendTraceMacro_gates_length]
    rfl
  · exact
      TargetEmitterProgramSemantics.macroResult_scratch
        runtime TargetEmitterPlan.tracePlan
        TargetEmitterPlan.traceCheckRelative
        TargetEmitterPlan.traceGateCount
  · simp only [TargetEmitterProgramSemantics.incrementCurrentGateResult]
    rw [TargetEmitterProgramSemantics.macroResult_checks]
    rw [invariant.checks, invariant.outputIndex]
    simp [TargetEmitterSemanticSchedule.checkCoordinates,
      RawBuilder.appendTraceMacro,
      TargetEmitterPlan.traceCheckRelative,
      RawBuilder.outputGateIndex]
  · simp only [TargetEmitterProgramSemantics.incrementCurrentGateResult]
    calc
      traced.targetTokens =
          runtime.targetTokens ++
            TargetEmitterProgramSemantics.plannedGateTokens
              runtime TargetEmitterPlan.tracePlan :=
        TargetEmitterProgramSemantics.macroResult_targetTokens
          runtime TargetEmitterPlan.tracePlan
          TargetEmitterPlan.traceCheckRelative
          TargetEmitterPlan.traceGateCount
      _ =
          tokenPrefix ++
            (encodeGateListTokens assembly.gates ++
              encodeGateListTokens
                (TargetEmitterProgramSemantics.evaluatedGates
                  runtime TargetEmitterPlan.tracePlan)) := by
        simp [TargetEmitterProgramSemantics.plannedGateTokens,
          invariant.targetTokens, List.append_assoc]
      _ =
          tokenPrefix ++
            encodeGateListTokens
              (assembly.gates ++
                TargetEmitterProgramSemantics.evaluatedGates
                  runtime TargetEmitterPlan.tracePlan) := by
        rw [encodeGateListTokens_append_constructive]
      _ =
          tokenPrefix ++
            encodeGateListTokens
              (RawBuilder.appendTraceMacro
                inputs totalGates gate assembly).gates := by
        rw [gatesEq]

private theorem appendGateResult_advances_invariant_constructive
    (inputs totalGates gate : Nat)
    (assembly : MacroAssembly) (sourceGate : RawGate)
    (tokenPrefix : List Token) (runtime : Runtime)
    (invariant :
      MacroInvariant inputs totalGates gate assembly
        tokenPrefix runtime) :
    let left :=
      RawBuilder.appendSourceMacro inputs totalGates gate 0
        assembly sourceGate.left
    let right :=
      RawBuilder.appendSourceMacro inputs totalGates gate 1
        left sourceGate.right
    let trace :=
      RawBuilder.appendTraceMacro inputs totalGates gate right
    MacroInvariant inputs totalGates (gate + 1) trace tokenPrefix
      (TargetEmitterSemanticSchedule.appendGateResult
        sourceGate runtime) := by
  dsimp only
  let left :=
    RawBuilder.appendSourceMacro inputs totalGates gate 0
      assembly sourceGate.left
  let right :=
    RawBuilder.appendSourceMacro inputs totalGates gate 1
      left sourceGate.right
  let afterLeft :=
    TargetEmitterSemanticSchedule.appendSourceResult
      0 sourceGate.left runtime
  let afterRight :=
    TargetEmitterSemanticSchedule.appendSourceResult
      1 sourceGate.right afterLeft
  have leftInvariant :
      MacroInvariant inputs totalGates gate left
        tokenPrefix afterLeft := by
    simpa [left, afterLeft,
      TargetEmitterSemanticSchedule.appendSourceResult] using
      sourceMacro_preserves_invariant_constructive
        inputs totalGates gate 0 assembly sourceGate.left
        tokenPrefix runtime invariant
  have rightInvariant :
      MacroInvariant inputs totalGates gate right
        tokenPrefix afterRight := by
    simpa [right, afterRight,
      TargetEmitterSemanticSchedule.appendSourceResult] using
      sourceMacro_preserves_invariant_constructive
        inputs totalGates gate 1 left sourceGate.right
        tokenPrefix afterLeft leftInvariant
  have traceInvariant :=
    traceMacro_advances_invariant_constructive
      inputs totalGates gate right tokenPrefix afterRight
      rightInvariant
  simpa [TargetEmitterSemanticSchedule.appendGateResult,
    afterLeft, afterRight, left, right] using traceInvariant

private theorem appendGateListResults_preserves_invariant_constructive
    (inputs totalGates gate : Nat)
    (assembly : MacroAssembly) (sourceGates : List RawGate)
    (tokenPrefix : List Token) (runtime : Runtime)
    (invariant :
      MacroInvariant inputs totalGates gate assembly
        tokenPrefix runtime) :
    MacroInvariant inputs totalGates (gate + sourceGates.length)
      (RawBuilder.assembleGates
        inputs totalGates gate assembly sourceGates)
      tokenPrefix
      (TargetEmitterSemanticSchedule.appendGateListResults
        sourceGates runtime) := by
  induction sourceGates generalizing gate assembly runtime with
  | nil =>
      simpa [RawBuilder.assembleGates,
        TargetEmitterSemanticSchedule.appendGateListResults] using
        invariant
  | cons sourceGate rest inductionHypothesis =>
      let left :=
        RawBuilder.appendSourceMacro inputs totalGates gate 0
          assembly sourceGate.left
      let right :=
        RawBuilder.appendSourceMacro inputs totalGates gate 1
          left sourceGate.right
      let trace :=
        RawBuilder.appendTraceMacro inputs totalGates gate right
      let afterGate :=
        TargetEmitterSemanticSchedule.appendGateResult
          sourceGate runtime
      have gateInvariant :
          MacroInvariant inputs totalGates (gate + 1) trace
            tokenPrefix afterGate := by
        simpa [left, right, trace, afterGate] using
          appendGateResult_advances_invariant_constructive
            inputs totalGates gate assembly sourceGate
            tokenPrefix runtime invariant
      have tailInvariant :=
        inductionHypothesis (gate + 1) trace afterGate gateInvariant
      have gateIndexEq :
          (gate + 1) + rest.length =
            gate + (rest.length + 1) := by
        omega
      rw [gateIndexEq] at tailInvariant
      simpa [RawBuilder.assembleGates,
        TargetEmitterSemanticSchedule.appendGateListResults,
        left, right, trace, afterGate] using tailInvariant

theorem rawPrefix_invariant (raw : RawCircuit) :
    MacroInvariant raw.normalize.inputCount
      raw.normalize.gates.length raw.gates.length
      (rawPrefixAssembly raw)
      (TargetEmitterSemanticSchedule.headerTokens raw)
      (rawPrefixRuntime raw) := by
  have full :=
    appendGateListResults_preserves_invariant_constructive
      raw.normalize.inputCount raw.normalize.gates.length 0
      RawBuilder.emptyAssembly raw.gates
      (TargetEmitterSemanticSchedule.headerTokens raw)
      (TargetEmitterSemanticSchedule.normalizedMacroStartRuntime raw)
      (TargetEmitterSemanticSchedule.normalizedMacroStart_invariant raw)
  simpa [rawPrefixAssembly, rawPrefixRuntime] using full

private theorem normalizedMacroRuntime_invariant_constructive
    (raw : RawCircuit) :
    MacroInvariant raw.normalize.inputCount
      raw.normalize.gates.length raw.normalize.gates.length
      (RawBuilder.macroAssembly raw.normalize)
      (TargetEmitterSemanticSchedule.headerTokens raw)
      (TargetEmitterSemanticSchedule.normalizedMacroRuntime raw) := by
  have full :=
    appendGateListResults_preserves_invariant_constructive
      raw.normalize.inputCount raw.normalize.gates.length 0
      RawBuilder.emptyAssembly raw.normalize.gates
      (TargetEmitterSemanticSchedule.headerTokens raw)
      (TargetEmitterSemanticSchedule.normalizedMacroStartRuntime raw)
      (TargetEmitterSemanticSchedule.normalizedMacroStart_invariant raw)
  simpa [RawBuilder.macroAssembly,
    TargetEmitterSemanticSchedule.normalizedMacroRuntime] using full

/-- Exact register state after the source gate list, before output
normalization. -/
theorem rawPrefixRuntime_registers
    (raw : RawCircuit) :
    (rawPrefixRuntime raw).registers =
      { TargetEmitterLedger.ledgerRegisters raw with
        currentGate := raw.gates.length
        outputIndex := (rawPrefixAssembly raw).gates.length } := by
  let invariant := rawPrefix_invariant raw
  apply registers_ext
  · cases raw with
    | mk inputs gates output =>
        cases output with
        | gate index =>
            simpa [TargetEmitterLedger.ledgerRegisters,
              RawCircuit.normalize] using invariant.inputCount
        | input index =>
            simpa [TargetEmitterLedger.ledgerRegisters,
              RawCircuit.normalize] using invariant.inputCount
        | constant value =>
            cases value <;>
              simpa [TargetEmitterLedger.ledgerRegisters,
                RawCircuit.normalize] using invariant.inputCount
  · simpa [TargetEmitterLedger.ledgerRegisters,
      TargetEmitterLedger.normalizedGateCount_eq_normalize] using
      invariant.normalizedGateCount
  · unfold rawPrefixRuntime
    rw [appendGateListResults_carrierWidth]
    simp [
      TargetEmitterSemanticSchedule.normalizedMacroStartRuntime,
      TargetEmitterSemanticSchedule.initialRuntime,
      TargetEmitterProgramSemantics.headerResult_registers,
      TargetEmitterLedger.ledgerRegisters]
  · unfold rawPrefixRuntime
    rw [appendGateListResults_baseline]
    simp [
      TargetEmitterSemanticSchedule.normalizedMacroStartRuntime,
      TargetEmitterSemanticSchedule.initialRuntime,
      TargetEmitterProgramSemantics.headerResult_registers,
      TargetEmitterLedger.ledgerRegisters]
  · exact invariant.currentGate
  · exact invariant.outputIndex

theorem rawPrefixAssembly_gates_length (raw : RawCircuit) :
    (rawPrefixAssembly raw).gates.length =
      RawBuilder.gateListMacroGateCount raw.gates := by
  simp [rawPrefixAssembly, RawBuilder.assembleGates_gates_length,
    RawBuilder.emptyAssembly]

/-- Constructive controller range at the raw-output classifier. -/
theorem rawPrefix_controllerRange (raw : RawCircuit) :
    ControllerRange raw (rawPrefixRuntime raw).registers := by
  rw [rawPrefixRuntime_registers]
  refine
    { inputCount_eq := rfl
      normalizedGateCount_eq := rfl
      carrierWidth_eq := rfl
      baseline_eq := rfl
      currentGate_le := ?_
      outputIndex_le := ?_ }
  · simp only
    cases raw with
    | mk inputs gates output =>
        cases output with
        | gate index =>
            simp [TargetEmitterLedger.normalizedGateCount,
              TargetEmitterLedger.normalizationAddedGates]
        | input index =>
            simp [TargetEmitterLedger.normalizedGateCount,
              TargetEmitterLedger.normalizationAddedGates]
        | constant value =>
            cases value <;>
              simp [TargetEmitterLedger.normalizedGateCount,
                TargetEmitterLedger.normalizationAddedGates]
  · rw [rawPrefixAssembly_gates_length,
      ← TargetEmitterLedger.gateListMacroWeight_eq_rawBuilder]
    simp only
    simp [TargetEmitterLedger.baselineValue]
    omega

private theorem controllerRange_outputOffset
    {raw : RawCircuit}
    {registers : TargetEmitter.UnaryRegisters}
    (range : ControllerRange raw registers)
    (offset : Nat)
    (room :
      registers.outputIndex + offset ≤
        TargetEmitterLedger.baselineValue raw + 4) :
    ControllerRange raw
      { registers with
        outputIndex := registers.outputIndex + offset } := by
  exact
    { inputCount_eq := range.inputCount_eq
      normalizedGateCount_eq := range.normalizedGateCount_eq
      carrierWidth_eq := range.carrierWidth_eq
      baseline_eq := range.baseline_eq
      currentGate_le := range.currentGate_le
      outputIndex_le := room }

private theorem rawPrefix_output_room
    (raw : RawCircuit) :
    (rawPrefixRuntime raw).registers.outputIndex +
          TargetEmitterLedger.normalizationMacroWeight raw.output ≤
      TargetEmitterLedger.baselineValue raw + 4 := by
  rw [rawPrefixRuntime_registers]
  simp only
  rw [rawPrefixAssembly_gates_length,
    ← TargetEmitterLedger.gateListMacroWeight_eq_rawBuilder]
  simp [TargetEmitterLedger.baselineValue]
  omega

/-- All six controller-range boundaries needed by the fixed two-gate input
normalization block, derived from the input-output raw circuit itself. -/
theorem inputNormalizationRanges
    (inputs : Nat) (gates : List RawGate) (index : Nat) :
    let raw : RawCircuit :=
      { inputCount := inputs
        gates := gates
        output := .input index }
    InputNormalizationRanges raw (outputCapturedRuntime raw) := by
  dsimp only
  let raw : RawCircuit :=
    { inputCount := inputs
      gates := gates
      output := .input index }
  let runtime := outputCapturedRuntime raw
  have initialRange :
      ControllerRange raw runtime.registers := by
    simpa [runtime, outputCapturedRuntime] using
      rawPrefix_controllerRange raw
  have fullRoom :
      runtime.registers.outputIndex + 68 ≤
        TargetEmitterLedger.baselineValue raw + 4 := by
    simpa [runtime, outputCapturedRuntime, raw,
      TargetEmitterLedger.normalizationMacroWeight] using
      rawPrefix_output_room raw
  have room (offset : Nat) (bound : offset ≤ 68) :
      runtime.registers.outputIndex + offset ≤
        TargetEmitterLedger.baselineValue raw + 4 := by
    omega
  refine
    { initial := initialRange
      afterFirstLeft := ?_
      afterFirstRight := ?_
      afterFirstTrace := ?_
      afterSecondLeft := ?_
      afterSecondRight := ?_
      afterSecondTrace := ?_
      nextGate := ?_ }
  · simpa [TargetEmitterProgramSemantics.macroResult_registers,
      TargetEmitterPlan.sourceGateCount] using
      controllerRange_outputOffset initialRange 10
        (room 10 (by omega))
  · simpa [TargetEmitterProgramSemantics.macroResult_registers,
      TargetEmitterPlan.sourceGateCount, Nat.add_assoc] using
      controllerRange_outputOffset initialRange 12
        (room 12 (by omega))
  · simpa [TargetEmitterProgramSemantics.macroResult_registers,
      TargetEmitterPlan.sourceGateCount,
      TargetEmitterPlan.traceGateCount, Nat.add_assoc] using
      controllerRange_outputOffset initialRange 30
        (room 30 (by omega))
  · simpa [TargetEmitterProgramSemantics.macroResult_registers,
      TargetEmitterPlan.sourceGateCount,
      TargetEmitterPlan.traceGateCount, Nat.add_assoc] using
      controllerRange_outputOffset initialRange 40
        (room 40 (by omega))
  · simpa [TargetEmitterProgramSemantics.macroResult_registers,
      TargetEmitterPlan.sourceGateCount,
      TargetEmitterPlan.traceGateCount, Nat.add_assoc] using
      controllerRange_outputOffset initialRange 50
        (room 50 (by omega))
  · simpa [TargetEmitterProgramSemantics.macroResult_registers,
      TargetEmitterPlan.sourceGateCount,
      TargetEmitterPlan.traceGateCount, Nat.add_assoc] using
      controllerRange_outputOffset initialRange 68 fullRoom
  · have registersEq := rawPrefixRuntime_registers raw
    have currentEq :
        (rawPrefixRuntime raw).registers.currentGate =
          gates.length := by
      simpa [raw] using
        congrArg
          (fun registers : TargetEmitter.UnaryRegisters =>
            registers.currentGate) registersEq
    have bound :
        (rawPrefixRuntime raw).registers.currentGate ≤
          gates.length + 1 := by
      rw [currentEq]
      omega
    simpa [outputCapturedRuntime,
      TargetEmitterProgramSemantics.macroResult_registers,
      TargetEmitterPlan.sourceGateCount,
      TargetEmitterPlan.traceGateCount,
      TargetEmitterLedger.normalizedGateCount,
      TargetEmitterLedger.normalizationAddedGates,
      Nat.add_assoc] using bound

/-- The three controller-range boundaries needed by either fixed
constant-output normalization block. -/
theorem constantNormalizationRanges
    (inputs : Nat) (gates : List RawGate) (value : Bool) :
    let raw : RawCircuit :=
      { inputCount := inputs
        gates := gates
        output := .constant value }
    ConstantNormalizationRanges raw value
      (outputCapturedRuntime raw) := by
  dsimp only
  let raw : RawCircuit :=
    { inputCount := inputs
      gates := gates
      output := .constant value }
  let runtime := outputCapturedRuntime raw
  have initialRange :
      ControllerRange raw runtime.registers := by
    simpa [runtime, outputCapturedRuntime] using
      rawPrefix_controllerRange raw
  cases value with
  | false =>
      have fullRoom :
          runtime.registers.outputIndex + 22 ≤
            TargetEmitterLedger.baselineValue raw + 4 := by
        simpa [runtime, outputCapturedRuntime, raw,
          TargetEmitterLedger.normalizationMacroWeight] using
          rawPrefix_output_room raw
      refine
        { initial := initialRange
          afterLeft := ?_
          afterRight := ?_ }
      · simpa [TargetEmitterProgramSemantics.macroResult_registers,
          TargetEmitterPlan.constantNormalizationKind,
          TargetEmitterPlan.sourceGateCount] using
          controllerRange_outputOffset initialRange 2 (by omega)
      · simpa [TargetEmitterProgramSemantics.macroResult_registers,
          TargetEmitterPlan.constantNormalizationKind,
          TargetEmitterPlan.sourceGateCount, Nat.add_assoc] using
          controllerRange_outputOffset initialRange 4 (by omega)
  | true =>
      have fullRoom :
          runtime.registers.outputIndex + 24 ≤
            TargetEmitterLedger.baselineValue raw + 4 := by
        simpa [runtime, outputCapturedRuntime, raw,
          TargetEmitterLedger.normalizationMacroWeight] using
          rawPrefix_output_room raw
      refine
        { initial := initialRange
          afterLeft := ?_
          afterRight := ?_ }
      · simpa [TargetEmitterProgramSemantics.macroResult_registers,
          TargetEmitterPlan.constantNormalizationKind,
          TargetEmitterPlan.sourceGateCount] using
          controllerRange_outputOffset initialRange 3 (by omega)
      · simpa [TargetEmitterProgramSemantics.macroResult_registers,
          TargetEmitterPlan.constantNormalizationKind,
          TargetEmitterPlan.sourceGateCount, Nat.add_assoc] using
          controllerRange_outputOffset initialRange 6 (by omega)

/-- Physical traversal cursor after the selected output branch.  Input
normalization emits two synthetic gates while advancing this cursor once;
constant normalization emits one synthetic gate without needing another
gate-list iteration. -/
def normalizationCurrentGate (raw : RawCircuit) : Nat :=
  match raw.output with
  | .input _ => raw.gates.length + 1
  | .constant _ | .gate _ => raw.gates.length

theorem normalizedMacroRuntime_registers (raw : RawCircuit) :
    (TargetEmitterSemanticSchedule.normalizedMacroRuntime raw).registers =
      { TargetEmitterLedger.ledgerRegisters raw with
        currentGate := raw.normalize.gates.length
        outputIndex :=
          (RawBuilder.macroAssembly raw.normalize).gates.length } := by
  let invariant :=
    normalizedMacroRuntime_invariant_constructive raw
  apply registers_ext
  · cases raw with
    | mk inputs gates output =>
        cases output with
        | gate index =>
            simpa [TargetEmitterLedger.ledgerRegisters,
              RawCircuit.normalize] using invariant.inputCount
        | input index =>
            simpa [TargetEmitterLedger.ledgerRegisters,
              RawCircuit.normalize] using invariant.inputCount
        | constant value =>
            cases value <;>
              simpa [TargetEmitterLedger.ledgerRegisters,
                RawCircuit.normalize] using invariant.inputCount
  · simpa [TargetEmitterLedger.ledgerRegisters,
      TargetEmitterLedger.normalizedGateCount_eq_normalize] using
      invariant.normalizedGateCount
  · unfold TargetEmitterSemanticSchedule.normalizedMacroRuntime
    rw [appendGateListResults_carrierWidth]
    simp [TargetEmitterSemanticSchedule.normalizedMacroStartRuntime,
      TargetEmitterSemanticSchedule.initialRuntime,
      TargetEmitterProgramSemantics.headerResult_registers,
      TargetEmitterLedger.ledgerRegisters]
  · unfold TargetEmitterSemanticSchedule.normalizedMacroRuntime
    rw [appendGateListResults_baseline]
    simp [TargetEmitterSemanticSchedule.normalizedMacroStartRuntime,
      TargetEmitterSemanticSchedule.initialRuntime,
      TargetEmitterProgramSemantics.headerResult_registers,
      TargetEmitterLedger.ledgerRegisters]
  · exact invariant.currentGate
  · exact invariant.outputIndex

theorem normalizationAssembly_gates_length (raw : RawCircuit) :
    (normalizationAssembly raw).gates.length =
      (rawPrefixAssembly raw).gates.length +
        TargetEmitterLedger.normalizationMacroWeight raw.output := by
  unfold normalizationAssembly
  rw [RawBuilder.assembleGates_gates_length]
  cases raw with
  | mk inputs gates output =>
      cases output with
      | gate index =>
          simp [normalizationSuffix,
            TargetEmitterLedger.normalizationMacroWeight,
            RawBuilder.gateListMacroGateCount]
      | input index =>
          simp [normalizationSuffix,
            TargetEmitterLedger.normalizationMacroWeight,
            RawBuilder.gateListMacroGateCount,
            RawBuilder.gateMacroGateCount,
            RawBuilder.sourceMacroGateCount]
      | constant value =>
          cases value <;>
            simp [normalizationSuffix,
              TargetEmitterLedger.normalizationMacroWeight,
              RawBuilder.gateListMacroGateCount,
              RawBuilder.gateMacroGateCount,
              RawBuilder.sourceMacroGateCount]

theorem normalizedMacroAssembly_gates_length (raw : RawCircuit) :
    (RawBuilder.macroAssembly raw.normalize).gates.length =
      (rawPrefixAssembly raw).gates.length +
        TargetEmitterLedger.normalizationMacroWeight raw.output := by
  rw [← normalizationAssembly_eq_macroAssembly]
  exact normalizationAssembly_gates_length raw

/-- Exact physical register state after the raw-output normalization branch. -/
theorem normalizationRuntime_registers (raw : RawCircuit) :
    (normalizationRuntime raw).registers =
      { TargetEmitterLedger.ledgerRegisters raw with
        currentGate := normalizationCurrentGate raw
        outputIndex :=
          (RawBuilder.macroAssembly raw.normalize).gates.length } := by
  have macroLength := normalizedMacroAssembly_gates_length raw
  cases raw with
  | mk inputs gates output =>
      cases output with
      | gate index =>
          rw [normalizationRuntime]
          apply registers_ext <;>
            simp [outputCapturedRuntime,
              TargetEmitterProgramSemantics.resetScratchResult,
              normalizationCurrentGate,
              rawPrefixRuntime_registers,
              TargetEmitterLedger.normalizationMacroWeight,
              RawCircuit.normalize] at macroLength ⊢ <;>
            omega
      | input index =>
          rw [normalizationRuntime]
          apply registers_ext
          all_goals
            simp [outputCapturedRuntime,
              TargetEmitterProgramSemantics.inputNormalizationResult,
              TargetEmitterProgramSemantics.macroResult_registers,
              TargetEmitterProgramSemantics.incrementCurrentGateResult,
              TargetEmitterPlan.sourceGateCount,
              TargetEmitterPlan.traceGateCount,
              normalizationCurrentGate,
              rawPrefixRuntime_registers,
              TargetEmitterLedger.normalizationMacroWeight,
              RawCircuit.normalize, Nat.add_assoc] at macroLength ⊢ <;>
            omega
      | constant value =>
          cases value <;>
            rw [normalizationRuntime] <;>
            apply registers_ext
          all_goals
            simp [outputCapturedRuntime,
              TargetEmitterProgramSemantics.constantNormalizationResult,
              TargetEmitterProgramSemantics.macroResult_registers,
              TargetEmitterPlan.constantNormalizationKind,
              TargetEmitterPlan.sourceGateCount,
              TargetEmitterPlan.traceGateCount,
              normalizationCurrentGate,
              rawPrefixRuntime_registers,
              TargetEmitterLedger.normalizationMacroWeight,
              RawCircuit.normalize, Nat.add_assoc] at macroLength ⊢ <;>
            omega

theorem normalizationRuntime_scratch (raw : RawCircuit) :
    (normalizationRuntime raw).scratch = 0 := by
  cases raw with
  | mk inputs gates output =>
      cases output with
      | gate index =>
          simp [normalizationRuntime,
            TargetEmitterProgramSemantics.resetScratchResult]
      | input index =>
          exact
            TargetEmitterProgramSemantics.inputNormalizationResult_scratch
              (outputCapturedRuntime
                { inputCount := inputs
                  gates := gates
                  output := .input index })
      | constant value =>
          exact
            TargetEmitterProgramSemantics.constantNormalizationResult_scratch
              value
              (outputCapturedRuntime
                { inputCount := inputs
                  gates := gates
                  output := .constant value })

theorem normalizationRuntime_scratch_eq_normalized
    (raw : RawCircuit) :
    (normalizationRuntime raw).scratch =
      (TargetEmitterSemanticSchedule.normalizedMacroRuntime raw).scratch := by
  rw [normalizationRuntime_scratch]
  exact
    (normalizedMacroRuntime_invariant_constructive raw).scratch.symm

theorem normalizationRuntime_checks (raw : RawCircuit) :
    (normalizationRuntime raw).checks =
      TargetEmitterSemanticSchedule.checkCoordinates
        (RawBuilder.macroAssembly raw.normalize).checks := by
  have prefixChecks := (rawPrefix_invariant raw).checks
  have prefixOutput := (rawPrefix_invariant raw).outputIndex
  rw [← normalizationAssembly_eq_macroAssembly]
  cases raw with
  | mk inputs gates output =>
      cases output with
      | gate index =>
          simpa [normalizationRuntime, normalizationAssembly,
            normalizationSuffix,
            outputCapturedRuntime,
            TargetEmitterProgramSemantics.resetScratchResult,
            RawBuilder.assembleGates] using prefixChecks
      | input index =>
          rw [normalizationRuntime,
            TargetEmitterProgramSemantics.inputNormalizationResult_checks]
          simp [outputCapturedRuntime,
            normalizationAssembly, normalizationSuffix,
            RawBuilder.assembleGates,
            RawBuilder.appendSourceMacro,
            RawBuilder.appendTraceMacro,
            RawBuilder.appendTemplate,
            RawBuilder.equalityTemplate_length,
            RawBuilder.constantOneTemplate_length,
            RawBuilder.traceTemplate_length,
            TargetEmitterSemanticSchedule.checkCoordinates,
            RawBuilder.outputGateIndex,
            prefixChecks, prefixOutput, List.append_assoc]
      | constant value =>
          cases value with
          | false =>
              rw [normalizationRuntime,
                TargetEmitterProgramSemantics.constantNormalizationResult_false_checks]
              simp [outputCapturedRuntime,
                normalizationAssembly, normalizationSuffix,
                RawBuilder.assembleGates,
                RawBuilder.appendSourceMacro,
                RawBuilder.appendTraceMacro,
                RawBuilder.appendTemplate,
                RawBuilder.constantOneTemplate_length,
                TargetEmitterSemanticSchedule.checkCoordinates,
                RawBuilder.outputGateIndex,
                prefixChecks, prefixOutput, List.append_assoc]
          | true =>
              rw [normalizationRuntime,
                TargetEmitterProgramSemantics.constantNormalizationResult_true_checks]
              simp [outputCapturedRuntime,
                normalizationAssembly, normalizationSuffix,
                RawBuilder.assembleGates,
                RawBuilder.appendSourceMacro,
                RawBuilder.appendTraceMacro,
                RawBuilder.appendTemplate,
                RawBuilder.constantZeroTemplate_length,
                TargetEmitterSemanticSchedule.checkCoordinates,
                RawBuilder.outputGateIndex,
                prefixChecks, prefixOutput, List.append_assoc]

theorem normalizationRuntime_checks_eq_normalized
    (raw : RawCircuit) :
    (normalizationRuntime raw).checks =
      (TargetEmitterSemanticSchedule.normalizedMacroRuntime raw).checks := by
  rw [normalizationRuntime_checks]
  exact
    (normalizedMacroRuntime_invariant_constructive raw).checks.symm

private theorem encodeGateListTokens_append
    (first second : List RawGate) :
    encodeGateListTokens (first ++ second) =
      encodeGateListTokens first ++ encodeGateListTokens second := by
  induction first with
  | nil =>
      rfl
  | cons gate rest inductionHypothesis =>
      simp only [List.cons_append, encodeGateListTokens,
        inductionHypothesis, List.append_assoc]

private theorem macroResult_targetTokens_of_append
    (runtime : Runtime) (plan : List TargetEmitterPlan.PlannedGate)
    (relative count : Nat)
    (assembly next : MacroAssembly) (tokenPrefix : List Token)
    (tokens :
      runtime.targetTokens =
        tokenPrefix ++ encodeGateListTokens assembly.gates)
    (gates :
      assembly.gates ++
          TargetEmitterProgramSemantics.evaluatedGates runtime plan =
        next.gates) :
    (TargetEmitterProgramSemantics.macroResult
      runtime plan relative count).targetTokens =
        tokenPrefix ++ encodeGateListTokens next.gates := by
  calc
    (TargetEmitterProgramSemantics.macroResult
        runtime plan relative count).targetTokens =
      runtime.targetTokens ++
        TargetEmitterProgramSemantics.plannedGateTokens runtime plan :=
      TargetEmitterProgramSemantics.macroResult_targetTokens
        runtime plan relative count
    _ =
      tokenPrefix ++
        (encodeGateListTokens assembly.gates ++
          encodeGateListTokens
            (TargetEmitterProgramSemantics.evaluatedGates runtime plan)) := by
      simp [tokens, TargetEmitterProgramSemantics.plannedGateTokens,
        List.append_assoc]
    _ =
      tokenPrefix ++
        encodeGateListTokens
          (assembly.gates ++
            TargetEmitterProgramSemantics.evaluatedGates runtime plan) := by
      rw [encodeGateListTokens_append]
    _ = tokenPrefix ++ encodeGateListTokens next.gates := by
      rw [gates]

private theorem listBinding_three
    (first second third : RawSource) :
    RawBuilder.listBinding [first, second, third] =
      RawBuilder.rawBinding3 first second third := by
  funext index
  cases index with
  | zero => rfl
  | succ firstIndex =>
      cases firstIndex with
      | zero => rfl
      | succ secondIndex =>
          cases secondIndex with
          | zero => rfl
          | succ rest => rfl

private theorem listBinding_four
    (first second third fourth : RawSource) :
    RawBuilder.listBinding [first, second, third, fourth] =
      RawBuilder.rawBinding4 first second third fourth := by
  funext index
  cases index with
  | zero => rfl
  | succ firstIndex =>
      cases firstIndex with
      | zero => rfl
      | succ secondIndex =>
          cases secondIndex with
          | zero => rfl
          | succ thirdIndex =>
              cases thirdIndex with
              | zero => rfl
              | succ rest => rfl

private theorem sourcePlan_appends_raw_gates_of_captured
    (inputs totalGates gate side : Nat)
    (assembly : MacroAssembly) (source : RawSource)
    (runtime : Runtime)
    (inputCount :
      runtime.registers.inputCount = inputs)
    (normalizedGateCount :
      runtime.registers.normalizedGateCount = totalGates)
    (currentGate :
      runtime.registers.currentGate = gate)
    (outputIndex :
      runtime.registers.outputIndex = assembly.gates.length)
    (captured :
      runtime.captured =
        TargetEmitterSemanticSchedule.capturedValue source) :
    assembly.gates ++
        TargetEmitterProgramSemantics.evaluatedGates runtime
          (TargetEmitterPlan.sourcePlan
            (TargetEmitterSemanticSchedule.sourceKind source) side) =
      (RawBuilder.appendSourceMacro inputs totalGates gate side
        assembly source).gates := by
  have runtimeEq :
      TargetEmitterSemanticSchedule.withCaptured source runtime =
        runtime := by
    apply runtime_ext
    · simpa [TargetEmitterSemanticSchedule.withCaptured] using
        captured.symm
    · rfl
    · rfl
    · rfl
    · rfl
  rw [← runtimeEq]
  exact
    sourcePlan_appends_raw_gates_constructive
      inputs totalGates gate side assembly source runtime
      inputCount normalizedGateCount currentGate outputIndex

private theorem constantSourcePlan_appends_raw_gates
    (inputs totalGates gate side : Nat)
    (assembly : MacroAssembly) (value : Bool)
    (runtime : Runtime)
    (inputCount :
      runtime.registers.inputCount = inputs)
    (normalizedGateCount :
      runtime.registers.normalizedGateCount = totalGates)
    (currentGate :
      runtime.registers.currentGate = gate)
    (outputIndex :
      runtime.registers.outputIndex = assembly.gates.length) :
    assembly.gates ++
        TargetEmitterProgramSemantics.evaluatedGates runtime
          (TargetEmitterPlan.sourcePlan
            (TargetEmitterSemanticSchedule.sourceKind
              (.constant value)) side) =
      (RawBuilder.appendSourceMacro inputs totalGates gate side
        assembly (.constant value)).gates := by
  have gates :=
    sourcePlan_appends_raw_gates_constructive
      inputs totalGates gate side assembly (.constant value) runtime
      inputCount normalizedGateCount currentGate outputIndex
  have evaluatedEq :
      TargetEmitterProgramSemantics.evaluatedGates runtime
          (TargetEmitterPlan.sourcePlan
            (TargetEmitterSemanticSchedule.sourceKind
              (.constant value)) side) =
        TargetEmitterProgramSemantics.evaluatedGates
          (TargetEmitterSemanticSchedule.withCaptured
            (.constant value) runtime)
          (TargetEmitterPlan.sourcePlan
            (TargetEmitterSemanticSchedule.sourceKind
              (.constant value)) side) := by
    cases value <;> rfl
  rw [evaluatedEq]
  exact gates

/-- The biased source plan used by physical input normalization emits the
same gate macro as the ordinary gate-source plan at the following logical
gate, while the physical traversal cursor is still at its predecessor. -/
private theorem syntheticGatePlan_appends_raw_gates
    (inputs totalGates gate side : Nat)
    (assembly : MacroAssembly) (runtime : Runtime)
    (inputCount :
      runtime.registers.inputCount = inputs)
    (normalizedGateCount :
      runtime.registers.normalizedGateCount = totalGates)
    (currentGate :
      runtime.registers.currentGate = gate)
    (outputIndex :
      runtime.registers.outputIndex = assembly.gates.length) :
    assembly.gates ++
        TargetEmitterProgramSemantics.evaluatedGates runtime
          (TargetEmitterPlan.syntheticGatePlan 1 0 side) =
      (RawBuilder.appendSourceMacro inputs totalGates (gate + 1)
        side assembly (.gate gate)).gates := by
  subst inputs
  subst totalGates
  subst gate
  simp only [TargetEmitterProgramSemantics.evaluatedGates,
    TargetEmitterPlan.syntheticGatePlan,
    TargetEmitterPlan.syntheticGateBindings,
    TargetEmitterPlan.instantiateTemplate,
    TargetEmitterPlan.evaluate_instantiateTemplateAt]
  change
    assembly.gates ++ List.map _ RawBuilder.equalityTemplate = _
  simp [TargetEmitterPlan.PlannedSource.evaluate,
    TargetEmitterPlan.sourceLockAt,
    TargetEmitterPlan.occurrenceAt,
    TargetEmitterPlan.traceCoordinateAt,
    TargetEmitterPlan.sourceLock_evaluated,
    TargetEmitterPlan.occurrence_evaluated,
    TargetEmitterPlan.traceCoordinate_evaluated,
    TargetEmitterPlan.outputIndex,
    TargetEmitterPlan.NatExpression.evaluate_counter,
    TargetEmitterPlan.NatExpression.evaluate_addOffset,
    TargetEmitterPlan.NatExpression.evaluateCounter,
    RawBuilder.appendSourceMacro, RawBuilder.appendTemplate,
    listBinding_three, outputIndex,
    RawBuilder.sourceLockCoordinate,
    RawBuilder.occurrenceCoordinate,
    RawBuilder.sourceValueCoordinate,
    RawBuilder.traceCoordinate, Nat.add_assoc]
  intro templateGate membership
  congr 1
  · have lockEq :
        runtime.registers.inputCount +
              (3 * runtime.registers.normalizedGateCount +
                (2 * runtime.registers.currentGate + (side + 2))) =
            runtime.registers.inputCount +
              (3 * runtime.registers.normalizedGateCount +
                (2 * (runtime.registers.currentGate + 1) + side)) := by
        omega
    have occurrenceEq :
        runtime.registers.inputCount +
              (runtime.registers.normalizedGateCount +
                (2 * runtime.registers.currentGate + (side + 2))) =
            runtime.registers.inputCount +
              (runtime.registers.normalizedGateCount +
                (2 * (runtime.registers.currentGate + 1) + side)) := by
        omega
    rw [lockEq, occurrenceEq]

/-- The biased trace plan has the same interpretation as the ordinary trace
plan at the following logical gate. -/
private theorem tracePlanAt_appends_raw_gates
    (inputs totalGates gate : Nat)
    (assembly : MacroAssembly) (runtime : Runtime)
    (inputCount :
      runtime.registers.inputCount = inputs)
    (normalizedGateCount :
      runtime.registers.normalizedGateCount = totalGates)
    (currentGate :
      runtime.registers.currentGate = gate)
    (outputIndex :
      runtime.registers.outputIndex = assembly.gates.length) :
    assembly.gates ++
        TargetEmitterProgramSemantics.evaluatedGates runtime
          (TargetEmitterPlan.tracePlanAt 1) =
      (RawBuilder.appendTraceMacro inputs totalGates (gate + 1)
        assembly).gates := by
  subst inputs
  subst totalGates
  subst gate
  simp only [TargetEmitterProgramSemantics.evaluatedGates,
    TargetEmitterPlan.tracePlanAt,
    TargetEmitterPlan.traceBindingsAt,
    TargetEmitterPlan.instantiateTemplate,
    TargetEmitterPlan.evaluate_instantiateTemplateAt]
  change
    assembly.gates ++ List.map _ RawBuilder.traceTemplate = _
  simp [TargetEmitterPlan.PlannedSource.evaluate,
    TargetEmitterPlan.traceLockAt,
    TargetEmitterPlan.traceCoordinateAt,
    TargetEmitterPlan.occurrenceAt,
    TargetEmitterPlan.traceLock_evaluated,
    TargetEmitterPlan.traceCoordinate_evaluated,
    TargetEmitterPlan.occurrence_evaluated,
    TargetEmitterPlan.outputIndex,
    TargetEmitterPlan.NatExpression.evaluate_counter,
    TargetEmitterPlan.NatExpression.evaluate_addOffset,
    TargetEmitterPlan.NatExpression.evaluateCounter,
    RawBuilder.appendTraceMacro, RawBuilder.appendTemplate,
    listBinding_four, outputIndex,
    RawBuilder.traceLockCoordinate, RawBuilder.traceCoordinate,
    RawBuilder.occurrenceCoordinate, Nat.add_assoc]
  intro templateGate membership
  congr 1 <;> omega

private structure TokenInvariant
    (inputs totalGates physicalGate : Nat)
    (assembly : MacroAssembly) (tokenPrefix : List Token)
    (runtime : Runtime) : Prop where
  inputCount :
    runtime.registers.inputCount = inputs
  normalizedGateCount :
    runtime.registers.normalizedGateCount = totalGates
  currentGate :
    runtime.registers.currentGate = physicalGate
  outputIndex :
    runtime.registers.outputIndex = assembly.gates.length
  targetTokens :
    runtime.targetTokens =
      tokenPrefix ++ encodeGateListTokens assembly.gates

private theorem macroResult_preserves_tokenInvariant
    (inputs totalGates physicalGate : Nat)
    (assembly next : MacroAssembly) (tokenPrefix : List Token)
    (runtime : Runtime) (plan : List TargetEmitterPlan.PlannedGate)
    (relative count : Nat)
    (invariant :
      TokenInvariant inputs totalGates physicalGate assembly
        tokenPrefix runtime)
    (gates :
      assembly.gates ++
          TargetEmitterProgramSemantics.evaluatedGates runtime plan =
        next.gates)
    (length :
      next.gates.length = assembly.gates.length + count) :
    TokenInvariant inputs totalGates physicalGate next tokenPrefix
      (TargetEmitterProgramSemantics.macroResult
        runtime plan relative count) := by
  refine
    { inputCount := ?_
      normalizedGateCount := ?_
      currentGate := ?_
      outputIndex := ?_
      targetTokens := ?_ }
  · simpa [TargetEmitterProgramSemantics.macroResult_registers] using
      invariant.inputCount
  · simpa [TargetEmitterProgramSemantics.macroResult_registers] using
      invariant.normalizedGateCount
  · simpa [TargetEmitterProgramSemantics.macroResult_registers] using
      invariant.currentGate
  · rw [TargetEmitterProgramSemantics.macroResult_registers]
    simp only
    rw [invariant.outputIndex, length]
  · exact macroResult_targetTokens_of_append
      runtime plan relative count assembly next tokenPrefix
      invariant.targetTokens gates

private theorem sourcePlan_preserves_tokenInvariant_of_captured
    (inputs totalGates physicalGate side : Nat)
    (assembly : MacroAssembly) (source : RawSource)
    (tokenPrefix : List Token) (runtime : Runtime)
    (invariant :
      TokenInvariant inputs totalGates physicalGate assembly
        tokenPrefix runtime)
    (captured :
      runtime.captured =
        TargetEmitterSemanticSchedule.capturedValue source) :
    TokenInvariant inputs totalGates physicalGate
      (RawBuilder.appendSourceMacro inputs totalGates physicalGate
        side assembly source)
      tokenPrefix
      (TargetEmitterProgramSemantics.macroResult runtime
        (TargetEmitterPlan.sourcePlan
          (TargetEmitterSemanticSchedule.sourceKind source) side)
        (TargetEmitterPlan.sourceCheckRelative
          (TargetEmitterSemanticSchedule.sourceKind source))
        (TargetEmitterPlan.sourceGateCount
          (TargetEmitterSemanticSchedule.sourceKind source))) := by
  apply macroResult_preserves_tokenInvariant
    inputs totalGates physicalGate assembly
      (RawBuilder.appendSourceMacro inputs totalGates physicalGate
        side assembly source)
      tokenPrefix runtime
      (TargetEmitterPlan.sourcePlan
        (TargetEmitterSemanticSchedule.sourceKind source) side)
      (TargetEmitterPlan.sourceCheckRelative
        (TargetEmitterSemanticSchedule.sourceKind source))
      (TargetEmitterPlan.sourceGateCount
        (TargetEmitterSemanticSchedule.sourceKind source))
      invariant
  · exact sourcePlan_appends_raw_gates_of_captured
      inputs totalGates physicalGate side assembly source runtime
      invariant.inputCount invariant.normalizedGateCount
      invariant.currentGate invariant.outputIndex captured
  · rw [RawBuilder.appendSourceMacro_gates_length]
    cases source with
    | input index => rfl
    | constant value =>
        cases value <;> rfl
    | gate index => rfl

private theorem constantSourcePlan_preserves_tokenInvariant
    (inputs totalGates physicalGate side : Nat)
    (assembly : MacroAssembly) (value : Bool)
    (tokenPrefix : List Token) (runtime : Runtime)
    (invariant :
      TokenInvariant inputs totalGates physicalGate assembly
        tokenPrefix runtime) :
    TokenInvariant inputs totalGates physicalGate
      (RawBuilder.appendSourceMacro inputs totalGates physicalGate
        side assembly (.constant value))
      tokenPrefix
      (TargetEmitterProgramSemantics.macroResult runtime
        (TargetEmitterPlan.sourcePlan
          (TargetEmitterSemanticSchedule.sourceKind
            (.constant value)) side)
        (TargetEmitterPlan.sourceCheckRelative
          (TargetEmitterSemanticSchedule.sourceKind
            (.constant value)))
        (TargetEmitterPlan.sourceGateCount
          (TargetEmitterSemanticSchedule.sourceKind
            (.constant value)))) := by
  apply macroResult_preserves_tokenInvariant
    inputs totalGates physicalGate assembly
      (RawBuilder.appendSourceMacro inputs totalGates physicalGate
        side assembly (.constant value))
      tokenPrefix runtime
      (TargetEmitterPlan.sourcePlan
        (TargetEmitterSemanticSchedule.sourceKind
          (.constant value)) side)
      (TargetEmitterPlan.sourceCheckRelative
        (TargetEmitterSemanticSchedule.sourceKind
          (.constant value)))
      (TargetEmitterPlan.sourceGateCount
        (TargetEmitterSemanticSchedule.sourceKind
          (.constant value)))
      invariant
  · exact constantSourcePlan_appends_raw_gates
      inputs totalGates physicalGate side assembly value runtime
      invariant.inputCount invariant.normalizedGateCount
      invariant.currentGate invariant.outputIndex
  · rw [RawBuilder.appendSourceMacro_gates_length]
    cases value <;> rfl

private theorem tracePlan_preserves_tokenInvariant
    (inputs totalGates physicalGate : Nat)
    (assembly : MacroAssembly) (tokenPrefix : List Token)
    (runtime : Runtime)
    (invariant :
      TokenInvariant inputs totalGates physicalGate assembly
        tokenPrefix runtime) :
    TokenInvariant inputs totalGates physicalGate
      (RawBuilder.appendTraceMacro inputs totalGates physicalGate
        assembly)
      tokenPrefix
      (TargetEmitterProgramSemantics.macroResult runtime
        TargetEmitterPlan.tracePlan
        TargetEmitterPlan.traceCheckRelative
        TargetEmitterPlan.traceGateCount) := by
  apply macroResult_preserves_tokenInvariant
    inputs totalGates physicalGate assembly
      (RawBuilder.appendTraceMacro inputs totalGates physicalGate
        assembly)
      tokenPrefix runtime TargetEmitterPlan.tracePlan
      TargetEmitterPlan.traceCheckRelative
      TargetEmitterPlan.traceGateCount invariant
  · exact tracePlan_appends_raw_gates_constructive
      inputs totalGates physicalGate assembly runtime
      invariant.inputCount invariant.normalizedGateCount
      invariant.currentGate invariant.outputIndex
  · rw [RawBuilder.appendTraceMacro_gates_length]
    rfl

private theorem syntheticGatePlan_preserves_tokenInvariant
    (inputs totalGates physicalGate side : Nat)
    (assembly : MacroAssembly) (tokenPrefix : List Token)
    (runtime : Runtime)
    (invariant :
      TokenInvariant inputs totalGates physicalGate assembly
        tokenPrefix runtime) :
    TokenInvariant inputs totalGates physicalGate
      (RawBuilder.appendSourceMacro inputs totalGates
        (physicalGate + 1) side assembly (.gate physicalGate))
      tokenPrefix
      (TargetEmitterProgramSemantics.macroResult runtime
        (TargetEmitterPlan.syntheticGatePlan 1 0 side)
        (TargetEmitterPlan.sourceCheckRelative .gate)
        (TargetEmitterPlan.sourceGateCount .gate)) := by
  apply macroResult_preserves_tokenInvariant
    inputs totalGates physicalGate assembly
      (RawBuilder.appendSourceMacro inputs totalGates
        (physicalGate + 1) side assembly (.gate physicalGate))
      tokenPrefix runtime
      (TargetEmitterPlan.syntheticGatePlan 1 0 side)
      (TargetEmitterPlan.sourceCheckRelative .gate)
      (TargetEmitterPlan.sourceGateCount .gate) invariant
  · exact syntheticGatePlan_appends_raw_gates
      inputs totalGates physicalGate side assembly runtime
      invariant.inputCount invariant.normalizedGateCount
      invariant.currentGate invariant.outputIndex
  · rw [RawBuilder.appendSourceMacro_gates_length]
    rfl

private theorem tracePlanAt_preserves_tokenInvariant
    (inputs totalGates physicalGate : Nat)
    (assembly : MacroAssembly) (tokenPrefix : List Token)
    (runtime : Runtime)
    (invariant :
      TokenInvariant inputs totalGates physicalGate assembly
        tokenPrefix runtime) :
    TokenInvariant inputs totalGates physicalGate
      (RawBuilder.appendTraceMacro inputs totalGates
        (physicalGate + 1) assembly)
      tokenPrefix
      (TargetEmitterProgramSemantics.macroResult runtime
        (TargetEmitterPlan.tracePlanAt 1)
        TargetEmitterPlan.traceCheckRelative
        TargetEmitterPlan.traceGateCount) := by
  apply macroResult_preserves_tokenInvariant
    inputs totalGates physicalGate assembly
      (RawBuilder.appendTraceMacro inputs totalGates
        (physicalGate + 1) assembly)
      tokenPrefix runtime (TargetEmitterPlan.tracePlanAt 1)
      TargetEmitterPlan.traceCheckRelative
      TargetEmitterPlan.traceGateCount invariant
  · exact tracePlanAt_appends_raw_gates
      inputs totalGates physicalGate assembly runtime
      invariant.inputCount invariant.normalizedGateCount
      invariant.currentGate invariant.outputIndex
  · rw [RawBuilder.appendTraceMacro_gates_length]
    rfl

private theorem outputCaptured_tokenInvariant
    (raw : RawCircuit) :
    TokenInvariant raw.normalize.inputCount
      raw.normalize.gates.length raw.gates.length
      (rawPrefixAssembly raw)
      (TargetEmitterSemanticSchedule.headerTokens raw)
      (outputCapturedRuntime raw) := by
  let invariant := rawPrefix_invariant raw
  refine
    { inputCount := ?_
      normalizedGateCount := ?_
      currentGate := ?_
      outputIndex := ?_
      targetTokens := ?_ }
  · simpa [outputCapturedRuntime] using invariant.inputCount
  · simpa [outputCapturedRuntime] using invariant.normalizedGateCount
  · simpa [outputCapturedRuntime] using invariant.currentGate
  · simpa [outputCapturedRuntime] using invariant.outputIndex
  · simpa [outputCapturedRuntime] using invariant.targetTokens

theorem normalizationRuntime_targetTokens (raw : RawCircuit) :
    (normalizationRuntime raw).targetTokens =
      TargetEmitterSemanticSchedule.headerTokens raw ++
        encodeGateListTokens
          (RawBuilder.macroAssembly raw.normalize).gates := by
  rw [← normalizationAssembly_eq_macroAssembly]
  cases outputEq : raw.output with
  | gate index =>
      simpa [normalizationRuntime, outputEq,
        normalizationAssembly, normalizationSuffix,
        outputCapturedRuntime,
        TargetEmitterProgramSemantics.resetScratchResult,
        RawBuilder.assembleGates] using
        (rawPrefix_invariant raw).targetTokens
  | input index =>
      let start := outputCapturedRuntime raw
      let prefixAssembly := rawPrefixAssembly raw
      let firstLeftAssembly :=
        RawBuilder.appendSourceMacro raw.normalize.inputCount
          raw.normalize.gates.length raw.gates.length 0
          prefixAssembly (.input index)
      let firstRightAssembly :=
        RawBuilder.appendSourceMacro raw.normalize.inputCount
          raw.normalize.gates.length raw.gates.length 1
          firstLeftAssembly (.constant true)
      let firstTraceAssembly :=
        RawBuilder.appendTraceMacro raw.normalize.inputCount
          raw.normalize.gates.length raw.gates.length
          firstRightAssembly
      let secondLeftAssembly :=
        RawBuilder.appendSourceMacro raw.normalize.inputCount
          raw.normalize.gates.length (raw.gates.length + 1) 0
          firstTraceAssembly (.gate raw.gates.length)
      let secondRightAssembly :=
        RawBuilder.appendSourceMacro raw.normalize.inputCount
          raw.normalize.gates.length (raw.gates.length + 1) 1
          secondLeftAssembly (.gate raw.gates.length)
      let secondTraceAssembly :=
        RawBuilder.appendTraceMacro raw.normalize.inputCount
          raw.normalize.gates.length (raw.gates.length + 1)
          secondRightAssembly
      let firstLeft :=
        TargetEmitterProgramSemantics.macroResult start
          (TargetEmitterPlan.sourcePlan .input 0)
          (TargetEmitterPlan.sourceCheckRelative .input)
          (TargetEmitterPlan.sourceGateCount .input)
      let firstRight :=
        TargetEmitterProgramSemantics.macroResult firstLeft
          (TargetEmitterPlan.sourcePlan .constantTrue 1)
          (TargetEmitterPlan.sourceCheckRelative .constantTrue)
          (TargetEmitterPlan.sourceGateCount .constantTrue)
      let firstTrace :=
        TargetEmitterProgramSemantics.macroResult firstRight
          TargetEmitterPlan.tracePlan
          TargetEmitterPlan.traceCheckRelative
          TargetEmitterPlan.traceGateCount
      let secondLeft :=
        TargetEmitterProgramSemantics.macroResult firstTrace
          (TargetEmitterPlan.syntheticGatePlan 1 0 0)
          (TargetEmitterPlan.sourceCheckRelative .gate)
          (TargetEmitterPlan.sourceGateCount .gate)
      let secondRight :=
        TargetEmitterProgramSemantics.macroResult secondLeft
          (TargetEmitterPlan.syntheticGatePlan 1 0 1)
          (TargetEmitterPlan.sourceCheckRelative .gate)
          (TargetEmitterPlan.sourceGateCount .gate)
      let secondTrace :=
        TargetEmitterProgramSemantics.macroResult secondRight
          (TargetEmitterPlan.tracePlanAt 1)
          TargetEmitterPlan.traceCheckRelative
          TargetEmitterPlan.traceGateCount
      have initial :
          TokenInvariant raw.normalize.inputCount
            raw.normalize.gates.length raw.gates.length
            prefixAssembly
            (TargetEmitterSemanticSchedule.headerTokens raw)
            start := by
        simpa [start, prefixAssembly] using
          outputCaptured_tokenInvariant raw
      have captured :
          start.captured =
            TargetEmitterSemanticSchedule.capturedValue (.input index) := by
        simp [start, outputCapturedRuntime, outputEq,
          TargetEmitterSemanticSchedule.capturedValue]
      have afterFirstLeft :
          TokenInvariant raw.normalize.inputCount
            raw.normalize.gates.length raw.gates.length
            firstLeftAssembly
            (TargetEmitterSemanticSchedule.headerTokens raw)
            firstLeft := by
        simpa [firstLeftAssembly, firstLeft,
          TargetEmitterSemanticSchedule.sourceKind] using
          sourcePlan_preserves_tokenInvariant_of_captured
            raw.normalize.inputCount raw.normalize.gates.length
            raw.gates.length 0 prefixAssembly (.input index)
            (TargetEmitterSemanticSchedule.headerTokens raw)
            start initial captured
      have afterFirstRight :
          TokenInvariant raw.normalize.inputCount
            raw.normalize.gates.length raw.gates.length
            firstRightAssembly
            (TargetEmitterSemanticSchedule.headerTokens raw)
            firstRight := by
        simpa [firstRightAssembly, firstRight,
          TargetEmitterSemanticSchedule.sourceKind] using
          constantSourcePlan_preserves_tokenInvariant
            raw.normalize.inputCount raw.normalize.gates.length
            raw.gates.length 1 firstLeftAssembly true
            (TargetEmitterSemanticSchedule.headerTokens raw)
            firstLeft afterFirstLeft
      have afterFirstTrace :
          TokenInvariant raw.normalize.inputCount
            raw.normalize.gates.length raw.gates.length
            firstTraceAssembly
            (TargetEmitterSemanticSchedule.headerTokens raw)
            firstTrace := by
        simpa [firstTraceAssembly, firstTrace] using
          tracePlan_preserves_tokenInvariant
            raw.normalize.inputCount raw.normalize.gates.length
            raw.gates.length firstRightAssembly
            (TargetEmitterSemanticSchedule.headerTokens raw)
            firstRight afterFirstRight
      have afterSecondLeft :
          TokenInvariant raw.normalize.inputCount
            raw.normalize.gates.length raw.gates.length
            secondLeftAssembly
            (TargetEmitterSemanticSchedule.headerTokens raw)
            secondLeft := by
        simpa [secondLeftAssembly, secondLeft] using
          syntheticGatePlan_preserves_tokenInvariant
            raw.normalize.inputCount raw.normalize.gates.length
            raw.gates.length 0 firstTraceAssembly
            (TargetEmitterSemanticSchedule.headerTokens raw)
            firstTrace afterFirstTrace
      have afterSecondRight :
          TokenInvariant raw.normalize.inputCount
            raw.normalize.gates.length raw.gates.length
            secondRightAssembly
            (TargetEmitterSemanticSchedule.headerTokens raw)
            secondRight := by
        simpa [secondRightAssembly, secondRight] using
          syntheticGatePlan_preserves_tokenInvariant
            raw.normalize.inputCount raw.normalize.gates.length
            raw.gates.length 1 secondLeftAssembly
            (TargetEmitterSemanticSchedule.headerTokens raw)
            secondLeft afterSecondLeft
      have afterSecondTrace :
          TokenInvariant raw.normalize.inputCount
            raw.normalize.gates.length raw.gates.length
            secondTraceAssembly
            (TargetEmitterSemanticSchedule.headerTokens raw)
            secondTrace := by
        simpa [secondTraceAssembly, secondTrace] using
          tracePlanAt_preserves_tokenInvariant
            raw.normalize.inputCount raw.normalize.gates.length
            raw.gates.length secondRightAssembly
            (TargetEmitterSemanticSchedule.headerTokens raw)
            secondRight afterSecondRight
      simpa [normalizationRuntime, outputEq,
        TargetEmitterProgramSemantics.inputNormalizationResult,
        TargetEmitterProgramSemantics.incrementCurrentGateResult,
        normalizationAssembly, normalizationSuffix,
        RawBuilder.assembleGates,
        start, prefixAssembly,
        firstLeftAssembly, firstRightAssembly, firstTraceAssembly,
        secondLeftAssembly, secondRightAssembly, secondTraceAssembly,
        firstLeft, firstRight, firstTrace,
        secondLeft, secondRight, secondTrace] using
        afterSecondTrace.targetTokens
  | constant value =>
      cases value with
      | false =>
          let start := outputCapturedRuntime raw
          let prefixAssembly := rawPrefixAssembly raw
          let leftAssembly :=
            RawBuilder.appendSourceMacro raw.normalize.inputCount
              raw.normalize.gates.length raw.gates.length 0
              prefixAssembly (.constant true)
          let rightAssembly :=
            RawBuilder.appendSourceMacro raw.normalize.inputCount
              raw.normalize.gates.length raw.gates.length 1
              leftAssembly (.constant true)
          let traceAssembly :=
            RawBuilder.appendTraceMacro raw.normalize.inputCount
              raw.normalize.gates.length raw.gates.length
              rightAssembly
          let left :=
            TargetEmitterProgramSemantics.macroResult start
              (TargetEmitterPlan.sourcePlan .constantTrue 0)
              (TargetEmitterPlan.sourceCheckRelative .constantTrue)
              (TargetEmitterPlan.sourceGateCount .constantTrue)
          let right :=
            TargetEmitterProgramSemantics.macroResult left
              (TargetEmitterPlan.sourcePlan .constantTrue 1)
              (TargetEmitterPlan.sourceCheckRelative .constantTrue)
              (TargetEmitterPlan.sourceGateCount .constantTrue)
          let trace :=
            TargetEmitterProgramSemantics.macroResult right
              TargetEmitterPlan.tracePlan
              TargetEmitterPlan.traceCheckRelative
              TargetEmitterPlan.traceGateCount
          have initial :
              TokenInvariant raw.normalize.inputCount
                raw.normalize.gates.length raw.gates.length
                prefixAssembly
                (TargetEmitterSemanticSchedule.headerTokens raw)
                start := by
            simpa [start, prefixAssembly] using
              outputCaptured_tokenInvariant raw
          have afterLeft :
              TokenInvariant raw.normalize.inputCount
                raw.normalize.gates.length raw.gates.length
                leftAssembly
                (TargetEmitterSemanticSchedule.headerTokens raw)
                left := by
            simpa [leftAssembly, left,
              TargetEmitterSemanticSchedule.sourceKind] using
              constantSourcePlan_preserves_tokenInvariant
                raw.normalize.inputCount raw.normalize.gates.length
                raw.gates.length 0 prefixAssembly true
                (TargetEmitterSemanticSchedule.headerTokens raw)
                start initial
          have afterRight :
              TokenInvariant raw.normalize.inputCount
                raw.normalize.gates.length raw.gates.length
                rightAssembly
                (TargetEmitterSemanticSchedule.headerTokens raw)
                right := by
            simpa [rightAssembly, right,
              TargetEmitterSemanticSchedule.sourceKind] using
              constantSourcePlan_preserves_tokenInvariant
                raw.normalize.inputCount raw.normalize.gates.length
                raw.gates.length 1 leftAssembly true
                (TargetEmitterSemanticSchedule.headerTokens raw)
                left afterLeft
          have afterTrace :
              TokenInvariant raw.normalize.inputCount
                raw.normalize.gates.length raw.gates.length
                traceAssembly
                (TargetEmitterSemanticSchedule.headerTokens raw)
                trace := by
            simpa [traceAssembly, trace] using
              tracePlan_preserves_tokenInvariant
                raw.normalize.inputCount raw.normalize.gates.length
                raw.gates.length rightAssembly
                (TargetEmitterSemanticSchedule.headerTokens raw)
                right afterRight
          simpa [normalizationRuntime, outputEq,
            TargetEmitterProgramSemantics.constantNormalizationResult,
            TargetEmitterPlan.constantNormalizationKind,
            normalizationAssembly, normalizationSuffix,
            RawBuilder.assembleGates,
            start, prefixAssembly, leftAssembly, rightAssembly,
            traceAssembly, left, right, trace] using
            afterTrace.targetTokens
      | true =>
          let start := outputCapturedRuntime raw
          let prefixAssembly := rawPrefixAssembly raw
          let leftAssembly :=
            RawBuilder.appendSourceMacro raw.normalize.inputCount
              raw.normalize.gates.length raw.gates.length 0
              prefixAssembly (.constant false)
          let rightAssembly :=
            RawBuilder.appendSourceMacro raw.normalize.inputCount
              raw.normalize.gates.length raw.gates.length 1
              leftAssembly (.constant false)
          let traceAssembly :=
            RawBuilder.appendTraceMacro raw.normalize.inputCount
              raw.normalize.gates.length raw.gates.length
              rightAssembly
          let left :=
            TargetEmitterProgramSemantics.macroResult start
              (TargetEmitterPlan.sourcePlan .constantFalse 0)
              (TargetEmitterPlan.sourceCheckRelative .constantFalse)
              (TargetEmitterPlan.sourceGateCount .constantFalse)
          let right :=
            TargetEmitterProgramSemantics.macroResult left
              (TargetEmitterPlan.sourcePlan .constantFalse 1)
              (TargetEmitterPlan.sourceCheckRelative .constantFalse)
              (TargetEmitterPlan.sourceGateCount .constantFalse)
          let trace :=
            TargetEmitterProgramSemantics.macroResult right
              TargetEmitterPlan.tracePlan
              TargetEmitterPlan.traceCheckRelative
              TargetEmitterPlan.traceGateCount
          have initial :
              TokenInvariant raw.normalize.inputCount
                raw.normalize.gates.length raw.gates.length
                prefixAssembly
                (TargetEmitterSemanticSchedule.headerTokens raw)
                start := by
            simpa [start, prefixAssembly] using
              outputCaptured_tokenInvariant raw
          have afterLeft :
              TokenInvariant raw.normalize.inputCount
                raw.normalize.gates.length raw.gates.length
                leftAssembly
                (TargetEmitterSemanticSchedule.headerTokens raw)
                left := by
            simpa [leftAssembly, left,
              TargetEmitterSemanticSchedule.sourceKind] using
              constantSourcePlan_preserves_tokenInvariant
                raw.normalize.inputCount raw.normalize.gates.length
                raw.gates.length 0 prefixAssembly false
                (TargetEmitterSemanticSchedule.headerTokens raw)
                start initial
          have afterRight :
              TokenInvariant raw.normalize.inputCount
                raw.normalize.gates.length raw.gates.length
                rightAssembly
                (TargetEmitterSemanticSchedule.headerTokens raw)
                right := by
            simpa [rightAssembly, right,
              TargetEmitterSemanticSchedule.sourceKind] using
              constantSourcePlan_preserves_tokenInvariant
                raw.normalize.inputCount raw.normalize.gates.length
                raw.gates.length 1 leftAssembly false
                (TargetEmitterSemanticSchedule.headerTokens raw)
                left afterLeft
          have afterTrace :
              TokenInvariant raw.normalize.inputCount
                raw.normalize.gates.length raw.gates.length
                traceAssembly
                (TargetEmitterSemanticSchedule.headerTokens raw)
                trace := by
            simpa [traceAssembly, trace] using
              tracePlan_preserves_tokenInvariant
                raw.normalize.inputCount raw.normalize.gates.length
                raw.gates.length rightAssembly
                (TargetEmitterSemanticSchedule.headerTokens raw)
                right afterRight
          simpa [normalizationRuntime, outputEq,
            TargetEmitterProgramSemantics.constantNormalizationResult,
            TargetEmitterPlan.constantNormalizationKind,
            normalizationAssembly, normalizationSuffix,
            RawBuilder.assembleGates,
            start, prefixAssembly, leftAssembly, rightAssembly,
            traceAssembly, left, right, trace] using
            afterTrace.targetTokens

theorem normalizationRuntime_targetTokens_eq_normalized
    (raw : RawCircuit) :
    (normalizationRuntime raw).targetTokens =
      (TargetEmitterSemanticSchedule.normalizedMacroRuntime raw).targetTokens := by
  rw [normalizationRuntime_targetTokens]
  exact
    (normalizedMacroRuntime_invariant_constructive raw).targetTokens.symm

end PNP.Concrete.LockedNAND.TargetEmitterSemanticNormalization
