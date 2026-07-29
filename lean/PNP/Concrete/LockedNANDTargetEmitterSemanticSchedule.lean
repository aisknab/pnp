/-
Copyright (c) 2026 PNP Labs.

Logical schedule invariants for the grammar-only locked-NAND target emitter.

This file connects the pure named-program semantics to the independent raw
builder one selected source and one trace block at a time.  It does not run a
machine and it does not give the executable controller a source-dependent
schedule.
-/

import PNP.Concrete.LockedNANDTargetEmitterCapacity

namespace PNP.Concrete.LockedNAND.TargetEmitterSemanticSchedule

open PNP.Concrete

abbrev Runtime := TargetEmitterProgramSemantics.Runtime
abbrev MacroAssembly := RawBuilder.MacroAssembly

def sourceKind : RawSource → TargetEmitterPlan.SourceKind
  | .input _ => .input
  | .constant false => .constantFalse
  | .constant true => .constantTrue
  | .gate _ => .gate

def capturedValue : RawSource → Nat
  | .input index => index
  | .constant _ => 0
  | .gate index => index

def withCaptured (source : RawSource) (runtime : Runtime) : Runtime :=
  { runtime with captured := capturedValue source }

def checkCoordinates (checks : List RawSource) : List Nat :=
  checks.map RawBuilder.outputGateIndex

/-- Logical state shared by source-order macro traversal.  The retained
source cursor changes `captured` independently, so it is intentionally not
part of this invariant. -/
structure MacroInvariant
    (inputs totalGates gate : Nat)
    (assembly : MacroAssembly)
    (tokenPrefix : List Token)
    (runtime : Runtime) : Prop where
  inputCount :
    runtime.registers.inputCount = inputs
  normalizedGateCount :
    runtime.registers.normalizedGateCount = totalGates
  currentGate :
    runtime.registers.currentGate = gate
  outputIndex :
    runtime.registers.outputIndex = assembly.gates.length
  scratch :
    runtime.scratch = 0
  checks :
    runtime.checks = checkCoordinates assembly.checks
  targetTokens :
    runtime.targetTokens =
      tokenPrefix ++ encodeGateListTokens assembly.gates

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

private theorem listBinding_two
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

theorem sourcePlan_appends_raw_gates
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
          (withCaptured source runtime)
          (TargetEmitterPlan.sourcePlan (sourceKind source) side) =
      (RawBuilder.appendSourceMacro
        inputs totalGates gate side assembly source).gates := by
  subst inputs
  subst totalGates
  subst gate
  cases source with
  | input index =>
      simp only [withCaptured, capturedValue, sourceKind,
        TargetEmitterProgramSemantics.evaluatedGates,
        TargetEmitterPlan.sourcePlan,
        TargetEmitterPlan.sourceBindings,
        TargetEmitterPlan.instantiateTemplate,
        TargetEmitterPlan.sourceTemplate,
        TargetEmitterPlan.evaluate_instantiateTemplateAt]
      change
        assembly.gates ++
            List.map _ RawBuilder.equalityTemplate =
          _
      simp [TargetEmitterPlan.PlannedSource.evaluate,
        TargetEmitterPlan.sourceLock_evaluated,
        TargetEmitterPlan.occurrence_evaluated,
        TargetEmitterPlan.capturedIndex,
        TargetEmitterPlan.outputIndex,
        TargetEmitterPlan.NatExpression.evaluate_counter,
        TargetEmitterPlan.NatExpression.evaluateCounter,
        RawBuilder.appendSourceMacro, RawBuilder.appendTemplate,
        listBinding_three, outputIndex,
        RawBuilder.sourceLockCoordinate,
        RawBuilder.occurrenceCoordinate,
        RawBuilder.sourceValueCoordinate,
        RawBuilder.primaryCoordinate, Nat.add_assoc]
  | constant value =>
      cases value with
      | false =>
          simp only [withCaptured, capturedValue, sourceKind,
            TargetEmitterProgramSemantics.evaluatedGates,
            TargetEmitterPlan.sourcePlan,
            TargetEmitterPlan.sourceBindings,
            TargetEmitterPlan.instantiateTemplate,
            TargetEmitterPlan.sourceTemplate,
            TargetEmitterPlan.evaluate_instantiateTemplateAt]
          change
            assembly.gates ++
                List.map _ RawBuilder.constantZeroTemplate =
              _
          simp [TargetEmitterPlan.PlannedSource.evaluate,
            TargetEmitterPlan.sourceLock_evaluated,
            TargetEmitterPlan.occurrence_evaluated,
            TargetEmitterPlan.outputIndex,
            TargetEmitterPlan.NatExpression.evaluate_counter,
            TargetEmitterPlan.NatExpression.evaluateCounter,
            RawBuilder.appendSourceMacro, RawBuilder.appendTemplate,
            listBinding_two, outputIndex,
            RawBuilder.sourceLockCoordinate,
            RawBuilder.occurrenceCoordinate, Nat.add_assoc]
      | true =>
          simp only [withCaptured, capturedValue, sourceKind,
            TargetEmitterProgramSemantics.evaluatedGates,
            TargetEmitterPlan.sourcePlan,
            TargetEmitterPlan.sourceBindings,
            TargetEmitterPlan.instantiateTemplate,
            TargetEmitterPlan.sourceTemplate,
            TargetEmitterPlan.evaluate_instantiateTemplateAt]
          change
            assembly.gates ++
                List.map _ RawBuilder.constantOneTemplate =
              _
          simp [TargetEmitterPlan.PlannedSource.evaluate,
            TargetEmitterPlan.sourceLock_evaluated,
            TargetEmitterPlan.occurrence_evaluated,
            TargetEmitterPlan.outputIndex,
            TargetEmitterPlan.NatExpression.evaluate_counter,
            TargetEmitterPlan.NatExpression.evaluateCounter,
            RawBuilder.appendSourceMacro, RawBuilder.appendTemplate,
            listBinding_two, outputIndex,
            RawBuilder.sourceLockCoordinate,
            RawBuilder.occurrenceCoordinate, Nat.add_assoc]
  | gate index =>
      simp only [withCaptured, capturedValue, sourceKind,
        TargetEmitterProgramSemantics.evaluatedGates,
        TargetEmitterPlan.sourcePlan,
        TargetEmitterPlan.sourceBindings,
        TargetEmitterPlan.instantiateTemplate,
        TargetEmitterPlan.sourceTemplate,
        TargetEmitterPlan.evaluate_instantiateTemplateAt]
      change
        assembly.gates ++
            List.map _ RawBuilder.equalityTemplate =
          _
      simp [TargetEmitterPlan.PlannedSource.evaluate,
        TargetEmitterPlan.sourceLock_evaluated,
        TargetEmitterPlan.occurrence_evaluated,
        TargetEmitterPlan.rawGateTrace_evaluated,
        TargetEmitterPlan.outputIndex,
        TargetEmitterPlan.NatExpression.evaluate_counter,
        TargetEmitterPlan.NatExpression.evaluateCounter,
        RawBuilder.appendSourceMacro, RawBuilder.appendTemplate,
        listBinding_three, outputIndex,
        RawBuilder.sourceLockCoordinate,
        RawBuilder.occurrenceCoordinate,
        RawBuilder.sourceValueCoordinate,
        RawBuilder.traceCoordinate, Nat.add_assoc]

theorem tracePlan_appends_raw_gates
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
  change
    assembly.gates ++
        List.map _ RawBuilder.traceTemplate =
      _
  simp [TargetEmitterPlan.PlannedSource.evaluate,
    RawBuilder.appendTraceMacro, RawBuilder.appendTemplate,
    listBinding_four,
    TargetEmitterPlan.traceLock_evaluated,
    TargetEmitterPlan.traceCoordinate_evaluated,
    TargetEmitterPlan.occurrence_evaluated,
    TargetEmitterPlan.outputIndex,
    TargetEmitterPlan.NatExpression.evaluate_counter,
    TargetEmitterPlan.NatExpression.evaluateCounter,
    outputIndex,
    RawBuilder.traceLockCoordinate, RawBuilder.traceCoordinate,
    RawBuilder.occurrenceCoordinate, Nat.add_assoc]

theorem sourceMacro_preserves_invariant
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
        (withCaptured source runtime)
        (TargetEmitterPlan.sourcePlan (sourceKind source) side)
        (TargetEmitterPlan.sourceCheckRelative (sourceKind source))
        (TargetEmitterPlan.sourceGateCount (sourceKind source))) := by
  let gates :=
    TargetEmitterPlan.sourcePlan (sourceKind source) side
  let relative :=
    TargetEmitterPlan.sourceCheckRelative (sourceKind source)
  let count :=
    TargetEmitterPlan.sourceGateCount (sourceKind source)
  let capturedRuntime := withCaptured source runtime
  let final :=
    TargetEmitterProgramSemantics.macroResult
      capturedRuntime gates relative count
  have gatesEq :
      assembly.gates ++
          TargetEmitterProgramSemantics.evaluatedGates
            capturedRuntime gates =
        (RawBuilder.appendSourceMacro
          inputs totalGates gate side assembly source).gates := by
    exact sourcePlan_appends_raw_gates
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
  · simpa [final, capturedRuntime, withCaptured, gates, relative, count,
      TargetEmitterProgramSemantics.macroResult,
      TargetEmitterProgramSemantics.resetScratchResult,
      TargetEmitterProgramSemantics.incrementOutputResult,
      TargetEmitterProgramSemantics.checkPushResult,
      TargetEmitterProgramSemantics.gatesResult_registers] using
      invariant.inputCount
  · simpa [final, capturedRuntime, withCaptured, gates, relative, count,
      TargetEmitterProgramSemantics.macroResult,
      TargetEmitterProgramSemantics.resetScratchResult,
      TargetEmitterProgramSemantics.incrementOutputResult,
      TargetEmitterProgramSemantics.checkPushResult,
      TargetEmitterProgramSemantics.gatesResult_registers] using
      invariant.normalizedGateCount
  · simpa [final, capturedRuntime, withCaptured, gates, relative, count,
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
          TargetEmitterPlan.sourceGateCount (sourceKind source) =
        (RawBuilder.appendSourceMacro
          inputs totalGates gate side assembly source).gates.length
    rw [invariant.outputIndex,
      RawBuilder.appendSourceMacro_gates_length]
    cases source with
    | input index =>
        rfl
    | constant value =>
        cases value <;> rfl
    | gate index =>
        rfl
  · exact
      TargetEmitterProgramSemantics.macroResult_scratch
        capturedRuntime gates relative count
  · rw [TargetEmitterProgramSemantics.macroResult_checks]
    simp only [withCaptured]
    rw [invariant.checks, invariant.outputIndex]
    cases source with
    | input index =>
        simp [checkCoordinates, RawBuilder.appendSourceMacro,
          sourceKind, TargetEmitterPlan.sourceCheckRelative,
          RawBuilder.outputGateIndex]
    | constant value =>
        cases value <;>
          simp [checkCoordinates, RawBuilder.appendSourceMacro,
            sourceKind, TargetEmitterPlan.sourceCheckRelative,
            RawBuilder.outputGateIndex]
    | gate index =>
        simp [checkCoordinates, RawBuilder.appendSourceMacro,
          sourceKind, TargetEmitterPlan.sourceCheckRelative,
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
        simp [capturedRuntime, withCaptured,
          TargetEmitterProgramSemantics.plannedGateTokens,
          invariant.targetTokens, List.append_assoc]
      _ =
          tokenPrefix ++
            encodeGateListTokens
              (assembly.gates ++
                TargetEmitterProgramSemantics.evaluatedGates
                  capturedRuntime gates) := by
        rw [encodeGateListTokens_append]
      _ =
          tokenPrefix ++
            encodeGateListTokens
              (RawBuilder.appendSourceMacro
                inputs totalGates gate side assembly source).gates := by
        rw [gatesEq]

theorem traceMacro_advances_invariant
    (inputs totalGates gate : Nat)
    (assembly : MacroAssembly)
    (tokenPrefix : List Token) (runtime : Runtime)
    (invariant :
      MacroInvariant inputs totalGates gate assembly
        tokenPrefix runtime) :
    MacroInvariant inputs totalGates (gate + 1)
      (RawBuilder.appendTraceMacro
        inputs totalGates gate assembly)
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
  let final :=
    TargetEmitterProgramSemantics.incrementCurrentGateResult traced
  have gatesEq :
      assembly.gates ++
          TargetEmitterProgramSemantics.evaluatedGates
            runtime TargetEmitterPlan.tracePlan =
        (RawBuilder.appendTraceMacro
          inputs totalGates gate assembly).gates := by
    exact tracePlan_appends_raw_gates
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
  · simpa [final,
      TargetEmitterProgramSemantics.incrementCurrentGateResult,
      traced, TargetEmitterProgramSemantics.macroResult,
      TargetEmitterProgramSemantics.resetScratchResult,
      TargetEmitterProgramSemantics.incrementOutputResult,
      TargetEmitterProgramSemantics.checkPushResult,
      TargetEmitterProgramSemantics.gatesResult_registers] using
      invariant.inputCount
  · simpa [final,
      TargetEmitterProgramSemantics.incrementCurrentGateResult,
      traced, TargetEmitterProgramSemantics.macroResult,
      TargetEmitterProgramSemantics.resetScratchResult,
      TargetEmitterProgramSemantics.incrementOutputResult,
      TargetEmitterProgramSemantics.checkPushResult,
      TargetEmitterProgramSemantics.gatesResult_registers] using
      invariant.normalizedGateCount
  · simpa [final,
      TargetEmitterProgramSemantics.incrementCurrentGateResult,
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
    simp [checkCoordinates, RawBuilder.appendTraceMacro,
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
        rw [encodeGateListTokens_append]
      _ =
          tokenPrefix ++
            encodeGateListTokens
              (RawBuilder.appendTraceMacro
                inputs totalGates gate assembly).gates := by
        rw [gatesEq]

/-! ### Source-order gate traversal -/

def appendSourceResult
    (side : Nat) (source : RawSource)
    (runtime : Runtime) : Runtime :=
  TargetEmitterProgramSemantics.macroResult
    (withCaptured source runtime)
    (TargetEmitterPlan.sourcePlan (sourceKind source) side)
    (TargetEmitterPlan.sourceCheckRelative (sourceKind source))
    (TargetEmitterPlan.sourceGateCount (sourceKind source))

def appendGateResult
    (sourceGate : RawGate) (runtime : Runtime) : Runtime :=
  let left := appendSourceResult 0 sourceGate.left runtime
  let right := appendSourceResult 1 sourceGate.right left
  let trace :=
    TargetEmitterProgramSemantics.macroResult right
      TargetEmitterPlan.tracePlan
      TargetEmitterPlan.traceCheckRelative
      TargetEmitterPlan.traceGateCount
  TargetEmitterProgramSemantics.incrementCurrentGateResult trace

def appendGateListResults :
    List RawGate → Runtime → Runtime
  | [], runtime => runtime
  | sourceGate :: rest, runtime =>
      appendGateListResults rest
        (appendGateResult sourceGate runtime)

theorem appendGateResult_advances_invariant
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
    MacroInvariant inputs totalGates (gate + 1)
      trace tokenPrefix (appendGateResult sourceGate runtime) := by
  let left :=
    RawBuilder.appendSourceMacro inputs totalGates gate 0
      assembly sourceGate.left
  let right :=
    RawBuilder.appendSourceMacro inputs totalGates gate 1
      left sourceGate.right
  let trace :=
    RawBuilder.appendTraceMacro inputs totalGates gate right
  let afterLeft :=
    appendSourceResult 0 sourceGate.left runtime
  let afterRight :=
    appendSourceResult 1 sourceGate.right afterLeft
  have leftInvariant :
      MacroInvariant inputs totalGates gate left
        tokenPrefix afterLeft := by
    simpa [left, afterLeft, appendSourceResult] using
      sourceMacro_preserves_invariant
        inputs totalGates gate 0 assembly sourceGate.left
        tokenPrefix runtime invariant
  have rightInvariant :
      MacroInvariant inputs totalGates gate right
        tokenPrefix afterRight := by
    simpa [right, afterRight, appendSourceResult] using
      sourceMacro_preserves_invariant
        inputs totalGates gate 1 left sourceGate.right
        tokenPrefix afterLeft leftInvariant
  have traceInvariant :
      MacroInvariant inputs totalGates (gate + 1) trace
        tokenPrefix
        (TargetEmitterProgramSemantics.incrementCurrentGateResult
          (TargetEmitterProgramSemantics.macroResult afterRight
            TargetEmitterPlan.tracePlan
            TargetEmitterPlan.traceCheckRelative
            TargetEmitterPlan.traceGateCount)) := by
    exact traceMacro_advances_invariant
      inputs totalGates gate right tokenPrefix afterRight
      rightInvariant
  simpa [appendGateResult, afterLeft, afterRight, left, right, trace] using
    traceInvariant

theorem appendGateListResults_preserves_invariant
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
      (appendGateListResults sourceGates runtime) := by
  induction sourceGates generalizing gate assembly runtime with
  | nil =>
      simpa [RawBuilder.assembleGates, appendGateListResults] using
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
      let afterGate := appendGateResult sourceGate runtime
      have gateInvariant :
          MacroInvariant inputs totalGates (gate + 1) trace
            tokenPrefix afterGate := by
        simpa [left, right, trace, afterGate] using
          appendGateResult_advances_invariant
            inputs totalGates gate assembly sourceGate
            tokenPrefix runtime invariant
      have tailInvariant :=
        inductionHypothesis (gate + 1) trace afterGate gateInvariant
      have gateIndexEq :
          (gate + 1) + rest.length =
            gate + (rest.length + 1) := by
        omega
      rw [gateIndexEq] at tailInvariant
      simpa [RawBuilder.assembleGates, appendGateListResults,
        left, right, trace, afterGate] using
        tailInvariant

/-! ### Canonical normalized macro prefix -/

def initialRuntime (raw : RawCircuit) : Runtime :=
  { captured := 0
    scratch := 0
    registers := TargetEmitterLedger.ledgerRegisters raw
    checks := []
    targetTokens := [] }

def headerTokens (raw : RawCircuit) : List Token :=
  (TargetEmitterProgramSemantics.headerResult
    (initialRuntime raw)).targetTokens

def canonicalHeaderTokens (raw : RawCircuit) : List Token :=
  let targetInstance := RawBuilder.rawLockedInstance raw
  [.version0] ++
    encodeNatTokens targetInstance.candidate.inputCount ++
    encodeNatTokens targetInstance.candidate.gates.length ++
    encodeNatTokens targetInstance.candidate.outputs.length

theorem headerTokens_eq_canonicalHeaderTokens
    (raw : RawCircuit) :
    headerTokens raw = canonicalHeaderTokens raw := by
  rw [headerTokens,
    TargetEmitterProgramSemantics.headerResult_targetTokens]
  simp only [initialRuntime, List.nil_append,
    canonicalHeaderTokens]
  rw [TargetEmitterLedger.ledgerRegisters_carrierWidth,
    TargetEmitterLedger.ledgerRegisters_baseline,
    RawBuilder.rawLockedInstance_gate_length,
    RawBuilder.rawLockedInstance_output_length]

/-- Gate traversal starts after the header's final unary natural has been
consumed by the first block-local scratch reset.  This is a logical schedule
boundary; the physical capture proof retains and bounds the actual
`baseline + 1` scratch value. -/
def normalizedMacroStartRuntime (raw : RawCircuit) : Runtime :=
  { TargetEmitterProgramSemantics.headerResult
      (initialRuntime raw) with
    scratch := 0 }

def normalizedMacroRuntime (raw : RawCircuit) : Runtime :=
  appendGateListResults raw.normalize.gates
    (normalizedMacroStartRuntime raw)

theorem normalizedMacroStart_invariant
    (raw : RawCircuit) :
    MacroInvariant raw.normalize.inputCount
      raw.normalize.gates.length 0 RawBuilder.emptyAssembly
      (headerTokens raw) (normalizedMacroStartRuntime raw) := by
  refine
    { inputCount := ?_
      normalizedGateCount := ?_
      currentGate := ?_
      outputIndex := ?_
      scratch := rfl
      checks := ?_
      targetTokens := ?_ }
  · cases raw with
    | mk inputs gates output =>
        cases output with
        | input index => rfl
        | gate index => rfl
        | constant value =>
            cases value <;> rfl
  · simpa [normalizedMacroStartRuntime,
      TargetEmitterProgramSemantics.headerResult_registers,
      initialRuntime, TargetEmitterLedger.ledgerRegisters] using
      TargetEmitterLedger.normalizedGateCount_eq_normalize raw
  · rfl
  · rfl
  · rfl
  · simp [headerTokens, normalizedMacroStartRuntime,
      RawBuilder.emptyAssembly, encodeGateListTokens]

theorem normalizedMacroRuntime_invariant
    (raw : RawCircuit) :
    MacroInvariant raw.normalize.inputCount
      raw.normalize.gates.length raw.normalize.gates.length
      (RawBuilder.macroAssembly raw.normalize)
      (headerTokens raw) (normalizedMacroRuntime raw) := by
  have full :=
    appendGateListResults_preserves_invariant
      raw.normalize.inputCount raw.normalize.gates.length 0
      RawBuilder.emptyAssembly raw.normalize.gates
      (headerTokens raw) (normalizedMacroStartRuntime raw)
      (normalizedMacroStart_invariant raw)
  simpa [normalizedMacroRuntime, RawBuilder.macroAssembly] using full

theorem normalizedMacroRuntime_targetTokens
    (raw : RawCircuit) :
    (normalizedMacroRuntime raw).targetTokens =
      headerTokens raw ++
        encodeGateListTokens
          (RawBuilder.macroAssembly raw.normalize).gates :=
  (normalizedMacroRuntime_invariant raw).targetTokens

theorem normalizedMacroRuntime_checks
    (raw : RawCircuit) :
    (normalizedMacroRuntime raw).checks =
      checkCoordinates
        (RawBuilder.macroAssembly raw.normalize).checks :=
  (normalizedMacroRuntime_invariant raw).checks

theorem normalizedMacroRuntime_outputIndex
    (raw : RawCircuit) :
    (normalizedMacroRuntime raw).registers.outputIndex =
      (RawBuilder.macroAssembly raw.normalize).gates.length :=
  (normalizedMacroRuntime_invariant raw).outputIndex

end PNP.Concrete.LockedNAND.TargetEmitterSemanticSchedule
