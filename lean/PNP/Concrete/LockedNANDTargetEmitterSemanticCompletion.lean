/-
Copyright (c) 2026 PNP Labs.

Closed pure semantics for the grammar-only locked-NAND target emitter.

This file joins the independently verified normalization, right-folded
prefix, final-template, and output phases.  The executable controller still
receives only the raw bit word; the definitions below are proof-side
semantics used to identify its exact emitted token word.
-/

import PNP.Concrete.LockedNANDTargetEmitterSemanticFinal
import PNP.Concrete.LockedNANDTargetEmitterSemanticNormalization

namespace PNP.Concrete.LockedNAND.TargetEmitterSemanticCompletion

open PNP.Concrete

abbrev Runtime := TargetEmitterProgramSemantics.Runtime
abbrev PrefixRun := TargetEmitterSemanticPrefix.PrefixRun
abbrev PrefixAssembly := RawBuilder.PrefixAssembly

/-- Oldest-first logical check coordinates produced by the normalized macro
assembly. -/
def checkCoordinates (raw : RawCircuit) : List Nat :=
  TargetEmitterSemanticSchedule.checkCoordinates
    (RawBuilder.macroAssembly raw.normalize).checks

/-- Exact right-fold boundary after every normalized macro check has been
consumed. -/
def prefixRun (raw : RawCircuit) : PrefixRun :=
  TargetEmitterSemanticPrefix.runPrefix
    (checkCoordinates raw)
    (TargetEmitterSemanticNormalization.normalizationRuntime raw)

/-- The raw gate-output branch retains the source-captured index.  The two
normalizing branches retain the physical cursor at the synthesized output
gate. -/
def outputTraceExpression (raw : RawCircuit) :
    TargetEmitterPlan.NatExpression :=
  match raw.output with
  | .gate _ => TargetEmitterPlan.rawGateTrace
  | .input _ | .constant _ => TargetEmitterPlan.traceCoordinate

/-- The empty normalized program takes the explicit false-prefix final
block.  Every nonempty normalized program takes the positive final block. -/
def finalRuntime (raw : RawCircuit) : Runtime :=
  if checkCoordinates raw = [] then
    TargetEmitterProgramSemantics.finalResult
      (prefixRun raw).runtime TargetEmitterPlan.finalZeroPlan
  else
    TargetEmitterProgramSemantics.finalResult
      (prefixRun raw).runtime
      (TargetEmitterPlan.finalPositivePlan
        (outputTraceExpression raw))

/-- Pure result after the complete output tuple and threshold have been
serialized. -/
def completeRuntime (raw : RawCircuit) : Runtime :=
  TargetEmitterSemanticOutput.completeOutputResult (finalRuntime raw)

private structure PrefixStable
    (initial : Runtime) (result : PrefixRun) : Prop where
  captured : result.runtime.captured = initial.captured
  inputCount :
    result.runtime.registers.inputCount =
      initial.registers.inputCount
  normalizedGateCount :
    result.runtime.registers.normalizedGateCount =
      initial.registers.normalizedGateCount
  carrierWidth :
    result.runtime.registers.carrierWidth =
      initial.registers.carrierWidth
  baseline :
    result.runtime.registers.baseline =
      initial.registers.baseline
  currentGate :
    result.runtime.registers.currentGate =
      initial.registers.currentGate

private theorem runPrefix_stable
    (coordinates : List Nat) (runtime : Runtime) :
    PrefixStable runtime
      (TargetEmitterSemanticPrefix.runPrefix coordinates runtime) := by
  induction coordinates generalizing runtime with
  | nil =>
      rw [TargetEmitterSemanticPrefix.runPrefix]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons head rest inductionHypothesis =>
      cases rest with
      | nil =>
          rw [TargetEmitterSemanticPrefix.runPrefix]
          exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      | cons next tail =>
          let tailInput : Runtime :=
            { runtime with checks := next :: tail }
          have stableTail :
              PrefixStable tailInput
                (TargetEmitterSemanticPrefix.runPrefix
                  (next :: tail) tailInput) :=
            inductionHypothesis tailInput
          cases tail with
          | nil =>
              rw [TargetEmitterSemanticPrefix.runPrefix]
              refine
                { captured := stableTail.captured.trans ?_
                  inputCount := ?_
                  normalizedGateCount := ?_
                  carrierWidth := ?_
                  baseline := ?_
                  currentGate := ?_ }
              · rfl
              · rw [
                  TargetEmitterProgramSemantics.firstPrefixResult_registers]
                exact stableTail.inputCount
              · rw [
                  TargetEmitterProgramSemantics.firstPrefixResult_registers]
                exact stableTail.normalizedGateCount
              · rw [
                  TargetEmitterProgramSemantics.firstPrefixResult_registers]
                exact stableTail.carrierWidth
              · rw [
                  TargetEmitterProgramSemantics.firstPrefixResult_registers]
                exact stableTail.baseline
              · rw [
                  TargetEmitterProgramSemantics.firstPrefixResult_registers]
                exact stableTail.currentGate
          | cons third more =>
              rw [TargetEmitterSemanticPrefix.runPrefix]
              refine
                { captured := stableTail.captured.trans ?_
                  inputCount := ?_
                  normalizedGateCount := ?_
                  carrierWidth := ?_
                  baseline := ?_
                  currentGate := ?_ }
              · rfl
              · rw [
                  TargetEmitterProgramSemantics.nextPrefixResult_registers]
                exact stableTail.inputCount
              · rw [
                  TargetEmitterProgramSemantics.nextPrefixResult_registers]
                exact stableTail.normalizedGateCount
              · rw [
                  TargetEmitterProgramSemantics.nextPrefixResult_registers]
                exact stableTail.carrierWidth
              · rw [
                  TargetEmitterProgramSemantics.nextPrefixResult_registers]
                exact stableTail.baseline
              · rw [
                  TargetEmitterProgramSemantics.nextPrefixResult_registers]
                exact stableTail.currentGate

private theorem checkCoordinates_length (raw : RawCircuit) :
    (checkCoordinates raw).length =
      3 * raw.normalize.gates.length := by
  exact
    TargetEmitterSemanticPrefix.macroAssembly_checkCoordinates_length
      raw.normalize

private theorem prefixRun_builder (raw : RawCircuit) :
    let macros := RawBuilder.macroAssembly raw.normalize
    let built :=
      RawBuilder.appendPrefix macros.gates macros.checks
    (prefixRun raw).output = built.output ∧
      (prefixRun raw).runtime.targetTokens =
        TargetEmitterSemanticSchedule.headerTokens raw ++
          encodeGateListTokens built.gates := by
  dsimp only
  have exactRun :=
    TargetEmitterSemanticPrefix.runPrefix_appends_builder
      (RawBuilder.macroAssembly raw.normalize).gates
      (checkCoordinates raw)
      (TargetEmitterSemanticSchedule.headerTokens raw)
      (TargetEmitterSemanticNormalization.normalizationRuntime raw)
      (TargetEmitterSemanticNormalization.normalizationRuntime_scratch raw)
      (by
        have registers :=
          TargetEmitterSemanticNormalization.normalizationRuntime_registers
            raw
        exact congrArg
          (fun value : TargetEmitter.UnaryRegisters =>
            value.outputIndex)
          registers)
      (TargetEmitterSemanticNormalization.normalizationRuntime_checks raw)
      (TargetEmitterSemanticNormalization.normalizationRuntime_targetTokens
        raw)
  have gateShape :
      TargetEmitterSemanticPrefix.gateChecks (checkCoordinates raw) =
        (RawBuilder.macroAssembly raw.normalize).checks := by
    simpa [checkCoordinates] using
      TargetEmitterSemanticPrefix.macroAssembly_gateChecks raw.normalize
  rw [gateShape] at exactRun
  simpa [prefixRun] using exactRun

private theorem checkCoordinates_nonempty_has_two
    (raw : RawCircuit)
    (nonempty : checkCoordinates raw ≠ []) :
    ∃ prior second newest,
      checkCoordinates raw = prior ++ [second, newest] := by
  have positive : 0 < raw.normalize.gates.length := by
    apply Nat.pos_of_ne_zero
    intro zero
    apply nonempty
    apply List.eq_nil_of_length_eq_zero
    rw [checkCoordinates_length, zero]
  have lengthAtLeastTwo : 2 ≤ (checkCoordinates raw).length := by
    rw [checkCoordinates_length]
    omega
  have reverseLength :
      2 ≤ (checkCoordinates raw).reverse.length := by
    simpa using lengthAtLeastTwo
  cases reversedEq : (checkCoordinates raw).reverse with
  | nil =>
      simp [reversedEq] at reverseLength
  | cons newest tail =>
      cases tail with
      | nil =>
          simp [reversedEq] at reverseLength
      | cons second priorReversed =>
          refine ⟨priorReversed.reverse, second, newest, ?_⟩
          have recovered :=
            congrArg List.reverse reversedEq
          simpa [List.reverse_reverse, List.reverse_cons,
            List.append_assoc] using recovered

private theorem prefixRun_positive_base
    (raw : RawCircuit)
    (nonempty : checkCoordinates raw ≠ []) :
    (prefixRun raw).runtime.registers.outputIndex + 1 =
      (RawBuilder.appendPrefix
        (RawBuilder.macroAssembly raw.normalize).gates
        (RawBuilder.macroAssembly raw.normalize).checks).gates.length := by
  let macros := RawBuilder.macroAssembly raw.normalize
  let runtime :=
    TargetEmitterSemanticNormalization.normalizationRuntime raw
  have correct :=
    TargetEmitterSemanticPrefix.runPrefix_correct
      macros.gates.length (checkCoordinates raw)
      (TargetEmitterSemanticSchedule.headerTokens raw ++
        encodeGateListTokens macros.gates)
      runtime
      (TargetEmitterSemanticNormalization.normalizationRuntime_scratch raw)
      (by
        have registers :=
          TargetEmitterSemanticNormalization.normalizationRuntime_registers
            raw
        exact congrArg
          (fun value : TargetEmitter.UnaryRegisters =>
            value.outputIndex)
          registers)
      (TargetEmitterSemanticNormalization.normalizationRuntime_checks raw)
      (TargetEmitterSemanticNormalization.normalizationRuntime_targetTokens
        raw)
  have gateShape :
      TargetEmitterSemanticPrefix.gateChecks (checkCoordinates raw) =
        macros.checks := by
    simpa [checkCoordinates, macros] using
      TargetEmitterSemanticPrefix.macroAssembly_gateChecks raw.normalize
  have outputIndexEq := correct.outputIndex
  rw [gateShape] at outputIndexEq
  have scheduledPositive :
      0 <
        (TargetEmitterSemanticPrefix.prefixSchedule macros.gates.length
          macros.checks).gates.length := by
    rw [TargetEmitterSemanticPrefix.prefixSchedule_gates_length]
    have lengthAtLeastTwo :
        2 ≤ (checkCoordinates raw).length := by
      rcases checkCoordinates_nonempty_has_two raw nonempty with
        ⟨prior, second, newest, equality⟩
      rw [equality, List.length_append]
      simp
    have checksLength :
        macros.checks.length = (checkCoordinates raw).length := by
      rw [← gateShape]
      simp [TargetEmitterSemanticPrefix.gateChecks]
    rw [checksLength]
    omega
  rw [show
    (prefixRun raw).runtime.registers.outputIndex =
      macros.gates.length +
        ((TargetEmitterSemanticPrefix.prefixSchedule
          macros.gates.length macros.checks).gates.length - 1) from
      outputIndexEq]
  rw [←
    TargetEmitterSemanticPrefix.prefixSchedule_gates_eq_appendPrefix
      macros.gates macros.checks]
  simp only [List.length_append]
  omega

private theorem prefixRun_positive_output
    (raw : RawCircuit)
    (nonempty : checkCoordinates raw ≠ []) :
    (RawBuilder.appendPrefix
      (RawBuilder.macroAssembly raw.normalize).gates
      (RawBuilder.macroAssembly raw.normalize).checks).output =
        .gate (prefixRun raw).runtime.registers.outputIndex := by
  let macros := RawBuilder.macroAssembly raw.normalize
  let runtime :=
    TargetEmitterSemanticNormalization.normalizationRuntime raw
  have correct :=
    TargetEmitterSemanticPrefix.runPrefix_correct
      macros.gates.length (checkCoordinates raw)
      (TargetEmitterSemanticSchedule.headerTokens raw ++
        encodeGateListTokens macros.gates)
      runtime
      (TargetEmitterSemanticNormalization.normalizationRuntime_scratch raw)
      (by
        have registers :=
          TargetEmitterSemanticNormalization.normalizationRuntime_registers
            raw
        exact congrArg
          (fun value : TargetEmitter.UnaryRegisters =>
            value.outputIndex)
          registers)
      (TargetEmitterSemanticNormalization.normalizationRuntime_checks raw)
      (TargetEmitterSemanticNormalization.normalizationRuntime_targetTokens
        raw)
  have gateShape :
      TargetEmitterSemanticPrefix.gateChecks (checkCoordinates raw) =
        macros.checks := by
    simpa [checkCoordinates, macros] using
      TargetEmitterSemanticPrefix.macroAssembly_gateChecks raw.normalize
  have scheduledNonempty :
      (TargetEmitterSemanticPrefix.prefixSchedule macros.gates.length
        macros.checks).gates ≠ [] := by
    intro empty
    have lengthAtLeastTwo :
        2 ≤ (checkCoordinates raw).length := by
      rcases checkCoordinates_nonempty_has_two raw nonempty with
        ⟨prior, second, newest, equality⟩
      rw [equality, List.length_append]
      simp
    have checksLength :
        macros.checks.length = (checkCoordinates raw).length := by
      rw [← gateShape]
      simp [TargetEmitterSemanticPrefix.gateChecks]
    have checkLengthAtLeastTwo : 2 ≤ macros.checks.length := by
      rw [checksLength]
      exact lengthAtLeastTwo
    have differencePositive :
        0 < macros.checks.length - 1 := by
      omega
    have scheduledPositive :
        0 <
          (TargetEmitterSemanticPrefix.prefixSchedule
            macros.gates.length macros.checks).gates.length := by
      rw [TargetEmitterSemanticPrefix.prefixSchedule_gates_length]
      omega
    rw [empty] at scheduledPositive
    simp at scheduledPositive
  have scheduledNonemptyGateChecks :
      (TargetEmitterSemanticPrefix.prefixSchedule macros.gates.length
        (TargetEmitterSemanticPrefix.gateChecks
          (checkCoordinates raw))).gates ≠ [] := by
    rw [gateShape]
    exact scheduledNonempty
  have resultGate :=
    correct.output_is_gate scheduledNonemptyGateChecks
  have builderOutput := (prefixRun_builder raw).1
  exact builderOutput.symm.trans resultGate

private theorem prefixRun_zero
    (raw : RawCircuit)
    (empty : checkCoordinates raw = []) :
    (prefixRun raw).runtime =
        TargetEmitterSemanticNormalization.normalizationRuntime raw ∧
      (RawBuilder.macroAssembly raw.normalize).gates = [] ∧
      (RawBuilder.appendPrefix
        (RawBuilder.macroAssembly raw.normalize).gates
        (RawBuilder.macroAssembly raw.normalize).checks) =
          { gates := [], output := .constant false } := by
  have normalizedEmpty :
      raw.normalize.gates = [] := by
    cases normalizedEq : raw.normalize.gates with
    | nil =>
        rfl
    | cons gate rest =>
        have lengths := congrArg List.length empty
        rw [checkCoordinates_length, normalizedEq] at lengths
        simp at lengths
  have macroGatesEmpty :
      (RawBuilder.macroAssembly raw.normalize).gates = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [RawBuilder.macroAssembly_gates_length]
    cases normalizedEq : raw.normalize.gates with
    | nil =>
        rfl
    | cons gate rest =>
        simp [normalizedEq] at normalizedEmpty
  have macroChecksEmpty :
      (RawBuilder.macroAssembly raw.normalize).checks = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [RawBuilder.macroAssembly_checks_length]
    rw [normalizedEmpty]
    rfl
  refine ⟨?_, macroGatesEmpty, ?_⟩
  · simp [prefixRun, empty,
      TargetEmitterSemanticPrefix.runPrefix]
  · simp [macroGatesEmpty, macroChecksEmpty,
      RawBuilder.appendPrefix]

private theorem outputTraceExpression_eq_rawGateTrace_of_empty
    (raw : RawCircuit)
    (empty : checkCoordinates raw = []) :
    outputTraceExpression raw = TargetEmitterPlan.rawGateTrace := by
  have normalizedEmpty :
      raw.normalize.gates = [] := by
    cases normalizedEq : raw.normalize.gates with
    | nil =>
        rfl
    | cons gate rest =>
        have lengths := congrArg List.length empty
        rw [checkCoordinates_length, normalizedEq] at lengths
        simp at lengths
  cases raw with
  | mk inputs gates output =>
      cases output with
      | gate index =>
          rfl
      | input index =>
          simp [RawCircuit.normalize] at normalizedEmpty
      | constant value =>
          cases value <;>
            simp [RawCircuit.normalize] at normalizedEmpty

private theorem prefixRun_finalLock
    (raw : RawCircuit) :
    TargetEmitterPlan.finalLock.evaluate
        (prefixRun raw).runtime.registers
        (prefixRun raw).runtime.captured 0 =
      RawBuilder.finalLockCoordinate
        raw.normalize.inputCount raw.normalize.gates.length := by
  have stable :=
    runPrefix_stable (checkCoordinates raw)
      (TargetEmitterSemanticNormalization.normalizationRuntime raw)
  have registers :=
    TargetEmitterSemanticNormalization.normalizationRuntime_registers raw
  have inputCount :
      (prefixRun raw).runtime.registers.inputCount =
        (TargetEmitterSemanticNormalization.normalizationRuntime
          raw).registers.inputCount := by
    simpa [prefixRun] using stable.inputCount
  have normalizedGateCount :
      (prefixRun raw).runtime.registers.normalizedGateCount =
        (TargetEmitterSemanticNormalization.normalizationRuntime
          raw).registers.normalizedGateCount := by
    simpa [prefixRun] using stable.normalizedGateCount
  rw [TargetEmitterPlan.finalLock_evaluated]
  rw [inputCount, normalizedGateCount]
  rw [show
    (TargetEmitterSemanticNormalization.normalizationRuntime raw).registers =
      { TargetEmitterLedger.ledgerRegisters raw with
        currentGate :=
          TargetEmitterSemanticNormalization.normalizationCurrentGate raw
        outputIndex :=
          (RawBuilder.macroAssembly raw.normalize).gates.length } from
      registers]
  cases raw with
  | mk inputs gates output =>
      cases output with
      | gate index =>
          simp [TargetEmitterLedger.ledgerRegisters,
            TargetEmitterLedger.normalizedGateCount_eq_normalize,
            RawBuilder.finalLockCoordinate, RawCircuit.normalize]
      | input index =>
          simp [TargetEmitterLedger.ledgerRegisters,
            TargetEmitterLedger.normalizedGateCount_eq_normalize,
            RawBuilder.finalLockCoordinate, RawCircuit.normalize]
      | constant value =>
          cases value <;>
            simp [TargetEmitterLedger.ledgerRegisters,
              TargetEmitterLedger.normalizedGateCount_eq_normalize,
              RawBuilder.finalLockCoordinate, RawCircuit.normalize]

private theorem normalizationRuntime_captured
    (raw : RawCircuit) :
    (TargetEmitterSemanticNormalization.normalizationRuntime raw).captured =
      TargetEmitterSemanticSchedule.capturedValue raw.output := by
  cases raw with
  | mk inputs gates output =>
      cases output with
      | gate index =>
          rfl
      | input index =>
          rfl
      | constant value =>
          cases value <;> rfl

private theorem prefixRun_outputTrace
    (raw : RawCircuit) :
    (outputTraceExpression raw).evaluate
        (prefixRun raw).runtime.registers
        (prefixRun raw).runtime.captured 0 =
      RawBuilder.traceCoordinate
        raw.normalize.inputCount raw.normalize.gates.length
        (RawBuilder.outputGateIndex raw.normalize.output) := by
  have stable :=
    runPrefix_stable (checkCoordinates raw)
      (TargetEmitterSemanticNormalization.normalizationRuntime raw)
  have registers :=
    TargetEmitterSemanticNormalization.normalizationRuntime_registers raw
  have captured :
      (prefixRun raw).runtime.captured =
        TargetEmitterSemanticSchedule.capturedValue raw.output := by
    calc
      (prefixRun raw).runtime.captured =
          (TargetEmitterSemanticNormalization.normalizationRuntime
            raw).captured := by
        simpa [prefixRun] using stable.captured
      _ = TargetEmitterSemanticSchedule.capturedValue raw.output :=
        normalizationRuntime_captured raw
  have inputCount :
      (prefixRun raw).runtime.registers.inputCount =
        raw.normalize.inputCount := by
    calc
      (prefixRun raw).runtime.registers.inputCount =
          (TargetEmitterSemanticNormalization.normalizationRuntime
            raw).registers.inputCount := by
        simpa [prefixRun] using stable.inputCount
      _ = raw.normalize.inputCount := by
        have projected := congrArg
          (fun value : TargetEmitter.UnaryRegisters =>
            value.inputCount)
          registers
        cases raw with
        | mk inputs gates output =>
            cases output with
            | gate index =>
                simpa [TargetEmitterLedger.ledgerRegisters,
                  RawCircuit.normalize] using projected
            | input index =>
                simpa [TargetEmitterLedger.ledgerRegisters,
                  RawCircuit.normalize] using projected
            | constant value =>
                cases value <;>
                  simpa [TargetEmitterLedger.ledgerRegisters,
                    RawCircuit.normalize] using projected
  have currentGate :
      (prefixRun raw).runtime.registers.currentGate =
        TargetEmitterSemanticNormalization.normalizationCurrentGate raw := by
    calc
      (prefixRun raw).runtime.registers.currentGate =
          (TargetEmitterSemanticNormalization.normalizationRuntime
            raw).registers.currentGate := by
        simpa [prefixRun] using stable.currentGate
      _ =
          TargetEmitterSemanticNormalization.normalizationCurrentGate raw := by
        exact congrArg
          (fun value : TargetEmitter.UnaryRegisters =>
            value.currentGate)
          registers
  cases raw with
  | mk inputs gates output =>
      cases output with
      | gate index =>
          simp [outputTraceExpression,
            TargetEmitterPlan.rawGateTrace_evaluated,
            captured, inputCount,
            TargetEmitterSemanticSchedule.capturedValue,
            RawCircuit.normalize, RawBuilder.traceCoordinate,
            RawBuilder.outputGateIndex]
      | input index =>
          simp [outputTraceExpression,
            TargetEmitterPlan.traceCoordinate_evaluated,
            inputCount, currentGate,
            TargetEmitterSemanticNormalization.normalizationCurrentGate,
            RawCircuit.normalize, RawBuilder.traceCoordinate,
            RawBuilder.outputGateIndex]
      | constant value =>
          cases value <;>
            simp [outputTraceExpression,
              TargetEmitterPlan.traceCoordinate_evaluated,
              inputCount, currentGate,
              TargetEmitterSemanticNormalization.normalizationCurrentGate,
              RawCircuit.normalize, RawBuilder.traceCoordinate,
              RawBuilder.outputGateIndex]

private theorem finalRuntime_targetTokens (raw : RawCircuit) :
    (finalRuntime raw).targetTokens =
      TargetEmitterSemanticSchedule.canonicalHeaderTokens raw ++
        encodeGateListTokens
          (RawBuilder.rawLockedInstance raw).candidate.gates := by
  by_cases empty : checkCoordinates raw = []
  · rw [finalRuntime, if_pos empty]
    rcases prefixRun_zero raw empty with
      ⟨runtimeEq, macroGatesEmpty, builtEq⟩
    have builder := prefixRun_builder raw
    have tokenPrefix :
        (prefixRun raw).runtime.targetTokens =
          TargetEmitterSemanticSchedule.headerTokens raw := by
      rw [builder.2, builtEq]
      simp [encodeGateListTokens]
    have finalTokens :=
      TargetEmitterSemanticFinal.finalZeroResult_targetTokens
        (prefixRun raw).runtime []
        (RawBuilder.finalLockCoordinate
          raw.normalize.inputCount raw.normalize.gates.length)
        (RawBuilder.traceCoordinate
          raw.normalize.inputCount raw.normalize.gates.length
          (RawBuilder.outputGateIndex raw.normalize.output))
        (TargetEmitterSemanticSchedule.headerTokens raw)
        (by simpa [encodeGateListTokens] using tokenPrefix)
        (by
          rw [runtimeEq]
          have registers :=
            TargetEmitterSemanticNormalization.normalizationRuntime_registers
              raw
          rw [registers, macroGatesEmpty])
        (prefixRun_finalLock raw)
        (by
          rw [←
            outputTraceExpression_eq_rawGateTrace_of_empty raw empty]
          exact prefixRun_outputTrace raw)
    rw [TargetEmitterSemanticSchedule.headerTokens_eq_canonicalHeaderTokens]
      at finalTokens
    simpa [RawBuilder.rawLockedInstance, builtEq] using finalTokens
  · rw [finalRuntime, if_neg empty]
    let macros := RawBuilder.macroAssembly raw.normalize
    let built :=
      RawBuilder.appendPrefix macros.gates macros.checks
    have builder := prefixRun_builder raw
    have finalTokens :=
      TargetEmitterSemanticFinal.finalPositiveResult_targetTokens
        (prefixRun raw).runtime built.gates built.output
        (outputTraceExpression raw)
        (RawBuilder.finalLockCoordinate
          raw.normalize.inputCount raw.normalize.gates.length)
        (RawBuilder.traceCoordinate
          raw.normalize.inputCount raw.normalize.gates.length
          (RawBuilder.outputGateIndex raw.normalize.output))
        (TargetEmitterSemanticSchedule.headerTokens raw)
        builder.2
        (prefixRun_positive_base raw empty)
        (prefixRun_positive_output raw empty)
        (prefixRun_finalLock raw)
        (prefixRun_outputTrace raw)
    rw [TargetEmitterSemanticSchedule.headerTokens_eq_canonicalHeaderTokens]
      at finalTokens
    simpa [RawBuilder.rawLockedInstance, macros, built] using finalTokens

private theorem finalRuntime_registers (raw : RawCircuit) :
    (finalRuntime raw).registers = (prefixRun raw).runtime.registers := by
  by_cases empty : checkCoordinates raw = []
  · rw [finalRuntime, if_pos empty,
      TargetEmitterProgramSemantics.finalResult_registers]
  · rw [finalRuntime, if_neg empty,
      TargetEmitterProgramSemantics.finalResult_registers]

/-- The complete pure controller schedule emits the independent raw builder's
canonical token word for every decoded raw circuit, including raw circuits
that fail later semantic elaboration. -/
theorem completeRuntime_targetTokens (raw : RawCircuit) :
    (completeRuntime raw).targetTokens =
      encodeLockedInstanceTokens
        (RawBuilder.rawLockedInstance raw) := by
  apply
    TargetEmitterSemanticOutput.completeOutputResult_eq_rawLockedInstanceTokens
      raw (finalRuntime raw)
  · exact finalRuntime_targetTokens raw
  · rw [finalRuntime_registers]
    have stable :=
      runPrefix_stable (checkCoordinates raw)
        (TargetEmitterSemanticNormalization.normalizationRuntime raw)
    have baseline :
        (prefixRun raw).runtime.registers.baseline =
          (TargetEmitterSemanticNormalization.normalizationRuntime
            raw).registers.baseline := by
      simpa [prefixRun] using stable.baseline
    rw [baseline]
    have registers :=
      TargetEmitterSemanticNormalization.normalizationRuntime_registers raw
    rw [registers]
    exact TargetEmitterLedger.ledgerRegisters_baseline raw

/-- The final gate-list/header word is a literal prefix of the complete
serialized target; the output phase only appends framing, outputs, threshold,
and the instance terminator. -/
theorem finalRuntime_targetTokens_prefix
    (raw : RawCircuit) :
    ∃ suffix,
      (completeRuntime raw).targetTokens =
        (finalRuntime raw).targetTokens ++ suffix := by
  let rawInstance := RawBuilder.rawLockedInstance raw
  let suffix : List Token :=
    [.programEnd] ++
      encodeSourceListTokens rawInstance.candidate.outputs ++
      [.outputsEnd, .threshold] ++
      encodeNatTokens rawInstance.baseline ++
      [.instanceEnd]
  refine ⟨suffix, ?_⟩
  rw [completeRuntime_targetTokens, finalRuntime_targetTokens]
  simp [encodeLockedInstanceTokens,
    TargetEmitterSemanticSchedule.canonicalHeaderTokens,
    rawInstance, suffix, List.append_assoc]

/-- The right-folded prefix consumes the entire logical check stack, and the
selected final block preserves that empty stack. -/
theorem finalRuntime_checks_empty (raw : RawCircuit) :
    (finalRuntime raw).checks = [] := by
  let runtime :=
    TargetEmitterSemanticNormalization.normalizationRuntime raw
  have correct :=
    TargetEmitterSemanticPrefix.runPrefix_correct
      runtime.registers.outputIndex (checkCoordinates raw)
      runtime.targetTokens runtime
      (by
        simpa [runtime] using
          TargetEmitterSemanticNormalization.normalizationRuntime_scratch raw)
      rfl
      (by
        simpa [runtime, checkCoordinates] using
          TargetEmitterSemanticNormalization.normalizationRuntime_checks raw)
      rfl
  have prefixChecks :
      (prefixRun raw).runtime.checks = [] := by
    simpa [prefixRun, runtime] using correct.checks
  by_cases empty : checkCoordinates raw = []
  · rw [finalRuntime, if_pos empty,
      TargetEmitterProgramSemantics.finalResult_checks]
    exact prefixChecks
  · rw [finalRuntime, if_neg empty,
      TargetEmitterProgramSemantics.finalResult_checks]
    exact prefixChecks

end PNP.Concrete.LockedNAND.TargetEmitterSemanticCompletion
