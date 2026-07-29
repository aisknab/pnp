/-
Copyright (c) 2026 PNP Labs.

Capacity invariants for the fixed grammar-only locked-NAND target emitter.

The executable controller uses one source-derived capacity:

  64 * encoded source cells + 64.

This file proves, from the literal source encoding, that the capacity has a
strict reserve for every coordinate family used by the closed emitter plan.
The dynamic part of the argument is deliberately small: `ControllerRange`
records only the two registers changed by the controller.  All other register
values are pinned to the audited source ledger.
-/

import PNP.Concrete.LockedNANDTargetEmitterRuntimeProgram

namespace PNP.Concrete.LockedNAND.TargetEmitterCapacity

open PNP.Concrete

/-! ### Source-derived arithmetic -/

private theorem sourceMacroWeight_le_ten
    (source : RawSource) :
    TargetEmitterLedger.sourceMacroWeight source ≤ 10 := by
  cases source with
  | input index =>
      simp [TargetEmitterLedger.sourceMacroWeight]
  | gate index =>
      simp [TargetEmitterLedger.sourceMacroWeight]
  | constant value =>
      cases value <;>
        simp [TargetEmitterLedger.sourceMacroWeight]

private theorem gateMacroWeight_le_thirtyEight
    (gate : RawGate) :
    TargetEmitterLedger.gateMacroWeight gate ≤ 38 := by
  cases gate with
  | mk left right =>
      have leftBound := sourceMacroWeight_le_ten left
      have rightBound := sourceMacroWeight_le_ten right
      simp only [TargetEmitterLedger.gateMacroWeight]
      omega

private theorem gateListMacroWeight_le
    (gates : List RawGate) :
    TargetEmitterLedger.gateListMacroWeight gates ≤
      38 * gates.length := by
  induction gates with
  | nil =>
      exact Nat.le_refl _
  | cons gate rest inductionHypothesis =>
      have gateBound := gateMacroWeight_le_thirtyEight gate
      simp only [TargetEmitterLedger.gateListMacroWeight,
        List.length_cons]
      omega

private theorem normalizationAddedGates_le_two
    (source : RawSource) :
    TargetEmitterLedger.normalizationAddedGates source ≤ 2 := by
  cases source with
  | input index =>
      simp [TargetEmitterLedger.normalizationAddedGates]
  | gate index =>
      simp [TargetEmitterLedger.normalizationAddedGates]
  | constant value =>
      cases value <;>
        simp [TargetEmitterLedger.normalizationAddedGates]

private theorem normalizationMacroWeight_le_sixtyEight
    (source : RawSource) :
    TargetEmitterLedger.normalizationMacroWeight source ≤ 68 := by
  cases source with
  | input index =>
      simp [TargetEmitterLedger.normalizationMacroWeight]
  | gate index =>
      simp [TargetEmitterLedger.normalizationMacroWeight]
  | constant value =>
      cases value <;>
        simp [TargetEmitterLedger.normalizationMacroWeight]

private theorem sourceCells_length_ge_two
    (source : RawSource) :
    2 ≤ (SourceParser.sourceCells source).length := by
  cases source with
  | input index =>
      simp [SourceParser.sourceCells, SourceParser.natCells_length]
  | gate index =>
      simp [SourceParser.sourceCells, SourceParser.natCells_length]
  | constant value =>
      cases value <;> decide

/-- Even the empty-gate circuit has fourteen packed cells. -/
theorem fourteen_le_circuitCells_length
    (raw : RawCircuit) :
    14 ≤ (SourceParser.circuitCells raw).length := by
  cases raw with
  | mk inputs gates output =>
      have outputLength := sourceCells_length_ge_two output
      simp [SourceParser.circuitCells, SourceParser.natCells_length]
      omega

/-- The unary input-count field is no longer than the complete source. -/
theorem inputCount_le_circuitCells_length
    (raw : RawCircuit) :
    raw.inputCount ≤ (SourceParser.circuitCells raw).length := by
  cases raw with
  | mk inputs gates output =>
      simp [SourceParser.circuitCells, SourceParser.natCells_length]
      omega

/-- The unary gate-count field is no longer than the complete source. -/
theorem gateCount_le_circuitCells_length
    (raw : RawCircuit) :
    raw.gates.length ≤
      (SourceParser.circuitCells raw).length := by
  cases raw with
  | mk inputs gates output =>
      simp [SourceParser.circuitCells, SourceParser.natCells_length]
      omega

/-- Normalization appends at most two gates. -/
theorem normalizedGateCount_le_cells_add_two
    (raw : RawCircuit) :
    TargetEmitterLedger.normalizedGateCount raw ≤
      (SourceParser.circuitCells raw).length + 2 := by
  have gates := gateCount_le_circuitCells_length raw
  have added := normalizationAddedGates_le_two raw.output
  simp only [TargetEmitterLedger.normalizedGateCount]
  omega

/-- The baseline leaves sixty-four unary cells free.  This is the central
reserve used by all template-local and output-fold bounds below. -/
theorem baseline_add_sixtyFour_le_slotCapacity
    (raw : RawCircuit) :
    TargetEmitterLedger.baselineValue raw + 64 ≤
      TargetEmitterLedger.slotCapacity raw := by
  have gateWeights := gateListMacroWeight_le raw.gates
  have normalizationWeight :=
    normalizationMacroWeight_le_sixtyEight raw.output
  have gates := gateCount_le_circuitCells_length raw
  have normalized := normalizedGateCount_le_cells_add_two raw
  have cells := fourteen_le_circuitCells_length raw
  have subtraction :
      3 * TargetEmitterLedger.normalizedGateCount raw - 1 ≤
        3 * TargetEmitterLedger.normalizedGateCount raw :=
    Nat.sub_le _ _
  simp only [TargetEmitterLedger.baselineValue,
    TargetEmitterLedger.slotCapacity]
  omega

/-- The baseline also leaves room for one complete source-carried natural.
This is stronger than a fixed additive reserve when a source index is large. -/
theorem baseline_add_cells_add_two_le_slotCapacity
    (raw : RawCircuit) :
    TargetEmitterLedger.baselineValue raw +
          (SourceParser.circuitCells raw).length + 2 ≤
      TargetEmitterLedger.slotCapacity raw := by
  have gateWeights := gateListMacroWeight_le raw.gates
  have normalizationWeight :=
    normalizationMacroWeight_le_sixtyEight raw.output
  have gates := gateCount_le_circuitCells_length raw
  have normalized := normalizedGateCount_le_cells_add_two raw
  have cells := fourteen_le_circuitCells_length raw
  have subtraction :
      3 * TargetEmitterLedger.normalizedGateCount raw - 1 ≤
        3 * TargetEmitterLedger.normalizedGateCount raw :=
    Nat.sub_le _ _
  simp only [TargetEmitterLedger.baselineValue,
    TargetEmitterLedger.slotCapacity]
  omega

/-- One envelope covers the header values and all source/trace coordinates. -/
theorem coordinateEnvelope_lt_slotCapacity
    (raw : RawCircuit) :
    raw.inputCount +
          7 * TargetEmitterLedger.normalizedGateCount raw + 4 <
      TargetEmitterLedger.slotCapacity raw := by
  have inputs := inputCount_le_circuitCells_length raw
  have normalized := normalizedGateCount_le_cells_add_two raw
  simp only [TargetEmitterLedger.slotCapacity]
  omega

theorem baseline_add_four_lt_slotCapacity
    (raw : RawCircuit) :
    TargetEmitterLedger.baselineValue raw + 4 <
      TargetEmitterLedger.slotCapacity raw := by
  have reserve := baseline_add_sixtyFour_le_slotCapacity raw
  omega

theorem baseline_add_one_lt_slotCapacity
    (raw : RawCircuit) :
    TargetEmitterLedger.baselineValue raw + 1 <
      TargetEmitterLedger.slotCapacity raw := by
  have reserve := baseline_add_sixtyFour_le_slotCapacity raw
  omega

/-! ### Every captured source index is physically represented -/

/-- Unary natural carried by a source tag.  Constants carry zero. -/
def sourceCaptureValue : RawSource → Nat
  | .input index => index
  | .constant _ => 0
  | .gate index => index

/-- Sources that the controller can focus in the canonical circuit word. -/
inductive CircuitSource (raw : RawCircuit) : RawSource → Prop where
  | output :
      CircuitSource raw raw.output
  | gateLeft
      {gate : RawGate}
      (member : gate ∈ raw.gates) :
      CircuitSource raw gate.left
  | gateRight
      {gate : RawGate}
      (member : gate ∈ raw.gates) :
      CircuitSource raw gate.right

theorem sourceCaptureValue_succ_le_sourceCells_length
    (source : RawSource) :
    sourceCaptureValue source + 1 ≤
      (SourceParser.sourceCells source).length := by
  cases source with
  | input index =>
      simp [sourceCaptureValue, SourceParser.sourceCells,
        SourceParser.natCells_length]
      omega
  | gate index =>
      simp [sourceCaptureValue, SourceParser.sourceCells,
        SourceParser.natCells_length]
      omega
  | constant value =>
      cases value <;>
        simp [sourceCaptureValue, SourceParser.sourceCells]

private theorem leftSourceCells_length_le_gateListCells
    {gate : RawGate} {gates : List RawGate}
    (member : gate ∈ gates) :
    (SourceParser.sourceCells gate.left).length ≤
      (SourceParser.gateListCells gates).length := by
  induction gates with
  | nil =>
      simp at member
  | cons head rest inductionHypothesis =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · simp only [SourceParser.gateListCells,
          SourceParser.gateCells, List.length_append,
          List.length_cons, List.length_nil]
        omega
      · have tailBound := inductionHypothesis member
        simp only [SourceParser.gateListCells, List.length_append]
        omega

private theorem rightSourceCells_length_le_gateListCells
    {gate : RawGate} {gates : List RawGate}
    (member : gate ∈ gates) :
    (SourceParser.sourceCells gate.right).length ≤
      (SourceParser.gateListCells gates).length := by
  induction gates with
  | nil =>
      simp at member
  | cons head rest inductionHypothesis =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · simp only [SourceParser.gateListCells,
          SourceParser.gateCells, List.length_append,
          List.length_cons, List.length_nil]
        omega
      · have tailBound := inductionHypothesis member
        simp only [SourceParser.gateListCells, List.length_append]
        omega

theorem CircuitSource.sourceCells_length_le_circuitCells_length
    {raw : RawCircuit} {source : RawSource}
    (member : CircuitSource raw source) :
    (SourceParser.sourceCells source).length ≤
      (SourceParser.circuitCells raw).length := by
  cases member with
  | output =>
      simp only [SourceParser.circuitCells, List.length_append,
        List.length_cons, List.length_nil]
      omega
  | gateLeft gateMember =>
      have sourceBound :=
        leftSourceCells_length_le_gateListCells gateMember
      simp only [SourceParser.circuitCells, List.length_append,
        List.length_cons, List.length_nil]
      omega
  | gateRight gateMember =>
      have sourceBound :=
        rightSourceCells_length_le_gateListCells gateMember
      simp only [SourceParser.circuitCells, List.length_append,
        List.length_cons, List.length_nil]
      omega

theorem circuitSourceCaptureValue_succ_le_cells
    {raw : RawCircuit} {source : RawSource}
    (member : CircuitSource raw source) :
    sourceCaptureValue source + 1 ≤
      (SourceParser.circuitCells raw).length := by
  exact Nat.le_trans
    (sourceCaptureValue_succ_le_sourceCells_length source)
    member.sourceCells_length_le_circuitCells_length

theorem circuitInputIndex_succ_le_cells
    {raw : RawCircuit} {index : Nat}
    (member : CircuitSource raw (.input index)) :
    index + 1 ≤ (SourceParser.circuitCells raw).length := by
  simpa [sourceCaptureValue] using
    circuitSourceCaptureValue_succ_le_cells member

theorem circuitGateIndex_succ_le_cells
    {raw : RawCircuit} {index : Nat}
    (member : CircuitSource raw (.gate index)) :
    index + 1 ≤ (SourceParser.circuitCells raw).length := by
  simpa [sourceCaptureValue] using
    circuitSourceCaptureValue_succ_le_cells member

/-- A zero-scratch focused capture has the extra literal blank required by
the source-capture machine. -/
theorem focusedSourceCaptureReserve
    {raw : RawCircuit} {source : RawSource}
    (member : CircuitSource raw source) :
    0 + sourceCaptureValue source + 1 ≤
      TargetEmitterLedger.slotCapacity raw := by
  have captured := circuitSourceCaptureValue_succ_le_cells member
  simp only [TargetEmitterLedger.slotCapacity]
  omega

/-- The first capture follows the header, whose final natural leaves
`baseline + 1` in scratch.  The source-derived capacity reserves that scratch,
the largest possible captured source natural, and the required trailing
blank simultaneously. -/
theorem headerFocusedSourceCaptureReserve
    {raw : RawCircuit} {source : RawSource}
    (member : CircuitSource raw source) :
    TargetEmitterLedger.baselineValue raw + 1 +
          sourceCaptureValue source + 1 ≤
      TargetEmitterLedger.slotCapacity raw := by
  have captured := circuitSourceCaptureValue_succ_le_cells member
  have reserve := baseline_add_cells_add_two_le_slotCapacity raw
  omega

theorem focusedSourceCaptureReserve_of_equal
    {raw : RawCircuit} {source : RawSource}
    {scratch captured : Nat}
    (member : CircuitSource raw source)
    (scratchZero : scratch = 0)
    (capturedEq : captured = sourceCaptureValue source) :
    scratch + captured + 1 ≤
      TargetEmitterLedger.slotCapacity raw := by
  subst scratch
  subst captured
  exact focusedSourceCaptureReserve member

theorem headerFocusedSourceCaptureReserve_of_equal
    {raw : RawCircuit} {source : RawSource}
    {scratch captured : Nat}
    (member : CircuitSource raw source)
    (scratchEq :
      scratch = TargetEmitterLedger.baselineValue raw + 1)
    (capturedEq : captured = sourceCaptureValue source) :
    scratch + captured + 1 ≤
      TargetEmitterLedger.slotCapacity raw := by
  subst scratch
  subst captured
  exact headerFocusedSourceCaptureReserve member

/-! ### Dynamic controller-register invariant -/

/-- The four immutable ledger fields remain source-derived; the controller
advances only within the normalized-gate and emitted-baseline ranges. -/
structure ControllerRange
    (raw : RawCircuit)
    (registers : TargetEmitter.UnaryRegisters) : Prop where
  inputCount_eq :
    registers.inputCount = raw.inputCount
  normalizedGateCount_eq :
    registers.normalizedGateCount =
      TargetEmitterLedger.normalizedGateCount raw
  carrierWidth_eq :
    registers.carrierWidth =
      TargetEmitterLedger.carrierWidthValue raw
  baseline_eq :
    registers.baseline =
      TargetEmitterLedger.baselineValue raw
  currentGate_le :
    registers.currentGate ≤
      TargetEmitterLedger.normalizedGateCount raw
  outputIndex_le :
    registers.outputIndex ≤
      TargetEmitterLedger.baselineValue raw + 4

theorem initialControllerRange
    (raw : RawCircuit) :
    ControllerRange raw
      (TargetEmitterLedger.ledgerRegisters raw) := by
  refine
    { inputCount_eq := rfl
      normalizedGateCount_eq := rfl
      carrierWidth_eq := rfl
      baseline_eq := rfl
      currentGate_le := ?_
      outputIndex_le := ?_ }
  · simp [TargetEmitterLedger.ledgerRegisters]
  · simp [TargetEmitterLedger.ledgerRegisters]

/-- Initial compatibility with the stable runtime-program interface. -/
theorem initialLedgerFits
    (raw : RawCircuit) :
    TargetEmitterRuntimeProgram.LedgerFits
      (TargetEmitterLedger.slotCapacity raw)
      (TargetEmitterLedger.ledgerRegisters raw) := by
  exact
    { inputCount :=
        TargetEmitterLedger.inputCount_le_slotCapacity raw
      normalizedGateCount :=
        TargetEmitterLedger.normalizedGateCount_le_slotCapacity raw
      carrierWidth :=
        TargetEmitterLedger.carrierWidthValue_le_slotCapacity raw
      baseline :=
        TargetEmitterLedger.baselineValue_le_slotCapacity raw
      currentGate := by
        simp [TargetEmitterLedger.ledgerRegisters,
          TargetEmitterLedger.slotCapacity]
      outputIndex := by
        simp [TargetEmitterLedger.ledgerRegisters,
          TargetEmitterLedger.slotCapacity] }

theorem ControllerRange.ledgerFits
    {raw : RawCircuit}
    {registers : TargetEmitter.UnaryRegisters}
    (range : ControllerRange raw registers) :
    TargetEmitterRuntimeProgram.LedgerFits
      (TargetEmitterLedger.slotCapacity raw) registers := by
  have baselineReserve :=
    baseline_add_sixtyFour_le_slotCapacity raw
  have normalizedBound :=
    TargetEmitterLedger.normalizedGateCount_le_slotCapacity raw
  refine
    { inputCount := ?_
      normalizedGateCount := ?_
      carrierWidth := ?_
      baseline := ?_
      currentGate := ?_
      outputIndex := ?_ }
  · rw [range.inputCount_eq]
    exact TargetEmitterLedger.inputCount_le_slotCapacity raw
  · rw [range.normalizedGateCount_eq]
    exact normalizedBound
  · rw [range.carrierWidth_eq]
    exact
      TargetEmitterLedger.carrierWidthValue_le_slotCapacity raw
  · rw [range.baseline_eq]
    exact TargetEmitterLedger.baselineValue_le_slotCapacity raw
  · exact Nat.le_trans range.currentGate_le normalizedBound
  · exact Nat.le_trans range.outputIndex_le (by omega)

theorem ControllerRange.currentGate_lt_slotCapacity
    {raw : RawCircuit}
    {registers : TargetEmitter.UnaryRegisters}
    (range : ControllerRange raw registers) :
    registers.currentGate <
      TargetEmitterLedger.slotCapacity raw := by
  have envelope := coordinateEnvelope_lt_slotCapacity raw
  exact Nat.lt_of_le_of_lt
    (Nat.le_trans range.currentGate_le (by omega)) envelope

theorem ControllerRange.outputIndex_add_eighteen_lt_slotCapacity
    {raw : RawCircuit}
    {registers : TargetEmitter.UnaryRegisters}
    (range : ControllerRange raw registers) :
    registers.outputIndex + 18 <
      TargetEmitterLedger.slotCapacity raw := by
  have reserve := baseline_add_sixtyFour_le_slotCapacity raw
  have outputRange := range.outputIndex_le
  have outputBound :
      registers.outputIndex + 18 ≤
        TargetEmitterLedger.baselineValue raw + 22 := by
    omega
  have strict :
      TargetEmitterLedger.baselineValue raw + 22 <
        TargetEmitterLedger.baselineValue raw + 64 := by
    omega
  exact Nat.lt_of_le_of_lt outputBound
    (Nat.lt_of_lt_of_le strict reserve)

theorem ControllerRange.incrementCurrentGate
    {raw : RawCircuit}
    {registers : TargetEmitter.UnaryRegisters}
    (range : ControllerRange raw registers)
    (next :
      registers.currentGate + 1 ≤
        TargetEmitterLedger.normalizedGateCount raw) :
    ControllerRange raw
      (TargetEmitterRuntimePrimitives.incrementRegisters
        .currentGate registers) := by
  cases registers
  simp only [TargetEmitterRuntimePrimitives.incrementRegisters] at *
  exact
    { inputCount_eq := range.inputCount_eq
      normalizedGateCount_eq := range.normalizedGateCount_eq
      carrierWidth_eq := range.carrierWidth_eq
      baseline_eq := range.baseline_eq
      currentGate_le := next
      outputIndex_le := range.outputIndex_le }

theorem ControllerRange.incrementOutputIndex
    {raw : RawCircuit}
    {registers : TargetEmitter.UnaryRegisters}
    (range : ControllerRange raw registers)
    (next :
      registers.outputIndex + 1 ≤
        TargetEmitterLedger.baselineValue raw + 4) :
    ControllerRange raw
      (TargetEmitterRuntimePrimitives.incrementRegisters
        .outputIndex registers) := by
  cases registers
  simp only [TargetEmitterRuntimePrimitives.incrementRegisters] at *
  exact
    { inputCount_eq := range.inputCount_eq
      normalizedGateCount_eq := range.normalizedGateCount_eq
      carrierWidth_eq := range.carrierWidth_eq
      baseline_eq := range.baseline_eq
      currentGate_le := range.currentGate_le
      outputIndex_le := next }

/-! ### Closed-plan coordinates -/

/-- Bounds for every named `NatExpression` used by the concrete controller.
The only parameter bounds are the literal choices made by the closed plan:
source sides and synthetic biases are zero or one, and block-local offsets
are at most eighteen. -/
structure PlanBounds
    (raw : RawCircuit)
    (registers : TargetEmitter.UnaryRegisters)
    (captured scratch : Nat) : Prop where
  inputCount :
    TargetEmitterPlan.inputCount.evaluate registers captured scratch <
      TargetEmitterLedger.slotCapacity raw
  normalizedGateCount :
    TargetEmitterPlan.normalizedGateCount.evaluate registers captured scratch <
      TargetEmitterLedger.slotCapacity raw
  carrierWidth :
    TargetEmitterPlan.carrierWidth.evaluate registers captured scratch <
      TargetEmitterLedger.slotCapacity raw
  baseline :
    TargetEmitterPlan.baseline.evaluate registers captured scratch <
      TargetEmitterLedger.slotCapacity raw
  currentGate :
    TargetEmitterPlan.currentGate.evaluate registers captured scratch <
      TargetEmitterLedger.slotCapacity raw
  outputIndex :
    TargetEmitterPlan.outputIndex.evaluate registers captured scratch <
      TargetEmitterLedger.slotCapacity raw
  capturedIndex :
    TargetEmitterPlan.capturedIndex.evaluate registers captured scratch <
      TargetEmitterLedger.slotCapacity raw
  poppedCheck :
    TargetEmitterPlan.poppedCheck.evaluate registers captured scratch <
      TargetEmitterLedger.slotCapacity raw
  sourceLock :
    ∀ side, side ≤ 1 →
      (TargetEmitterPlan.sourceLock side).evaluate registers captured scratch <
        TargetEmitterLedger.slotCapacity raw
  occurrence :
    ∀ side, side ≤ 1 →
      (TargetEmitterPlan.occurrence side).evaluate registers captured scratch <
        TargetEmitterLedger.slotCapacity raw
  traceLock :
    TargetEmitterPlan.traceLock.evaluate registers captured scratch <
      TargetEmitterLedger.slotCapacity raw
  traceCoordinate :
    TargetEmitterPlan.traceCoordinate.evaluate registers captured scratch <
      TargetEmitterLedger.slotCapacity raw
  rawGateTrace :
    TargetEmitterPlan.rawGateTrace.evaluate registers captured scratch <
      TargetEmitterLedger.slotCapacity raw
  finalLock :
    TargetEmitterPlan.finalLock.evaluate registers captured scratch <
      TargetEmitterLedger.slotCapacity raw
  localGate :
    ∀ offset, offset ≤ 18 →
      (TargetEmitterPlan.localGate offset).evaluate registers captured scratch <
        TargetEmitterLedger.slotCapacity raw
  checkAt :
    ∀ relative, relative ≤ 18 →
      (TargetEmitterPlan.checkAt relative).evaluate registers captured scratch <
        TargetEmitterLedger.slotCapacity raw
  currentGateAt :
    ∀ bias, bias ≤ 1 →
      (TargetEmitterPlan.currentGateAt bias).evaluate registers captured scratch <
        TargetEmitterLedger.slotCapacity raw
  sourceLockAt :
    ∀ gateBias side, gateBias ≤ 1 → side ≤ 1 →
      (TargetEmitterPlan.sourceLockAt gateBias side).evaluate
          registers captured scratch <
        TargetEmitterLedger.slotCapacity raw
  occurrenceAt :
    ∀ gateBias side, gateBias ≤ 1 → side ≤ 1 →
      (TargetEmitterPlan.occurrenceAt gateBias side).evaluate
          registers captured scratch <
        TargetEmitterLedger.slotCapacity raw
  traceLockAt :
    ∀ gateBias, gateBias ≤ 1 →
      (TargetEmitterPlan.traceLockAt gateBias).evaluate registers captured scratch <
        TargetEmitterLedger.slotCapacity raw
  traceCoordinateAt :
    ∀ gateBias, gateBias ≤ 1 →
      (TargetEmitterPlan.traceCoordinateAt gateBias).evaluate
          registers captured scratch <
        TargetEmitterLedger.slotCapacity raw

theorem planBounds
    {raw : RawCircuit}
    {registers : TargetEmitter.UnaryRegisters}
    {captured scratch : Nat}
    (range : ControllerRange raw registers)
    (capturedBound :
      captured + 1 ≤ (SourceParser.circuitCells raw).length)
    (scratchBound :
      scratch < TargetEmitterLedger.slotCapacity raw) :
    PlanBounds raw registers captured scratch := by
  have coordinateEnvelope := coordinateEnvelope_lt_slotCapacity raw
  have outputEnvelope :=
    range.outputIndex_add_eighteen_lt_slotCapacity
  have baselineReserve :=
    baseline_add_sixtyFour_le_slotCapacity raw
  have normalizedBound :=
    normalizedGateCount_le_cells_add_two raw
  have inputBound := inputCount_le_circuitCells_length raw
  have currentBound := range.currentGate_le
  have outputRange := range.outputIndex_le
  have capturedCapacity :
      captured < TargetEmitterLedger.slotCapacity raw := by
    simp only [TargetEmitterLedger.slotCapacity]
    omega
  refine
    { inputCount := ?_
      normalizedGateCount := ?_
      carrierWidth := ?_
      baseline := ?_
      currentGate := ?_
      outputIndex := ?_
      capturedIndex := ?_
      poppedCheck := ?_
      sourceLock := ?_
      occurrence := ?_
      traceLock := ?_
      traceCoordinate := ?_
      rawGateTrace := ?_
      finalLock := ?_
      localGate := ?_
      checkAt := ?_
      currentGateAt := ?_
      sourceLockAt := ?_
      occurrenceAt := ?_
      traceLockAt := ?_
      traceCoordinateAt := ?_ }
  · simp [TargetEmitterPlan.inputCount, TargetEmitterPlan.NatExpression.evaluate,
      TargetEmitterPlan.NatExpression.counter,
      TargetEmitterPlan.NatExpression.evaluateCounter, range.inputCount_eq]
    exact Nat.lt_of_le_of_lt (by omega) coordinateEnvelope
  · simp [TargetEmitterPlan.normalizedGateCount, TargetEmitterPlan.NatExpression.evaluate,
      TargetEmitterPlan.NatExpression.counter,
      TargetEmitterPlan.NatExpression.evaluateCounter,
      range.normalizedGateCount_eq]
    exact Nat.lt_of_le_of_lt (by omega) coordinateEnvelope
  · simp [TargetEmitterPlan.carrierWidth, TargetEmitterPlan.NatExpression.evaluate,
      TargetEmitterPlan.NatExpression.counter,
      TargetEmitterPlan.NatExpression.evaluateCounter,
      range.carrierWidth_eq,
      TargetEmitterLedger.carrierWidthValue]
    exact Nat.lt_of_le_of_lt (by omega) coordinateEnvelope
  · simp [TargetEmitterPlan.baseline, TargetEmitterPlan.NatExpression.evaluate,
      TargetEmitterPlan.NatExpression.counter,
      TargetEmitterPlan.NatExpression.evaluateCounter, range.baseline_eq]
    omega
  · simp [TargetEmitterPlan.currentGate, TargetEmitterPlan.NatExpression.evaluate,
      TargetEmitterPlan.NatExpression.counter,
      TargetEmitterPlan.NatExpression.evaluateCounter]
    exact range.currentGate_lt_slotCapacity
  · simp [TargetEmitterPlan.outputIndex, TargetEmitterPlan.NatExpression.evaluate,
      TargetEmitterPlan.NatExpression.counter,
      TargetEmitterPlan.NatExpression.evaluateCounter]
    omega
  · simpa [TargetEmitterPlan.capturedIndex, TargetEmitterPlan.NatExpression.evaluate,
      TargetEmitterPlan.NatExpression.counter,
      TargetEmitterPlan.NatExpression.evaluateCounter] using capturedCapacity
  · simpa [TargetEmitterPlan.poppedCheck, TargetEmitterPlan.NatExpression.evaluate,
      TargetEmitterPlan.NatExpression.counter,
      TargetEmitterPlan.NatExpression.evaluateCounter] using scratchBound
  · intro side sideBound
    rw [TargetEmitterPlan.sourceLock_evaluated]
    rw [range.inputCount_eq, range.normalizedGateCount_eq]
    exact Nat.lt_of_le_of_lt (by omega) coordinateEnvelope
  · intro side sideBound
    rw [TargetEmitterPlan.occurrence_evaluated]
    rw [range.inputCount_eq, range.normalizedGateCount_eq]
    exact Nat.lt_of_le_of_lt (by omega) coordinateEnvelope
  · rw [TargetEmitterPlan.traceLock_evaluated]
    rw [range.inputCount_eq, range.normalizedGateCount_eq]
    exact Nat.lt_of_le_of_lt (by omega) coordinateEnvelope
  · rw [TargetEmitterPlan.traceCoordinate_evaluated]
    rw [range.inputCount_eq]
    exact Nat.lt_of_le_of_lt (by omega) coordinateEnvelope
  · rw [TargetEmitterPlan.rawGateTrace_evaluated]
    rw [range.inputCount_eq]
    simp only [TargetEmitterLedger.slotCapacity]
    omega
  · rw [TargetEmitterPlan.finalLock_evaluated]
    rw [range.inputCount_eq, range.normalizedGateCount_eq]
    exact Nat.lt_of_le_of_lt (by omega) coordinateEnvelope
  · intro offset offsetBound
    rw [TargetEmitterPlan.localGate_evaluated]
    omega
  · intro relative relativeBound
    rw [TargetEmitterPlan.checkAt_evaluated]
    omega
  · intro bias biasBound
    simp only [TargetEmitterPlan.currentGateAt,
      TargetEmitterPlan.NatExpression.evaluate_addOffset]
    simp [TargetEmitterPlan.currentGate, TargetEmitterPlan.NatExpression.evaluate,
      TargetEmitterPlan.NatExpression.counter,
      TargetEmitterPlan.NatExpression.evaluateCounter]
    exact Nat.lt_of_le_of_lt (by omega) coordinateEnvelope
  · intro gateBias side gateBiasBound sideBound
    simp only [TargetEmitterPlan.sourceLockAt,
      TargetEmitterPlan.NatExpression.evaluate_addOffset]
    rw [
      TargetEmitterPlan.sourceLock_evaluated]
    rw [range.inputCount_eq, range.normalizedGateCount_eq]
    exact Nat.lt_of_le_of_lt (by omega) coordinateEnvelope
  · intro gateBias side gateBiasBound sideBound
    simp only [TargetEmitterPlan.occurrenceAt,
      TargetEmitterPlan.NatExpression.evaluate_addOffset]
    rw [
      TargetEmitterPlan.occurrence_evaluated]
    rw [range.inputCount_eq, range.normalizedGateCount_eq]
    exact Nat.lt_of_le_of_lt (by omega) coordinateEnvelope
  · intro gateBias gateBiasBound
    simp only [TargetEmitterPlan.traceLockAt,
      TargetEmitterPlan.NatExpression.evaluate_addOffset]
    rw [
      TargetEmitterPlan.traceLock_evaluated]
    rw [range.inputCount_eq, range.normalizedGateCount_eq]
    exact Nat.lt_of_le_of_lt (by omega) coordinateEnvelope
  · intro gateBias gateBiasBound
    simp only [TargetEmitterPlan.traceCoordinateAt,
      TargetEmitterPlan.NatExpression.evaluate_addOffset]
    rw [
      TargetEmitterPlan.traceCoordinate_evaluated]
    rw [range.inputCount_eq]
    exact Nat.lt_of_le_of_lt (by omega) coordinateEnvelope

/-! ### Header, template, prefix, final, and output reserves -/

def templateLocalOffsets
    (template : List TargetEmitterPlan.TemplateGate) : List Nat :=
  template.flatMap fun gate =>
    let left :=
      match gate.left with
      | .binding _ => []
      | .localGate index => [index]
    let right :=
      match gate.right with
      | .binding _ => []
      | .localGate index => [index]
    left ++ right

def supportedTemplates : List (List TargetEmitterPlan.TemplateGate) :=
  [ TargetEmitterPlan.equalityTemplate
  , TargetEmitterPlan.constantZeroTemplate
  , TargetEmitterPlan.constantOneTemplate
  , TargetEmitterPlan.traceTemplate
  , TargetEmitterPlan.prefixTemplate
  , TargetEmitterPlan.finalTemplate
  ]

/-- The largest literal local reference is trace-template gate sixteen. -/
theorem supportedTemplate_localOffset_le_sixteen
    {template : List TargetEmitterPlan.TemplateGate} {offset : Nat}
    (supported : template ∈ supportedTemplates)
    (member : offset ∈ templateLocalOffsets template) :
    offset ≤ 16 := by
  simp [supportedTemplates] at supported
  rcases supported with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [templateLocalOffsets, TargetEmitterPlan.equalityTemplate,
      TargetEmitterPlan.constantZeroTemplate, TargetEmitterPlan.constantOneTemplate,
      TargetEmitterPlan.traceTemplate, TargetEmitterPlan.prefixTemplate,
      TargetEmitterPlan.finalTemplate] at member
  all_goals omega

/-- Any local reference in any emitted template is strictly in capacity.
The optional base bias is the one-cell bias of `finalPositivePlan`. -/
theorem supportedTemplate_localCoordinate_lt_slotCapacity
    {raw : RawCircuit}
    {registers : TargetEmitter.UnaryRegisters}
    (range : ControllerRange raw registers)
    {template : List TargetEmitterPlan.TemplateGate} {offset baseBias : Nat}
    (supported : template ∈ supportedTemplates)
    (member : offset ∈ templateLocalOffsets template)
    (baseBiasBound : baseBias ≤ 1) :
    registers.outputIndex + baseBias + offset <
      TargetEmitterLedger.slotCapacity raw := by
  have offsetBound :=
    supportedTemplate_localOffset_le_sixteen supported member
  have envelope :=
    range.outputIndex_add_eighteen_lt_slotCapacity
  omega

structure BlockBounds
    (raw : RawCircuit)
    (registers : TargetEmitter.UnaryRegisters) : Prop where
  headerCarrierWidth :
    registers.carrierWidth <
      TargetEmitterLedger.slotCapacity raw
  headerGateCount :
    registers.baseline + 4 <
      TargetEmitterLedger.slotCapacity raw
  headerOutputCount :
    registers.baseline + 1 <
      TargetEmitterLedger.slotCapacity raw
  headerFocusedCapture :
    ∀ source, CircuitSource raw source →
      registers.baseline + 1 + sourceCaptureValue source + 1 ≤
        TargetEmitterLedger.slotCapacity raw
  sourceBlock :
    registers.outputIndex + 10 <
      TargetEmitterLedger.slotCapacity raw
  traceBlock :
    registers.outputIndex + 18 <
      TargetEmitterLedger.slotCapacity raw
  prefixBlock :
    registers.outputIndex + 2 <
      TargetEmitterLedger.slotCapacity raw
  finalBlock :
    registers.outputIndex + 4 <
      TargetEmitterLedger.slotCapacity raw
  outputLastBaseline :
    registers.baseline + 3 <
      TargetEmitterLedger.slotCapacity raw

theorem blockBounds
    {raw : RawCircuit}
    {registers : TargetEmitter.UnaryRegisters}
    (range : ControllerRange raw registers) :
    BlockBounds raw registers := by
  have coordinateEnvelope := coordinateEnvelope_lt_slotCapacity raw
  have outputEnvelope :=
    range.outputIndex_add_eighteen_lt_slotCapacity
  have baselineReserve :=
    baseline_add_sixtyFour_le_slotCapacity raw
  refine
    { headerCarrierWidth := ?_
      headerGateCount := ?_
      headerOutputCount := ?_
      headerFocusedCapture := ?_
      sourceBlock := by omega
      traceBlock := outputEnvelope
      prefixBlock := by omega
      finalBlock := by omega
      outputLastBaseline := ?_ }
  · rw [range.carrierWidth_eq]
    simp only [TargetEmitterLedger.carrierWidthValue]
    exact Nat.lt_of_le_of_lt (by omega) coordinateEnvelope
  · rw [range.baseline_eq]
    exact baseline_add_four_lt_slotCapacity raw
  · rw [range.baseline_eq]
    exact baseline_add_one_lt_slotCapacity raw
  · intro source member
    rw [range.baseline_eq]
    exact headerFocusedSourceCaptureReserve member
  · rw [range.baseline_eq]
    omega

end PNP.Concrete.LockedNAND.TargetEmitterCapacity
