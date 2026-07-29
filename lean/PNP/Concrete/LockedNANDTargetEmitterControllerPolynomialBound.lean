/-
Copyright (c) 2026 PNP Labs.

Closed encoded-input polynomial accounting for the grammar-only locked-NAND
target-emitter controller.

The detailed trace modules expose exact source-derived envelopes.  This file
forgets their semantic shape and dominates every retained-source, target,
check-stack, and primitive-program quantity by one deliberately conservative
polynomial in the canonical strict-v0 bit length.
-/

import PNP.Concrete.LockedNANDTargetEmitterControllerCompletionTrace
import PNP.Concrete.LockedNANDTargetEmitterSpec

namespace PNP.Concrete.LockedNAND.TargetEmitterControllerPolynomialBound

open PNP.Concrete
open TargetEmitterController

set_option maxRecDepth 10000
set_option maxHeartbeats 100000

abbrev Runtime := TargetEmitterProgramSemantics.Runtime

/-- Positive shift used by every closed majorant. -/
def shiftedSize (bitLength : Nat) : Nat :=
  bitLength + 1

/-- A factored quadratic unit used to keep kernel arithmetic small. -/
def squareUnit (bitLength : Nat) : Nat :=
  100000 * shiftedSize bitLength * shiftedSize bitLength

/-- One quadratic logical-data budget.  Its factored coefficient keeps the
subsequent arithmetic transparent and independent of semantic schedules. -/
def dataMajorant (bitLength : Nat) : Nat :=
  1000 * squareUnit bitLength

/-- One quadratic physical-footprint budget for every fixed controller
program reached in any phase. -/
def masterMajorant (bitLength : Nat) : Nat :=
  20 * dataMajorant bitLength

/-- Uniform charge for any fixed primitive block once its footprint is below
`masterMajorant`. -/
def phaseUnit (bitLength : Nat) : Nat :=
  TargetEmitterControllerCompletionTrace.normalizationProgramLimit *
    (TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
      (masterMajorant bitLength) + 1)

/-- Closed work-step bound for the complete post-ledger controller. -/
def controllerWorkBound (bitLength : Nat) : Nat :=
  256 * shiftedSize bitLength * phaseUnit bitLength

/-- Closed work-step bound for scanner failure or scanner/ledger/controller
success on an arbitrary raw bitstring. -/
def allInputWorkBound (bitLength : Nat) : Nat :=
  512 * shiftedSize bitLength * phaseUnit bitLength

/-- Literal degree-five polynomial evaluating to `controllerWorkBound`. -/
def controllerWorkTimePolynomial : NatPolynomial :=
  let shifted : NatPolynomial :=
    .add .variable (.constant 1)
  let data : NatPolynomial :=
    .mul (.constant 1000)
      (.mul (.constant 100000) (.mul shifted shifted))
  let master : NatPolynomial :=
    .mul (.constant 20) data
  let unit : NatPolynomial :=
    .mul
      (.constant
        TargetEmitterControllerCompletionTrace.normalizationProgramLimit)
      (.add
        (.add
          (.mul (.constant 100) (.mul master master))
          (.constant 100))
        (.constant 1))
  .mul (.constant 256) (.mul shifted unit)

theorem controllerWorkTimePolynomial_eval (bitLength : Nat) :
    controllerWorkTimePolynomial.eval bitLength =
      controllerWorkBound bitLength := by
  simp [controllerWorkTimePolynomial, controllerWorkBound, phaseUnit,
    TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope,
    masterMajorant, dataMajorant, squareUnit, shiftedSize, NatPolynomial.eval,
    Nat.mul_assoc]

/-- Literal all-input work polynomial, twice the decoded-controller budget. -/
def allInputWorkTimePolynomial : NatPolynomial :=
  .mul (.constant 2) controllerWorkTimePolynomial

theorem allInputWorkTimePolynomial_eval (bitLength : Nat) :
    allInputWorkTimePolynomial.eval bitLength =
      allInputWorkBound bitLength := by
  rw [allInputWorkTimePolynomial, NatPolynomial.eval_mul,
    controllerWorkTimePolynomial_eval]
  unfold controllerWorkBound allInputWorkBound
  calc
    2 * (256 * shiftedSize bitLength * phaseUnit bitLength) =
        (2 * 256) * shiftedSize bitLength * phaseUnit bitLength := by
      ac_rfl
    _ = 512 * shiftedSize bitLength * phaseUnit bitLength := by
      rw [show 2 * 256 = 512 by omega]

/-- Six-transition raw compilation of the all-input work polynomial. -/
def compiledRawTimePolynomial : NatPolynomial :=
  .mul (.constant 6) allInputWorkTimePolynomial

theorem compiledRawTimePolynomial_eval (bitLength : Nat) :
    compiledRawTimePolynomial.eval bitLength =
      6 * allInputWorkBound bitLength := by
  simp [compiledRawTimePolynomial, allInputWorkTimePolynomial_eval]

private theorem shifted_positive (bitLength : Nat) :
    1 ≤ shiftedSize bitLength := by
  unfold shiftedSize
  omega

private theorem cells_le_bitLength (raw : RawCircuit) :
    (SourceParser.circuitCells raw).length ≤
      (encodeCircuit raw).length := by
  rw [SourceParser.encodeCircuit_length_eq]
  omega

private theorem cells_le_shifted (raw : RawCircuit) :
    (SourceParser.circuitCells raw).length ≤
      shiftedSize (encodeCircuit raw).length := by
  have := cells_le_bitLength raw
  unfold shiftedSize
  omega

private theorem gates_le_shifted (raw : RawCircuit) :
    raw.gates.length ≤ shiftedSize (encodeCircuit raw).length := by
  exact Nat.le_trans
    (TargetEmitterCapacity.gateCount_le_circuitCells_length raw)
    (cells_le_shifted raw)

private theorem capacity_le_sixtyFour_shifted (raw : RawCircuit) :
    TargetEmitterLedger.slotCapacity raw ≤
      64 * shiftedSize (encodeCircuit raw).length := by
  have cells :
      (SourceParser.circuitCells raw).length + 1 ≤
        shiftedSize (encodeCircuit raw).length := by
    have := cells_le_bitLength raw
    unfold shiftedSize
    omega
  simpa [TargetEmitterLedger.slotCapacity, Nat.mul_add] using
    Nat.mul_le_mul_left 64 cells

private theorem capacity_add_one_le_sixtyFive_shifted
    (raw : RawCircuit) :
    TargetEmitterLedger.slotCapacity raw + 1 ≤
      65 * shiftedSize (encodeCircuit raw).length := by
  have capacity := capacity_le_sixtyFour_shifted raw
  have positive := shifted_positive (encodeCircuit raw).length
  omega

private theorem coefficient_square_le_unit
    (bitLength coefficient : Nat)
    (coefficientBound : coefficient ≤ 100000) :
    coefficient * shiftedSize bitLength * shiftedSize bitLength ≤
      squareUnit bitLength := by
  unfold squareUnit
  exact Nat.mul_le_mul_right (shiftedSize bitLength)
    (Nat.mul_le_mul_right (shiftedSize bitLength) coefficientBound)

private theorem data_le_master (bitLength : Nat) :
    dataMajorant bitLength ≤ masterMajorant bitLength := by
  unfold masterMajorant
  omega

private theorem one_le_data (bitLength : Nat) :
    1 ≤ dataMajorant bitLength := by
  have unitPositive :
      1 ≤ squareUnit bitLength := by
    have square :
        1 ≤ shiftedSize bitLength * shiftedSize bitLength :=
      Nat.mul_le_mul (shifted_positive bitLength)
        (shifted_positive bitLength)
    have coefficient :=
      coefficient_square_le_unit bitLength 1 (by decide)
    exact Nat.le_trans square (by simpa only [Nat.one_mul] using coefficient)
  unfold dataMajorant
  have scaled :
      1 * squareUnit bitLength ≤
        1000 * squareUnit bitLength :=
    Nat.mul_le_mul_right (squareUnit bitLength)
      (show 1 ≤ 1000 by decide)
  exact Nat.le_trans unitPositive (by
    simpa only [Nat.one_mul] using scaled)

private theorem one_le_master (bitLength : Nat) :
    1 ≤ masterMajorant bitLength :=
  Nat.le_trans (one_le_data bitLength) (data_le_master bitLength)

private theorem primitive_mono
    {first second : Nat} (bound : first ≤ second) :
    TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope first ≤
      TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope second := by
  have square := Nat.mul_le_mul bound bound
  unfold TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 100 square) 100

private theorem primitive_add_one_le_phaseUnit
    (bitLength : Nat) :
    TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
          (masterMajorant bitLength) + 1 ≤
      phaseUnit bitLength := by
  unfold phaseUnit
  have positive :
      1 ≤
        TargetEmitterControllerCompletionTrace.normalizationProgramLimit := by
    decide
  simpa [Nat.mul_comm] using
    Nat.mul_le_mul_left
      (TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
        (masterMajorant bitLength) + 1)
      positive

theorem one_le_phaseUnit (bitLength : Nat) :
    1 ≤ phaseUnit bitLength := by
  exact Nat.le_trans
    (by
      unfold TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
      omega)
    (primitive_add_one_le_phaseUnit bitLength)

private theorem header_target_length_le
    (raw : RawCircuit) :
    (TargetEmitterProgramSemantics.headerResult
        (TargetEmitterControllerHeaderTrace.initialRuntime raw)).targetTokens.length ≤
      256 * shiftedSize (encodeCircuit raw).length := by
  have carrier :=
    TargetEmitterLedger.carrierWidthValue_le_slotCapacity raw
  have baseline :=
    TargetEmitterLedger.baselineValue_le_slotCapacity raw
  have capacity := capacity_le_sixtyFour_shifted raw
  have positive := shifted_positive (encodeCircuit raw).length
  rw [TargetEmitterProgramSemantics.headerResult_targetTokens]
  simp only [TargetEmitterControllerHeaderTrace.initialRuntime,
    List.nil_append, List.length_append, List.length_cons, List.length_nil,
    TargetEmitterSpec.encodeNatTokens_length,
    TargetEmitterLedger.ledgerRegisters]
  omega

private theorem header_checkCells_zero
    (raw : RawCircuit) :
    TargetEmitterRuntimeProgramBound.checkCells
        (TargetEmitterProgramSemantics.headerResult
          (TargetEmitterControllerHeaderTrace.initialRuntime raw)).checks =
      0 := by
  rw [TargetEmitterProgramSemantics.headerResult_checks]
  rfl

private theorem gate_growth_le
    (raw : RawCircuit) :
    raw.gates.length *
        TargetEmitterControllerGateListTrace.gatePerGateGrowth raw ≤
      99840 * shiftedSize (encodeCircuit raw).length *
        shiftedSize (encodeCircuit raw).length := by
  have gates := gates_le_shifted raw
  have capacity := capacity_add_one_le_sixtyFive_shifted raw
  have perGate :
      TargetEmitterControllerGateListTrace.gatePerGateGrowth raw ≤
        99840 * shiftedSize (encodeCircuit raw).length := by
    change
      3 * (512 * (TargetEmitterLedger.slotCapacity raw + 1)) ≤
        99840 * shiftedSize (encodeCircuit raw).length
    have scaled := Nat.mul_le_mul_left 1536 capacity
    calc
      3 * (512 * (TargetEmitterLedger.slotCapacity raw + 1)) =
          1536 * (TargetEmitterLedger.slotCapacity raw + 1) := by
        rw [← Nat.mul_assoc, show 3 * 512 = 1536 by decide]
      _ ≤
          1536 * (65 * shiftedSize (encodeCircuit raw).length) := scaled
      _ = 99840 * shiftedSize (encodeCircuit raw).length := by
        rw [← Nat.mul_assoc, show 1536 * 65 = 99840 by decide]
  have product := Nat.mul_le_mul gates perGate
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using product

private theorem gateListRuntime_data_tight
    (raw : RawCircuit) :
    (TargetEmitterControllerGateListTrace.gateListRuntime
          raw).targetTokens.length ≤
        10 * squareUnit (encodeCircuit raw).length ∧
      TargetEmitterRuntimeProgramBound.checkCells
          (TargetEmitterControllerGateListTrace.gateListRuntime raw).checks ≤
        10 * squareUnit (encodeCircuit raw).length := by
  rcases
      TargetEmitterControllerGateListTrace.gateListRuntime_data_le raw with
    ⟨targetBound, checkBound⟩
  have header := header_target_length_le raw
  have headerSquare :
      256 * shiftedSize (encodeCircuit raw).length ≤
        256 * shiftedSize (encodeCircuit raw).length *
          shiftedSize (encodeCircuit raw).length := by
    simpa using Nat.mul_le_mul_left
      (256 * shiftedSize (encodeCircuit raw).length)
      (shifted_positive (encodeCircuit raw).length)
  have growth := gate_growth_le raw
  have checksZero := header_checkCells_zero raw
  rw [checksZero, Nat.zero_add] at checkBound
  have targetCombined :
      256 * shiftedSize (encodeCircuit raw).length +
          99840 * shiftedSize (encodeCircuit raw).length *
            shiftedSize (encodeCircuit raw).length ≤
        10 * squareUnit (encodeCircuit raw).length := by
    have headerQuota :
        256 * shiftedSize (encodeCircuit raw).length ≤
          squareUnit (encodeCircuit raw).length :=
      Nat.le_trans headerSquare
        (coefficient_square_le_unit _ 256 (by decide))
    have growthQuota :
        99840 * shiftedSize (encodeCircuit raw).length *
            shiftedSize (encodeCircuit raw).length ≤
          squareUnit (encodeCircuit raw).length :=
      coefficient_square_le_unit _ 99840 (by decide)
    have summed :
        256 * shiftedSize (encodeCircuit raw).length +
            99840 * shiftedSize (encodeCircuit raw).length *
              shiftedSize (encodeCircuit raw).length ≤
          2 * squareUnit (encodeCircuit raw).length := by
      omega
    omega
  have checkCombined :
      99840 * shiftedSize (encodeCircuit raw).length *
          shiftedSize (encodeCircuit raw).length ≤
        10 * squareUnit (encodeCircuit raw).length := by
    have growthQuota :=
      coefficient_square_le_unit
        (encodeCircuit raw).length 99840 (by decide)
    omega
  constructor
  · exact Nat.le_trans targetBound
      (Nat.le_trans (Nat.add_le_add header growth) targetCombined)
  · exact Nat.le_trans checkBound (Nat.le_trans growth checkCombined)

private theorem gateListRuntime_data_le
    (raw : RawCircuit) :
    (TargetEmitterControllerGateListTrace.gateListRuntime
          raw).targetTokens.length ≤
        dataMajorant (encodeCircuit raw).length ∧
      TargetEmitterRuntimeProgramBound.checkCells
          (TargetEmitterControllerGateListTrace.gateListRuntime raw).checks ≤
        dataMajorant (encodeCircuit raw).length := by
  rcases gateListRuntime_data_tight raw with ⟨target, checks⟩
  have scale :
      10 * squareUnit (encodeCircuit raw).length ≤
        dataMajorant (encodeCircuit raw).length := by
    unfold dataMajorant
    exact Nat.mul_le_mul_right _ (by decide)
  exact
    ⟨Nat.le_trans target scale, Nat.le_trans checks scale⟩

private theorem normalizationRuntime_data_tight
    (raw : RawCircuit) :
    (TargetEmitterSemanticNormalization.normalizationRuntime
          raw).targetTokens.length ≤
        30 * squareUnit (encodeCircuit raw).length ∧
      TargetEmitterRuntimeProgramBound.checkCells
          (TargetEmitterSemanticNormalization.normalizationRuntime
            raw).checks ≤
        30 * squareUnit (encodeCircuit raw).length := by
  rcases gateListRuntime_data_tight raw with
    ⟨gateTarget, gateChecks⟩
  rcases
      TargetEmitterControllerCompletionTrace.normalizationRuntime_data_le raw with
    ⟨target, checks⟩
  have capacity := capacity_add_one_le_sixtyFive_shifted raw
  have growth :
      TargetEmitterControllerCompletionTrace.normalizationDataGrowth raw ≤
        1064960 * shiftedSize (encodeCircuit raw).length := by
    unfold TargetEmitterControllerCompletionTrace.normalizationDataGrowth
      TargetEmitterControllerCompletionTrace.normalizationProgramLimit
    calc
      16384 * (TargetEmitterLedger.slotCapacity raw + 1) ≤
          16384 * (65 * shiftedSize (encodeCircuit raw).length) :=
        Nat.mul_le_mul_left 16384 capacity
      _ = 1064960 * shiftedSize (encodeCircuit raw).length := by
        rw [← Nat.mul_assoc, show 16384 * 65 = 1064960 by decide]
  have growthUnit :
      1064960 * shiftedSize (encodeCircuit raw).length ≤
        20 * squareUnit (encodeCircuit raw).length := by
    have lifted :
        1064960 * shiftedSize (encodeCircuit raw).length ≤
          1064960 * shiftedSize (encodeCircuit raw).length *
            shiftedSize (encodeCircuit raw).length := by
      simpa using Nat.mul_le_mul_left
        (1064960 * shiftedSize (encodeCircuit raw).length)
        (shifted_positive (encodeCircuit raw).length)
    have coefficient :
        1064960 * shiftedSize (encodeCircuit raw).length *
            shiftedSize (encodeCircuit raw).length ≤
          20 * squareUnit (encodeCircuit raw).length := by
      unfold squareUnit
      have coefficientBound :
          1064960 ≤ 20 * 100000 := by omega
      have multiplied :=
        Nat.mul_le_mul_right (shiftedSize (encodeCircuit raw).length)
          (Nat.mul_le_mul_right
            (shiftedSize (encodeCircuit raw).length) coefficientBound)
      simpa only [Nat.mul_assoc] using multiplied
    exact Nat.le_trans lifted coefficient
  have combined :
      10 * squareUnit (encodeCircuit raw).length +
        20 * squareUnit (encodeCircuit raw).length ≤
          30 * squareUnit (encodeCircuit raw).length := by
    omega
  constructor
  · exact Nat.le_trans target
      (Nat.le_trans (Nat.add_le_add gateTarget
        (Nat.le_trans growth growthUnit)) combined)
  · exact Nat.le_trans checks
      (Nat.le_trans (Nat.add_le_add gateChecks
        (Nat.le_trans growth growthUnit)) combined)

private theorem normalizationRuntime_data_le
    (raw : RawCircuit) :
    (TargetEmitterSemanticNormalization.normalizationRuntime
          raw).targetTokens.length ≤
        dataMajorant (encodeCircuit raw).length ∧
      TargetEmitterRuntimeProgramBound.checkCells
          (TargetEmitterSemanticNormalization.normalizationRuntime
            raw).checks ≤
        dataMajorant (encodeCircuit raw).length := by
  rcases normalizationRuntime_data_tight raw with ⟨target, checks⟩
  have scale :
      30 * squareUnit (encodeCircuit raw).length ≤
        dataMajorant (encodeCircuit raw).length := by
    unfold dataMajorant
    exact Nat.mul_le_mul_right _ (by decide)
  exact
    ⟨Nat.le_trans target scale, Nat.le_trans checks scale⟩

private theorem raw_output_formula_le_data
    (size : Nat) (positive : 1 ≤ size) :
    4 *
        (409 * size +
            100 * size * (605 * size) +
          100 * size * (302 * size)) ≤
      1000 * (100000 * size * size) := by
  let quota := 100000 * size * size
  have linearQuota : 409 * size ≤ quota := by
    have lifted :
        409 * size ≤ 409 * size * size := by
      simpa using Nat.mul_le_mul_left (409 * size) positive
    have coefficient :
        409 * size * size ≤ quota := by
      exact Nat.mul_le_mul_right size
        (Nat.mul_le_mul_right size (by decide))
    exact Nat.le_trans lifted coefficient
  have firstProductQuota :
      100 * size * (605 * size) ≤ quota := by
    have right :
        605 * size ≤ 1000 * size :=
      Nat.mul_le_mul_right size (by decide)
    have product := Nat.mul_le_mul (Nat.le_refl (100 * size)) right
    calc
      100 * size * (605 * size) ≤
          (100 * size) * (1000 * size) := product
      _ = 100000 * size * size := by
        calc
          (100 * size) * (1000 * size) =
              (100 * 1000) * size * size := by ac_rfl
          _ = 100000 * size * size := by
            rw [show 100 * 1000 = 100000 by omega]
      _ = quota := rfl
  have secondProductQuota :
      100 * size * (302 * size) ≤ quota := by
    have right :
        302 * size ≤ 1000 * size :=
      Nat.mul_le_mul_right size (by decide)
    have product := Nat.mul_le_mul (Nat.le_refl (100 * size)) right
    calc
      100 * size * (302 * size) ≤
          (100 * size) * (1000 * size) := product
      _ = 100000 * size * size := by
        calc
          (100 * size) * (1000 * size) =
              (100 * 1000) * size * size := by ac_rfl
          _ = 100000 * size * size := by
            rw [show 100 * 1000 = 100000 by omega]
      _ = quota := rfl
  have inner :
      409 * size +
          100 * size * (605 * size) +
        100 * size * (302 * size) ≤
        3 * quota := by
    omega
  have scaled := Nat.mul_le_mul_left 4 inner
  calc
    4 *
        (409 * size +
            100 * size * (605 * size) +
          100 * size * (302 * size)) ≤
        4 * (3 * quota) := scaled
    _ = 12 * quota := by omega
    _ ≤ 1000 * quota :=
      Nat.mul_le_mul_right quota (by decide)
    _ = 1000 * (100000 * size * size) := rfl

private theorem rawTargetOutputPolynomial_le_data (bitLength : Nat) :
    TargetEmitterSpec.rawTargetOutputSizePolynomial.eval bitLength ≤
      dataMajorant bitLength := by
  rw [TargetEmitterSpec.rawTargetOutputSizePolynomial_eval]
  simpa only [dataMajorant, squareUnit, shiftedSize] using
    raw_output_formula_le_data (bitLength + 1)
      (Nat.succ_le_succ (Nat.zero_le bitLength))

private theorem finalRuntime_target_le_data
    (raw : RawCircuit) :
    (TargetEmitterSemanticCompletion.finalRuntime
          raw).targetTokens.length ≤
      dataMajorant (encodeCircuit raw).length := by
  rcases
      TargetEmitterSemanticCompletion.finalRuntime_targetTokens_prefix raw with
    ⟨suffix, shape⟩
  have prefixLength :
      (TargetEmitterSemanticCompletion.finalRuntime
          raw).targetTokens.length ≤
        (TargetEmitterSemanticCompletion.completeRuntime
          raw).targetTokens.length := by
    rw [shape, List.length_append]
    omega
  have completeTokens :
      (TargetEmitterSemanticCompletion.completeRuntime
          raw).targetTokens.length ≤
        (RawBuilder.targetBytes (encodeCircuit raw)).length := by
    rw [TargetEmitterSemanticCompletion.completeRuntime_targetTokens]
    rw [RawBuilder.targetBytes_of_decoded
      (encodeCircuit raw) raw (decodeCircuit_encodeCircuit raw)]
    rw [encodeLockedInstance, encodeTokens_length]
    omega
  have bytesBound :=
    TargetEmitterSpec.targetBytes_length_le (encodeCircuit raw)
  have polynomialBound :
      TargetEmitterSpec.rawTargetOutputSizePolynomial.eval
          (encodeCircuit raw).length ≤
        dataMajorant (encodeCircuit raw).length := by
    exact rawTargetOutputPolynomial_le_data _
  exact Nat.le_trans prefixLength
    (Nat.le_trans completeTokens
      (Nat.le_trans bytesBound polynomialBound))

private theorem finalRuntime_checks_le_data
    (raw : RawCircuit) :
    TargetEmitterRuntimeProgramBound.checkCells
        (TargetEmitterSemanticCompletion.finalRuntime raw).checks ≤
      dataMajorant (encodeCircuit raw).length := by
  rw [TargetEmitterSemanticCompletion.finalRuntime_checks_empty]
  exact Nat.zero_le _

private theorem checkCount_le_two_shifted
    (raw : RawCircuit) :
    (TargetEmitterSemanticCompletion.checkCoordinates raw).length ≤
      2 * shiftedSize (encodeCircuit raw).length := by
  have normalized :=
    TargetEmitterCapacity.normalizedGateCount_le_cells_add_two raw
  have cells :=
    TargetEmitterCapacity.fourteen_le_circuitCells_length raw
  have encoded := SourceParser.encodeCircuit_length_eq raw
  rw [TargetEmitterSemanticCompletion.checkCoordinates,
    TargetEmitterSemanticPrefix.macroAssembly_checkCoordinates_length]
  change
    3 * raw.normalize.gates.length ≤
      2 * shiftedSize (encodeCircuit raw).length
  rw [← TargetEmitterLedger.normalizedGateCount_eq_normalize]
  unfold shiftedSize
  omega

private theorem unit_le_data (bitLength : Nat) :
    squareUnit bitLength ≤ dataMajorant bitLength := by
  unfold dataMajorant
  have scaled :
      1 * squareUnit bitLength ≤
        1000 * squareUnit bitLength :=
    Nat.mul_le_mul_right (squareUnit bitLength) (by decide)
  simpa only [Nat.one_mul] using scaled

private theorem coefficient_square_le_data
    (bitLength coefficient : Nat)
    (coefficientBound : coefficient ≤ 100000000) :
    coefficient * shiftedSize bitLength * shiftedSize bitLength ≤
      dataMajorant bitLength := by
  have factored : coefficient ≤ 1000 * 100000 := by
    omega
  have multiplied :=
    Nat.mul_le_mul_right (shiftedSize bitLength)
      (Nat.mul_le_mul_right (shiftedSize bitLength) factored)
  unfold dataMajorant squareUnit
  simpa only [Nat.mul_assoc] using multiplied

private theorem coefficient_linear_le_data
    (bitLength coefficient : Nat)
    (coefficientBound : coefficient ≤ 100000000) :
    coefficient * shiftedSize bitLength ≤
      dataMajorant bitLength := by
  have lifted :
      coefficient * shiftedSize bitLength ≤
        coefficient * shiftedSize bitLength * shiftedSize bitLength := by
    simpa using Nat.mul_le_mul_left
      (coefficient * shiftedSize bitLength)
      (shifted_positive bitLength)
  exact Nat.le_trans lifted
    (coefficient_square_le_data bitLength coefficient coefficientBound)

private theorem capacity_le_data (raw : RawCircuit) :
    TargetEmitterLedger.slotCapacity raw ≤
      dataMajorant (encodeCircuit raw).length := by
  exact Nat.le_trans (capacity_le_sixtyFour_shifted raw)
    (coefficient_linear_le_data _ 64 (by decide))

private theorem cells_length_le_data (raw : RawCircuit) :
    (SourceParser.circuitCells raw).length ≤
      dataMajorant (encodeCircuit raw).length := by
  have shifted :
      shiftedSize (encodeCircuit raw).length ≤
        dataMajorant (encodeCircuit raw).length := by
    simpa only [Nat.one_mul] using
      coefficient_linear_le_data
        (encodeCircuit raw).length 1 (by decide)
  exact Nat.le_trans (cells_le_shifted raw) shifted

private theorem markedSource_length_le_data (raw : RawCircuit) :
    (TargetEmitterControllerCompletionTrace.markedSource raw).length ≤
      dataMajorant (encodeCircuit raw).length := by
  rw [TargetEmitterControllerCompletionTrace.markedSource_length]
  exact cells_length_le_data raw

private theorem outputCrossed_length_le_data (raw : RawCircuit) :
    (TargetEmitterControllerGateListTrace.outputCrossedCells raw).length ≤
      dataMajorant (encodeCircuit raw).length := by
  have prefixBound :
      (TargetEmitterControllerGateListTrace.outputCrossedCells raw).length ≤
        (TargetEmitterControllerCompletionTrace.markedSource raw).length := by
    unfold TargetEmitterControllerCompletionTrace.markedSource
    rw [List.length_append, List.length_append]
    omega
  exact Nat.le_trans prefixBound (markedSource_length_le_data raw)

private theorem outputValue_le_data (raw : RawCircuit) :
    TargetEmitterControllerGateTrace.sourceValue raw.output ≤
      dataMajorant (encodeCircuit raw).length := by
  have sourceBound :
      TargetEmitterControllerGateTrace.sourceValue raw.output ≤
        (SourceParser.sourceCells raw.output).length := by
    cases outputEq : raw.output with
    | input index =>
        simp [TargetEmitterControllerGateTrace.sourceValue,
          SourceParser.sourceCells, SourceParser.natCells_length] <;>
          omega
    | gate index =>
        simp [TargetEmitterControllerGateTrace.sourceValue,
          SourceParser.sourceCells, SourceParser.natCells_length] <;>
          omega
    | constant value =>
        cases value <;>
          simp [TargetEmitterControllerGateTrace.sourceValue,
            SourceParser.sourceCells]
  have suffix :
      (SourceParser.sourceCells raw.output).length ≤
        (SourceParser.circuitCells raw).length := by
    simp [SourceParser.circuitCells]
    omega
  exact Nat.le_trans sourceBound
    (Nat.le_trans suffix (cells_length_le_data raw))

private theorem programGrowth_le_data
    (raw : RawCircuit) (programLength : Nat)
    (programBound :
      programLength ≤
        TargetEmitterControllerCompletionTrace.normalizationProgramLimit) :
    programLength *
        (3 * TargetEmitterLedger.slotCapacity raw + 3) ≤
      dataMajorant (encodeCircuit raw).length := by
  have capacity := capacity_le_sixtyFour_shifted raw
  have positive := shifted_positive (encodeCircuit raw).length
  have factor :
      3 * TargetEmitterLedger.slotCapacity raw + 3 ≤
        195 * shiftedSize (encodeCircuit raw).length := by
    omega
  have product := Nat.mul_le_mul programBound factor
  have expanded :
      TargetEmitterControllerCompletionTrace.normalizationProgramLimit *
          (195 * shiftedSize (encodeCircuit raw).length) =
        3194880 * shiftedSize (encodeCircuit raw).length := by
    unfold TargetEmitterControllerCompletionTrace.normalizationProgramLimit
    rw [← Nat.mul_assoc, show 16384 * 195 = 3194880 by omega]
  rw [expanded] at product
  exact Nat.le_trans product
    (coefficient_linear_le_data _ 3194880 (by decide))

private theorem footprintParts_le_master
    (raw : RawCircuit)
    (sourceLength targetLength checkLength programLength : Nat)
    (sourceBound :
      sourceLength ≤ dataMajorant (encodeCircuit raw).length)
    (targetBound :
      targetLength ≤ 3 * dataMajorant (encodeCircuit raw).length)
    (checkBound :
      checkLength ≤ 3 * dataMajorant (encodeCircuit raw).length)
    (programBound :
      programLength ≤
        TargetEmitterControllerCompletionTrace.normalizationProgramLimit) :
    TargetEmitterLedger.slotCapacity raw + sourceLength +
          2 * targetLength + checkLength +
          programLength *
            (3 * TargetEmitterLedger.slotCapacity raw + 3) + 1 ≤
      masterMajorant (encodeCircuit raw).length := by
  have capacity := capacity_le_data raw
  have growth := programGrowth_le_data raw programLength programBound
  have positive := one_le_data (encodeCircuit raw).length
  unfold masterMajorant
  omega

private theorem runtimeFootprint_le_master
    (raw : RawCircuit) (source : List WorkSymbol)
    (runtime : Runtime) (programLength : Nat)
    (sourceBound :
      source.length ≤ dataMajorant (encodeCircuit raw).length)
    (targetBound :
      runtime.targetTokens.length ≤
        3 * dataMajorant (encodeCircuit raw).length)
    (checkBound :
      TargetEmitterRuntimeProgramBound.checkCells runtime.checks ≤
        3 * dataMajorant (encodeCircuit raw).length)
    (programBound :
      programLength ≤
        TargetEmitterControllerCompletionTrace.normalizationProgramLimit) :
    TargetEmitterRuntimeProgramBound.runtimeFootprint
        (TargetEmitterLedger.slotCapacity raw) source runtime programLength ≤
      masterMajorant (encodeCircuit raw).length := by
  unfold TargetEmitterRuntimeProgramBound.runtimeFootprint
  exact footprintParts_le_master raw source.length
    runtime.targetTokens.length
    (TargetEmitterRuntimeProgramBound.checkCells runtime.checks)
    programLength sourceBound targetBound checkBound programBound

private theorem programEnvelope_le_phaseUnit
    (raw : RawCircuit) (source : List WorkSymbol)
    (runtime : Runtime) (primitives : List TargetEmitterPlan.Primitive)
    (sourceBound :
      source.length ≤ dataMajorant (encodeCircuit raw).length)
    (targetBound :
      runtime.targetTokens.length ≤
        3 * dataMajorant (encodeCircuit raw).length)
    (checkBound :
      TargetEmitterRuntimeProgramBound.checkCells runtime.checks ≤
        3 * dataMajorant (encodeCircuit raw).length)
    (programBound :
      primitives.length ≤
        TargetEmitterControllerCompletionTrace.normalizationProgramLimit) :
    TargetEmitterRuntimeProgramBound.programWorkEnvelope
        (TargetEmitterLedger.slotCapacity raw) source runtime primitives ≤
      phaseUnit (encodeCircuit raw).length := by
  have footprint :=
    runtimeFootprint_le_master raw source runtime primitives.length
      sourceBound targetBound checkBound programBound
  have primitive :=
    Nat.add_le_add_right (primitive_mono footprint) 1
  have product := Nat.mul_le_mul programBound primitive
  unfold TargetEmitterRuntimeProgramBound.programWorkEnvelope phaseUnit
  exact product

private theorem master_le_primitive_add_one (bitLength : Nat) :
    masterMajorant bitLength ≤
      TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
          (masterMajorant bitLength) + 1 := by
  have positive := one_le_master bitLength
  have square :
      masterMajorant bitLength ≤
        masterMajorant bitLength * masterMajorant bitLength := by
    simpa using Nat.mul_le_mul_left (masterMajorant bitLength) positive
  unfold TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
  have scaled :=
    Nat.mul_le_mul_left 100 square
  omega

private theorem master_le_phaseUnit (bitLength : Nat) :
    masterMajorant bitLength ≤ phaseUnit bitLength := by
  exact Nat.le_trans (master_le_primitive_add_one bitLength)
    (primitive_add_one_le_phaseUnit bitLength)

private theorem data_le_phaseUnit (bitLength : Nat) :
    dataMajorant bitLength ≤ phaseUnit bitLength :=
  Nat.le_trans (data_le_master bitLength)
    (master_le_phaseUnit bitLength)

private theorem header_target_le_data (raw : RawCircuit) :
    (TargetEmitterProgramSemantics.headerResult
        (TargetEmitterControllerHeaderTrace.initialRuntime raw)).targetTokens.length ≤
      dataMajorant (encodeCircuit raw).length := by
  exact Nat.le_trans (header_target_length_le raw)
    (coefficient_linear_le_data _ 256 (by decide))

private theorem gateGrowthBudget_le_data (raw : RawCircuit) :
    3 * raw.gates.length *
        TargetEmitterControllerGateBound.gateBlockGrowth
          (TargetEmitterLedger.slotCapacity raw) ≤
      dataMajorant (encodeCircuit raw).length := by
  calc
    3 * raw.gates.length *
          TargetEmitterControllerGateBound.gateBlockGrowth
            (TargetEmitterLedger.slotCapacity raw) =
        raw.gates.length *
          TargetEmitterControllerGateListTrace.gatePerGateGrowth raw := by
      unfold TargetEmitterControllerGateListTrace.gatePerGateGrowth
      ac_rfl
    _ ≤ 99840 * shiftedSize (encodeCircuit raw).length *
          shiftedSize (encodeCircuit raw).length :=
      gate_growth_le raw
    _ ≤ squareUnit (encodeCircuit raw).length :=
      coefficient_square_le_unit _ 99840 (by decide)
    _ ≤ dataMajorant (encodeCircuit raw).length :=
      unit_le_data _

private theorem gateTargetLimit_le_three_data (raw : RawCircuit) :
    TargetEmitterControllerGateBound.gateTargetLimit
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterProgramSemantics.headerResult
          (TargetEmitterControllerHeaderTrace.initialRuntime raw))
        raw.gates.length ≤
      3 * dataMajorant (encodeCircuit raw).length := by
  have header := header_target_le_data raw
  have growth := gateGrowthBudget_le_data raw
  unfold TargetEmitterControllerGateBound.gateTargetLimit
  omega

private theorem gateCheckLimit_le_three_data (raw : RawCircuit) :
    TargetEmitterControllerGateBound.gateCheckLimit
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterProgramSemantics.headerResult
          (TargetEmitterControllerHeaderTrace.initialRuntime raw))
        raw.gates.length ≤
      3 * dataMajorant (encodeCircuit raw).length := by
  have growth := gateGrowthBudget_le_data raw
  have empty := header_checkCells_zero raw
  unfold TargetEmitterControllerGateBound.gateCheckLimit
  rw [empty]
  omega

private theorem gateMasterSize_le_master (raw : RawCircuit) :
    TargetEmitterControllerGateBound.gateMasterSize
        (TargetEmitterLedger.slotCapacity raw)
        (SourceParser.circuitCells raw).length
        (TargetEmitterProgramSemantics.headerResult
          (TargetEmitterControllerHeaderTrace.initialRuntime raw))
        raw.gates.length ≤
      masterMajorant (encodeCircuit raw).length := by
  unfold TargetEmitterControllerGateBound.gateMasterSize
  exact footprintParts_le_master raw
    (SourceParser.circuitCells raw).length
    (TargetEmitterControllerGateBound.gateTargetLimit
      (TargetEmitterLedger.slotCapacity raw)
      (TargetEmitterProgramSemantics.headerResult
        (TargetEmitterControllerHeaderTrace.initialRuntime raw))
      raw.gates.length)
    (TargetEmitterControllerGateBound.gateCheckLimit
      (TargetEmitterLedger.slotCapacity raw)
      (TargetEmitterProgramSemantics.headerResult
        (TargetEmitterControllerHeaderTrace.initialRuntime raw))
      raw.gates.length)
    TargetEmitterControllerGateBound.gateProgramLimit
    (cells_length_le_data raw)
    (gateTargetLimit_le_three_data raw)
    (gateCheckLimit_le_three_data raw)
    (by
      unfold TargetEmitterControllerGateBound.gateProgramLimit
        TargetEmitterControllerCompletionTrace.normalizationProgramLimit
      decide)

private theorem gateBlockUnit_le_phaseUnit (raw : RawCircuit) :
    TargetEmitterControllerGateBound.gateBlockUnit
        (TargetEmitterLedger.slotCapacity raw)
        (SourceParser.circuitCells raw).length
        (TargetEmitterProgramSemantics.headerResult
          (TargetEmitterControllerHeaderTrace.initialRuntime raw))
        raw.gates.length ≤
      phaseUnit (encodeCircuit raw).length := by
  have footprint := gateMasterSize_le_master raw
  have primitive :=
    Nat.add_le_add_right (primitive_mono footprint) 1
  have programBound :
      TargetEmitterControllerGateBound.gateProgramLimit ≤
        TargetEmitterControllerCompletionTrace.normalizationProgramLimit := by
    unfold TargetEmitterControllerGateBound.gateProgramLimit
      TargetEmitterControllerCompletionTrace.normalizationProgramLimit
    decide
  have product := Nat.mul_le_mul programBound primitive
  unfold TargetEmitterControllerGateBound.gateBlockUnit phaseUnit
  exact product

private theorem gateCaptureUnit_le_phaseUnit (raw : RawCircuit) :
    TargetEmitterControllerGateBound.gateCaptureUnit
        (TargetEmitterLedger.slotCapacity raw)
        (SourceParser.circuitCells raw).length ≤
      phaseUnit (encodeCircuit raw).length := by
  have capacity := capacity_le_data raw
  have source := cells_length_le_data raw
  have positive := one_le_data (encodeCircuit raw).length
  have sizeBound :
      TargetEmitterLedger.slotCapacity raw +
          (SourceParser.circuitCells raw).length + 1 ≤
        masterMajorant (encodeCircuit raw).length := by
    unfold masterMajorant
    omega
  have square := Nat.mul_le_mul sizeBound sizeBound
  have coefficient :
      15 *
          (masterMajorant (encodeCircuit raw).length *
            masterMajorant (encodeCircuit raw).length) ≤
        100 *
          (masterMajorant (encodeCircuit raw).length *
            masterMajorant (encodeCircuit raw).length) :=
    Nat.mul_le_mul_right _ (by decide)
  rw [TargetEmitterControllerGateBound.gateCaptureUnit,
    TargetEmitterControllerNormalizationBound.sourceCaptureTimePolynomial_eval]
  have bounded :
      15 *
          ((TargetEmitterLedger.slotCapacity raw +
              (SourceParser.circuitCells raw).length + 1) *
            (TargetEmitterLedger.slotCapacity raw +
              (SourceParser.circuitCells raw).length + 1)) ≤
        TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
            (masterMajorant (encodeCircuit raw).length) + 1 := by
    have scaled := Nat.mul_le_mul_left 15 square
    unfold TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
    omega
  exact Nat.le_trans (by
      simpa only [Nat.mul_assoc] using bounded)
    (primitive_add_one_le_phaseUnit _)

private theorem gateRestoreUnit_le_phaseUnit (raw : RawCircuit) :
    TargetEmitterControllerGateBound.gateRestoreUnit
        (SourceParser.circuitCells raw).length ≤
      phaseUnit (encodeCircuit raw).length := by
  have source := cells_length_le_data raw
  have positive := one_le_data (encodeCircuit raw).length
  have restore :
      (SourceParser.circuitCells raw).length + 2 ≤
        masterMajorant (encodeCircuit raw).length := by
    unfold masterMajorant
    omega
  unfold TargetEmitterControllerGateBound.gateRestoreUnit
  exact Nat.le_trans restore (master_le_phaseUnit _)

private theorem gateListUniformUnit_le_eight_phaseUnits
    (raw : RawCircuit) :
    TargetEmitterControllerGateListTrace.gateListUniformUnit raw ≤
      8 * phaseUnit (encodeCircuit raw).length := by
  have capture := gateCaptureUnit_le_phaseUnit raw
  have block := gateBlockUnit_le_phaseUnit raw
  have restore := gateRestoreUnit_le_phaseUnit raw
  have seven :
      7 ≤ phaseUnit (encodeCircuit raw).length := by
    have primitive :=
      primitive_add_one_le_phaseUnit (encodeCircuit raw).length
    unfold TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope at primitive
    omega
  unfold TargetEmitterControllerGateListTrace.gateListUniformUnit
    TargetEmitterControllerGateBound.gateUniformUnit
  omega

private theorem headerBlockEnvelope_le_phaseUnit (raw : RawCircuit) :
    TargetEmitterControllerHeaderBound.headerBlockEnvelope raw ≤
      phaseUnit (encodeCircuit raw).length := by
  unfold TargetEmitterControllerHeaderBound.headerBlockEnvelope
  exact programEnvelope_le_phaseUnit raw
    (SourceParser.circuitCells raw)
    (TargetEmitterControllerHeaderTrace.initialRuntime raw)
    TargetEmitterController.Plan.header
    (cells_length_le_data raw)
    (by simp [TargetEmitterControllerHeaderTrace.initialRuntime])
    (by simp [TargetEmitterControllerHeaderTrace.initialRuntime,
      TargetEmitterRuntimeProgramBound.checkCells,
      TargetEmitterCheckStack.recordsWord])
    (by
      unfold TargetEmitterControllerCompletionTrace.normalizationProgramLimit
      decide)

private theorem headerInitializeBridge_le_phaseUnit (raw : RawCircuit) :
    TargetEmitterCheckStack.Initialize.workSteps
          (TargetEmitterLedger.slotCapacity raw) + 1 ≤
      phaseUnit (encodeCircuit raw).length := by
  have capacity := capacity_le_sixtyFour_shifted raw
  have positive := shifted_positive (encodeCircuit raw).length
  have linear :
      TargetEmitterCheckStack.Initialize.workSteps
          (TargetEmitterLedger.slotCapacity raw) + 1 ≤
        931 * shiftedSize (encodeCircuit raw).length := by
    unfold TargetEmitterCheckStack.Initialize.workSteps
    omega
  exact Nat.le_trans linear
    (Nat.le_trans
      (coefficient_linear_le_data _ 931 (by decide))
      (data_le_phaseUnit _))

private theorem headerNavigatorBridge_le_phaseUnit (raw : RawCircuit) :
    TargetEmitterNavigator.headerWorkSteps
          raw.inputCount raw.gates.length + 1 ≤
      phaseUnit (encodeCircuit raw).length := by
  have inputs :=
    Nat.le_trans
      (TargetEmitterCapacity.inputCount_le_circuitCells_length raw)
      (cells_le_shifted raw)
  have gates := gates_le_shifted raw
  have positive := shifted_positive (encodeCircuit raw).length
  have linear :
      TargetEmitterNavigator.headerWorkSteps
          raw.inputCount raw.gates.length + 1 ≤
        12 * shiftedSize (encodeCircuit raw).length := by
    unfold TargetEmitterNavigator.headerWorkSteps
    omega
  exact Nat.le_trans linear
    (Nat.le_trans
      (coefficient_linear_le_data _ 12 (by decide))
      (data_le_phaseUnit _))

private theorem stackHeaderNavigatorEnvelope_le_three_phaseUnits
    (raw : RawCircuit) :
    TargetEmitterControllerHeaderBound.stackHeaderNavigatorEnvelope raw ≤
      3 * phaseUnit (encodeCircuit raw).length := by
  have initializeBound := headerInitializeBridge_le_phaseUnit raw
  have block := headerBlockEnvelope_le_phaseUnit raw
  have navigator := headerNavigatorBridge_le_phaseUnit raw
  unfold TargetEmitterControllerHeaderBound.stackHeaderNavigatorEnvelope
    TargetEmitterControllerHeaderBound.stackHeaderEnvelope
  omega

private theorem stackGateListUniformEnvelope_le_twelve_phaseUnits
    (raw : RawCircuit) :
    TargetEmitterControllerGateListTrace.stackGateListUniformEnvelope raw ≤
      12 * shiftedSize (encodeCircuit raw).length *
        phaseUnit (encodeCircuit raw).length := by
  have header :=
    stackHeaderNavigatorEnvelope_le_three_phaseUnits raw
  have unit := gateListUniformUnit_le_eight_phaseUnits raw
  have gates := gates_le_shifted raw
  have traversal := Nat.mul_le_mul gates unit
  have traversal' :
      raw.gates.length *
          TargetEmitterControllerGateListTrace.gateListUniformUnit raw ≤
        8 * shiftedSize (encodeCircuit raw).length *
          phaseUnit (encodeCircuit raw).length := by
    calc
      raw.gates.length *
          TargetEmitterControllerGateListTrace.gateListUniformUnit raw ≤
        shiftedSize (encodeCircuit raw).length *
          (8 * phaseUnit (encodeCircuit raw).length) := traversal
      _ = 8 * shiftedSize (encodeCircuit raw).length *
          phaseUnit (encodeCircuit raw).length := by ac_rfl
  have sizePositive := shifted_positive (encodeCircuit raw).length
  have phaseLift :
      phaseUnit (encodeCircuit raw).length ≤
        shiftedSize (encodeCircuit raw).length *
          phaseUnit (encodeCircuit raw).length := by
    simpa only [Nat.one_mul] using
      Nat.mul_le_mul_right
        (phaseUnit (encodeCircuit raw).length) sizePositive
  have three :
      3 ≤ phaseUnit (encodeCircuit raw).length := by
    have primitive :=
      primitive_add_one_le_phaseUnit (encodeCircuit raw).length
    unfold TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope at primitive
    omega
  have headerBridge :
      TargetEmitterControllerHeaderBound.stackHeaderNavigatorEnvelope raw +
          3 ≤
        4 * phaseUnit (encodeCircuit raw).length := by
    omega
  have headerLift :
      TargetEmitterControllerHeaderBound.stackHeaderNavigatorEnvelope raw +
          3 ≤
        4 *
          (shiftedSize (encodeCircuit raw).length *
            phaseUnit (encodeCircuit raw).length) := by
    exact Nat.le_trans headerBridge
      (Nat.mul_le_mul_left 4 phaseLift)
  have traversalCommon :
      raw.gates.length *
          TargetEmitterControllerGateListTrace.gateListUniformUnit raw ≤
        8 *
          (shiftedSize (encodeCircuit raw).length *
            phaseUnit (encodeCircuit raw).length) := by
    simpa only [Nat.mul_assoc] using traversal'
  have combined :=
    Nat.add_le_add headerLift traversalCommon
  unfold TargetEmitterControllerGateListTrace.stackGateListUniformEnvelope
    TargetEmitterControllerGateListTrace.gateListUniformEnvelope
  have commonBound :
      TargetEmitterControllerHeaderBound.stackHeaderNavigatorEnvelope raw +
            3 +
          raw.gates.length *
            TargetEmitterControllerGateListTrace.gateListUniformUnit raw ≤
        12 *
          (shiftedSize (encodeCircuit raw).length *
            phaseUnit (encodeCircuit raw).length) :=
    Nat.le_trans combined (by omega)
  simpa only [Nat.mul_assoc] using commonBound

private theorem appendGateListResults_nonempty_scratch
    (gate : RawGate) (rest : List RawGate) (runtime : Runtime) :
    (TargetEmitterSemanticSchedule.appendGateListResults
      (gate :: rest) runtime).scratch = 0 := by
  induction rest generalizing gate runtime with
  | nil => rfl
  | cons next tail inductionHypothesis =>
      simp only [TargetEmitterSemanticSchedule.appendGateListResults]
      exact inductionHypothesis next
        (TargetEmitterSemanticSchedule.appendGateResult gate runtime)

private theorem gateListRuntime_scratch_le_data (raw : RawCircuit) :
    (TargetEmitterControllerGateListTrace.gateListRuntime raw).scratch ≤
      dataMajorant (encodeCircuit raw).length := by
  have capacity := capacity_le_data raw
  have reserve :=
    TargetEmitterCapacity.baseline_add_sixtyFour_le_slotCapacity raw
  cases raw with
  | mk inputs gates output =>
      cases gates with
      | nil =>
          simp [TargetEmitterControllerGateListTrace.gateListRuntime,
            TargetEmitterSemanticSchedule.appendGateListResults,
            TargetEmitterControllerHeaderTrace.initialRuntime,
            TargetEmitterProgramSemantics.headerResult_scratch,
            TargetEmitterLedger.ledgerRegisters] at *
          omega
      | cons gate rest =>
          have zero :=
            appendGateListResults_nonempty_scratch gate rest
              (TargetEmitterProgramSemantics.headerResult
                (TargetEmitterControllerHeaderTrace.initialRuntime
                  { inputCount := inputs
                    gates := gate :: rest
                    output := output }))
          change
            (TargetEmitterSemanticSchedule.appendGateListResults
              (gate :: rest)
              (TargetEmitterProgramSemantics.headerResult
                (TargetEmitterControllerHeaderTrace.initialRuntime
                  { inputCount := inputs
                    gates := gate :: rest
                    output := output }))).scratch ≤
              dataMajorant
                (encodeCircuit
                  { inputCount := inputs
                    gates := gate :: rest
                    output := output }).length
          rw [zero]
          exact Nat.zero_le _

private theorem sourceCapturePolynomial_data_le_phaseUnit
    (raw : RawCircuit) :
    TargetEmitterControllerNormalizationBound.sourceCaptureTimePolynomial.eval
        (dataMajorant (encodeCircuit raw).length) ≤
      phaseUnit (encodeCircuit raw).length := by
  have positive := one_le_data (encodeCircuit raw).length
  have size :
      dataMajorant (encodeCircuit raw).length + 1 ≤
        masterMajorant (encodeCircuit raw).length := by
    unfold masterMajorant
    omega
  have square := Nat.mul_le_mul size size
  have scaled := Nat.mul_le_mul_left 15 square
  have coefficient :
      15 *
          (masterMajorant (encodeCircuit raw).length *
            masterMajorant (encodeCircuit raw).length) ≤
        100 *
          (masterMajorant (encodeCircuit raw).length *
            masterMajorant (encodeCircuit raw).length) :=
    Nat.mul_le_mul_right _ (by decide)
  rw [
    TargetEmitterControllerNormalizationBound.sourceCaptureTimePolynomial_eval]
  have primitive :
      15 *
          ((dataMajorant (encodeCircuit raw).length + 1) *
            (dataMajorant (encodeCircuit raw).length + 1)) ≤
        TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
            (masterMajorant (encodeCircuit raw).length) + 1 := by
    unfold TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
    omega
  exact Nat.le_trans (by
      simpa only [Nat.mul_assoc] using primitive)
    (primitive_add_one_le_phaseUnit _)

private theorem outputSourceCaptureEnvelope_le_phaseUnit
    (raw : RawCircuit) :
    TargetEmitterControllerNormalizationBound.sourceCaptureEnvelope
        (TargetEmitterControllerGateListTrace.outputCrossedCells raw).length
        (TargetEmitterControllerGateListTrace.gateListRuntime raw).scratch
        (TargetEmitterControllerGateTrace.sourceValue raw.output) ≤
      phaseUnit (encodeCircuit raw).length := by
  have bounded :=
    TargetEmitterControllerNormalizationBound.sourceCaptureEnvelope_le_timePolynomial
      (outputCrossed_length_le_data raw)
      (gateListRuntime_scratch_le_data raw)
      (outputValue_le_data raw)
  exact Nat.le_trans bounded
    (sourceCapturePolynomial_data_le_phaseUnit raw)

private theorem physicalCapturedRuntime_data_le (raw : RawCircuit) :
    (TargetEmitterControllerCompletionTrace.physicalCapturedRuntime
          raw).targetTokens.length ≤
        dataMajorant (encodeCircuit raw).length ∧
      TargetEmitterRuntimeProgramBound.checkCells
          (TargetEmitterControllerCompletionTrace.physicalCapturedRuntime
            raw).checks ≤
        dataMajorant (encodeCircuit raw).length := by
  rcases gateListRuntime_data_le raw with ⟨target, checks⟩
  simpa [TargetEmitterControllerCompletionTrace.physicalCapturedRuntime,
    TargetEmitterControllerGateTrace.capturedRuntime] using
    And.intro target checks

private theorem inputNormalizationEnvelope_le_phaseUnit
    (raw : RawCircuit) :
    TargetEmitterControllerNormalizationBound.inputNormalizationEnvelope
        raw (TargetEmitterControllerCompletionTrace.markedSource raw)
        (TargetEmitterControllerCompletionTrace.physicalCapturedRuntime raw) ≤
      phaseUnit (encodeCircuit raw).length := by
  rcases physicalCapturedRuntime_data_le raw with ⟨target, checks⟩
  unfold
    TargetEmitterControllerNormalizationBound.inputNormalizationEnvelope
  exact programEnvelope_le_phaseUnit raw
    (TargetEmitterControllerCompletionTrace.markedSource raw)
    (TargetEmitterControllerCompletionTrace.physicalCapturedRuntime raw)
    TargetEmitterController.Plan.inputNormalization
    (markedSource_length_le_data raw)
    (by omega)
    (by omega)
    (by
      unfold TargetEmitterControllerCompletionTrace.normalizationProgramLimit
      decide)

private theorem constantNormalizationEnvelope_le_phaseUnit
    (raw : RawCircuit) (value : Bool) :
    TargetEmitterControllerNormalizationBound.constantNormalizationEnvelope
        raw (TargetEmitterControllerCompletionTrace.markedSource raw)
        (TargetEmitterControllerCompletionTrace.physicalCapturedRuntime raw)
        value ≤
      phaseUnit (encodeCircuit raw).length := by
  rcases physicalCapturedRuntime_data_le raw with ⟨target, checks⟩
  unfold
    TargetEmitterControllerNormalizationBound.constantNormalizationEnvelope
  exact programEnvelope_le_phaseUnit raw
    (TargetEmitterControllerCompletionTrace.markedSource raw)
    (TargetEmitterControllerCompletionTrace.physicalCapturedRuntime raw)
    (TargetEmitterController.Plan.constantNormalization value)
    (markedSource_length_le_data raw)
    (by omega)
    (by omega)
    (by
      cases value <;>
        unfold
          TargetEmitterControllerCompletionTrace.normalizationProgramLimit <;>
        decide)

private theorem outputGateResetEnvelope_le_phaseUnit
    (raw : RawCircuit) :
    TargetEmitterControllerNormalizationBound.outputGateResetEnvelope
        raw (TargetEmitterControllerCompletionTrace.markedSource raw)
        (TargetEmitterControllerCompletionTrace.physicalCapturedRuntime raw) ≤
      phaseUnit (encodeCircuit raw).length := by
  rcases physicalCapturedRuntime_data_le raw with ⟨target, checks⟩
  unfold TargetEmitterControllerNormalizationBound.outputGateResetEnvelope
  exact programEnvelope_le_phaseUnit raw
    (TargetEmitterControllerCompletionTrace.markedSource raw)
    (TargetEmitterControllerCompletionTrace.physicalCapturedRuntime raw)
    TargetEmitterController.Plan.outputGateReset
    (markedSource_length_le_data raw)
    (by omega)
    (by omega)
    (by
      unfold TargetEmitterControllerCompletionTrace.normalizationProgramLimit
      decide)

private theorem outputNormalizationUniformEnvelope_le_two_phaseUnits
    (raw : RawCircuit) :
    TargetEmitterControllerCompletionTrace.outputNormalizationUniformEnvelope
        raw ≤
      2 * phaseUnit (encodeCircuit raw).length := by
  have captureRaw := outputSourceCaptureEnvelope_le_phaseUnit raw
  cases outputEq : raw.output with
  | input index =>
      have capture :
          TargetEmitterControllerNormalizationBound.sourceCaptureEnvelope
              (TargetEmitterControllerGateListTrace.outputCrossedCells
                raw).length
              (TargetEmitterControllerGateListTrace.gateListRuntime raw).scratch
              index ≤
            phaseUnit (encodeCircuit raw).length := by
        simpa only [outputEq,
          TargetEmitterControllerGateTrace.sourceValue] using captureRaw
      have block := inputNormalizationEnvelope_le_phaseUnit raw
      rw [
        TargetEmitterControllerCompletionTrace.outputNormalizationUniformEnvelope,
        outputEq]
      have added := Nat.add_le_add capture block
      change
        TargetEmitterControllerNormalizationBound.sourceCaptureEnvelope
              (TargetEmitterControllerGateListTrace.outputCrossedCells
                raw).length
              (TargetEmitterControllerGateListTrace.gateListRuntime raw).scratch
              index +
            TargetEmitterControllerNormalizationBound.inputNormalizationEnvelope
              raw (TargetEmitterControllerCompletionTrace.markedSource raw)
              (TargetEmitterControllerCompletionTrace.physicalCapturedRuntime
                raw) ≤
          2 * phaseUnit (encodeCircuit raw).length
      simpa only [Nat.two_mul] using added
  | gate index =>
      have capture :
          TargetEmitterControllerNormalizationBound.sourceCaptureEnvelope
              (TargetEmitterControllerGateListTrace.outputCrossedCells
                raw).length
              (TargetEmitterControllerGateListTrace.gateListRuntime raw).scratch
              index ≤
            phaseUnit (encodeCircuit raw).length := by
        simpa only [outputEq,
          TargetEmitterControllerGateTrace.sourceValue] using captureRaw
      have block := outputGateResetEnvelope_le_phaseUnit raw
      rw [
        TargetEmitterControllerCompletionTrace.outputNormalizationUniformEnvelope,
        outputEq]
      have added := Nat.add_le_add capture block
      change
        TargetEmitterControllerNormalizationBound.sourceCaptureEnvelope
              (TargetEmitterControllerGateListTrace.outputCrossedCells
                raw).length
              (TargetEmitterControllerGateListTrace.gateListRuntime raw).scratch
              index +
            TargetEmitterControllerNormalizationBound.outputGateResetEnvelope
              raw (TargetEmitterControllerCompletionTrace.markedSource raw)
              (TargetEmitterControllerCompletionTrace.physicalCapturedRuntime
                raw) ≤
          2 * phaseUnit (encodeCircuit raw).length
      simpa only [Nat.two_mul] using added
  | constant value =>
      have capture :
          TargetEmitterControllerNormalizationBound.sourceCaptureEnvelope
              (TargetEmitterControllerGateListTrace.outputCrossedCells
                raw).length
              (TargetEmitterControllerGateListTrace.gateListRuntime raw).scratch
              0 ≤
            phaseUnit (encodeCircuit raw).length := by
        cases value <;>
          simpa only [outputEq,
            TargetEmitterControllerGateTrace.sourceValue] using captureRaw
      have block := constantNormalizationEnvelope_le_phaseUnit raw value
      rw [
        TargetEmitterControllerCompletionTrace.outputNormalizationUniformEnvelope,
        outputEq]
      have added := Nat.add_le_add capture block
      change
        TargetEmitterControllerNormalizationBound.sourceCaptureEnvelope
              (TargetEmitterControllerGateListTrace.outputCrossedCells
                raw).length
              (TargetEmitterControllerGateListTrace.gateListRuntime raw).scratch
              0 +
            TargetEmitterControllerNormalizationBound.constantNormalizationEnvelope
              raw (TargetEmitterControllerCompletionTrace.markedSource raw)
              (TargetEmitterControllerCompletionTrace.physicalCapturedRuntime
                raw) value ≤
          2 * phaseUnit (encodeCircuit raw).length
      simpa only [Nat.two_mul] using added

private theorem prefixBlockBudget_le_three_shifted (raw : RawCircuit) :
    (TargetEmitterSemanticCompletion.checkCoordinates raw).length + 1 ≤
      3 * shiftedSize (encodeCircuit raw).length := by
  have checks := checkCount_le_two_shifted raw
  have positive := shifted_positive (encodeCircuit raw).length
  omega

private theorem prefixBlockGrowth_le_fourThousandOneHundredSixty_shifted
    (raw : RawCircuit) :
    TargetEmitterControllerPrefixBound.prefixBlockGrowth
        (TargetEmitterLedger.slotCapacity raw) ≤
      4160 * shiftedSize (encodeCircuit raw).length := by
  have capacity := capacity_add_one_le_sixtyFive_shifted raw
  have scaled := Nat.mul_le_mul_left 64 capacity
  unfold TargetEmitterControllerPrefixBound.prefixBlockGrowth
    TargetEmitterControllerPrefixBound.prefixProgramLimit
  calc
    64 * (TargetEmitterLedger.slotCapacity raw + 1) ≤
        64 * (65 * shiftedSize (encodeCircuit raw).length) := scaled
    _ = 4160 * shiftedSize (encodeCircuit raw).length := by
      rw [← Nat.mul_assoc, show 64 * 65 = 4160 by omega]

private theorem prefixGrowthBudget_le_data (raw : RawCircuit) :
    ((TargetEmitterSemanticCompletion.checkCoordinates raw).length + 1) *
        TargetEmitterControllerPrefixBound.prefixBlockGrowth
          (TargetEmitterLedger.slotCapacity raw) ≤
      dataMajorant (encodeCircuit raw).length := by
  have budget := prefixBlockBudget_le_three_shifted raw
  have growth :=
    prefixBlockGrowth_le_fourThousandOneHundredSixty_shifted raw
  have product := Nat.mul_le_mul budget growth
  calc
    ((TargetEmitterSemanticCompletion.checkCoordinates raw).length + 1) *
          TargetEmitterControllerPrefixBound.prefixBlockGrowth
            (TargetEmitterLedger.slotCapacity raw) ≤
        (3 * shiftedSize (encodeCircuit raw).length) *
          (4160 * shiftedSize (encodeCircuit raw).length) := product
    _ = 12480 * shiftedSize (encodeCircuit raw).length *
          shiftedSize (encodeCircuit raw).length := by
      calc
        (3 * shiftedSize (encodeCircuit raw).length) *
            (4160 * shiftedSize (encodeCircuit raw).length) =
          (3 * 4160) * shiftedSize (encodeCircuit raw).length *
            shiftedSize (encodeCircuit raw).length := by ac_rfl
        _ = 12480 * shiftedSize (encodeCircuit raw).length *
            shiftedSize (encodeCircuit raw).length := by
          rw [show 3 * 4160 = 12480 by omega]
    _ ≤ dataMajorant (encodeCircuit raw).length :=
      coefficient_square_le_data _ 12480 (by decide)

private theorem prefixTargetLimit_le_three_data (raw : RawCircuit) :
    TargetEmitterControllerPrefixBound.prefixTargetLimit
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterSemanticNormalization.normalizationRuntime raw)
        ((TargetEmitterSemanticCompletion.checkCoordinates raw).length + 1) ≤
      3 * dataMajorant (encodeCircuit raw).length := by
  rcases normalizationRuntime_data_le raw with ⟨target, _⟩
  have growth := prefixGrowthBudget_le_data raw
  unfold TargetEmitterControllerPrefixBound.prefixTargetLimit
  omega

private theorem prefixCheckLimit_le_three_data (raw : RawCircuit) :
    TargetEmitterControllerPrefixBound.prefixCheckLimit
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterSemanticNormalization.normalizationRuntime raw)
        ((TargetEmitterSemanticCompletion.checkCoordinates raw).length + 1) ≤
      3 * dataMajorant (encodeCircuit raw).length := by
  rcases normalizationRuntime_data_le raw with ⟨_, checks⟩
  have growth := prefixGrowthBudget_le_data raw
  unfold TargetEmitterControllerPrefixBound.prefixCheckLimit
  omega

private theorem prefixMasterSize_le_master (raw : RawCircuit) :
    TargetEmitterControllerPrefixBound.prefixMasterSize
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterControllerCompletionTrace.markedSource raw)
        (TargetEmitterSemanticNormalization.normalizationRuntime raw)
        ((TargetEmitterSemanticCompletion.checkCoordinates raw).length + 1) ≤
      masterMajorant (encodeCircuit raw).length := by
  unfold TargetEmitterControllerPrefixBound.prefixMasterSize
  exact footprintParts_le_master raw
    (TargetEmitterControllerCompletionTrace.markedSource raw).length
    (TargetEmitterControllerPrefixBound.prefixTargetLimit
      (TargetEmitterLedger.slotCapacity raw)
      (TargetEmitterSemanticNormalization.normalizationRuntime raw)
      ((TargetEmitterSemanticCompletion.checkCoordinates raw).length + 1))
    (TargetEmitterControllerPrefixBound.prefixCheckLimit
      (TargetEmitterLedger.slotCapacity raw)
      (TargetEmitterSemanticNormalization.normalizationRuntime raw)
      ((TargetEmitterSemanticCompletion.checkCoordinates raw).length + 1))
    TargetEmitterControllerPrefixBound.prefixProgramLimit
    (markedSource_length_le_data raw)
    (prefixTargetLimit_le_three_data raw)
    (prefixCheckLimit_le_three_data raw)
    (by
      unfold TargetEmitterControllerPrefixBound.prefixProgramLimit
        TargetEmitterControllerCompletionTrace.normalizationProgramLimit
      decide)

private theorem prefixBlockUnit_le_phaseUnit (raw : RawCircuit) :
    TargetEmitterControllerPrefixBound.prefixBlockUnit
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterControllerCompletionTrace.markedSource raw)
        (TargetEmitterSemanticNormalization.normalizationRuntime raw)
        ((TargetEmitterSemanticCompletion.checkCoordinates raw).length + 1) ≤
      phaseUnit (encodeCircuit raw).length := by
  have footprint := prefixMasterSize_le_master raw
  have primitive :=
    Nat.add_le_add_right (primitive_mono footprint) 1
  have programBound :
      TargetEmitterControllerPrefixBound.prefixProgramLimit ≤
        TargetEmitterControllerCompletionTrace.normalizationProgramLimit := by
    unfold TargetEmitterControllerPrefixBound.prefixProgramLimit
      TargetEmitterControllerCompletionTrace.normalizationProgramLimit
    decide
  have product := Nat.mul_le_mul programBound primitive
  unfold TargetEmitterControllerPrefixBound.prefixBlockUnit phaseUnit
  exact product

private theorem fourteenCapacity_le_data (raw : RawCircuit) :
    14 * TargetEmitterLedger.slotCapacity raw ≤
      dataMajorant (encodeCircuit raw).length := by
  have capacity := capacity_le_sixtyFour_shifted raw
  have scaled := Nat.mul_le_mul_left 14 capacity
  have bound :=
    coefficient_linear_le_data
      (encodeCircuit raw).length 896 (by decide)
  calc
    14 * TargetEmitterLedger.slotCapacity raw ≤
        14 * (64 * shiftedSize (encodeCircuit raw).length) := scaled
    _ = 896 * shiftedSize (encodeCircuit raw).length := by
      rw [← Nat.mul_assoc, show 14 * 64 = 896 by omega]
    _ ≤ dataMajorant (encodeCircuit raw).length := bound

private theorem twoCheckCapacity_le_data (raw : RawCircuit) :
    2 *
        ((TargetEmitterSemanticCompletion.checkCoordinates raw).length *
          TargetEmitterLedger.slotCapacity raw) ≤
      dataMajorant (encodeCircuit raw).length := by
  have checks := checkCount_le_two_shifted raw
  have capacity := capacity_le_sixtyFour_shifted raw
  have product := Nat.mul_le_mul checks capacity
  have scaled := Nat.mul_le_mul_left 2 product
  calc
    2 *
        ((TargetEmitterSemanticCompletion.checkCoordinates raw).length *
          TargetEmitterLedger.slotCapacity raw) ≤
      2 *
        ((2 * shiftedSize (encodeCircuit raw).length) *
          (64 * shiftedSize (encodeCircuit raw).length)) := scaled
    _ = 256 * shiftedSize (encodeCircuit raw).length *
          shiftedSize (encodeCircuit raw).length := by
      calc
        2 *
            ((2 * shiftedSize (encodeCircuit raw).length) *
              (64 * shiftedSize (encodeCircuit raw).length)) =
          (2 * 2 * 64) * shiftedSize (encodeCircuit raw).length *
            shiftedSize (encodeCircuit raw).length := by ac_rfl
        _ = 256 * shiftedSize (encodeCircuit raw).length *
            shiftedSize (encodeCircuit raw).length := by
          rw [show 2 * 2 * 64 = 256 by omega]
    _ ≤ dataMajorant (encodeCircuit raw).length :=
      coefficient_square_le_data _ 256 (by decide)

private theorem twoCapacity_le_data (raw : RawCircuit) :
    2 * TargetEmitterLedger.slotCapacity raw ≤
      dataMajorant (encodeCircuit raw).length := by
  have capacity := capacity_le_sixtyFour_shifted raw
  have scaled := Nat.mul_le_mul_left 2 capacity
  have bound :=
    coefficient_linear_le_data
      (encodeCircuit raw).length 128 (by decide)
  calc
    2 * TargetEmitterLedger.slotCapacity raw ≤
        2 * (64 * shiftedSize (encodeCircuit raw).length) := scaled
    _ = 128 * shiftedSize (encodeCircuit raw).length := by
      rw [← Nat.mul_assoc, show 2 * 64 = 128 by omega]
    _ ≤ dataMajorant (encodeCircuit raw).length := bound

private theorem prefixPopUnit_le_phaseUnit (raw : RawCircuit) :
    TargetEmitterControllerPrefixBound.prefixPopUnit
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterSemanticCompletion.checkCoordinates raw).length ≤
      phaseUnit (encodeCircuit raw).length := by
  have fourteen := fourteenCapacity_le_data raw
  have twoChecks := twoCheckCapacity_le_data raw
  have capacity := capacity_le_data raw
  have twoCapacity := twoCapacity_le_data raw
  have positive := one_le_data (encodeCircuit raw).length
  have thousand :
      1000 ≤ dataMajorant (encodeCircuit raw).length := by
    have unitPositive :
        1 ≤ squareUnit (encodeCircuit raw).length := by
      exact Nat.le_trans
        (by
          have sizePositive :=
            shifted_positive (encodeCircuit raw).length
          exact Nat.mul_le_mul sizePositive sizePositive)
        (by
          have coefficient :=
            coefficient_square_le_unit
              (encodeCircuit raw).length 1 (by decide)
          simpa only [Nat.one_mul] using coefficient)
    unfold dataMajorant
    have scaled := Nat.mul_le_mul_left 1000 unitPositive
    simpa only [Nat.mul_one] using scaled
  have thirtyNine :
      39 ≤ dataMajorant (encodeCircuit raw).length := by
    omega
  have fortyThree :
      43 ≤ dataMajorant (encodeCircuit raw).length := by
    omega
  have outer :
      14 * TargetEmitterLedger.slotCapacity raw +
              2 *
                ((TargetEmitterSemanticCompletion.checkCoordinates raw).length *
                  TargetEmitterLedger.slotCapacity raw) +
            TargetEmitterLedger.slotCapacity raw + 39 ≤
        masterMajorant (encodeCircuit raw).length := by
    unfold masterMajorant
    omega
  have inner :
      14 * TargetEmitterLedger.slotCapacity raw +
              2 *
                ((TargetEmitterSemanticCompletion.checkCoordinates raw).length *
                  TargetEmitterLedger.slotCapacity raw) +
            2 * TargetEmitterLedger.slotCapacity raw + 43 ≤
        masterMajorant (encodeCircuit raw).length := by
    unfold masterMajorant
    omega
  have capacityMaster :=
    Nat.le_trans capacity (data_le_master (encodeCircuit raw).length)
  have product := Nat.mul_le_mul capacityMaster inner
  have masterPositive := one_le_master (encodeCircuit raw).length
  have masterSquare :
      masterMajorant (encodeCircuit raw).length ≤
        masterMajorant (encodeCircuit raw).length *
          masterMajorant (encodeCircuit raw).length := by
    simpa using Nat.mul_le_mul_left
      (masterMajorant (encodeCircuit raw).length) masterPositive
  have pop :
      TargetEmitterControllerPrefixBound.prefixPopUnit
          (TargetEmitterLedger.slotCapacity raw)
          (TargetEmitterSemanticCompletion.checkCoordinates raw).length ≤
        masterMajorant (encodeCircuit raw).length +
          masterMajorant (encodeCircuit raw).length *
            masterMajorant (encodeCircuit raw).length := by
    unfold TargetEmitterControllerPrefixBound.prefixPopUnit
    exact Nat.add_le_add outer product
  have primitive :
      masterMajorant (encodeCircuit raw).length +
            masterMajorant (encodeCircuit raw).length *
              masterMajorant (encodeCircuit raw).length ≤
        TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
            (masterMajorant (encodeCircuit raw).length) + 1 := by
    unfold TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
    omega
  exact Nat.le_trans pop
    (Nat.le_trans primitive (primitive_add_one_le_phaseUnit _))

private theorem controllerPrefixUniformEnvelope_le_six_phaseUnits
    (raw : RawCircuit) :
    TargetEmitterControllerCompletionTrace.controllerPrefixUniformEnvelope
        raw ≤
      6 * shiftedSize (encodeCircuit raw).length *
        phaseUnit (encodeCircuit raw).length := by
  have budget := prefixBlockBudget_le_three_shifted raw
  have pop := prefixPopUnit_le_phaseUnit raw
  have block := prefixBlockUnit_le_phaseUnit raw
  have unit :
      TargetEmitterControllerPrefixBound.prefixPopUnit
            (TargetEmitterLedger.slotCapacity raw)
            (TargetEmitterSemanticCompletion.checkCoordinates raw).length +
          TargetEmitterControllerPrefixBound.prefixBlockUnit
            (TargetEmitterLedger.slotCapacity raw)
            (TargetEmitterControllerCompletionTrace.markedSource raw)
            (TargetEmitterSemanticNormalization.normalizationRuntime raw)
            ((TargetEmitterSemanticCompletion.checkCoordinates raw).length + 1) ≤
        2 * phaseUnit (encodeCircuit raw).length := by
    omega
  have product := Nat.mul_le_mul budget unit
  unfold
    TargetEmitterControllerCompletionTrace.controllerPrefixUniformEnvelope
    TargetEmitterControllerPrefixBound.prefixUniformEnvelope
  calc
    ((TargetEmitterSemanticCompletion.checkCoordinates raw).length + 1) *
          (TargetEmitterControllerPrefixBound.prefixPopUnit
              (TargetEmitterLedger.slotCapacity raw)
              (TargetEmitterSemanticCompletion.checkCoordinates raw).length +
            TargetEmitterControllerPrefixBound.prefixBlockUnit
              (TargetEmitterLedger.slotCapacity raw)
              (TargetEmitterControllerCompletionTrace.markedSource raw)
              (TargetEmitterSemanticNormalization.normalizationRuntime raw)
              ((TargetEmitterSemanticCompletion.checkCoordinates raw).length +
                1)) ≤
        (3 * shiftedSize (encodeCircuit raw).length) *
          (2 * phaseUnit (encodeCircuit raw).length) := product
    _ = 6 * shiftedSize (encodeCircuit raw).length *
        phaseUnit (encodeCircuit raw).length := by ac_rfl

private theorem outputCapacityProduct_le_data (raw : RawCircuit) :
    TargetEmitterLedger.slotCapacity raw *
        (TargetEmitterLedger.slotCapacity raw + 2) ≤
      dataMajorant (encodeCircuit raw).length := by
  have capacity := capacity_le_sixtyFour_shifted raw
  have positive := shifted_positive (encodeCircuit raw).length
  have second :
      TargetEmitterLedger.slotCapacity raw + 2 ≤
        66 * shiftedSize (encodeCircuit raw).length := by
    omega
  have product := Nat.mul_le_mul capacity second
  calc
    TargetEmitterLedger.slotCapacity raw *
          (TargetEmitterLedger.slotCapacity raw + 2) ≤
        (64 * shiftedSize (encodeCircuit raw).length) *
          (66 * shiftedSize (encodeCircuit raw).length) := product
    _ = 4224 * shiftedSize (encodeCircuit raw).length *
          shiftedSize (encodeCircuit raw).length := by
      calc
        (64 * shiftedSize (encodeCircuit raw).length) *
            (66 * shiftedSize (encodeCircuit raw).length) =
          (64 * 66) * shiftedSize (encodeCircuit raw).length *
            shiftedSize (encodeCircuit raw).length := by ac_rfl
        _ = 4224 * shiftedSize (encodeCircuit raw).length *
            shiftedSize (encodeCircuit raw).length := by
          rw [show 64 * 66 = 4224 by omega]
    _ ≤ dataMajorant (encodeCircuit raw).length :=
      coefficient_square_le_data _ 4224 (by decide)

private theorem outputTargetLimit_le_three_data (raw : RawCircuit) :
    TargetEmitterControllerOutputBound.outputTargetLimit
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterSemanticCompletion.finalRuntime raw) ≤
      3 * dataMajorant (encodeCircuit raw).length := by
  have target := finalRuntime_target_le_data raw
  have product := outputCapacityProduct_le_data raw
  have positive := one_le_data (encodeCircuit raw).length
  unfold TargetEmitterControllerOutputBound.outputTargetLimit
  omega

private theorem outputMasterSize_le_master (raw : RawCircuit) :
    TargetEmitterControllerOutputBound.outputMasterSize
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterControllerCompletionTrace.markedSource raw)
        (TargetEmitterSemanticCompletion.finalRuntime raw) ≤
      masterMajorant (encodeCircuit raw).length := by
  unfold TargetEmitterControllerOutputBound.outputMasterSize
  exact footprintParts_le_master raw
    (TargetEmitterControllerCompletionTrace.markedSource raw).length
    (TargetEmitterControllerOutputBound.outputTargetLimit
      (TargetEmitterLedger.slotCapacity raw)
      (TargetEmitterSemanticCompletion.finalRuntime raw))
    (TargetEmitterRuntimeProgramBound.checkCells
      (TargetEmitterSemanticCompletion.finalRuntime raw).checks)
    11
    (markedSource_length_le_data raw)
    (outputTargetLimit_le_three_data raw)
    (by
      have checks := finalRuntime_checks_le_data raw
      omega)
    (by
      unfold TargetEmitterControllerCompletionTrace.normalizationProgramLimit
      decide)

private theorem outputBlockUnit_le_phaseUnit (raw : RawCircuit) :
    TargetEmitterControllerOutputBound.outputBlockUnit
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterControllerCompletionTrace.markedSource raw)
        (TargetEmitterSemanticCompletion.finalRuntime raw) ≤
      phaseUnit (encodeCircuit raw).length := by
  have footprint := outputMasterSize_le_master raw
  have primitive :=
    Nat.add_le_add_right (primitive_mono footprint) 1
  have programBound :
      11 ≤
        TargetEmitterControllerCompletionTrace.normalizationProgramLimit := by
    unfold TargetEmitterControllerCompletionTrace.normalizationProgramLimit
    decide
  have product := Nat.mul_le_mul programBound primitive
  unfold TargetEmitterControllerOutputBound.outputBlockUnit phaseUnit
  exact product

private theorem outputCompareUnit_le_phaseUnit (raw : RawCircuit) :
    TargetEmitterControllerOutputBound.outputCompareUnit
        (TargetEmitterLedger.slotCapacity raw) ≤
      phaseUnit (encodeCircuit raw).length := by
  have capacity := capacity_add_one_le_sixtyFive_shifted raw
  have first := Nat.mul_le_mul_left 50 capacity
  have scaled := Nat.mul_le_mul first capacity
  have data :
      TargetEmitterControllerOutputBound.outputCompareUnit
          (TargetEmitterLedger.slotCapacity raw) ≤
        dataMajorant (encodeCircuit raw).length := by
    unfold TargetEmitterControllerOutputBound.outputCompareUnit
    calc
      50 * (TargetEmitterLedger.slotCapacity raw + 1) *
            (TargetEmitterLedger.slotCapacity raw + 1) ≤
        50 * (65 * shiftedSize (encodeCircuit raw).length) *
            (65 * shiftedSize (encodeCircuit raw).length) := scaled
      _ = 211250 * shiftedSize (encodeCircuit raw).length *
          shiftedSize (encodeCircuit raw).length := by
        calc
          50 * (65 * shiftedSize (encodeCircuit raw).length) *
                (65 * shiftedSize (encodeCircuit raw).length) =
            (50 * 65 * 65) *
              shiftedSize (encodeCircuit raw).length *
                shiftedSize (encodeCircuit raw).length := by ac_rfl
          _ = 211250 * shiftedSize (encodeCircuit raw).length *
              shiftedSize (encodeCircuit raw).length := by
            rw [show 50 * 65 * 65 = 211250 by omega]
      _ ≤ dataMajorant (encodeCircuit raw).length :=
        coefficient_square_le_data _ 211250 (by decide)
  exact Nat.le_trans data (data_le_phaseUnit _)

private theorem outputFinalizer_le_phaseUnit (raw : RawCircuit) :
    TargetEmitterControllerOutputTrace.finalizerPathSteps
        (TargetEmitterControllerCompletionTrace.markedSource raw) ≤
      phaseUnit (encodeCircuit raw).length := by
  have source := markedSource_length_le_data raw
  have positive := one_le_data (encodeCircuit raw).length
  have master :
      (TargetEmitterControllerCompletionTrace.markedSource raw).length + 2 ≤
        masterMajorant (encodeCircuit raw).length := by
    unfold masterMajorant
    omega
  unfold TargetEmitterControllerOutputTrace.finalizerPathSteps
    TargetEmitterCursorFinalizer.workSteps
  exact Nat.le_trans master (master_le_phaseUnit _)

private theorem finalRuntime_baseline_add_one_le_sixtyFive_shifted
    (raw : RawCircuit) :
    (TargetEmitterSemanticCompletion.finalRuntime
          raw).registers.baseline + 1 ≤
      65 * shiftedSize (encodeCircuit raw).length := by
  have range :=
    TargetEmitterControllerCompletionTrace.finalRuntime_range raw
  have baseline :
      (TargetEmitterSemanticCompletion.finalRuntime
          raw).registers.baseline ≤
        TargetEmitterLedger.slotCapacity raw := by
    rw [range.baseline_eq]
    exact TargetEmitterLedger.baselineValue_le_slotCapacity raw
  have capacity := capacity_le_sixtyFour_shifted raw
  have positive := shifted_positive (encodeCircuit raw).length
  omega

private theorem controllerOutputUniformEnvelope_le_oneHundredThirtyTwo_phaseUnits
    (raw : RawCircuit) :
    TargetEmitterControllerCompletionTrace.controllerOutputUniformEnvelope
        raw ≤
      132 * shiftedSize (encodeCircuit raw).length *
        phaseUnit (encodeCircuit raw).length := by
  have block := outputBlockUnit_le_phaseUnit raw
  have compare := outputCompareUnit_le_phaseUnit raw
  have finalizer := outputFinalizer_le_phaseUnit raw
  have count :=
    finalRuntime_baseline_add_one_le_sixtyFive_shifted raw
  have loopUnit :
      TargetEmitterControllerOutputBound.outputCompareUnit
            (TargetEmitterLedger.slotCapacity raw) +
          TargetEmitterControllerOutputBound.outputBlockUnit
            (TargetEmitterLedger.slotCapacity raw)
            (TargetEmitterControllerCompletionTrace.markedSource raw)
            (TargetEmitterSemanticCompletion.finalRuntime raw) ≤
        2 * phaseUnit (encodeCircuit raw).length := by
    omega
  have loop := Nat.mul_le_mul count loopUnit
  have loopCommon :
      ((TargetEmitterSemanticCompletion.finalRuntime
            raw).registers.baseline + 1) *
          (TargetEmitterControllerOutputBound.outputCompareUnit
              (TargetEmitterLedger.slotCapacity raw) +
            TargetEmitterControllerOutputBound.outputBlockUnit
              (TargetEmitterLedger.slotCapacity raw)
              (TargetEmitterControllerCompletionTrace.markedSource raw)
              (TargetEmitterSemanticCompletion.finalRuntime raw)) ≤
        130 *
          (shiftedSize (encodeCircuit raw).length *
            phaseUnit (encodeCircuit raw).length) := by
    calc
      ((TargetEmitterSemanticCompletion.finalRuntime
            raw).registers.baseline + 1) *
          (TargetEmitterControllerOutputBound.outputCompareUnit
              (TargetEmitterLedger.slotCapacity raw) +
            TargetEmitterControllerOutputBound.outputBlockUnit
              (TargetEmitterLedger.slotCapacity raw)
              (TargetEmitterControllerCompletionTrace.markedSource raw)
              (TargetEmitterSemanticCompletion.finalRuntime raw)) ≤
        (65 * shiftedSize (encodeCircuit raw).length) *
          (2 * phaseUnit (encodeCircuit raw).length) := loop
      _ = 130 *
          (shiftedSize (encodeCircuit raw).length *
            phaseUnit (encodeCircuit raw).length) := by ac_rfl
  have sizePositive := shifted_positive (encodeCircuit raw).length
  have phaseLift :
      phaseUnit (encodeCircuit raw).length ≤
        shiftedSize (encodeCircuit raw).length *
          phaseUnit (encodeCircuit raw).length := by
    simpa only [Nat.one_mul] using
      Nat.mul_le_mul_right
        (phaseUnit (encodeCircuit raw).length) sizePositive
  have endpoints :
      TargetEmitterControllerOutputBound.outputBlockUnit
            (TargetEmitterLedger.slotCapacity raw)
            (TargetEmitterControllerCompletionTrace.markedSource raw)
            (TargetEmitterSemanticCompletion.finalRuntime raw) +
          TargetEmitterControllerOutputTrace.finalizerPathSteps
            (TargetEmitterControllerCompletionTrace.markedSource raw) ≤
        2 *
          (shiftedSize (encodeCircuit raw).length *
            phaseUnit (encodeCircuit raw).length) := by
    have liftedBlock := Nat.le_trans block phaseLift
    have liftedFinalizer := Nat.le_trans finalizer phaseLift
    omega
  unfold
    TargetEmitterControllerCompletionTrace.controllerOutputUniformEnvelope
    TargetEmitterControllerOutputBound.outputUniformEnvelope
  have combined := Nat.add_le_add endpoints loopCommon
  have common :
      (TargetEmitterControllerOutputBound.outputBlockUnit
            (TargetEmitterLedger.slotCapacity raw)
            (TargetEmitterControllerCompletionTrace.markedSource raw)
            (TargetEmitterSemanticCompletion.finalRuntime raw) +
          TargetEmitterControllerOutputTrace.finalizerPathSteps
            (TargetEmitterControllerCompletionTrace.markedSource raw)) +
        ((TargetEmitterSemanticCompletion.finalRuntime
              raw).registers.baseline + 1) *
          (TargetEmitterControllerOutputBound.outputCompareUnit
              (TargetEmitterLedger.slotCapacity raw) +
            TargetEmitterControllerOutputBound.outputBlockUnit
              (TargetEmitterLedger.slotCapacity raw)
              (TargetEmitterControllerCompletionTrace.markedSource raw)
              (TargetEmitterSemanticCompletion.finalRuntime raw)) ≤
        132 *
          (shiftedSize (encodeCircuit raw).length *
            phaseUnit (encodeCircuit raw).length) :=
    Nat.le_trans combined (by omega)
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    Nat.mul_assoc] using common

/-- The scanner's published cubic grammar budget fits inside one controller
phase unit for every raw bit length. -/
theorem grammarWorkBound_le_phaseUnit (bitLength : Nat) :
    TargetEmitterGrammarScanner.grammarWorkBound bitLength ≤
      phaseUnit bitLength := by
  have shiftedMaster :
      shiftedSize bitLength ≤ masterMajorant bitLength := by
    have shiftedData :
        shiftedSize bitLength ≤ dataMajorant bitLength := by
      simpa only [Nat.one_mul] using
        coefficient_linear_le_data bitLength 1 (by decide)
    exact Nat.le_trans shiftedData (data_le_master bitLength)
  have squareMaster :
      shiftedSize bitLength * shiftedSize bitLength ≤
        masterMajorant bitLength := by
    have squareData :
        shiftedSize bitLength * shiftedSize bitLength ≤
          dataMajorant bitLength := by
      simpa only [Nat.one_mul] using
        coefficient_square_le_data bitLength 1 (by decide)
    exact Nat.le_trans squareData (data_le_master bitLength)
  have cube :=
    Nat.mul_le_mul squareMaster shiftedMaster
  have scaled := Nat.mul_le_mul_left 4096 cube
  have coefficient :
      4096 ≤
        TargetEmitterControllerCompletionTrace.normalizationProgramLimit := by
    unfold TargetEmitterControllerCompletionTrace.normalizationProgramLimit
    decide
  have squarePrimitive :
      masterMajorant bitLength * masterMajorant bitLength ≤
        TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
            (masterMajorant bitLength) + 1 := by
    unfold TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
    omega
  have phase := Nat.mul_le_mul coefficient squarePrimitive
  rw [TargetEmitterGrammarScanner.grammarWorkBound_polynomial]
  exact Nat.le_trans (by
      simpa only [shiftedSize, Nat.mul_assoc] using scaled)
    (by
      unfold phaseUnit
      exact phase)

/-- The complete ledger phase and its graph bridge fit inside one controller
phase unit at the source circuit's encoded bit length. -/
theorem ledgerWorkSteps_add_one_le_phaseUnit (raw : RawCircuit) :
    TargetEmitterLedger.workSteps raw + 1 ≤
      phaseUnit (encodeCircuit raw).length := by
  have work :=
    TargetEmitterLedger.workSteps_le_polynomialWorkBound raw
  rw [TargetEmitterLedger.polynomialWorkBound_eq] at work
  have cells := cells_le_shifted raw
  have square := Nat.mul_le_mul cells cells
  have quadratic :
      6166 * (SourceParser.circuitCells raw).length *
          (SourceParser.circuitCells raw).length ≤
        dataMajorant (encodeCircuit raw).length := by
    have scaled := Nat.mul_le_mul_left 6166 square
    exact Nat.le_trans (by
        simpa only [Nat.mul_assoc] using scaled)
      (coefficient_square_le_data _ 6166 (by decide))
  have linear :
      12702 * (SourceParser.circuitCells raw).length ≤
        dataMajorant (encodeCircuit raw).length := by
    have scaled := Nat.mul_le_mul_left 12702 cells
    exact Nat.le_trans scaled
      (coefficient_linear_le_data _ 12702 (by decide))
  have constant :
      6650 ≤ dataMajorant (encodeCircuit raw).length := by
    have positive := shifted_positive (encodeCircuit raw).length
    have squarePositive :
        1 ≤ shiftedSize (encodeCircuit raw).length *
          shiftedSize (encodeCircuit raw).length :=
      Nat.mul_le_mul positive positive
    have lifted :
        6650 ≤
          6650 * shiftedSize (encodeCircuit raw).length *
            shiftedSize (encodeCircuit raw).length := by
      have scaled := Nat.mul_le_mul_left 6650 squarePositive
      calc
        6650 = 6650 * 1 := by rw [Nat.mul_one]
        _ ≤ 6650 *
            (shiftedSize (encodeCircuit raw).length *
              shiftedSize (encodeCircuit raw).length) := scaled
        _ = 6650 * shiftedSize (encodeCircuit raw).length *
            shiftedSize (encodeCircuit raw).length := by
          rw [Nat.mul_assoc]
    exact Nat.le_trans lifted
      (coefficient_square_le_data _ 6650 (by decide))
  have bounded :
      TargetEmitterLedger.workSteps raw + 1 ≤
        4 * dataMajorant (encodeCircuit raw).length := by
    have one := one_le_data (encodeCircuit raw).length
    omega
  have master :
      4 * dataMajorant (encodeCircuit raw).length ≤
        masterMajorant (encodeCircuit raw).length := by
    unfold masterMajorant
    exact Nat.mul_le_mul_right _ (by decide)
  exact Nat.le_trans bounded
    (Nat.le_trans master (master_le_phaseUnit _))

/-- The complete source-derived controller envelope is dominated by the
literal closed polynomial in the canonical strict-v0 bit length. -/
theorem controllerUniformEnvelope_le_workBound (raw : RawCircuit) :
    TargetEmitterControllerCompletionTrace.controllerUniformEnvelope raw ≤
      controllerWorkBound (encodeCircuit raw).length := by
  let common :=
    shiftedSize (encodeCircuit raw).length *
      phaseUnit (encodeCircuit raw).length
  have gateRaw :=
    stackGateListUniformEnvelope_le_twelve_phaseUnits raw
  have gate :
      TargetEmitterControllerGateListTrace.stackGateListUniformEnvelope raw ≤
        12 * common := by
    simpa only [common, Nat.mul_assoc] using gateRaw
  have normalizationRaw :=
    outputNormalizationUniformEnvelope_le_two_phaseUnits raw
  have sizePositive := shifted_positive (encodeCircuit raw).length
  have phaseLift :
      phaseUnit (encodeCircuit raw).length ≤ common := by
    simpa only [common, Nat.one_mul] using
      Nat.mul_le_mul_right
        (phaseUnit (encodeCircuit raw).length) sizePositive
  have normalization :
      TargetEmitterControllerCompletionTrace.outputNormalizationUniformEnvelope
          raw ≤
        2 * common := by
    exact Nat.le_trans normalizationRaw
      (Nat.mul_le_mul_left 2 phaseLift)
  have prefixRaw :=
    controllerPrefixUniformEnvelope_le_six_phaseUnits raw
  have prefixBound :
      TargetEmitterControllerCompletionTrace.controllerPrefixUniformEnvelope
          raw ≤
        6 * common := by
    simpa only [common, Nat.mul_assoc] using prefixRaw
  have outputRaw :=
    controllerOutputUniformEnvelope_le_oneHundredThirtyTwo_phaseUnits raw
  have output :
      TargetEmitterControllerCompletionTrace.controllerOutputUniformEnvelope
          raw ≤
        132 * common := by
    simpa only [common, Nat.mul_assoc] using outputRaw
  have first := Nat.add_le_add gate normalization
  have second := Nat.add_le_add first prefixBound
  have all := Nat.add_le_add second output
  have boundedCommon :
      TargetEmitterControllerCompletionTrace.controllerUniformEnvelope raw ≤
        152 * common := by
    unfold TargetEmitterControllerCompletionTrace.controllerUniformEnvelope
    calc
      _ ≤ ((12 * common + 2 * common) + 6 * common) +
          132 * common := all
      _ = 152 * common := by
        simp only [← Nat.add_mul]
  have relaxed :
      152 * common ≤ 256 * common :=
    Nat.mul_le_mul_right common (by decide)
  unfold controllerWorkBound
  simpa only [common, Nat.mul_assoc] using
    Nat.le_trans boundedCommon relaxed

/-- Exact controller completion with its work bound exposed directly as the
evaluation of a closed `NatPolynomial`. -/
theorem controller_complete_path_polynomial
    (raw : RawCircuit) :
    ∃ gateListSteps normalizationSteps prefixSteps outputSteps finalTape,
      WorkMachineProgramPath.AcceptPath TargetEmitterController.graph
        (.node TargetEmitterController.stackInitializeRef) .accept
        (gateListSteps + normalizationSteps + prefixSteps + outputSteps)
        (TargetEmitterLedger.finalConfiguration raw).tape finalTape ∧
      TargetEmitterControllerOutputTrace.FinalTapeRepresents
        (TargetEmitterLedger.slotCapacity raw)
        (TargetEmitterSemanticCompletion.completeRuntime raw).scratch
        (TargetEmitterSemanticCompletion.completeRuntime raw).registers
        (TargetEmitterSemanticCompletion.completeRuntime raw).checks
        (TargetEmitterControllerCompletionTrace.markedSource raw)
        (TargetEmitterSemanticCompletion.completeRuntime raw).targetTokens
        finalTape ∧
      (encodeWorkTape finalTape).outputBits =
        encodeTokens
          (TargetEmitterSemanticCompletion.completeRuntime
            raw).targetTokens ∧
      gateListSteps + normalizationSteps + prefixSteps + outputSteps ≤
        controllerWorkTimePolynomial.eval (encodeCircuit raw).length := by
  rcases
      TargetEmitterControllerCompletionTrace.controller_complete_path_bounded
        raw with
    ⟨gateListSteps, normalizationSteps, prefixSteps, outputSteps,
      finalTape, path, represents, bound⟩
  refine
    ⟨gateListSteps, normalizationSteps, prefixSteps, outputSteps,
      finalTape, path, represents, ?_, ?_⟩
  · have equivalent :
        WorkTape.BlankEquivalent finalTape
          (TargetEmitterCursorFinalizer.finalTape
            (TargetEmitterControllerCompletionTrace.markedSource raw)
            (SourceParser.packedTokenCells
              (TargetEmitterSemanticCompletion.completeRuntime
                raw).targetTokens)
            (TargetEmitterRuntimePrimitives.fixedWorkspace
              (TargetEmitterLedger.slotCapacity raw)
              (TargetEmitterSemanticCompletion.completeRuntime raw).scratch
              (TargetEmitterSemanticCompletion.completeRuntime raw).registers
              (TargetEmitterSemanticCompletion.completeRuntime raw).checks)
            []) := by
      simpa [TargetEmitterControllerOutputTrace.FinalTapeRepresents] using
        represents
    exact
      (TargetEmitterControllerCompletionTrace.encodeWorkTape_outputBits_eq_of_blankEquivalent
        equivalent).trans
        (TargetEmitterControllerOutputTrace.canonicalFinal_output_eq
          (TargetEmitterControllerCompletionTrace.markedSource raw)
          (TargetEmitterSemanticCompletion.completeRuntime raw).targetTokens
          (TargetEmitterLedger.slotCapacity raw)
          (TargetEmitterSemanticCompletion.completeRuntime raw).scratch
          (TargetEmitterSemanticCompletion.completeRuntime raw).registers
          (TargetEmitterSemanticCompletion.completeRuntime raw).checks)
  rw [controllerWorkTimePolynomial_eval]
  exact Nat.le_trans bound (controllerUniformEnvelope_le_workBound raw)
end PNP.Concrete.LockedNAND.TargetEmitterControllerPolynomialBound
