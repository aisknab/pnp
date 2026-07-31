/-
Copyright (c) 2026 PNP Labs.

A closed encoded-input polynomial envelope for the canonical CNF-to-NAND
controller.

The constants in this file are deliberately coarse.  The physical controller
has a fixed finite descriptor table, while its retained source, unary bank,
target, and check stack are all bounded by the canonical CNF token count.
Keeping one generous factored majorant makes the eventual completion theorem
easy to audit and avoids exposing a proof-side controller schedule as an
executable input.
-/

import PNP.Concrete.CNFToNANDController
import PNP.Concrete.CNFToNANDControllerCanonicalTrace
import PNP.Concrete.CNFToNANDWorkspace
import PNP.Concrete.LockedNANDTargetEmitterRuntimeProgramBound

namespace PNP.Concrete.CNFToNANDControllerPolynomialBound

open PNP.Concrete
open PNP.Concrete.LockedNAND
open PNP.Concrete.CNFToNANDController

set_option maxRecDepth 1000000

/-! ## Closed polynomial -/

/-- Positive shift used throughout the coarse accounting. -/
def shiftedSize (bitLength : Nat) : Nat :=
  bitLength + 1

/-- One quadratic encoded-input unit. -/
def squareUnit (bitLength : Nat) : Nat :=
  1000000 * shiftedSize bitLength * shiftedSize bitLength

/-- Logical target/check-stack budget. -/
def dataMajorant (bitLength : Nat) : Nat :=
  1000 * squareUnit bitLength

/-- Physical footprint budget supplied to every primitive-program bound. -/
def masterMajorant (bitLength : Nat) : Nat :=
  100 * dataMajorant bitLength

/-- Uniform primitive count reserved for every fixed controller descriptor. -/
def descriptorProgramLimit : Nat :=
  64

/-- One complete fixed descriptor invocation, including primitive bridges. -/
def phaseUnit (bitLength : Nat) : Nat :=
  descriptorProgramLimit *
    (TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
      (masterMajorant bitLength) + 1)

/-- Coarse degree-six controller work bound.  The two leading shifted-size
factors pay for every canonical traversal and stack fold. -/
def controllerWorkBound (bitLength : Nat) : Nat :=
  4096 * shiftedSize bitLength * shiftedSize bitLength *
    phaseUnit bitLength

/-- Literal `NatPolynomial` representation of `controllerWorkBound`. -/
def controllerWorkTimePolynomial : NatPolynomial :=
  let shifted : NatPolynomial :=
    .add .variable (.constant 1)
  let square : NatPolynomial :=
    .mul (.constant 1000000) (.mul shifted shifted)
  let data : NatPolynomial :=
    .mul (.constant 1000) square
  let master : NatPolynomial :=
    .mul (.constant 100) data
  let unit : NatPolynomial :=
    .mul (.constant descriptorProgramLimit)
      (.add
        (.add
          (.mul (.constant 100) (.mul master master))
          (.constant 100))
        (.constant 1))
  .mul (.constant 4096)
    (.mul shifted (.mul shifted unit))

theorem controllerWorkTimePolynomial_eval (bitLength : Nat) :
    controllerWorkTimePolynomial.eval bitLength =
      controllerWorkBound bitLength := by
  simp [controllerWorkTimePolynomial, controllerWorkBound, phaseUnit,
    TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope,
    masterMajorant, dataMajorant, squareUnit, shiftedSize,
    NatPolynomial.eval, Nat.mul_assoc]

/-- Six raw transitions implement each work transition. -/
def compiledRawTimePolynomial : NatPolynomial :=
  .mul (.constant 6) controllerWorkTimePolynomial

theorem compiledRawTimePolynomial_eval (bitLength : Nat) :
    compiledRawTimePolynomial.eval bitLength =
      6 * controllerWorkBound bitLength := by
  simp [compiledRawTimePolynomial,
    controllerWorkTimePolynomial_eval]

/-! ## Canonical encoded-CNF size facts -/

theorem one_le_shiftedSize (bitLength : Nat) :
    1 ≤ shiftedSize bitLength := by
  unfold shiftedSize
  omega

theorem formulaTokens_le_shiftedSize (formula : CNFFormula) :
    (CNFToNANDWorkspace.formulaTokens formula).length ≤
      shiftedSize (encodeCNF formula).length := by
  rw [CNFToNANDWorkspace.canonicalEncodedBits_length]
  unfold shiftedSize
  omega

theorem carrierCells_le_sixteen_shiftedSize
    (formula : CNFFormula) :
    (SourceParser.circuitCells
      (CNFToNANDWorkspace.carrierCircuit formula)).length ≤
        16 * shiftedSize (encodeCNF formula).length := by
  rw [CNFToNANDWorkspace.carrierCircuit_cells_length,
    CNFToNANDWorkspace.canonicalEncodedBits_length]
  unfold shiftedSize
  omega

theorem capacity_le_1024_shiftedSize (formula : CNFFormula) :
    CNFToNANDWorkspace.capacity formula ≤
      1024 * shiftedSize (encodeCNF formula).length := by
  rw [CNFToNANDWorkspace.capacity_exact,
    CNFToNANDWorkspace.canonicalEncodedBits_length]
  unfold shiftedSize
  omega

theorem compilerGateCount_le_sixteen_shiftedSize
    (formula : CNFFormula) :
    CNFToNANDWorkspace.compilerGateCount formula ≤
      16 * shiftedSize (encodeCNF formula).length := by
  have bounded :=
    CNFToNANDWorkspace.compilerGateCount_le_tokenBound formula
  rw [CNFToNANDWorkspace.canonicalEncodedBits_length]
  unfold shiftedSize
  omega

theorem formulaStackMarker_le_1024_shiftedSize
    (formula : CNFFormula) :
    CNFToNANDWorkspace.formulaStackMarker formula ≤
      1024 * shiftedSize (encodeCNF formula).length := by
  exact Nat.le_trans
    (CNFToNANDWorkspace.formulaStackMarker_le_capacity formula)
    (capacity_le_1024_shiftedSize formula)

theorem carrierTokenCount_le_sixteen_shiftedSize
    (formula : CNFFormula) :
    (CNFToNANDCarrierEncoder.Source.carrierTokens
      (CNFToNANDWorkspace.formulaTokens formula)).length ≤
        16 * shiftedSize (encodeCNF formula).length := by
  rw [CNFToNANDCarrierEncoder.Source.carrierTokens_length,
    CNFToNANDWorkspace.canonicalEncodedBits_length]
  unfold shiftedSize
  omega

/-! ## Majorant plumbing -/

private theorem shiftedSize_le_squareUnit (bitLength : Nat) :
    shiftedSize bitLength ≤ squareUnit bitLength := by
  have positive := one_le_shiftedSize bitLength
  have square :
      shiftedSize bitLength ≤
        shiftedSize bitLength * shiftedSize bitLength := by
    simpa only [Nat.mul_comm, Nat.one_mul] using
      Nat.mul_le_mul_left (shiftedSize bitLength) positive
  unfold squareUnit
  have scaled :=
    Nat.mul_le_mul_right
      (shiftedSize bitLength * shiftedSize bitLength)
      (show 1 ≤ 1000000 by decide)
  exact Nat.le_trans square (by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using scaled)

private theorem coefficient_linear_le_squareUnit
    (bitLength coefficient : Nat)
    (coefficientBound : coefficient ≤ 1000000) :
    coefficient * shiftedSize bitLength ≤ squareUnit bitLength := by
  have lifted :
      coefficient * shiftedSize bitLength ≤
        coefficient * shiftedSize bitLength * shiftedSize bitLength := by
    simpa only [Nat.mul_one] using
      Nat.mul_le_mul_left
        (coefficient * shiftedSize bitLength)
        (one_le_shiftedSize bitLength)
  have scaled :
      coefficient * shiftedSize bitLength * shiftedSize bitLength ≤
        squareUnit bitLength := by
    unfold squareUnit
    exact Nat.mul_le_mul_right (shiftedSize bitLength)
      (Nat.mul_le_mul_right
        (shiftedSize bitLength) coefficientBound)
  exact Nat.le_trans lifted scaled

private theorem squareUnit_le_dataMajorant (bitLength : Nat) :
    squareUnit bitLength ≤ dataMajorant bitLength := by
  unfold dataMajorant
  simpa only [Nat.one_mul] using
    Nat.mul_le_mul_right (squareUnit bitLength)
      (show 1 ≤ 1000 by decide)

private theorem dataMajorant_le_masterMajorant (bitLength : Nat) :
    dataMajorant bitLength ≤ masterMajorant bitLength := by
  unfold masterMajorant
  simpa only [Nat.one_mul] using
    Nat.mul_le_mul_right (dataMajorant bitLength)
      (show 1 ≤ 100 by decide)

theorem shiftedSize_le_masterMajorant (bitLength : Nat) :
    shiftedSize bitLength ≤ masterMajorant bitLength :=
  Nat.le_trans (shiftedSize_le_squareUnit bitLength)
    (Nat.le_trans (squareUnit_le_dataMajorant bitLength)
      (dataMajorant_le_masterMajorant bitLength))

theorem capacity_le_masterMajorant (formula : CNFFormula) :
    CNFToNANDWorkspace.capacity formula ≤
      masterMajorant (encodeCNF formula).length := by
  have coefficient :
      1024 * shiftedSize (encodeCNF formula).length ≤
        squareUnit (encodeCNF formula).length := by
    exact coefficient_linear_le_squareUnit _ 1024 (by decide)
  exact Nat.le_trans
    (capacity_le_1024_shiftedSize formula)
    (Nat.le_trans coefficient
      (Nat.le_trans (squareUnit_le_dataMajorant _)
        (dataMajorant_le_masterMajorant _)))

theorem carrierCells_le_masterMajorant (formula : CNFFormula) :
    (SourceParser.circuitCells
      (CNFToNANDWorkspace.carrierCircuit formula)).length ≤
        masterMajorant (encodeCNF formula).length := by
  exact Nat.le_trans
    (carrierCells_le_sixteen_shiftedSize formula)
    (Nat.le_trans
      (coefficient_linear_le_squareUnit _ 16 (by decide))
      (Nat.le_trans (squareUnit_le_dataMajorant _)
        (dataMajorant_le_masterMajorant _)))

theorem primitiveEnvelope_add_one_le_phaseUnit
    (bitLength : Nat) :
    TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
          (masterMajorant bitLength) + 1 ≤
      phaseUnit bitLength := by
  unfold phaseUnit descriptorProgramLimit
  simpa [Nat.mul_comm] using
    Nat.mul_le_mul_left
      (TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
        (masterMajorant bitLength) + 1)
      (show 1 ≤ 64 by decide)

theorem one_le_phaseUnit (bitLength : Nat) :
    1 ≤ phaseUnit bitLength := by
  exact Nat.le_trans
    (by
      unfold TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
      omega)
    (primitiveEnvelope_add_one_le_phaseUnit bitLength)

private theorem one_le_squareUnit (bitLength : Nat) :
    1 ≤ squareUnit bitLength := by
  have square :
      1 ≤ shiftedSize bitLength * shiftedSize bitLength :=
    Nat.mul_le_mul
      (one_le_shiftedSize bitLength)
      (one_le_shiftedSize bitLength)
  have scaled :
      1 * (shiftedSize bitLength * shiftedSize bitLength) ≤
        1000000 *
          (shiftedSize bitLength * shiftedSize bitLength) :=
    Nat.mul_le_mul_right
      (shiftedSize bitLength * shiftedSize bitLength)
      (show 1 ≤ 1000000 by decide)
  exact Nat.le_trans square (by
    simpa [squareUnit, Nat.mul_assoc] using scaled)

private theorem one_le_dataMajorant (bitLength : Nat) :
    1 ≤ dataMajorant bitLength :=
  Nat.le_trans (one_le_squareUnit bitLength)
    (squareUnit_le_dataMajorant bitLength)

private theorem one_le_masterMajorant (bitLength : Nat) :
    1 ≤ masterMajorant bitLength :=
  Nat.le_trans (one_le_dataMajorant bitLength)
    (dataMajorant_le_masterMajorant bitLength)

private theorem list_all_member_true
    {α : Type} (predicate : α → Bool) :
    ∀ (items : List α) (item : α),
      items.all predicate = true →
      item ∈ items →
      predicate item = true := by
  intro items
  induction items with
  | nil =>
      intro item _ member
      contradiction
  | cons first rest inductionHypothesis =>
      intro item allTrue member
      have bothTrue :
          predicate first = true ∧ rest.all predicate = true := by
        simpa [Bool.and_eq_true] using allTrue
      rcases List.mem_cons.mp member with itemEq | restMember
      · subst item
        exact bothTrue.1
      · exact inductionHypothesis item bothTrue.2 restMember

private theorem descriptor_primitives_length_le_twentyTwo
    (descriptor : BlockDescriptor)
    (member : descriptor ∈ blockDescriptors) :
    descriptor.primitives.length ≤ 22 := by
  have all :
      blockDescriptors.all
          (fun item => decide (item.primitives.length ≤ 22)) =
        true := by
    decide
  exact of_decide_eq_true
    (list_all_member_true _ blockDescriptors descriptor all member)

private theorem three_le_dataMajorant (bitLength : Nat) :
    3 ≤ dataMajorant bitLength := by
  have positive := one_le_shiftedSize bitLength
  have square :
      1 ≤ shiftedSize bitLength * shiftedSize bitLength :=
    Nat.mul_le_mul positive positive
  calc
    3 ≤ 1000 * 1000000 := by decide
    _ = (1000 * 1000000) * 1 := by rw [Nat.mul_one]
    _ ≤ (1000 * 1000000) *
          (shiftedSize bitLength * shiftedSize bitLength) :=
      Nat.mul_le_mul_left (1000 * 1000000) square
    _ = dataMajorant bitLength := by
      unfold dataMajorant squareUnit
      ac_rfl

private theorem runtimeFootprint_le_masterMajorant
    (bitLength capacity : Nat) (source : List WorkSymbol)
    (initial :
      PNP.Concrete.LockedNAND.TargetEmitterProgramSemantics.Runtime)
    (primitives : List TargetEmitterPlan.Primitive)
    (capacityBound : capacity ≤ dataMajorant bitLength)
    (sourceBound : source.length ≤ dataMajorant bitLength)
    (targetBound :
      initial.targetTokens.length ≤ dataMajorant bitLength)
    (checksBound :
      TargetEmitterRuntimeProgramBound.checkCells initial.checks ≤
        dataMajorant bitLength)
    (programLengthBound : primitives.length ≤ 22) :
    TargetEmitterRuntimeProgramBound.runtimeFootprint
        capacity source initial primitives.length ≤
      masterMajorant bitLength := by
  let data := dataMajorant bitLength
  have dataThree : 3 ≤ data := by
    simpa [data] using three_le_dataMajorant bitLength
  have variableTerm :
      primitives.length * (3 * capacity + 3) ≤
        22 * (3 * data + 3) :=
    Nat.mul_le_mul programLengthBound
      (Nat.add_le_add_right
        (Nat.mul_le_mul_left 3 capacityBound) 3)
  unfold TargetEmitterRuntimeProgramBound.runtimeFootprint
    masterMajorant
  dsimp [data] at dataThree variableTerm
  omega

/-- Every safe invocation of one fixed materialized controller descriptor is
covered by one common phase unit whenever its variable runtime data fits the
logical quadratic majorant. -/
theorem descriptorProgramEnvelope_le_phaseUnit
    (bitLength capacity : Nat) (source : List WorkSymbol)
    (initial :
      PNP.Concrete.LockedNAND.TargetEmitterProgramSemantics.Runtime)
    (descriptor : BlockDescriptor)
    (member : descriptor ∈ blockDescriptors)
    (capacityBound : capacity ≤ dataMajorant bitLength)
    (sourceBound : source.length ≤ dataMajorant bitLength)
    (targetBound :
      initial.targetTokens.length ≤ dataMajorant bitLength)
    (checksBound :
      TargetEmitterRuntimeProgramBound.checkCells initial.checks ≤
        dataMajorant bitLength) :
    TargetEmitterRuntimeProgramBound.programWorkEnvelope
        capacity source initial descriptor.primitives ≤
      phaseUnit bitLength := by
  have lengthTwentyTwo :=
    descriptor_primitives_length_le_twentyTwo descriptor member
  have footprint :=
    runtimeFootprint_le_masterMajorant bitLength capacity source
      initial descriptor.primitives capacityBound sourceBound
      targetBound checksBound lengthTwentyTwo
  have square := Nat.mul_le_mul footprint footprint
  have primitive :
      TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
          (TargetEmitterRuntimeProgramBound.runtimeFootprint
            capacity source initial descriptor.primitives.length) ≤
        TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
          (masterMajorant bitLength) := by
    unfold TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_left 100 square) 100
  have lengthSixtyFour :
      descriptor.primitives.length ≤ descriptorProgramLimit := by
    exact Nat.le_trans lengthTwentyTwo (by
      unfold descriptorProgramLimit
      decide)
  unfold TargetEmitterRuntimeProgramBound.programWorkEnvelope
    phaseUnit
  exact Nat.mul_le_mul lengthSixtyFour
    (Nat.add_le_add_right primitive 1)

private theorem coefficient_square_le_squareUnit
    (bitLength coefficient : Nat)
    (coefficientBound : coefficient ≤ 1000000) :
    coefficient * shiftedSize bitLength * shiftedSize bitLength ≤
      squareUnit bitLength := by
  unfold squareUnit
  exact Nat.mul_le_mul_right (shiftedSize bitLength)
    (Nat.mul_le_mul_right
      (shiftedSize bitLength) coefficientBound)

private theorem coefficient_square_le_dataMajorant
    (bitLength coefficient : Nat)
    (coefficientBound : coefficient ≤ 1000 * 1000000) :
    coefficient * shiftedSize bitLength * shiftedSize bitLength ≤
      dataMajorant bitLength := by
  unfold dataMajorant squareUnit
  have scaled :=
    Nat.mul_le_mul_right (shiftedSize bitLength)
      (Nat.mul_le_mul_right
        (shiftedSize bitLength) coefficientBound)
  simpa only [Nat.mul_assoc] using scaled

private theorem coefficient_linear_le_dataMajorant
    (bitLength coefficient : Nat)
    (coefficientBound : coefficient ≤ 1000000) :
    coefficient * shiftedSize bitLength ≤
      dataMajorant bitLength :=
  Nat.le_trans
    (coefficient_linear_le_squareUnit
      bitLength coefficient coefficientBound)
    (squareUnit_le_dataMajorant bitLength)

private theorem masterMajorant_le_phaseUnit (bitLength : Nat) :
    masterMajorant bitLength ≤ phaseUnit bitLength := by
  have squared :
      masterMajorant bitLength ≤
        masterMajorant bitLength * masterMajorant bitLength := by
    simpa only [Nat.mul_one] using
      Nat.mul_le_mul_left
        (masterMajorant bitLength)
        (one_le_masterMajorant bitLength)
  have enveloped :
      masterMajorant bitLength * masterMajorant bitLength ≤
        TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
            (masterMajorant bitLength) + 1 := by
    unfold TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
    omega
  exact Nat.le_trans squared
    (Nat.le_trans enveloped
      (primitiveEnvelope_add_one_le_phaseUnit bitLength))

private theorem dataMajorant_le_phaseUnit (bitLength : Nat) :
    dataMajorant bitLength ≤ phaseUnit bitLength :=
  Nat.le_trans (dataMajorant_le_masterMajorant bitLength)
    (masterMajorant_le_phaseUnit bitLength)

private theorem carrierCells_le_shiftedSize (formula : CNFFormula) :
    (SourceParser.circuitCells
      (CNFToNANDWorkspace.carrierCircuit formula)).length ≤
        shiftedSize
          (encodeCircuit
            (CNFToNANDWorkspace.carrierCircuit formula)).length := by
  rw [SourceParser.encodeCircuit_length_eq]
  unfold shiftedSize
  omega

private theorem carrierGrammarWorkBound_le_phaseUnit
    (formula : CNFFormula) :
    TargetEmitterGrammarScanner.grammarWorkBound
        (encodeCircuit
          (CNFToNANDWorkspace.carrierCircuit formula)).length ≤
      phaseUnit (encodeCNF formula).length := by
  let rawBitLength :=
    (encodeCircuit
      (CNFToNANDWorkspace.carrierCircuit formula)).length
  let bitLength := (encodeCNF formula).length
  let rawSize := shiftedSize rawBitLength
  let size := shiftedSize bitLength
  let master := masterMajorant bitLength
  have rawSizeBound : rawSize ≤ 16 * size := by
    dsimp [rawSize, rawBitLength, size, bitLength]
    rw [SourceParser.encodeCircuit_length_eq,
      CNFToNANDWorkspace.carrierCircuit_cells_length,
      CNFToNANDWorkspace.canonicalEncodedBits_length]
    unfold shiftedSize
    omega
  have sixteenSizeMaster : 16 * size ≤ master := by
    exact Nat.le_trans
      (coefficient_linear_le_squareUnit bitLength 16 (by decide))
      (Nat.le_trans (squareUnit_le_dataMajorant bitLength)
        (dataMajorant_le_masterMajorant bitLength))
  have rawSizeMaster : rawSize ≤ master :=
    Nat.le_trans rawSizeBound sixteenSizeMaster
  have rawSquareMaster :
      rawSize * rawSize ≤ master := by
    have rawSquareBound :=
      Nat.mul_le_mul rawSizeBound rawSizeBound
    have squareUnitBound :
        (16 * size) * (16 * size) ≤ squareUnit bitLength := by
      have coefficient :
          256 * size * size ≤ squareUnit bitLength := by
        simpa [size] using
          coefficient_square_le_squareUnit bitLength 256 (by decide)
      calc
        (16 * size) * (16 * size) =
            (16 * 16) * size * size := by ac_rfl
        _ = 256 * size * size := by
          rw [show 16 * 16 = 256 by decide]
        _ ≤ squareUnit bitLength := coefficient
    exact Nat.le_trans rawSquareBound
      (Nat.le_trans squareUnitBound
      (Nat.le_trans (squareUnit_le_dataMajorant bitLength)
        (dataMajorant_le_masterMajorant bitLength)))
  have cubeBound :
      rawSize * rawSize * rawSize ≤ master * master :=
    Nat.mul_le_mul rawSquareMaster rawSizeMaster
  have scaled :
      4096 * (rawSize * rawSize * rawSize) ≤
        4096 * (master * master) :=
    Nat.mul_le_mul_left 4096 cubeBound
  have phaseBound :
      4096 * (master * master) ≤
        phaseUnit bitLength := by
    unfold phaseUnit descriptorProgramLimit
      TargetEmitterRuntimeProgramBound.primitiveWorkEnvelope
    dsimp [master]
    have coefficient :
        4096 * (masterMajorant bitLength *
            masterMajorant bitLength) ≤
          6400 * (masterMajorant bitLength *
            masterMajorant bitLength) :=
      Nat.mul_le_mul_right
        (masterMajorant bitLength * masterMajorant bitLength)
        (show 4096 ≤ 6400 by decide)
    omega
  rw [TargetEmitterGrammarScanner.grammarWorkBound_polynomial]
  exact Nat.le_trans (by
      simpa [rawSize, shiftedSize, Nat.mul_assoc] using scaled)
    phaseBound

private theorem ledgerWorkSteps_add_one_le_phaseUnit
    (formula : CNFFormula) :
    TargetEmitterLedger.workSteps
          (CNFToNANDWorkspace.carrierCircuit formula) + 1 ≤
      phaseUnit (encodeCNF formula).length := by
  let raw := CNFToNANDWorkspace.carrierCircuit formula
  let bitLength := (encodeCNF formula).length
  let size := shiftedSize bitLength
  have cells :
      (SourceParser.circuitCells raw).length ≤ 16 * size := by
    simpa [raw, bitLength, size] using
      carrierCells_le_sixteen_shiftedSize formula
  have work :=
    TargetEmitterLedger.workSteps_le_polynomialWorkBound raw
  rw [TargetEmitterLedger.polynomialWorkBound_eq] at work
  have square := Nat.mul_le_mul cells cells
  have quadraticMajorant :
      1578496 * size * size ≤ dataMajorant bitLength :=
    coefficient_square_le_dataMajorant
      bitLength 1578496 (by decide)
  have quadratic :
      6166 * (SourceParser.circuitCells raw).length *
          (SourceParser.circuitCells raw).length ≤
        dataMajorant bitLength := by
    have scaled := Nat.mul_le_mul_left 6166 square
    calc
      6166 * (SourceParser.circuitCells raw).length *
            (SourceParser.circuitCells raw).length ≤
          6166 * ((16 * size) * (16 * size)) := by
        simpa only [Nat.mul_assoc] using scaled
      _ = (6166 * 16 * 16) * size * size := by ac_rfl
      _ = 1578496 * size * size := by
        rw [show 6166 * 16 * 16 = 1578496 by decide]
      _ ≤ dataMajorant bitLength := quadraticMajorant
  have linearMajorant :
      203232 * size ≤ dataMajorant bitLength :=
    coefficient_linear_le_dataMajorant
      bitLength 203232 (by decide)
  have linear :
      12702 * (SourceParser.circuitCells raw).length ≤
        dataMajorant bitLength := by
    have scaled := Nat.mul_le_mul_left 12702 cells
    calc
      12702 * (SourceParser.circuitCells raw).length ≤
          12702 * (16 * size) := scaled
      _ = (12702 * 16) * size := by ac_rfl
      _ = 203232 * size := by
        rw [show 12702 * 16 = 203232 by decide]
      _ ≤ dataMajorant bitLength := linearMajorant
  have constant :
      6650 ≤ dataMajorant bitLength := by
    have lifted :
        6650 ≤ 6650 * size := by
      simpa only [Nat.mul_one] using
        Nat.mul_le_mul_left 6650
          (one_le_shiftedSize bitLength)
    exact Nat.le_trans lifted
      (coefficient_linear_le_dataMajorant
        bitLength 6650 (by decide))
  have bounded :
      TargetEmitterLedger.workSteps raw + 1 ≤
        4 * dataMajorant bitLength := by
    have one := one_le_dataMajorant bitLength
    omega
  have master :
      4 * dataMajorant bitLength ≤ masterMajorant bitLength := by
    unfold masterMajorant
    exact Nat.mul_le_mul_right _ (by decide)
  exact Nat.le_trans bounded
    (Nat.le_trans master
      (masterMajorant_le_phaseUnit bitLength))

private theorem stackInitializeSteps_le_phaseUnit
    (formula : CNFFormula) :
    CNFToNANDControllerCanonicalTrace.stackInitializeSteps formula ≤
      phaseUnit (encodeCNF formula).length := by
  let bitLength := (encodeCNF formula).length
  let size := shiftedSize bitLength
  have capacity :=
    capacity_le_1024_shiftedSize formula
  have linear :
      TargetEmitterCheckStack.Initialize.workSteps
            (CNFToNANDWorkspace.capacity formula) + 1 ≤
        15000 * size := by
    unfold TargetEmitterCheckStack.Initialize.workSteps
    dsimp [bitLength, size] at capacity ⊢
    have positive := one_le_shiftedSize bitLength
    dsimp [bitLength] at positive
    omega
  exact Nat.le_trans (by
      simpa [CNFToNANDControllerCanonicalTrace.stackInitializeSteps,
        bitLength, size] using linear)
    (Nat.le_trans (by
        simpa [size] using
          coefficient_linear_le_dataMajorant
            bitLength 15000 (by decide))
      (dataMajorant_le_phaseUnit bitLength))

private theorem resetSteps_le_phaseUnit (bitLength : Nat) :
    CNFToNANDControllerCanonicalTrace.resetSteps ≤
      phaseUnit bitLength := by
  have lifted :
      9 ≤ 9 * shiftedSize bitLength := by
    simpa only [Nat.mul_one] using
      Nat.mul_le_mul_left 9 (one_le_shiftedSize bitLength)
  have data :
      9 * shiftedSize bitLength ≤ dataMajorant bitLength :=
    coefficient_linear_le_dataMajorant bitLength 9 (by decide)
  unfold CNFToNANDControllerCanonicalTrace.resetSteps
    TargetEmitterScratchReset.workSteps
  exact Nat.le_trans lifted
    (Nat.le_trans data (dataMajorant_le_phaseUnit bitLength))

private theorem workspaceZeroSteps_le_phaseUnit
    (formula : CNFFormula) :
    CNFToNANDControllerCanonicalTrace.workspaceZeroSteps formula ≤
      phaseUnit (encodeCNF formula).length := by
  let bitLength := (encodeCNF formula).length
  let size := shiftedSize bitLength
  have capacity :=
    capacity_le_1024_shiftedSize formula
  have work :=
    TargetEmitterScratchCompareSlot.workSteps_le_polynomialWorkBound
      .inputCount (CNFToNANDWorkspace.capacity formula) 0
  have linear :
      TargetEmitterScratchCompareSlot.workSteps .inputCount
            (CNFToNANDWorkspace.capacity formula) 0 + 1 ≤
        15000 * size := by
    unfold TargetEmitterScratchCompareSlot.polynomialWorkBound at work
    dsimp [bitLength, size] at capacity ⊢
    have positive := one_le_shiftedSize bitLength
    dsimp [bitLength] at positive
    omega
  exact Nat.le_trans (by
      simpa [CNFToNANDControllerCanonicalTrace.workspaceZeroSteps,
        bitLength, size] using linear)
    (Nat.le_trans (by
        simpa [size] using
          coefficient_linear_le_dataMajorant
            bitLength 15000 (by decide))
      (dataMajorant_le_phaseUnit bitLength))

/-! ## Canonical prefix cost -/

/-- The fixed carrier-validation pass is linear in the encoded CNF length. -/
theorem validationSteps_le_sixtyFour_shiftedSize
    (formula : CNFFormula) :
    CNFToNANDControllerCanonicalTrace.validationSteps formula ≤
      64 * shiftedSize (encodeCNF formula).length := by
  rw [CNFToNANDControllerCanonicalTrace.validationSteps_eq,
    CNFToNANDWorkspace.canonicalEncodedBits_length]
  unfold shiftedSize
  omega

private theorem validationSteps_le_phaseUnit
    (formula : CNFFormula) :
    CNFToNANDControllerCanonicalTrace.validationSteps formula ≤
      phaseUnit (encodeCNF formula).length := by
  let bitLength := (encodeCNF formula).length
  let size := shiftedSize bitLength
  have validationBound :
      CNFToNANDControllerCanonicalTrace.validationSteps formula ≤
        64 * size := by
    simpa [bitLength, size] using
      validationSteps_le_sixtyFour_shiftedSize formula
  have data :
      64 * size ≤ dataMajorant bitLength := by
    simpa [size] using
      coefficient_linear_le_dataMajorant bitLength 64 (by decide)
  exact Nat.le_trans validationBound
    (Nat.le_trans data (dataMajorant_le_phaseUnit bitLength))

/-- The complete scanner/ledger/initialization/reset/validation prefix uses
at most seven common controller phases. -/
theorem canonicalPrefixSteps_le_seven_phaseUnits
    (formula : CNFFormula) :
    CNFToNANDControllerCanonicalTrace.canonicalPrefixSteps formula ≤
      7 * phaseUnit (encodeCNF formula).length := by
  let raw := CNFToNANDWorkspace.carrierCircuit formula
  let bitLength := (encodeCNF formula).length
  let phase := phaseUnit bitLength
  have scanner :
      TargetEmitterGrammarScanner.canonicalSteps raw + 1 ≤
        2 * phase := by
    have canonical :=
      TargetEmitterGrammarScanner.canonicalSteps_le_grammarWorkBound raw
    have grammar :
        TargetEmitterGrammarScanner.grammarWorkBound
            (encodeCircuit raw).length ≤
          phase := by
      simpa [raw, bitLength, phase] using
        carrierGrammarWorkBound_le_phaseUnit formula
    have one : 1 ≤ phase := by
      simpa [phase] using one_le_phaseUnit bitLength
    omega
  have ledger :
      TargetEmitterLedger.workSteps raw + 1 ≤ phase := by
    simpa [raw, bitLength, phase] using
      ledgerWorkSteps_add_one_le_phaseUnit formula
  have stackInit :
      CNFToNANDControllerCanonicalTrace.stackInitializeSteps formula ≤
        phase := by
    simpa [bitLength, phase] using
      stackInitializeSteps_le_phaseUnit formula
  have reset :
      CNFToNANDControllerCanonicalTrace.resetSteps ≤ phase := by
    simpa [bitLength, phase] using resetSteps_le_phaseUnit bitLength
  have workspace :
      CNFToNANDControllerCanonicalTrace.workspaceZeroSteps formula ≤
        phase := by
    simpa [bitLength, phase] using
      workspaceZeroSteps_le_phaseUnit formula
  have validation :
      CNFToNANDControllerCanonicalTrace.validationSteps formula ≤
        phase := by
    simpa [bitLength, phase] using
      validationSteps_le_phaseUnit formula
  have prefixBound :
      CNFToNANDControllerCanonicalTrace.canonicalPrefixSteps formula ≤
        7 * phase := by
    unfold CNFToNANDControllerCanonicalTrace.canonicalPrefixSteps
      CNFToNANDControllerCanonicalTrace.initializedResetSteps
      CNFToNANDControllerCanonicalTrace.initializedPrefixSteps
      CNFToNANDControllerCanonicalTrace.prefixSteps
    dsimp [raw] at scanner ledger ⊢
    omega
  simpa [bitLength, phase] using prefixBound

/-- The complete scanner/ledger/initialization/reset/validation prefix is
bounded by the same closed encoded-input polynomial reserved for controller
completion. -/
theorem canonicalPrefixSteps_le_controllerWorkBound
    (formula : CNFFormula) :
    CNFToNANDControllerCanonicalTrace.canonicalPrefixSteps formula ≤
      controllerWorkBound (encodeCNF formula).length := by
  let bitLength := (encodeCNF formula).length
  let phase := phaseUnit bitLength
  have prefixBound :
      CNFToNANDControllerCanonicalTrace.canonicalPrefixSteps formula ≤
        7 * phase := by
    simpa [bitLength, phase] using
      canonicalPrefixSteps_le_seven_phaseUnits formula
  have sizePositive :
      1 ≤ shiftedSize bitLength * shiftedSize bitLength :=
    Nat.mul_le_mul
      (one_le_shiftedSize bitLength)
      (one_le_shiftedSize bitLength)
  have coefficient :
      7 ≤ 4096 *
          (shiftedSize bitLength * shiftedSize bitLength) := by
    have base : 7 ≤ 4096 := by decide
    exact Nat.le_trans base (by
      simpa only [Nat.mul_one] using
        Nat.mul_le_mul_left 4096 sizePositive)
  have scaled := Nat.mul_le_mul_right phase coefficient
  exact Nat.le_trans prefixBound (by
    simpa [controllerWorkBound, bitLength, phase,
      Nat.mul_assoc] using scaled)

end PNP.Concrete.CNFToNANDControllerPolynomialBound
