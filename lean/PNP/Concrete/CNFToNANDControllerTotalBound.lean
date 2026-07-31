/-
Copyright (c) 2026 PNP Labs.

Closed additive accounting for the complete canonical CNF-to-NAND
controller.

This module is kept separate from `CNFToNANDControllerPolynomialBound` so
the compiler's polynomial declaration does not acquire a dependency on the
structural count and emit traces.  The private lemmas below place the
canonical data in the shared logical majorant and close the additive
allocation for the prefix, count, and completion phases.
-/

import PNP.Concrete.CNFToNANDControllerCountTrace
import PNP.Concrete.CNFToNANDControllerCompletionTrace
import PNP.Concrete.CNFToNANDControllerPolynomialBound

namespace PNP.Concrete.CNFToNANDControllerTotalBound

open PNP.Concrete
open PNP.Concrete.LockedNAND
open PNP.Concrete.CNFToNANDController
open PNP.Concrete.CNFToNANDControllerPolynomialBound

set_option maxRecDepth 1000000

private theorem coefficient_linear_le_dataMajorant
    (bitLength coefficient : Nat)
    (coefficientBound : coefficient ≤ 1000 * 1000000) :
    coefficient * shiftedSize bitLength ≤ dataMajorant bitLength := by
  have positive := one_le_shiftedSize bitLength
  have lifted :
      coefficient * shiftedSize bitLength ≤
        coefficient *
          (shiftedSize bitLength * shiftedSize bitLength) := by
    have scaled :=
      Nat.mul_le_mul_left coefficient
        (show shiftedSize bitLength ≤
            shiftedSize bitLength * shiftedSize bitLength by
          simpa only [Nat.mul_one] using
            Nat.mul_le_mul_left (shiftedSize bitLength) positive)
    exact scaled
  have coefficientLifted :
      coefficient *
          (shiftedSize bitLength * shiftedSize bitLength) ≤
        (1000 * 1000000) *
          (shiftedSize bitLength * shiftedSize bitLength) :=
    Nat.mul_le_mul_right
      (shiftedSize bitLength * shiftedSize bitLength)
      coefficientBound
  calc
    coefficient * shiftedSize bitLength ≤
        coefficient *
          (shiftedSize bitLength * shiftedSize bitLength) :=
      lifted
    _ ≤ (1000 * 1000000) *
          (shiftedSize bitLength * shiftedSize bitLength) :=
      coefficientLifted
    _ = dataMajorant bitLength := by
      unfold dataMajorant squareUnit
      ac_rfl

private theorem formulaTokens_length_le_dataMajorant
    (formula : CNFFormula) :
    (CNFToNANDWorkspace.formulaTokens formula).length ≤
      dataMajorant (encodeCNF formula).length := by
  exact Nat.le_trans
    (formulaTokens_le_shiftedSize formula)
    (by
      simpa only [Nat.one_mul] using
        coefficient_linear_le_dataMajorant
          (encodeCNF formula).length 1 (by decide))

private theorem canonicalSource_length_le_dataMajorant
    (formula : CNFFormula) :
    (CNFToNANDControllerCanonicalTrace.canonicalSource formula).length ≤
      dataMajorant (encodeCNF formula).length := by
  exact Nat.le_trans
    (carrierCells_le_sixteen_shiftedSize formula)
    (coefficient_linear_le_dataMajorant
      (encodeCNF formula).length 16 (by decide))

private theorem capacity_le_dataMajorant
    (formula : CNFFormula) :
    CNFToNANDWorkspace.capacity formula ≤
      dataMajorant (encodeCNF formula).length := by
  exact Nat.le_trans
    (capacity_le_1024_shiftedSize formula)
    (coefficient_linear_le_dataMajorant
      (encodeCNF formula).length 1024 (by decide))

/-! ## Additive phase allocation -/

private theorem allocatedComponents_le_controllerWorkBound
    (bitLength prefixSteps countSteps completionSteps : Nat)
    (prefixBound : prefixSteps ≤ 7 * phaseUnit bitLength)
    (countBound :
      countSteps ≤
        1024 * shiftedSize bitLength * shiftedSize bitLength *
          phaseUnit bitLength)
    (completionBound :
      completionSteps ≤
        2048 * shiftedSize bitLength * shiftedSize bitLength *
          phaseUnit bitLength) :
    prefixSteps + countSteps + completionSteps ≤
      controllerWorkBound bitLength := by
  have sizeSquarePositive :
      1 ≤ shiftedSize bitLength * shiftedSize bitLength :=
    Nat.mul_le_mul
      (one_le_shiftedSize bitLength)
      (one_le_shiftedSize bitLength)
  have sevenCoefficient :
      7 ≤ 1024 *
          (shiftedSize bitLength * shiftedSize bitLength) := by
    exact Nat.le_trans (show 7 ≤ 1024 by decide) (by
      simpa only [Nat.mul_one] using
        Nat.mul_le_mul_left 1024 sizeSquarePositive)
  have prefixCommon :
      prefixSteps ≤
        1024 * shiftedSize bitLength * shiftedSize bitLength *
          phaseUnit bitLength := by
    exact Nat.le_trans prefixBound (by
      have scaled :=
        Nat.mul_le_mul_right (phaseUnit bitLength) sevenCoefficient
      simpa only [Nat.mul_assoc] using scaled)
  let common :=
    shiftedSize bitLength * shiftedSize bitLength *
      phaseUnit bitLength
  have prefixCommon' : prefixSteps ≤ 1024 * common := by
    simpa [common, Nat.mul_assoc] using prefixCommon
  have countBound' : countSteps ≤ 1024 * common := by
    simpa [common, Nat.mul_assoc] using countBound
  have completionBound' : completionSteps ≤ 2048 * common := by
    simpa [common, Nat.mul_assoc] using completionBound
  have combined :=
    Nat.add_le_add
      (Nat.add_le_add prefixCommon' countBound')
      completionBound'
  calc
    prefixSteps + countSteps + completionSteps ≤
        1024 * common + 1024 * common + 2048 * common :=
      combined
    _ = 4096 * common := by omega
    _ = controllerWorkBound bitLength := by
      simp [common, controllerWorkBound, Nat.mul_assoc]

/-! ## Closed canonical envelope -/

/-- Formula-indexed work envelope for the complete canonical controller:
the exact scanner/ledger prefix, the structural counting traversal, and the
exact-output completion traversal. -/
def canonicalEnvelope (formula : CNFFormula) : Nat :=
  CNFToNANDControllerCanonicalTrace.canonicalPrefixSteps formula +
    CNFToNANDControllerCountTrace.countPassEnvelope formula +
    CNFToNANDControllerCompletionTrace.completionEnvelope formula

/-- The three structural phases fit in the controller polynomial declared
solely from the encoded input length. -/
theorem canonicalEnvelope_le_controllerWorkBound
    (formula : CNFFormula) :
    canonicalEnvelope formula ≤
      controllerWorkBound (encodeCNF formula).length := by
  unfold canonicalEnvelope
  exact allocatedComponents_le_controllerWorkBound
    (encodeCNF formula).length
    (CNFToNANDControllerCanonicalTrace.canonicalPrefixSteps formula)
    (CNFToNANDControllerCountTrace.countPassEnvelope formula)
    (CNFToNANDControllerCompletionTrace.completionEnvelope formula)
    (canonicalPrefixSteps_le_seven_phaseUnits formula)
    (CNFToNANDControllerCountTrace.countPassEnvelope_le_allocated formula)
    (CNFToNANDControllerCompletionTrace.completionEnvelope_le_allocated
      formula)

end PNP.Concrete.CNFToNANDControllerTotalBound
