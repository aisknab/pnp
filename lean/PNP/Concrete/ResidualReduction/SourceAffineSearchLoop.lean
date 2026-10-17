import PNP.Concrete.ResidualReduction.SourceAffineSearchInstructions

/-! Complete zero-then-unit affine candidate search. The source-instruction
bound includes all unsuccessful candidates and repeated direction tests.
A missing success remains explicit; this search does not assert that an
improvement exists for every residual problem. -/

namespace PNP.Concrete.ResidualReduction.SourceAffineSearch
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear

def unitSearch {n k : Nat} (F : Family n) (forms : AffineMap F.length k) : Nat → Nat → Outcome
  | 0, i => ⟨true, i, 0, false⟩
  | count + 1, i => if (unitResult F forms i).2 then
      ⟨true, i, (unitResult F forms i).1, true⟩ else unitSearch F forms count (i + 1)
def unitFuel {n k : Nat} (F : Family n) (forms : AffineMap F.length k) : Nat → Nat → Nat
  | 0, _ => 1
  | count + 1, i => if (unitResult F forms i).2 then
      1 + ((unitCost F forms i + 2) + 1)
    else 1 + ((unitCost F forms i + 6) + unitFuel F forms count (i + 1))
def unitLoop : Block 22 := .loop 21 unitStep

theorem unitLoop_exec {n k : Nat} (F : Family n) (forms : AffineMap F.length k)
    (count i : Nat) (bound : i + count ≤ k) :
    Exec unitLoop (ready F forms true i 0 n count false).store (unitFuel F forms count i)
      (finished F forms (unitSearch F forms count i)).store := by
  induction count generalizing i with
  | zero => exact Exec.loopStop rfl
  | succ count ih =>
    have inside : i < k := by omega
    let current : Fin k := ⟨i, inside⟩
    cases h : (unitResult F forms i).2 with
    | false =>
      have first := unitStep_false F forms current count h
      have rest := ih (i + 1) (by omega)
      have checked := Exec.loopStep (source := (21 : Fin 22)) rfl first rest
      simpa only [unitLoop, unitFuel, unitSearch, h, Bool.false_eq_true, if_false, current] using checked
    | true =>
      have first := unitStep_true F forms current count h
      have last : Exec unitLoop (ready F forms true i (unitResult F forms i).1 0 0 true).store 1
          (ready F forms true i (unitResult F forms i).1 0 0 true).store := Exec.loopStop rfl
      have checked := Exec.loopStep (source := (21 : Fin 22)) rfl first last
      simpa only [unitLoop, unitFuel, unitSearch, h, if_true, finished, current] using checked

theorem unitFuel_bound {n k : Nat} (F : Family n) (forms : AffineMap F.length k)
    (count i : Nat) (bound : i + count ≤ k) :
    unitFuel F forms count i ≤ (directionBudget n k F.length + 7) * count + 1 := by
  induction count generalizing i with
  | zero => exact Nat.le_refl 1
  | succ count ih =>
    have inside : i < k := by omega
    have one := unitCost_bound F forms (⟨i, inside⟩ : Fin k)
    change unitCost F forms i ≤ directionBudget n k F.length at one
    have rest := ih (i + 1) (by omega)
    cases h : (unitResult F forms i).2 <;>
      simp only [unitFuel, h, Bool.false_eq_true, if_false, if_true, Nat.mul_add, Nat.mul_one] <;> omega

def outcome {n k : Nat} (F : Family n) (forms : AffineMap F.length k) : Outcome :=
  if (zeroResult F forms).2 then ⟨false, 0, (zeroResult F forms).1, true⟩ else unitSearch F forms k 0
def fuel {n k : Nat} (F : Family n) (forms : AffineMap F.length k) : Nat :=
  zeroCost F forms + if (zeroResult F forms).2 then 2 else 1 + (5 + unitFuel F forms k 0)
def continueUnits : Block 22 := .seq zeroAdvance unitLoop
def zeroDecision : Block 22 := .branch 8 continueUnits continueUnits .skip
def block : Block 22 := .seq (lifted SourceCandidateDirectionSearch.loop) zeroDecision

theorem block_exec {n k : Nat} (F : Family n) (forms : AffineMap F.length k) :
    Exec block (ready F forms false 0 0 n 0 false).store (fuel F forms)
      (finished F forms (outcome F forms)).store := by
  have first := zero_run F forms
  cases h : (zeroResult F forms).2 with
  | false =>
    rw [h] at first
    have rest := unitLoop_exec F forms k 0 (by omega)
    have started := Exec.seq (zeroAdvance_exec F forms (zeroResult F forms).1) rest
    have finish : Exec zeroDecision (ready F forms false 0 (zeroResult F forms).1 0 0 false).store
        (1 + (5 + unitFuel F forms k 0)) (finished F forms (unitSearch F forms k 0)).store :=
      Exec.zero (source := (8 : Fin 22)) rfl started
    simpa only [block, fuel, outcome, h, Bool.false_eq_true, if_false] using Exec.seq first finish
  | true =>
    rw [h] at first
    have finish : Exec zeroDecision (ready F forms false 0 (zeroResult F forms).1 0 0 true).store 2
        (ready F forms false 0 (zeroResult F forms).1 0 0 true).store :=
      Exec.one (source := (8 : Fin 22)) rfl (.skip _)
    simpa only [block, fuel, outcome, h, if_true, finished] using Exec.seq first finish

theorem fuel_bound {n k : Nat} (F : Family n) (forms : AffineMap F.length k) :
    fuel F forms ≤ (directionBudget n k F.length + 7) * (k + 1) := by
  have first := zeroCost_bound F forms
  have rest := unitFuel_bound F forms k 0 (by omega)
  cases h : (zeroResult F forms).2 <;>
    simp only [fuel, h, Bool.false_eq_true, if_false, if_true, Nat.mul_add, Nat.mul_one] <;> omega

theorem directionBudget_mono (n k rows N K R : Nat) (hn : n ≤ N) (hk : k ≤ K) (hr : rows ≤ R) :
    directionBudget n k rows ≤ directionBudget N K R := by
  have factor : 9 * k + 24 * n + 98 ≤ 9 * K + 24 * N + 98 := by omega
  have row := Nat.mul_le_mul factor hr
  have outer := Nat.mul_le_mul (show (9 * k + 24 * n + 98) * rows + 22 ≤
    (9 * K + 24 * N + 98) * R + 22 by omega) hn
  unfold directionBudget
  omega

theorem computed_fuel_bound {n : Nat} (F : Family n) (s : Space F.length)
    (computed : solve F.length (SourceClosure.affineMaskRows F) = some s) :
    fuel F s.forms ≤ (directionBudget n F.length F.length + 7) * (F.length + 1) := by
  have parameters := solve_some_parameter_bound (SourceClosure.affineMaskRows F) s computed
  have budget := directionBudget_mono n s.parameters F.length n F.length F.length
    (Nat.le_refl n) parameters (Nat.le_refl F.length)
  have total := Nat.mul_le_mul (show directionBudget n s.parameters F.length + 7 ≤
    directionBudget n F.length F.length + 7 by omega) (Nat.succ_le_succ parameters)
  exact Nat.le_trans (fuel_bound F s.forms) total

/-- The search cost is expressed in original source-packet length. Preparation,
solver execution and final witness serialization remain separate charged phases. -/
theorem original_input_fuel_bound {n : Nat} (F : Family n) (s : Space F.length)
    (computed : solve F.length (SourceClosure.affineMaskRows F) = some s) :
    let L := (SourceMatrixEncoding.codec.encode ⟨n, F⟩).length
    fuel F s.forms ≤ (directionBudget L L L + 7) * (L + 1) := by
  let L := (SourceMatrixEncoding.codec.encode ⟨n, F⟩).length
  have hn := SourceMatrixEncoding.dimension_bound n F
  have hr := SourceMatrixEncoding.rowCount_bound n F
  have budget := directionBudget_mono n F.length F.length L L L hn hr hr
  have total := Nat.mul_le_mul (show directionBudget n F.length F.length + 7 ≤
    directionBudget L L L + 7 by omega) (Nat.succ_le_succ hr)
  exact Nat.le_trans (computed_fuel_bound F s computed) total

end PNP.Concrete.ResidualReduction.SourceAffineSearch
