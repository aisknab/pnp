import PNP.Concrete.ResidualReduction.SourceCandidateDirectionSearch

/-! The outer affine-query search retains its source and map while visiting
zero and then every unit parameter. A protected outer counter is separate
from the inner direction counter. These instructions include all state
restoration and both successful and failed candidate exits. -/

namespace PNP.Concrete.ResidualReduction.SourceAffineSearch
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding

structure Outcome where
  unitParameter : Bool
  parameterIndex : Nat
  directionIndex : Nat
  found : Bool
deriving DecidableEq

def unitResult {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (i : Nat) : Nat × Bool :=
  if h : i < k then SourceCandidateDirectionSearch.scan
    (SourceCandidateDirectionSearch.active F forms (some ⟨i, h⟩)) n 0 else (0, false)
def unitCost {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (i : Nat) : Nat :=
  if h : i < k then SourceCandidateDirectionSearch.fuel F forms (some ⟨i, h⟩) n 0 else 0
def zeroResult {n k : Nat} (F : Family n) (forms : AffineMap F.length k) : Nat × Bool :=
  SourceCandidateDirectionSearch.scan (SourceCandidateDirectionSearch.active F forms none) n 0
def zeroCost {n k : Nat} (F : Family n) (forms : AffineMap F.length k) : Nat :=
  SourceCandidateDirectionSearch.fuel F forms none n 0
def directionBudget (n k rows : Nat) : Nat := ((9 * k + 24 * n + 98) * rows + 22) * n + 1

theorem unitCost_bound {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (i : Fin k) :
    unitCost F forms i.val ≤ directionBudget n k F.length := by
  rw [unitCost, dif_pos i.isLt]
  exact SourceCandidateDirectionSearch.fuel_bound F forms (some i) n 0 (by omega)
theorem zeroCost_bound {n k : Nat} (F : Family n) (forms : AffineMap F.length k) :
    zeroCost F forms ≤ directionBudget n k F.length :=
  SourceCandidateDirectionSearch.fuel_bound F forms none n 0 (by omega)

structure State where
  core : SourceCandidateDirectionSearch.State
  remaining : BitString
def State.frame (r : State) : Store 1 := .cons r.remaining .nil
def State.store (r : State) : Store 22 := Frame.join r.core.store r.frame
def lifted (body : Block 21) : Block 22 := Frame.block 1 body
theorem lifted_exec (body : Block 21) (r : State) (fuel : Nat) (after : SourceCandidateDirectionSearch.State)
    (checked : Exec body r.core.store fuel after.store) :
    Exec (lifted body) r.store fuel ({r with core := after}).store := Frame.execution checked r.frame

/-- Natural indices allow the exhausted cursor k without manufacturing a Fin k. -/
def ready {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (unitParameter : Bool)
    (i j inner outer : Nat) (found : Bool) : State :=
  ⟨⟨SourceCandidateEvaluation.result F j found, mapBits forms, List.replicate k true,
    List.replicate i true, (if unitParameter then [true] else []), List.replicate inner true⟩,
    List.replicate outer true⟩
def finished {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (outcome : Outcome) : State :=
  ready F forms outcome.unitParameter outcome.parameterIndex outcome.directionIndex
    (if outcome.found then 0 else n) 0 outcome.found

theorem unit_run {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (i : Fin k) (count : Nat) :
    Exec (lifted SourceCandidateDirectionSearch.loop) (ready F forms true i.val 0 n count false).store
      (unitCost F forms i.val)
      (ready F forms true i.val (unitResult F forms i.val).1 0 count (unitResult F forms i.val).2).store := by
  simp only [unitCost, unitResult, dif_pos i.isLt]
  exact lifted_exec _ (ready F forms true i.val 0 n count false) _ _
    (SourceCandidateDirectionSearch.complete_exec F forms (some i))

theorem zero_run {n k : Nat} (F : Family n) (forms : AffineMap F.length k) :
    Exec (lifted SourceCandidateDirectionSearch.loop) (ready F forms false 0 0 n 0 false).store
      (zeroCost F forms)
      (ready F forms false 0 (zeroResult F forms).1 0 0 (zeroResult F forms).2).store :=
  lifted_exec _ (ready F forms false 0 0 n 0 false) _ _
    (SourceCandidateDirectionSearch.complete_exec F forms none)

def advanceCursor : Block 22 := .seq (.action (.push 18 true))
  (.seq (.action (.clear 10)) (.action (.clear 15)))
def advanceCounters : Block 22 := .seq (.action (.copy 20 14)) (.action (.pop 21))
def advanceUnit : Block 22 := .seq advanceCursor advanceCounters

theorem advanceUnit_exec {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (i j count : Nat) :
    Exec advanceUnit (ready F forms true i j 0 (count + 1) false).store 5
      (ready F forms true (i + 1) 0 n count false).store := by
  have cursor : Exec advanceCursor (ready F forms true i j 0 (count + 1) false).store 3
      (ready F forms true (i + 1) 0 0 (count + 1) false).store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have counters : Exec advanceCounters (ready F forms true (i + 1) 0 0 (count + 1) false).store 2
      (ready F forms true (i + 1) 0 n count false).store := Exec.seq (.action _ _) (.action _ _)
  exact Exec.seq cursor counters

def unitDecision : Block 22 := .branch 8 advanceUnit advanceUnit (.action (.clear 21))
def unitStep : Block 22 := .seq (lifted SourceCandidateDirectionSearch.loop) unitDecision

theorem unitStep_false {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (i : Fin k) (count : Nat)
    (failed : (unitResult F forms i.val).2 = false) :
    Exec unitStep (ready F forms true i.val 0 n (count + 1) false).store
      (unitCost F forms i.val + 6) (ready F forms true (i.val + 1) 0 n count false).store := by
  have run := unit_run F forms i (count + 1)
  rw [failed] at run
  have finish : Exec unitDecision (ready F forms true i.val (unitResult F forms i.val).1 0 (count + 1) false).store 6
      (ready F forms true (i.val + 1) 0 n count false).store :=
    Exec.zero (source := (8 : Fin 22)) rfl (advanceUnit_exec F forms i.val (unitResult F forms i.val).1 count)
  exact Exec.seq run finish

theorem unitStep_true {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (i : Fin k) (count : Nat)
    (found : (unitResult F forms i.val).2 = true) :
    Exec unitStep (ready F forms true i.val 0 n (count + 1) false).store
      (unitCost F forms i.val + 2)
      (ready F forms true i.val (unitResult F forms i.val).1 0 0 true).store := by
  have run := unit_run F forms i (count + 1)
  rw [found] at run
  have finish : Exec unitDecision (ready F forms true i.val (unitResult F forms i.val).1 0 (count + 1) true).store 2
      (ready F forms true i.val (unitResult F forms i.val).1 0 0 true).store :=
    Exec.one (source := (8 : Fin 22)) rfl (.action _ _)
  exact Exec.seq run finish

def zeroCursor : Block 22 := .seq (.action (.push 19 true))
  (.seq (.action (.clear 10)) (.action (.clear 15)))
def zeroCounters : Block 22 := .seq (.action (.copy 20 14)) (.action (.copy 21 17))
def zeroAdvance : Block 22 := .seq zeroCursor zeroCounters
theorem zeroAdvance_exec {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (j : Nat) :
    Exec zeroAdvance (ready F forms false 0 j 0 0 false).store 5
      (ready F forms true 0 0 n k false).store := by
  have cursor : Exec zeroCursor (ready F forms false 0 j 0 0 false).store 3
      (ready F forms true 0 0 0 0 false).store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have counters : Exec zeroCounters (ready F forms true 0 0 0 0 false).store 2
      (ready F forms true 0 0 n k false).store := Exec.seq (.action _ _) (.action _ _)
  exact Exec.seq cursor counters

end PNP.Concrete.ResidualReduction.SourceAffineSearch
