import PNP.Concrete.ResidualReduction.SourceMatrixColumnLoop

/-! Complete source-derived affine-mask payload construction. The nested
literal loops generate all n*n equations in exactly the existing order.
The prepared input consists of the original family bytes and its unary
dimension, not a matrix or coefficient oracle. Raw packet validation and
matrix header serialization remain separate execution obligations. -/

namespace PNP.Concrete.ResidualReduction.SourceMatrixConstruction
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.SourceMatrixSchedule

def outerPrepare : Block 15 := .seq (.action (.copy 14 9)) (.action (.clear 11))
def outerAdvance : Block 15 := .seq (.action (.push 10 true))
  (.seq (.action (.clear 11)) (.action (.pop 13)))
def outerStep : Block 15 := .seq outerPrepare (.seq columnLoop outerAdvance)

theorem outerStep_exec {n : Nat} (F : Family n) (i : Fin n) (remaining : Nat) (output : BitString) :
    Exec outerStep (ready F i.val 0 (remaining + 1) 0 output).store
      (columnFuel n F.length i.val 0 n + 5)
      (ready F (i.val + 1) 0 remaining 0 ((columnBytes F i.val 0 n).reverse ++ output)).store := by
  have prepared : Exec outerPrepare (ready F i.val 0 (remaining + 1) 0 output).store 2
      (ready F i.val 0 (remaining + 1) n output).store := Exec.seq (.action _ _) (.action _ _)
  have columns : Exec columnLoop (ready F i.val 0 (remaining + 1) n output).store
      (columnFuel n F.length i.val 0 n)
      (ready F i.val n (remaining + 1) 0 ((columnBytes F i.val 0 n).reverse ++ output)).store := by
    simpa only [Nat.zero_add] using
      columnLoop_exec F i n 0 (remaining + 1) output (by omega)
  have advanced : Exec outerAdvance
      (ready F i.val n (remaining + 1) 0 ((columnBytes F i.val 0 n).reverse ++ output)).store 3
      (ready F (i.val + 1) 0 remaining 0 ((columnBytes F i.val 0 n).reverse ++ output)).store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have cost : columnFuel n F.length i.val 0 n + 5 = 2 + (columnFuel n F.length i.val 0 n + 3) := by omega
  simpa only [outerStep, cost] using Exec.seq prepared (Exec.seq columns advanced)

def matrixLoop : Block 15 := .loop 13 outerStep
def matrixFuel (n rows : Nat) : Nat → Nat → Nat
  | _, 0 => 1
  | i, count + 1 => 1 + ((columnFuel n rows i 0 n + 5) + matrixFuel n rows (i + 1) count)

theorem matrixLoop_exec {n : Nat} (F : Family n) (count i : Nat) (output : BitString)
    (bound : i + count ≤ n) :
    Exec matrixLoop (ready F i 0 count 0 output).store (matrixFuel n F.length i count)
      (ready F (i + count) 0 0 0 ((matrixBytes F i count).reverse ++ output)).store := by
  induction count generalizing i output with
  | zero => exact Exec.loopStop rfl
  | succ count ih =>
    have hi : i < n := by omega
    let current : Fin n := ⟨i, hi⟩
    have step := outerStep_exec F current count output
    have rest := ih (i + 1) ((columnBytes F i 0 n).reverse ++ output) (by omega)
    have checked := Exec.loopStep (source := (13 : Fin 15)) rfl step rest
    have index : i + 1 + count = i + (count + 1) := by omega
    simpa only [matrixLoop, matrixFuel, current, matrixBytes_succ, List.reverse_append,
      List.append_assoc, index] using checked

theorem matrixFuel_bound {n : Nat} (F : Family n) (count i : Nat) (bound : i + count ≤ n) :
    matrixFuel n F.length i count ≤ (((24 * n + 62) * F.length + 6) * n + 7) * count + 1 := by
  induction count generalizing i with
  | zero => exact Nat.le_refl 1
  | succ count ih =>
    have hi : i < n := by omega
    have one := columnFuel_bound F ⟨i, hi⟩ n 0 (by omega)
    have rest := ih (i + 1) (by omega)
    simp only [matrixFuel, Nat.mul_add, Nat.mul_one] at one rest ⊢
    omega

def inputState {n : Nat} (F : Family n) : State :=
  ⟨SourcePolarInstructions.working n 0 0 [] (familyBits F) [] [], [], [], []⟩
def seed : Block 15 := .seq (.action (.copy 12 0))
  (.seq (.action (.clear 0)) (.action (.copy 13 9)))
theorem seed_exec {n : Nat} (F : Family n) : Exec seed (inputState F).store 3 (ready F 0 0 n 0 []).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))

def reorder : Block 15 := .seq (.seq (.action (.copy 3 8)) (.action (.clear 8)))
  (lifted (MatrixReconstruction.lift ClauseQuery.reverseLoop))
theorem reorder_exec {n : Nat} (F : Family n) (word : BitString) :
    Exec reorder (ready F n 0 0 0 word.reverse).store (4 * word.length + 3)
      (ready F n 0 0 0 word).store := by
  let before := ready F n 0 0 0 word.reverse
  let prepared : State := {before with core := {before.core with core := {before.core.core with excess := word.reverse, output := []}}}
  have copied : Exec (.seq (.action (.copy (3 : Fin 15) 8)) (.action (.clear 8))) before.store 2 prepared.store :=
    Exec.seq (.action _ _) (.action _ _)
  have core : Exec ClauseQuery.reverseLoop prepared.core.core.store (4 * word.length + 1)
      (ready F n 0 0 0 word).core.core.store := by
    simpa only [prepared, before, ready, SourcePolarInstructions.working, MatrixInstructions.base,
      List.length_reverse, List.reverse_reverse, List.append_nil] using
      ClauseQuery.reverse_exec (ready F n 0 0 0 []).core.core word.reverse
  have inner := MatrixReconstruction.lift_exec ClauseQuery.reverseLoop prepared.core
    (4 * word.length + 1) (ready F n 0 0 0 word).core.core core
  have outer := lifted_exec (MatrixReconstruction.lift ClauseQuery.reverseLoop) prepared
    (4 * word.length + 1) (ready F n 0 0 0 word).core inner
  have cost : 4 * word.length + 3 = 2 + (4 * word.length + 1) := by omega
  simpa only [reorder, cost, prepared, before, ready] using Exec.seq copied outer

def payload : Block 15 := .seq seed (.seq matrixLoop reorder)
def payloadFuel (n rows : Nat) : Nat := matrixFuel n rows 0 n + 4 * ((rows + 1) * (n * n)) + 6

theorem payload_exec {n : Nat} (F : Family n) :
    Exec payload (inputState F).store (payloadFuel n F.length)
      (ready F n 0 0 0 (MatrixInstructions.matrixBits (SourceClosure.affineMaskRows F))).store := by
  have loop : Exec matrixLoop (ready F 0 0 n 0 []).store (matrixFuel n F.length 0 n)
      (ready F n 0 0 0 (matrixBytes F 0 n).reverse).store := by
    simpa only [Nat.zero_add, List.append_nil] using matrixLoop_exec F n 0 [] (by omega)
  have cost : payloadFuel n F.length = 3 + (matrixFuel n F.length 0 n + (4 * (matrixBytes F 0 n).length + 3)) := by
    rw [matrixBytes_length]; unfold payloadFuel; omega
  simpa only [payload, cost, matrixBytes_exact] using
    Exec.seq (seed_exec F) (Exec.seq loop (reorder_exec F (matrixBytes F 0 n)))

def payloadBudget (n rows : Nat) : Nat :=
  (((24 * n + 62) * rows + 6) * n + 7) * n + 4 * ((rows + 1) * (n * n)) + 7
theorem payloadFuel_bound {n : Nat} (F : Family n) : payloadFuel n F.length ≤ payloadBudget n F.length := by
  have main := matrixFuel_bound F n 0 (by omega)
  unfold payloadFuel payloadBudget
  omega

end PNP.Concrete.ResidualReduction.SourceMatrixConstruction
