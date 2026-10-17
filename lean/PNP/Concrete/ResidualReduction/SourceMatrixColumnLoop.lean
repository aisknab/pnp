import PNP.Concrete.ResidualReduction.SourceMatrixSchedule

/-! The inner source-matrix loop visits every second coordinate, restoring
the original family before each equation. Protected words retain the source
bytes and both loop counters. All copying, scanning, and counter steps are
included in the source-instruction fuel. -/

namespace PNP.Concrete.ResidualReduction.SourceMatrixConstruction
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.SourceMatrixSchedule
open PNP.Concrete.ResidualReduction.SourceMatrixRowInstructions

structure State where
  core : MatrixReconstruction.State
  source : BitString
  outer : BitString
  inner : BitString

def State.frame (r : State) : Store 3 := .cons r.source (.cons r.outer (.cons r.inner .nil))
def State.store (r : State) : Store 15 := Frame.join r.core.store r.frame
def lifted (body : Block 12) : Block 15 := Frame.block 3 body
theorem lifted_exec (body : Block 12) (r : State) (fuel : Nat) (after : MatrixReconstruction.State)
    (checked : Exec body r.core.store fuel after.store) :
    Exec (lifted body) r.store fuel ({r with core := after}).store := Frame.execution checked r.frame

def ready {n : Nat} (F : Family n) (i j outer inner : Nat) (output : BitString) : State :=
  ⟨SourcePolarInstructions.working n i j [] [] [] output, familyBits F,
    List.replicate outer true, List.replicate inner true⟩

def innerAdvance : Block 15 := .seq (.action (.push 11 true)) (.action (.pop 14))
def innerStep : Block 15 := .seq (.action (.copy 0 12)) (.seq (lifted matrixRow) innerAdvance)

theorem innerStep_exec {n : Nat} (F : Family n) (i j : Fin n)
    (outer remaining : Nat) (output : BitString) :
    Exec innerStep (ready F i.val j.val outer (remaining + 1) output).store
      (loopFuel n i.val j.val F.length + 4)
      (ready F i.val (j.val + 1) outer remaining ((equationBytes F i.val j.val).reverse ++ output)).store := by
  let before := ready F i.val j.val outer (remaining + 1) output
  let loaded : State := {before with core := SourcePolarInstructions.working n i.val j.val [] (familyBits F) [] output}
  let emitted : State := {before with core := SourcePolarInstructions.working n i.val j.val [] [] [] ((equationBytes F i.val j.val).reverse ++ output)}
  have copied : Exec (.action (.copy (0 : Fin 15) 12)) before.store 1 loaded.store := .action _ _
  have equation : Exec (lifted matrixRow) loaded.store (loopFuel n i.val j.val F.length + 1) emitted.store :=
    lifted_exec matrixRow loaded _ emitted.core (matrixRow_exec F i j [] output)
  have advanced : Exec innerAdvance emitted.store 2
      (ready F i.val (j.val + 1) outer remaining ((equationBytes F i.val j.val).reverse ++ output)).store :=
    Exec.seq (.action _ _) (.action _ _)
  have cost : loopFuel n i.val j.val F.length + 4 = 1 + ((loopFuel n i.val j.val F.length + 1) + 2) := by omega
  simpa only [innerStep, cost] using Exec.seq copied (Exec.seq equation advanced)

def columnLoop : Block 15 := .loop 14 innerStep
def columnFuel (n rows i : Nat) : Nat → Nat → Nat
  | _, 0 => 1
  | j, count + 1 => 1 + ((loopFuel n i j rows + 4) + columnFuel n rows i (j + 1) count)

theorem columnLoop_exec {n : Nat} (F : Family n) (i : Fin n)
    (count j outer : Nat) (output : BitString) (bound : j + count ≤ n) :
    Exec columnLoop (ready F i.val j outer count output).store
      (columnFuel n F.length i.val j count)
      (ready F i.val (j + count) outer 0 ((columnBytes F i.val j count).reverse ++ output)).store := by
  induction count generalizing j output with
  | zero => exact Exec.loopStop rfl
  | succ count ih =>
    have hj : j < n := by omega
    let current : Fin n := ⟨j, hj⟩
    have step := innerStep_exec F i current outer count output
    have rest := ih (j + 1) ((equationBytes F i.val j).reverse ++ output) (by omega)
    have checked := Exec.loopStep (source := (14 : Fin 15)) rfl step rest
    have index : j + 1 + count = j + (count + 1) := by omega
    simpa only [columnLoop, columnFuel, current, columnBytes_succ, List.reverse_append,
      List.append_assoc, index] using checked

/-- The bound includes every failed or successful coefficient test alike. -/
theorem columnFuel_bound {n : Nat} (F : Family n) (i : Fin n)
    (count j : Nat) (bound : j + count ≤ n) :
    columnFuel n F.length i.val j count ≤ ((24 * n + 62) * F.length + 6) * count + 1 := by
  induction count generalizing j with
  | zero => exact Nat.le_refl 1
  | succ count ih =>
    have hj : j < n := by omega
    have one := matrixRowFuel_bound F i ⟨j, hj⟩
    have rest := ih (j + 1) (by omega)
    simp only [columnFuel, Nat.mul_add, Nat.mul_one] at one rest ⊢
    omega

end PNP.Concrete.ResidualReduction.SourceMatrixConstruction
