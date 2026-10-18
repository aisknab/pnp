import PNP.Concrete.ResidualReduction.SourceCoefficientInstructions

/-! Source-row factor reads with protected dimension and coordinate counters.
Every scan is a literal finite-word loop. The same original row bytes are
restored before each read; the selected flag and affine constants cannot be
mistaken for linear coefficients. -/

namespace PNP.Concrete.ResidualReduction.SourcePolarInstructions
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixReconstruction
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.SourceCoefficientInstructions
open PNP.Concrete.ResidualReduction.FactoredContraction

def ticks (r : State) (second : Bool) : BitString := if second then r.pending else r.history
def indexRegister (second : Bool) : Fin 12 := if second then 11 else 10
def readCurrent (second : Bool) : Block 12 :=
  .seq (.action (.copy 2 (indexRegister second))) (lift read)
def readAfter (r : State) (k : Nat) : State :=
  {r with core := {r.core with input := r.core.input.drop k, remaining := [], excess := bitAt r.core.input k :: r.core.excess}}

theorem readCurrent_exec (r : State) (second : Bool) (k : Nat)
    (counter : ticks r second = List.replicate k true) :
    Exec (readCurrent second) r.store (3 * k + 4) (readAfter r k).store := by
  let prepared : State := {r with core := {r.core with remaining := List.replicate k true}}
  have copied : Exec (.action (.copy (2 : Fin 12) (indexRegister second))) r.store 1 prepared.store := by
    have direct : Exec (.action (.copy (2 : Fin 12) (indexRegister second))) r.store 1
        ({r with core := {r.core with remaining := ticks r second}}).store := by
      cases second <;> exact .action _ _
    simpa only [counter, prepared] using direct
  have body : Exec (lift read) prepared.store (3 * k + 3) (readAfter r k).store :=
    lift_exec read prepared _ (readAfter r k).core (read_exec r.core k)
  have cost : 3 * k + 4 = 1 + (3 * k + 3) := by omega
  simpa only [readCurrent, cost] using Exec.seq copied body

def restoreLeft : Block 12 := .seq (.action (.copy 0 7)) (.action (.pop 0))
def leftReady (r : State) : State := {r with core := {r.core with input := r.core.reserved.tail}}
theorem restoreLeft_exec (r : State) : Exec restoreLeft r.store 2 (leftReady r).store :=
  Exec.seq (.action _ _) (.action _ _)

def widthCounter : Block 12 := .seq (.action (.copy 2 9)) (.action (.push 2 true))
theorem widthCounter_exec (r : State) (n : Nat) (width : r.width = List.replicate n true) :
    Exec widthCounter r.store 2
      ({r with core := {r.core with remaining := List.replicate (n + 1) true}}).store := by
  have direct : Exec widthCounter r.store 2
      ({r with core := {r.core with remaining := true :: r.width}}).store :=
    Exec.seq (.action _ _) (.action _ _)
  simpa only [width, List.replicate_succ] using direct

def skipFactor : Block 12 := .seq widthCounter (lift dropLoop)
def skipped (r : State) (n : Nat) : State :=
  {r with core := {r.core with input := r.core.input.drop (n + 1), remaining := []}}
theorem skipFactor_exec (r : State) (n : Nat) (width : r.width = List.replicate n true) :
    Exec skipFactor r.store (3 * (n + 1) + 3) (skipped r n).store := by
  let prepared : State := {r with core := {r.core with remaining := List.replicate (n + 1) true}}
  have body : Exec (lift dropLoop) prepared.store (3 * (n + 1) + 1) (skipped r n).store :=
    lift_exec dropLoop prepared _ (skipped r n).core (drop_all r.core r.core.input (n + 1))
  have cost : 3 * (n + 1) + 3 = 2 + (3 * (n + 1) + 1) := by omega
  simpa only [skipFactor, cost] using Exec.seq (widthCounter_exec r n width) body

def restoreRight : Block 12 := .seq restoreLeft skipFactor
def rightReady (r : State) (n : Nat) : State := skipped (leftReady r) n
theorem restoreRight_exec (r : State) (n : Nat) (width : r.width = List.replicate n true) :
    Exec restoreRight r.store (3 * (n + 1) + 5) (rightReady r n).store := by
  have cost : 3 * (n + 1) + 5 = 2 + (3 * (n + 1) + 3) := by omega
  simpa only [restoreRight, rightReady, cost] using
    Exec.seq (restoreLeft_exec r) (skipFactor_exec (leftReady r) n width)

def readLeft (second : Bool) : Block 12 := .seq restoreLeft (readCurrent second)
def readRight (second : Bool) : Block 12 := .seq restoreRight (readCurrent second)
theorem readLeft_exec (r : State) (second : Bool) (k : Nat)
    (counter : ticks r second = List.replicate k true) :
    Exec (readLeft second) r.store (3 * k + 6) (readAfter (leftReady r) k).store := by
  have cost : 3 * k + 6 = 2 + (3 * k + 4) := by omega
  simpa only [readLeft, cost] using
    Exec.seq (restoreLeft_exec r) (readCurrent_exec (leftReady r) second k counter)
theorem readRight_exec (r : State) (second : Bool) (n k : Nat)
    (width : r.width = List.replicate n true) (counter : ticks r second = List.replicate k true) :
    Exec (readRight second) r.store (3 * (n + 1) + 3 * k + 9)
      (readAfter (rightReady r n) k).store := by
  have cost : 3 * (n + 1) + 3 * k + 9 = (3 * (n + 1) + 5) + (3 * k + 4) := by omega
  simpa only [readRight, cost] using
    Exec.seq (restoreRight_exec r n width) (readCurrent_exec (rightReady r n) second k counter)

def advance : Block 12 := .seq restoreRight (.seq skipFactor (.action (.clear 7)))
def advanced (r : State) (n : Nat) : State :=
  let after := skipped (rightReady r n) n
  {after with core := {after.core with reserved := []}}
theorem advance_exec (r : State) (n : Nat) (width : r.width = List.replicate n true) :
    Exec advance r.store (6 * (n + 1) + 9) (advanced r n).store := by
  have cleared : Exec (.action (.clear (7 : Fin 12))) (skipped (rightReady r n) n).store 1
      (advanced r n).store := .action _ _
  have cost : 6 * (n + 1) + 9 = (3 * (n + 1) + 5) + ((3 * (n + 1) + 3) + 1) := by omega
  simpa only [advance, cost] using Exec.seq (restoreRight_exec r n width)
    (Exec.seq (skipFactor_exec (rightReady r n) n width) cleared)

def working (n i j : Nat) (saved input stack output : BitString) : State :=
  ⟨{base 0 saved with input := input, excess := stack, output := output},
    List.replicate n true, List.replicate i true, List.replicate j true⟩

theorem left_source_bit {n : Nat} (r : Row n) (suffix : BitString) (k : Fin n) :
    bitAt ((rowWord r ++ suffix).tail) k.val = bitAt (affineWord r.left) k.val := by
  change bitAt ((affineWord r.left ++ affineWord r.right) ++ suffix) k.val = _
  rw [List.append_assoc]
  exact bitAt_append _ _ _ (by rw [affineWord_length]; omega)

theorem right_source_tail {n : Nat} (r : Row n) (suffix : BitString) :
    ((rowWord r ++ suffix).tail).drop (n + 1) = affineWord r.right ++ suffix := by
  change ((affineWord r.left ++ affineWord r.right) ++ suffix).drop (n + 1) = _
  rw [List.append_assoc, ← affineWord_length r.left, List.drop_left]

theorem right_source_bit {n : Nat} (r : Row n) (suffix : BitString) (k : Fin n) :
    bitAt (((rowWord r ++ suffix).tail).drop (n + 1)) k.val = bitAt (affineWord r.right) k.val := by
  rw [right_source_tail]
  exact bitAt_append _ _ _ (by rw [affineWord_length]; omega)

theorem source_end {n : Nat} (r : Row n) (suffix : BitString) :
    (((rowWord r ++ suffix).tail).drop (n + 1)).drop (n + 1) = suffix := by
  rw [right_source_tail, ← affineWord_length r.right, List.drop_left]

/-- Four scans restore the saved row each time, then the fixed Boolean
operation emits exactly one matrix coefficient. -/
def coefficient : Block 12 := .seq (readLeft false) <| .seq (readRight true) <|
  .seq (readRight false) <| .seq (readLeft true) (lift emitPolar)

theorem coefficient_exec {n : Nat} (row : Row n) (i j : Fin n)
    (input suffix stack output : BitString) :
    Exec coefficient (working n i.val j.val (rowWord row ++ suffix) input stack output).store
      (6 * i.val + 6 * j.val + 6 * (n + 1) + 39)
      (working n i.val j.val (rowWord row ++ suffix)
        (((rowWord row ++ suffix).tail).drop j.val) stack (polarBit row i.val j.val :: output)).store := by
  let r0 := working n i.val j.val (rowWord row ++ suffix) input stack output
  let r1 := readAfter (leftReady r0) i.val
  let r2 := readAfter (rightReady r1 n) j.val
  let r3 := readAfter (rightReady r2 n) i.val
  let r4 := readAfter (leftReady r3) j.val
  have first : Exec (readLeft false) r0.store (3 * i.val + 6) r1.store :=
    readLeft_exec r0 false i.val rfl
  have second : Exec (readRight true) r1.store (3 * (n + 1) + 3 * j.val + 9) r2.store :=
    readRight_exec r1 true n j.val rfl rfl
  have third : Exec (readRight false) r2.store (3 * (n + 1) + 3 * i.val + 9) r3.store :=
    readRight_exec r2 false n i.val rfl rfl
  have fourth : Exec (readLeft true) r3.store (3 * j.val + 6) r4.store :=
    readLeft_exec r3 true j.val rfl
  let done := working n i.val j.val (rowWord row ++ suffix)
    (((rowWord row ++ suffix).tail).drop j.val) stack (polarBit row i.val j.val :: output)
  have finish : Exec (lift emitPolar) r4.store 9 done.store := by
    let before := working n i.val j.val (rowWord row ++ suffix)
      (((rowWord row ++ suffix).tail).drop j.val) stack output
    have core := emitPolar_exec before.core (bitAt (affineWord row.left) i.val)
      (bitAt (affineWord row.right) j.val) (bitAt (affineWord row.right) i.val)
      (bitAt (affineWord row.left) j.val)
    have lifted := lift_exec emitPolar
      {before with core := {before.core with excess := bitAt (affineWord row.left) j.val :: bitAt (affineWord row.right) i.val :: bitAt (affineWord row.right) j.val :: bitAt (affineWord row.left) i.val :: stack}}
      9 done.core core
    simpa only [r4, r3, r2, r1, r0, before, done, readAfter, leftReady, rightReady,
      skipped, working, base, left_source_bit, right_source_bit, polarBit] using lifted
  have cost : 6 * i.val + 6 * j.val + 6 * (n + 1) + 39 =
      (3 * i.val + 6) + ((3 * (n + 1) + 3 * j.val + 9) +
        ((3 * (n + 1) + 3 * i.val + 9) + ((3 * j.val + 6) + 9))) := by omega
  simpa only [coefficient, cost] using
    Exec.seq first (Exec.seq second (Exec.seq third (Exec.seq fourth finish)))

def rowBlock : Block 12 := .seq (.action (.copy 7 0)) (.seq coefficient advance)

/-- One whole source row is consumed, with all four reads and final skipping
included. No matrix coefficient, basis vector, or equation is supplied. -/
theorem rowBlock_exec {n : Nat} (row : Row n) (i j : Fin n) (suffix stack output : BitString) :
    Exec rowBlock (working n i.val j.val [] (rowWord row ++ suffix) stack output).store
      (6 * i.val + 6 * j.val + 12 * (n + 1) + 49)
      (working n i.val j.val [] suffix stack (polarBit row i.val j.val :: output)).store := by
  let saved := working n i.val j.val (rowWord row ++ suffix) (rowWord row ++ suffix) stack output
  have save : Exec (.action (.copy (7 : Fin 12) 0))
      (working n i.val j.val [] (rowWord row ++ suffix) stack output).store 1 saved.store := .action _ _
  let emitted := working n i.val j.val (rowWord row ++ suffix)
    (((rowWord row ++ suffix).tail).drop j.val) stack (polarBit row i.val j.val :: output)
  have finish : Exec advance emitted.store (6 * (n + 1) + 9)
      (working n i.val j.val [] suffix stack (polarBit row i.val j.val :: output)).store := by
    simpa only [advanced, skipped, rightReady, leftReady, emitted, working, base, source_end] using
      advance_exec emitted n rfl
  have cost : 6 * i.val + 6 * j.val + 12 * (n + 1) + 49 =
      1 + ((6 * i.val + 6 * j.val + 6 * (n + 1) + 39) + (6 * (n + 1) + 9)) := by omega
  simpa only [rowBlock, cost] using Exec.seq save
    (Exec.seq (coefficient_exec row i j (rowWord row ++ suffix) suffix stack output) finish)

theorem rowFuel_bound {n : Nat} (i j : Fin n) :
    6 * i.val + 6 * j.val + 12 * (n + 1) + 49 ≤ 24 * n + 61 := by omega

end PNP.Concrete.ResidualReduction.SourcePolarInstructions
