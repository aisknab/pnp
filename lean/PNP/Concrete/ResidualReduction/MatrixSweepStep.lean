import PNP.Concrete.NormalizerRegisterFrame
import PNP.Concrete.ResidualReduction.MatrixColumnInstructions

/-! A literal matrix-sweep step with protected dimension and pivot-history words.
It invokes the checked column block, saves the pivot actually discovered there,
and reinitializes the next column. History construction is counted, not supplied.
The history records are consumed in increasing width during later reconstruction. -/

namespace PNP.Concrete.ResidualReduction.MatrixSweep
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixInstructions

structure State where
  core : Registers
  pending : BitString
  history : BitString

def State.frame (r : State) : Store 2 := .cons r.pending (.cons r.history .nil)
def State.store (r : State) : Store 11 := Frame.join r.core.store r.frame
def lift (body : Block 9) : Block 11 := Frame.block 2 body

theorem lift_exec (body : Block 9) (r : State) (fuel : Nat) (after : Registers)
    (checked : Exec body r.core.store fuel after.store) :
    Exec (lift body) r.store fuel ({r with core := after}).store :=
  Frame.execution checked r.frame

def start (n : Nat) (rows : System n) (history : BitString) : State :=
  ⟨{base n (matrixBits rows) with input := matrixBits rows}, List.replicate n true, history⟩

/-- The leading tag distinguishes a free column from a saved pivot. Its width
is determined by the sweep depth; no numeric value is expanded into unary. -/
def recordBits {n : Nat} : Option (Affine n) → BitString
  | none => [false]
  | some p => true :: (affineWord p).reverse

def recordFuel {n : Nat} : Option (Affine n) → Nat
  | none => 2
  | some _ => 4 * (n + 1) + 4

def recordInput (n : Nat) (pivot : Option (Affine n))
    (input saved pending history : BitString) : State :=
  ⟨{pivotResult n saved pivot with input := input, output := history}, pending, history⟩
def recordOutput (n : Nat) (pivot : Option (Affine n))
    (input saved pending history : BitString) : State :=
  let r := recordInput n pivot input saved pending history
  {r with core := {r.core with output := recordBits pivot ++ history}}

def positiveRecord : Block 11 :=
  .seq (.action (.copy 3 4)) (.seq (lift ClauseQuery.reverseLoop) (.action (.push 8 true)))
def savePivot : Block 11 := .branch 6 (.action (.push 8 false)) positiveRecord positiveRecord

theorem savePivot_exec (n : Nat) (pivot : Option (Affine n))
    (input saved pending history : BitString) :
    Exec savePivot (recordInput n pivot input saved pending history).store
      (recordFuel pivot) (recordOutput n pivot input saved pending history).store := by
  cases pivot with
  | none => exact Exec.empty rfl (.action _ _)
  | some p =>
    let r := recordInput n (some p) input saved pending history
    let loaded := {r with core := {r.core with excess := affineWord p}}
    let reversed := {r with core := {r.core with excess := [], output := (affineWord p).reverse ++ history}}
    have load : Exec (.action (.copy (3 : Fin 11) 4)) r.store 1 loaded.store := .action _ _
    have coreReverse := ClauseQuery.reverse_exec r.core (affineWord p)
    rw [affineWord_length] at coreReverse
    have rev : Exec (lift ClauseQuery.reverseLoop) loaded.store
        (4 * (n + 1) + 1) reversed.store :=
      lift_exec _ loaded _ reversed.core coreReverse
    have tag : Exec (.action (.push (8 : Fin 11) true)) reversed.store 1
        (recordOutput n (some p) input saved pending history).store := .action _ _
    have checked : Exec savePivot r.store (1 + (1 + ((4 * (n + 1) + 1) + 1)))
        (recordOutput n (some p) input saved pending history).store :=
      Exec.one (source := (6 : Fin 11)) rfl (Exec.seq load (Exec.seq rev tag))
    have cost : recordFuel (some p) = 1 + (1 + ((4 * (n + 1) + 1) + 1)) := by
      simp only [recordFuel]; omega
    rw [cost]
    exact checked

theorem recordBits_length_bound {n : Nat} (pivot : Option (Affine n)) :
    (recordBits pivot).length ≤ n + 2 := by
  cases pivot <;>
    simp only [recordBits, List.length_cons, List.length_nil, List.length_reverse,
      affineWord_length] <;> omega

theorem recordFuel_bound {n : Nat} (pivot : Option (Affine n)) :
    recordFuel pivot ≤ 4 * (n + 1) + 4 := by
  cases pivot <;> simp only [recordFuel] <;> omega

def afterColumn {n : Nat} (rows : System (n + 1)) (history : BitString) : State :=
  ⟨columnResult rows, List.replicate (n + 1) true, history⟩
def prepared {n : Nat} (rows : System (n + 1)) (history : BitString) : State :=
  recordInput n (choosePivot rows) (matrixBits (reducedRows rows))
    (matrixBits rows) (List.replicate (n + 1) true) history
def recorded {n : Nat} (rows : System (n + 1)) (history : BitString) : State :=
  recordOutput n (choosePivot rows) (matrixBits (reducedRows rows))
    (matrixBits rows) (List.replicate (n + 1) true) history
def saved {n : Nat} (rows : System (n + 1)) (history : BitString) : State :=
  {recorded rows history with history := recordBits (choosePivot rows) ++ history}

def prepareHistory : Block 11 := .seq (.action (.copy 0 8)) (.action (.copy 8 10))
theorem prepareHistory_exec {n : Nat} (rows : System (n + 1)) (history : BitString) :
    Exec prepareHistory (afterColumn rows history).store 2 (prepared rows history).store :=
  Exec.seq (.action _ _) (.action _ _)

def saveHistory : Block 11 := .action (.copy 10 8)
theorem saveHistory_exec {n : Nat} (rows : System (n + 1)) (history : BitString) :
    Exec saveHistory (recorded rows history).store 1 (saved rows history).store := .action _ _

def advanceDimension : Block 11 := .seq (.action (.pop 9)) (.action (.copy 1 9))
def advanced (r : State) : State :=
  {r with core := {r.core with target := r.pending.tail}, pending := r.pending.tail}
theorem advanceDimension_exec (r : State) :
    Exec advanceDimension r.store 2 (advanced r).store :=
  Exec.seq (.action _ _) (.action _ _)

def clearScratch : Block 9 :=
  .seq (.action (.clear 2)) (.seq (.action (.clear 3)) (.action (.clear 4)))
def scratchCleared (r : Registers) : Registers :=
  {r with remaining := [], excess := [], sign := []}
theorem clearScratch_exec (r : Registers) :
    Exec clearScratch r.store 3 (scratchCleared r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))

def clearResult : Block 9 :=
  .seq (.action (.clear 5)) (.seq (.action (.clear 6))
    (.seq (.action (.copy 7 0)) (.action (.clear 8))))
def resultCleared (r : Registers) : Registers :=
  {r with mode := [], active := [], reserved := r.input, output := []}
theorem clearResult_exec (r : Registers) :
    Exec clearResult r.store 4 (resultCleared r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))

def resetCore : Block 11 :=
  .seq advanceDimension (.seq (lift clearScratch) (lift clearResult))
def resetResult (r : State) : State where
  core :=
    { input := r.core.input
      target := r.pending.tail
      remaining := []
      excess := []
      sign := []
      mode := []
      active := []
      reserved := r.core.input
      output := [] }
  pending := r.pending.tail
  history := r.history

theorem resetCore_exec (r : State) : Exec resetCore r.store 9 (resetResult r).store := by
  let a := advanced r
  let b := {a with core := scratchCleared a.core}
  have first := advanceDimension_exec r
  have second : Exec (lift clearScratch) a.store 3 b.store :=
    lift_exec clearScratch a 3 b.core (clearScratch_exec a.core)
  have third : Exec (lift clearResult) b.store 4 (resetResult r).store :=
    lift_exec clearResult b 4 (resultCleared b.core) (clearResult_exec b.core)
  exact Exec.seq first (Exec.seq second third)

theorem reset_saved {n : Nat} (rows : System (n + 1)) (history : BitString) :
    resetResult (saved rows history) =
      start n (reducedRows rows) (recordBits (choosePivot rows) ++ history) := by
  simp only [resetResult, saved, recorded, recordOutput, recordInput, start, base,
    pivotResult, List.replicate_succ, List.tail_cons]

def body : Block 11 :=
  .seq (lift column) (.seq prepareHistory (.seq savePivot (.seq saveHistory resetCore)))
def bodyFuel {n : Nat} (rows : System (n + 1)) : Nat :=
  columnFuel rows + (2 + (recordFuel (choosePivot rows) + (1 + 9)))

theorem body_exec {n : Nat} (rows : System (n + 1)) (history : BitString) :
    Exec body (start (n + 1) rows history).store (bodyFuel rows)
      (start n (reducedRows rows) (recordBits (choosePivot rows) ++ history)).store := by
  have first : Exec (lift column) (start (n + 1) rows history).store
      (columnFuel rows) (afterColumn rows history).store :=
    lift_exec column (start (n + 1) rows history) _ (columnResult rows) (column_exec rows)
  have kept : Exec savePivot (prepared rows history).store (recordFuel (choosePivot rows))
      (recorded rows history).store :=
    savePivot_exec n (choosePivot rows) (matrixBits (reducedRows rows))
      (matrixBits rows) (List.replicate (n + 1) true) history
  have reset := resetCore_exec (saved rows history)
  rw [reset_saved] at reset
  exact Exec.seq first (Exec.seq (prepareHistory_exec rows history)
    (Exec.seq kept (Exec.seq (saveHistory_exec rows history) reset)))

theorem bodyFuel_bound {n : Nat} (rows : System (n + 1)) :
    bodyFuel rows ≤ (24 * (n + 1) + 36) * (rows.length + 1) := by
  have col := columnFuel_bound rows
  have recordedBound := recordFuel_bound (choosePivot rows)
  have extra := Nat.mul_le_mul_left (4 * (n + 1) + 16)
    (show 1 ≤ rows.length + 1 by omega)
  simp only [Nat.mul_one] at extra
  calc
    bodyFuel rows ≤ columnFuel rows + (4 * (n + 1) + 16) := by
      unfold bodyFuel; omega
    _ ≤ (20 * (n + 1) + 20) * (rows.length + 1) +
        (4 * (n + 1) + 16) * (rows.length + 1) := Nat.add_le_add col extra
    _ = (24 * (n + 1) + 36) * (rows.length + 1) := by
      rw [← Nat.add_mul]
      congr 1
      omega

end PNP.Concrete.ResidualReduction.MatrixSweep
