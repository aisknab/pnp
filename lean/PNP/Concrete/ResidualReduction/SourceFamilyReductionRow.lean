import PNP.Concrete.ResidualReduction.SourceFamilyReductionState

/-! Consume one row and collect its result. Every successful row is appended
in order to a reversed accumulator. A failure clears the sticky success flag;
later successful rows cannot restore it. Both cases consume one row counter. -/

namespace PNP.Concrete.ResidualReduction.SourceFamilyReductionRow
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding (rowWord rowWord_length)
open PNP.Concrete.ResidualReduction.SourceRowReductionState (work parameters emptyData reduceRow)
open PNP.Concrete.ResidualReduction.SourceFamilyReductionEncoding (emitted)
open PNP.Concrete.ResidualReduction.SourceFamilyReductionState

def afterRow {n : Nat} (t : TailForm n) (suffix : BitString) (p : Option (Row n))
    (remaining accumulator : BitString) (valid : Bool) (count : BitString) : Store 23 :=
  full (SourceRowReductionState.finished t suffix p) ⟨true :: remaining,accumulator,[valid],count⟩
def failFlag : Block 23 := .seq (.action (.clear 21)) (.action (.push 21 false))
def failCleanup : Block 23 := .seq (.action (.clear 8)) <|
  .seq (.action (.clear 17)) (.action (.pop 19))
def failure : Block 23 := .seq failFlag failCleanup

theorem failure_exec {n : Nat} (t : TailForm n) (suffix remaining accumulator : BitString)
    (valid : Bool) (count : BitString) :
    Exec failure (afterRow t suffix none remaining accumulator valid count) 5
      (state t suffix remaining accumulator false count) := by
  have flag : Exec failFlag (afterRow t suffix none remaining accumulator valid count) 2
      (afterRow t suffix none remaining accumulator false count) :=
    Exec.seq (.action _ _) (.action _ _)
  have clean : Exec failCleanup (afterRow t suffix none remaining accumulator false count) 3
      (state t suffix remaining accumulator false count) :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  exact Exec.seq flag clean

def prepare : Block 23 := .seq (.action (.pop 8)) (.action (.copy 7 20))
def store : Block 23 := .seq (.action (.copy 20 7)) <|
  .seq (.action (.clear 7)) <| .seq (.action (.clear 17)) (.action (.pop 19))
def success : Block 23 := .seq prepare (.seq (core (SourceMenuInsertOutput.append 8)) store)
def successFuel (n : Nat) : Nat := 4 * (2 * n + 3) + 11

theorem success_exec {n : Nat} (t : TailForm n) (p : Row n) (suffix remaining accumulator : BitString)
    (valid : Bool) (count : BitString) :
    Exec success (afterRow t suffix (some p) remaining accumulator valid count) (successFuel n)
      (state t suffix remaining ((rowWord p).reverse ++ accumulator) valid count) := by
  let s : Saved := ⟨true :: remaining,accumulator,[valid],count⟩
  let d := emptyData t suffix
  let r := {work n suffix with reserved := accumulator,output := rowWord p}
  let next := SourceMenuInsertOutput.appended r (rowWord p)
  have prep : Exec prepare (afterRow t suffix (some p) remaining accumulator valid count) 2
      (full (SourceRowReductionState.full r (parameters t) d) s) :=
    Exec.seq (.action _ _) (.action _ _)
  have append : Exec (SourceMenuInsertOutput.append 8) r.store (4 * (2 * n + 3) + 5) next.store := by
    have word : r.store.get 8 = rowWord p := rfl
    simpa only [SourceMenuInsertOutput.appendCost,word,rowWord_length,next] using
      SourceMenuInsertOutput.append_exec r 8
  have save : Exec store (full (SourceRowReductionState.full next (parameters t) d) s) 4
      (state t suffix remaining ((rowWord p).reverse ++ accumulator) valid count) :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
  have cost : successFuel n = 2 + ((4 * (2 * n + 3) + 5) + 4) := by unfold successFuel; omega
  simpa only [success,cost] using Exec.seq prep (Exec.seq (core_exec append (parameters t) d s) save)

def collect : Block 23 := .branch 8 .skip failure success
def collectFuel (n : Nat) : Option (Row n) → Nat
  | none => 6
  | some _ => 1 + successFuel n

theorem collect_exec {n : Nat} (t : TailForm n) (p : Option (Row n)) (suffix remaining accumulator : BitString)
    (valid : Bool) (count : BitString) :
    Exec collect (afterRow t suffix p remaining accumulator valid count) (collectFuel n p)
      (state t suffix remaining ((emitted p).reverse ++ accumulator) (valid && p.isSome) count) := by
  cases p with
  | none =>
    simpa only [collectFuel,emitted,List.reverse_nil,List.nil_append,Option.isSome_none,Bool.and_false] using
      (show Exec collect (afterRow t suffix none remaining accumulator valid count) 6
        (state t suffix remaining accumulator false count) from
          Exec.zero rfl (failure_exec t suffix remaining accumulator valid count))
  | some p =>
    simpa only [collectFuel,emitted,Option.isSome_some,Bool.and_true] using
      (show Exec collect (afterRow t suffix (some p) remaining accumulator valid count) (1 + successFuel n)
        (state t suffix remaining ((rowWord p).reverse ++ accumulator) valid count) from
          Exec.one rfl (success_exec t p suffix remaining accumulator valid count))

def block : Block 23 := .seq (row SourceRowReductionInstructions.block) collect
def fuel {n : Nat} (t : TailForm n) (r : Row (n + 1)) : Nat :=
  SourceRowReductionInstructions.fuel t r + collectFuel n (reduceRow t r)

theorem block_exec {n : Nat} (t : TailForm n) (r : Row (n + 1)) (suffix remaining accumulator : BitString)
    (valid : Bool) (count : BitString) :
    Exec block (state t (rowWord r ++ suffix) (true :: remaining) accumulator valid count) (fuel t r)
      (state t suffix remaining ((emitted (reduceRow t r)).reverse ++ accumulator)
        (valid && (reduceRow t r).isSome) count) :=
  Exec.seq (row_exec (SourceRowReductionInstructions.block_exec t r suffix)
    ⟨true :: remaining,accumulator,[valid],count⟩)
    (collect_exec t (reduceRow t r) suffix remaining accumulator valid count)

theorem collectFuel_bound {n : Nat} (p : Option (Row n)) :
    collectFuel n p ≤ 8 * (n + 1) + 16 := by
  cases p <;> simp only [collectFuel,successFuel] <;> omega
theorem fuel_bound {n : Nat} (t : TailForm n) (r : Row (n + 1)) :
    fuel t r ≤ 313 * (n + 1) + 235 := by
  have head := SourceRowReductionInstructions.fuel_bound t r
  have tail := collectFuel_bound (reduceRow t r)
  unfold fuel
  omega

end PNP.Concrete.ResidualReduction.SourceFamilyReductionRow
