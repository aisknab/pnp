import PNP.Concrete.ResidualReduction.SourceChartAffine
import PNP.Concrete.ResidualReduction.SourceMenuInsertOutput
import PNP.Concrete.NormalizerRegisterFrame

/-! Stream one complete source factor through the literal chart transformer.
The remaining input, chosen chart and weight stream are protected. The exact
transformed factor is appended to a reversed output accumulator; every read,
transfer, transformation and append is included in the instruction count. -/

namespace PNP.Concrete.ResidualReduction.SourceChartStream
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions

structure Saved where
  stream : BitString
  pivot : BitString
  tail : BitString
  width : BitString
  weights : BitString
  accumulator : BitString

def Saved.store (s : Saved) : Store 6 :=
  .cons s.stream <| .cons s.pivot <| .cons s.tail <| .cons s.width <|
    .cons s.weights (.cons s.accumulator .nil)
def full (r : Registers) (s : Saved) : Store 15 := Frame.join r.store s.store
def work (n : Nat) (input : BitString) : Registers :=
  ⟨input,List.replicate n true,[],[],[],[],[],[],[]⟩
def data {n : Nat} (k : Fin (n + 1)) (t : Point n)
    (stream weights accumulator : BitString) : Saved :=
  ⟨stream,List.replicate k.val true,(SourceEncoding.pointCodec n).encode t,
    List.replicate (n + 2) true,weights,accumulator⟩
def transformed {n : Nat} (f : Affine (n + 1)) (k : Fin (n + 1)) (t : Point n) : Affine (n + 1) :=
  aShear t (cut n k f)

def prepare : Block 15 := .seq (.action (.copy 0 8)) <|
  .seq (.action (.copy 2 10)) <| .seq (.action (.copy 7 11)) (.action (.clear 8))
def storeResult : Block 15 := .seq (.action (.copy 14 7)) <|
  .seq (.action (.copy 0 9)) (.action (.clear 7))
def block : Block 15 := .seq (.action (.copy 2 12)) <|
  .seq (Frame.block 6 copyLoop) <| .seq (.action (.copy 9 0)) <|
  .seq (Frame.block 6 ClauseQuery.reverseLoop) <| .seq prepare <|
  .seq (Frame.block 6 SourceChartAffine.block) <| .seq (.action (.copy 7 14)) <|
  .seq (Frame.block 6 (SourceMenuInsertOutput.append 8)) storeResult
def fuel (n pivot : Nat) : Nat := 22 * n + 9 * pivot + 57

theorem block_exec {n : Nat} (f : Affine (n + 1)) (k : Fin (n + 1)) (t : Point n)
    (suffix savedStream weights accumulator : BitString) :
    Exec block (full (work n (affineWord f ++ suffix)) (data k t savedStream weights accumulator))
      (fuel n k.val)
      (full (work n suffix) (data k t suffix weights ((affineWord (transformed f k t)).reverse ++ accumulator))) := by
  let d := data k t savedStream weights accumulator
  let ds := data k t suffix weights accumulator
  let before := work n (affineWord f ++ suffix)
  let loaded := {before with remaining := List.replicate (n + 2) true}
  let copied := {work n suffix with excess := (affineWord f).reverse}
  let reversed := {work n suffix with output := affineWord f}
  have load : Exec (.action (.copy (2 : Fin 15) 12)) (full before d) 1 (full loaded d) := .action _ _
  have copy : Exec copyLoop loaded.store (5 * (n + 2) + 1) copied.store := by
    simpa only [loaded,before,copied,work,affineWord_length,List.append_nil] using
      copy_exec (work n suffix) (affineWord f) suffix
  have save : Exec (.action (.copy (9 : Fin 15) 0)) (full copied d) 1 (full copied ds) := .action _ _
  have rev : Exec ClauseQuery.reverseLoop copied.store (4 * (n + 2) + 1) reversed.store := by
    simpa only [copied,reversed,work,List.length_reverse,affineWord_length,List.reverse_reverse,List.append_nil] using
      ClauseQuery.reverse_exec (work n suffix) (affineWord f).reverse
  have prep : Exec prepare (full reversed ds) 4 (full (SourceChartAffine.ready f k t) ds) :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
  have transform := Frame.execution (SourceChartAffine.block_exec f k t) ds.store
  let appendReady := {SourceChartAffine.finished f k t with reserved := accumulator}
  have accumulatorLoad : Exec (.action (.copy (7 : Fin 15) 14))
      (full (SourceChartAffine.finished f k t) ds) 1 (full appendReady ds) := .action _ _
  let appended := SourceMenuInsertOutput.appended appendReady (affineWord (transformed f k t))
  have append : Exec (SourceMenuInsertOutput.append 8) appendReady.store (4 * (n + 2) + 5) appended.store := by
    have output : appendReady.store.get 8 = affineWord (transformed f k t) := rfl
    simpa only [SourceMenuInsertOutput.appendCost,output,affineWord_length,appended] using
      SourceMenuInsertOutput.append_exec appendReady 8
  have store : Exec storeResult (full appended ds) 3
      (full (work n suffix) (data k t suffix weights ((affineWord (transformed f k t)).reverse ++ accumulator))) :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have cost : fuel n k.val = 1 + ((5 * (n + 2) + 1) + (1 +
      ((4 * (n + 2) + 1) + (4 + (SourceChartAffine.fuel n k.val + (1 + ((4 * (n + 2) + 5) + 3))))))) := by
    simp only [fuel,SourceChartAffine.fuel]
    omega
  simpa only [block,cost,full,before,d] using Exec.seq load
    (Exec.seq (Frame.execution copy d.store) (Exec.seq save
      (Exec.seq (Frame.execution rev ds.store) (Exec.seq prep
        (Exec.seq transform (Exec.seq accumulatorLoad (Exec.seq (Frame.execution append ds.store) store)))))))

theorem fuel_bound {n : Nat} (k : Fin (n + 1)) : fuel n k.val ≤ 31 * n + 57 := by
  have h := k.isLt
  simp only [fuel]
  omega

end PNP.Concrete.ResidualReduction.SourceChartStream
