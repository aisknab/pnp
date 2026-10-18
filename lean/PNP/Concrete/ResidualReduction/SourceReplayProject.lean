import PNP.Concrete.ResidualReduction.SourceReplayDecode

/-! The forward witness map on actual encoded coordinates. The pivot is read
from the point, removed in order, and used to select the exact chart shear.
This is the forward companion to reconstruction, not a history parser. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayProject
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceReplayState

theorem encode_direct {n : Nat} (k : Fin (n + 1)) (v : Point n) (x : Point (n + 1)) :
    encode k v x = SourceReplayPoint.sheared (cut n k x).1 (cut n k x).2 v := by
  cases h : cut n k x with
  | mk bit z => cases bit <;> simp only [encode,chart,h,shear,SourceReplayPoint.sheared,↓reduceIte]

def data {n : Nat} (k : Fin (n + 1)) (v : Point n) (x : Point (n + 1)) (s : Saved) : Saved :=
  {s with pivot := List.replicate k.val true,tail := (SourceEncoding.pointCodec n).encode v,point := (SourceEncoding.pointCodec (n + 1)).encode x,dimension := List.replicate n true}
def prepare : Block 16 := .seq (.action (.copy 0 13)) (.action (.copy 2 11))
def cutBlock : Block 16 := .seq prepare (core SourceChartAffine.cutBlock)
def cutResult {n : Nat} (k : Fin (n + 1)) (x : Point (n + 1)) : Registers :=
  {blank [] [] with sign := [(cut n k x).1],output := (SourceEncoding.pointCodec n).encode (cut n k x).2}
def clearInput : Block 16 := .action (.clear 0)
def cutPoint : Block 16 := .seq cutBlock clearInput

theorem cutPoint_exec {n : Nat} (k : Fin (n + 1)) (v : Point n) (x : Point (n + 1)) (s : Saved) :
    Exec cutPoint (work [] [] (data k v x s)) (9 * k.val + 9)
      (full (cutResult k x) (data k v x s)) := by
  obtain ⟨front,suffix,width,whole,tail⟩ := SourceChartAffine.cut_words SourceEncoding.unitCodec n k x
  let saved := data k v x s
  let before := {blank [] [] with input := (SourceEncoding.pointCodec (n + 1)).encode x,remaining := List.replicate k.val true}
  let after := {cutResult k x with input := suffix}
  have setup : Exec prepare (work [] [] saved) 2 (full before saved) :=
    Exec.seq (.action _ _) (.action _ _)
  have cutRun : Exec (core SourceChartAffine.cutBlock) (full before saved) (9 * k.val + 6) (full after saved) := by
    have checked := core_exec (SourceChartAffine.cut_exec (blank [] []) front suffix (cut n k x).1) saved
    simpa only [before,after,cutResult,blank,SourceEncoding.pointCodec,whole,tail,width] using checked
  have clear : Exec clearInput (full after saved) 1 (full (cutResult k x) saved) := .action _ _
  have cost : 9 * k.val + 9 = (2 + (9 * k.val + 6)) + 1 := by omega
  simpa only [cutPoint,cutBlock,cost,saved] using Exec.seq (Exec.seq setup cutRun) clear

def setupShear : Block 16 := .seq (.action (.copy 0 8)) (.seq (.action (.copy 5 12))
  (.seq (.action (.copy 2 14)) (.action (.clear 8))))
def block : Block 16 := .seq cutPoint (.seq setupShear
  (.seq (core SourceReplayPoint.shearBlock) (.action (.clear 4))))
def fuel (n pivot : Nat) (bit : Bool) : Nat := 9 * pivot + 14 + SourceReplayPoint.shearFuel n bit

theorem block_exec {n : Nat} (k : Fin (n + 1)) (v : Point n) (x : Point (n + 1)) (s : Saved) :
    Exec block (work [] [] (data k v x s)) (fuel n k.val (cut n k x).1)
      (work [] ((SourceEncoding.pointCodec n).encode (encode k v x)) (data k v x s)) := by
  let saved := data k v x s
  let ready := SourceReplayDecode.ready (cut n k x).1 (cut n k x).2 v
  let after := SourceReplayDecode.afterShear (cut n k x).1 (cut n k x).2 v
  have setup : Exec setupShear (full (cutResult k x) saved) 4 (full ready saved) :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
  have shearRun := core_exec (SourceReplayPoint.shear_point (blank [] []) (cut n k x).1 (cut n k x).2 v) saved
  have clear : Exec (.action (.clear (4 : Fin 16))) (full after saved) 1
      (work [] ((SourceEncoding.pointCodec n).encode (encode k v x)) saved) := by
    rw [encode_direct]
    exact .action _ _
  have cost : fuel n k.val (cut n k x).1 =
      (9 * k.val + 9) + (4 + (SourceReplayPoint.shearFuel n (cut n k x).1 + 1)) := by
    unfold fuel
    omega
  simpa only [block,cost,saved,ready,after,SourceReplayDecode.ready,SourceReplayDecode.afterShear,blank] using
    Exec.seq (cutPoint_exec k v x s) (Exec.seq setup (Exec.seq shearRun clear))

theorem fuel_bound (n pivot : Nat) (bit : Bool) (hp : pivot ≤ n) :
    fuel n pivot bit ≤ 20 * n + 20 := by
  have shear := SourceReplayPoint.shearFuel_bound n bit
  unfold fuel
  omega

end PNP.Concrete.ResidualReduction.SourceReplayProject
