import PNP.Concrete.ResidualReduction.SourceReplayState

/-! Compute the missing bit from actual stored source rows. Insert a false
pivot into the current point, evaluate every selected source product, save the
computed bit, and clear the working registers before reconstruction. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayEvaluate
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.SourceReplayState

def prepare : Block 16 := .seq (.action (.copy 0 13)) (.action (.copy 2 11))
def zeroPoint : Block 16 := .seq prepare (core (SourceReplayPoint.splice false))

theorem zeroPoint_exec {n : Nat} (F : Family (n + 1)) (w : Point F.length)
    (k : Fin (n + 1)) (v z : Point n) :
    Exec zeroPoint (work [] [] (data F w k v z)) (9 * k.val + 7)
      (work [] ((SourceEncoding.pointCodec (n + 1)).encode (insert n k (false,z))) (data F w k v z)) := by
  let s := data F w k v z
  let ready := {blank [] [] with input := (SourceEncoding.pointCodec n).encode z,remaining := List.replicate k.val true}
  have first : Exec prepare (work [] [] s) 2 (full ready s) := Exec.seq (.action _ _) (.action _ _)
  have last := core_exec (SourceReplayPoint.splice_point (blank [] []) k false z) s
  have cost : 9 * k.val + 7 = 2 + SourceReplayPoint.spliceFuel k.val := by
    unfold SourceReplayPoint.spliceFuel
    omega
  simpa only [zeroPoint,cost,s,ready,work,blank] using Exec.seq first last

def setup : Block 16 := .seq (.action (.copy 0 10)) (.seq (.action (.copy 1 14))
  (.seq (.action (.push 1 true)) (.seq (.action (.copy 7 8)) (.action (.clear 8)))))

theorem setup_exec {n : Nat} (F : Family (n + 1)) (w : Point F.length)
    (k : Fin (n + 1)) (v z : Point n) :
    Exec setup
      (work [] ((SourceEncoding.pointCodec (n + 1)).encode (insert n k (false,z))) (data F w k v z)) 5
      (full (SourceReplayValue.registers (familyBits F) (insert n k (false,z)) []) (data F w k v z)) :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _)
    (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))))

def capture : Block 16 := .seq (.action (.copy 15 8)) clean
theorem capture_exec (r : Registers) (s : Saved) (bit : Bool) (output : r.output = [bit]) :
    Exec capture (full r s) 11 (work [] [] {s with bit := [bit]}) := by
  have first : Exec (.action (.copy (15 : Fin 16) 8)) (full r s) 1 (full r {s with bit := r.output}) := .action _ _
  rw [output] at first
  exact Exec.seq first (clean_exec r {s with bit := [bit]})

def block : Block 16 := .seq zeroPoint (.seq setup (.seq (use10 SourceReplayValue.block) capture))
def fuel (n rows pivot : Nat) : Nat := 9 * pivot + 23 + SourceReplayValue.fuel (n + 1) rows

theorem block_exec {n : Nat} (F : Family (n + 1)) (w : Point F.length)
    (k : Fin (n + 1)) (v z : Point n) :
    Exec block (work [] [] (data F w k v z)) (fuel n F.length k.val)
      (work [] [] (evaluated (data F w k v z) (value F w k z))) := by
  have first := zeroPoint_exec F w k v z
  have setup := setup_exec F w k v z
  have compute := weighted_exec F w (insert n k (false,z)) [] (data F w k v z) rfl
  have last := capture_exec (SourceReplayValue.registers [] (insert n k (false,z)) [value F w k z])
    {data F w k v z with weights := []} (value F w k z) rfl
  have cost : fuel n F.length k.val =
      (9 * k.val + 7) + (5 + (SourceReplayValue.fuel (n + 1) F.length + 11)) := by
    unfold fuel
    omega
  simpa only [block,cost,evaluated,value] using Exec.seq first (Exec.seq setup (Exec.seq compute last))

end PNP.Concrete.ResidualReduction.SourceReplayEvaluate
