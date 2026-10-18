import PNP.Concrete.ResidualReduction.SourceReplayPoint
import PNP.Concrete.ResidualReduction.SourceChartedSuccessorWords

/-! Protected actual replay fields. The source rows, weights, pivot, tail and
current point are finite encoded data, not supplied evaluation results. The
computed missing bit has its own slot and is initially empty. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayState
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding

structure Saved where
  weights : BitString
  source : BitString
  pivot : BitString
  tail : BitString
  point : BitString
  dimension : BitString
  bit : BitString

def Saved.rest (s : Saved) : Store 6 :=
  .cons s.source <| .cons s.pivot <| .cons s.tail <| .cons s.point <| .cons s.dimension (.cons s.bit .nil)
def Saved.store (s : Saved) : Store 7 := .cons s.weights s.rest
def full (r : Registers) (s : Saved) : Store 16 := Frame.join r.store s.store
def blank (input output : BitString) : Registers := ⟨input,[],[],[],[],[],[],[],output⟩
def work (input output : BitString) (s : Saved) : Store 16 := full (blank input output) s
def core (b : Block 9) : Block 16 := Frame.block 7 b
theorem core_exec {b : Block 9} {before after : Registers} {used : Nat}
    (checked : Exec b before.store used after.store) (s : Saved) :
    Exec (core b) (full before s) used (full after s) := Frame.execution checked s.store

def use10 (b : Block 10) : Block 16 := Frame.block 6 b
theorem weighted_exec {n : Nat} (F : Family n) (w : Point F.length) (z : Point n)
    (output : BitString) (s : Saved)
    (weights : s.weights = (SourceEncoding.pointCodec F.length).encode w) :
    Exec (use10 SourceReplayValue.block) (full (SourceReplayValue.registers (familyBits F) z output) s)
      (SourceReplayValue.fuel n F.length)
      (full (SourceReplayValue.registers [] z (SourceBalance.weightedValue F w z :: output))
        {s with weights := []}) := by
  change Exec (Frame.block 6 SourceReplayValue.block)
    (Frame.join (SourceReplayValue.full (SourceReplayValue.registers (familyBits F) z output) s.weights) s.rest)
    (SourceReplayValue.fuel n F.length)
    (Frame.join (SourceReplayValue.full (SourceReplayValue.registers [] z (SourceBalance.weightedValue F w z :: output)) []) s.rest)
  rw [weights]
  exact Frame.execution (SourceReplayValue.block_exec F w z output) s.rest

def clean : Block 16 := core (SourceChartedSuccessorWords.clearAll 9)
theorem clean_exec (r : Registers) (s : Saved) :
    Exec clean (full r s) 10 (work [] [] s) :=
  Frame.execution (SourceChartedSuccessorWords.clearAll_exec r.store) s.store

def data {n : Nat} (F : Family (n + 1)) (w : Point F.length) (k : Fin (n + 1))
    (v z : Point n) : Saved :=
  ⟨(SourceEncoding.pointCodec F.length).encode w,familyBits F,List.replicate k.val true,
    (SourceEncoding.pointCodec n).encode v,(SourceEncoding.pointCodec n).encode z,List.replicate n true,[]⟩
def evaluated (s : Saved) (bit : Bool) : Saved := {s with weights := [],bit := [bit]}
def value {n : Nat} (F : Family (n + 1)) (w : Point F.length) (k : Fin (n + 1)) (z : Point n) : Bool :=
  SourceBalance.weightedValue F w (insert n k (false,z))

end PNP.Concrete.ResidualReduction.SourceReplayState
