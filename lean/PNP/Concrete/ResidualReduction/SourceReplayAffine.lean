import PNP.Concrete.ResidualReduction.SourceReplayAlgebra

/-! Literal affine evaluation on an encoded point. The existing dot loop is
reused, but the constant is read and XORed into the result instead of being
discarded as it is for homogeneous direction maps. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayAffine
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions

def finish : Block 9 := MatrixLinearCombinationInstructions.readInput fun constant =>
  SourceLinearMap.readSign fun bit => .action (.push 8 (Bool.xor constant bit))

theorem finish_exec (r : Registers) (constant bit : Bool) :
    Exec finish ({r with input := constant :: r.input,sign := [bit]}).store 5
      ({r with sign := [],output := Bool.xor constant bit :: r.output}).store := by
  unfold finish
  refine MatrixLinearCombinationInstructions.readInput_exec {r with sign := [bit]} constant _ 3 _ ?_
  exact SourceLinearMap.readSign_exec {r with sign := []} bit _ 1 _ (.action _ _)

private theorem restore (constant bit : Bool) :
    Bool.xor constant (Bool.xor bit constant) = bit := by
  cases constant <;> cases bit <;> rfl

def block : Block 9 := .seq SourceLinearMap.rowPrepare (.seq SourceLinearMap.dotLoop finish)
def fuel (n : Nat) : Nat := 9 * n + 10

theorem block_exec (r : Registers) {n : Nat} (f : Affine n) (z : Point n) (suffix : BitString) :
    Exec block
      ({r with input := affineWord f ++ suffix,target := List.replicate n true,reserved := (SourceEncoding.pointCodec n).encode z}).store (fuel n)
      ({r with input := suffix,target := List.replicate n true,reserved := (SourceEncoding.pointCodec n).encode z,remaining := [],mode := [],sign := [],output := aEval f z :: r.output}).store := by
  let before := {r with input := affineWord f ++ suffix,target := List.replicate n true,reserved := (SourceEncoding.pointCodec n).encode z}
  let prepared := {before with remaining := List.replicate n true,mode := (SourceEncoding.pointCodec n).encode z,sign := [false]}
  let done := {before with input := aConstant f :: suffix,remaining := [],mode := [],sign := [SourceLinearMap.value f z]}
  have prepare : Exec SourceLinearMap.rowPrepare before.store 4 prepared.store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
  have dot : Exec SourceLinearMap.dotLoop prepared.store (9 * n + 1) done.store := by
    simpa only [prepared,done,before,Bool.xor_false] using SourceLinearMap.dotLoop_exec before f z false suffix
  have last := finish_exec {before with input := suffix,remaining := [],mode := [],sign := []}
    (aConstant f) (SourceLinearMap.value f z)
  have cost : fuel n = 4 + ((9 * n + 1) + 5) := by unfold fuel; omega
  simpa only [block,cost,before,prepared,done,SourceLinearMap.value,restore] using
    Exec.seq prepare (Exec.seq dot last)

theorem fuel_mono {n N : Nat} (h : n ≤ N) : fuel n ≤ fuel N := by unfold fuel; omega

end PNP.Concrete.ResidualReduction.SourceReplayAffine
