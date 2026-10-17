import PNP.Concrete.ResidualReduction.MatrixPullbackInstructions
import PNP.Concrete.ResidualReduction.MatrixFreeInstructions

/-! Complete literal construction of the pivot branch. Zero coefficients are
constructed, every selected map row is accumulated, and the final affine
constant is applied before prepending the exact pullback to the unchanged map.
The bounds here are source-instruction bounds on prepared finite coefficients,
not yet an original-input runtime theorem for the complete contraction phase. -/

namespace PNP.Concrete.ResidualReduction.MatrixPivotMapInstructions
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.MatrixPullbackAlgebra
open PNP.Concrete.ResidualReduction.MatrixPullbackInstructions

def start {n k : Nat} (p : Affine n) (m : AffineMap n k) (saved : BitString) : Registers :=
  {base (k + 1) saved with input := mapBits m, active := affineWord p}

def initAccumulator : Block 9 :=
  .seq (.action (.copy 2 1)) <| .seq MatrixFreeInstructions.zeroPrefixLoop <|
    .seq (.action (.copy 4 8)) (.action (.clear 8))

theorem initAccumulator_exec {n k : Nat} (p : Affine n) (m : AffineMap n k) (saved : BitString) :
    Exec initAccumulator (start p m saved).store (3 * (k + 1) + 4)
      (selecting p m (aConst k false) saved).store := by
  have ready : Exec (.action (.copy 2 1)) (start p m saved).store 1
      ({start p m saved with remaining := List.replicate (k + 1) true}).store := .action _ _
  have zeroed : Exec MatrixFreeInstructions.zeroPrefixLoop
      ({start p m saved with remaining := List.replicate (k + 1) true}).store
      (3 * (k + 1) + 1)
      ({start p m saved with output := List.replicate (k + 1) false}).store := by
    simpa only [start, base, List.append_nil] using
      MatrixFreeInstructions.zeroPrefix_exec (start p m saved) (k + 1)
  have finished : Exec (.seq (.action (.copy 4 8)) (.action (.clear 8)))
      ({start p m saved with output := List.replicate (k + 1) false}).store 2
      ({base (k + 1) saved with input := mapBits m, active := affineWord p, sign := List.replicate (k + 1) false}).store :=
    Exec.seq (.action _ _) (.action _ _)
  have checked := Exec.seq ready (Exec.seq zeroed finished)
  have cost : 3 * (k + 1) + 4 = 1 + ((3 * (k + 1) + 1) + 2) := by omega
  simpa only [initAccumulator, selecting, start, base, affineWord_zero, List.append_nil, cost] using checked

def prepareConstant : Block 9 :=
  .seq (.action (.copy 0 4)) <| .seq (.action (.copy 2 1)) <|
    .seq (.action (.pop 2)) (.action (.clear 4))

def xorLast : Block 9 :=
  .branch 6 .skip
    (.branch 0 .skip (.action (.push 3 false)) (.action (.push 3 true)))
    (.branch 0 .skip (.action (.push 3 true)) (.action (.push 3 false)))

theorem xorLast_exec (r : Registers) (constant value : Bool) :
    Exec xorLast ({r with input := [value], active := [constant]}).store 3
      ({r with input := [value], active := [constant], excess := Bool.xor constant value :: r.excess}).store := by
  cases constant <;> cases value
  · exact Exec.zero rfl (Exec.zero rfl (.action _ _))
  · exact Exec.zero rfl (Exec.one rfl (.action _ _))
  · exact Exec.one rfl (Exec.zero rfl (.action _ _))
  · exact Exec.one rfl (Exec.one rfl (.action _ _))

def prepareOutput : Block 9 :=
  .seq (.action (.clear 0)) (.seq (.action (.clear 6)) (.action (.copy 8 7)))

def finish : Block 9 :=
  .seq prepareConstant <| .seq copyLoop <|
    .seq (.seq xorLast prepareOutput) ClauseQuery.reverseLoop

theorem finish_exec {k : Nat} (constant : Bool) (acc : Affine k) (saved : BitString) :
    Exec finish ({base (k + 1) saved with sign := affineWord acc, active := [constant]}).store
      (9 * k + 16)
      ({base (k + 1) saved with output := affineWord (aAdd (aConst k constant) acc) ++ saved}).store := by
  have ready : Exec prepareConstant
      ({base (k + 1) saved with sign := affineWord acc, active := [constant]}).store 4
      ({base (k + 1) saved with input := affineWord acc, remaining := List.replicate k true, active := [constant]}).store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
  have copied : Exec copyLoop
      ({base (k + 1) saved with input := affineWord acc, remaining := List.replicate k true, active := [constant]}).store
      (5 * k + 1)
      ({base (k + 1) saved with input := [aConstant acc], active := [constant], excess := (normalWord acc).reverse}).store := by
    simpa only [normalWord_length, ← word_split, base, List.append_nil] using
      copy_exec {base (k + 1) saved with active := [constant]} (normalWord acc) [aConstant acc]
  have toggled : Exec xorLast
      ({base (k + 1) saved with input := [aConstant acc], active := [constant], excess := (normalWord acc).reverse}).store 3
      ({base (k + 1) saved with input := [aConstant acc], active := [constant], excess := (affineWord (aAdd (aConst k constant) acc)).reverse}).store := by
    simpa only [word_constant_add, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.cons_append, List.nil_append] using
      xorLast_exec {base (k + 1) saved with excess := (normalWord acc).reverse} constant (aConstant acc)
  have outputReady : Exec prepareOutput
      ({base (k + 1) saved with input := [aConstant acc], active := [constant], excess := (affineWord (aAdd (aConst k constant) acc)).reverse}).store 3
      ({base (k + 1) saved with excess := (affineWord (aAdd (aConst k constant) acc)).reverse, output := saved}).store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have reversed : Exec ClauseQuery.reverseLoop
      ({base (k + 1) saved with excess := (affineWord (aAdd (aConst k constant) acc)).reverse, output := saved}).store
      (4 * (k + 1) + 1)
      ({base (k + 1) saved with output := affineWord (aAdd (aConst k constant) acc) ++ saved}).store := by
    simpa only [base, List.length_reverse, affineWord_length, List.reverse_reverse] using
      ClauseQuery.reverse_exec {base (k + 1) saved with output := saved}
        (affineWord (aAdd (aConst k constant) acc)).reverse
  have checked := Exec.seq ready (Exec.seq copied (Exec.seq (Exec.seq toggled outputReady) reversed))
  have cost : 9 * k + 16 = 4 + ((5 * k + 1) + ((3 + 3) + (4 * (k + 1) + 1))) := by omega
  simpa only [finish, cost] using checked

def block : Block 9 :=
  .seq initAccumulator (.seq MatrixPullbackInstructions.loop finish)
def fuel {n : Nat} (k : Nat) (p : Affine n) : Nat :=
  (3 * (k + 1) + 4) + (MatrixPullbackInstructions.fuel k p + (9 * k + 16))

theorem construct_exec {n k : Nat} (p : Affine n) (m : AffineMap n k) (saved : BitString) :
    Exec block (start p m saved).store (fuel k p)
      ({base (k + 1) saved with output := affineWord (pullback p m) ++ saved}).store := by
  have coefficients : aAdd (aConst k (aConstant p)) (selectedSum p m (aConst k false)) =
      pullback p m := (selectedSum_result p m (aConst k false)).trans (add_zero_right _)
  have finished := finish_exec (aConstant p) (selectedSum p m (aConst k false)) saved
  rw [coefficients] at finished
  exact Exec.seq (initAccumulator_exec p m saved)
    (Exec.seq (loop_exec p m (aConst k false) saved) finished)

theorem block_exec {n k : Nat} (p : Affine n) (m : AffineMap n k) :
    Exec block (start p m (mapBits m)).store (fuel k p)
      ({base (k + 1) (mapBits m) with output := mapBits (pivotMap p m)}).store :=
  construct_exec p m (mapBits m)

theorem fuel_bound {n : Nat} (k : Nat) (p : Affine n) :
    fuel k p ≤ 30 * (k + 2) * (n + 1) := by
  have scan := MatrixPullbackInstructions.fuel_bound k p
  simp only [fuel, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.mul_assoc] at *
  omega

def program : Program 9 := block.program 0 8

theorem program_run {n k : Nat} (p : Affine n) (m : AffineMap n k) :
    BitRegister.run program (fuel k p + 1) ⟨.running 0, (start p m (mapBits m)).store⟩ =
      ⟨.accepted, ({base (k + 1) (mapBits m) with output := mapBits (pivotMap p m)}).store⟩ :=
  (block_exec p m).program_run 0 8

end PNP.Concrete.ResidualReduction.MatrixPivotMapInstructions
