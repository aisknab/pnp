import PNP.Concrete.ResidualReduction.SourceReplayAffine
import PNP.Concrete.ResidualReduction.SourceMatrixEncoding

/-! Literal weighted source evaluation on an arbitrary encoded point. Stored
selection flags are ignored: the actual supplied weight bytes select rows.
Every row and both affine factors are read, including false weights and width
zero. This subroutine is later fed by the complete replay parser. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayValue
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceBalance
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.MatrixInstructions

def full (r : Registers) (weights : BitString) : Store 10 := Frame.join r.store (.cons weights .nil)
def core (b : Block 9) : Block 10 := Frame.block 1 b
theorem core_exec {b : Block 9} {before after : Registers} {used : Nat}
    (checked : Exec b before.store used after.store) (weights : BitString) :
    Exec (core b) (full before weights) used (full after weights) :=
  Frame.execution checked (.cons weights .nil)
def registers {n : Nat} (input : BitString) (z : Point n) (output : BitString) : Registers :=
  ⟨input,List.replicate n true,[],[],[],[],[],(SourceEncoding.pointCodec n).encode z,output⟩
def work {n : Nat} (input : BitString) (z : Point n) (weights output : BitString) : Store 10 :=
  full (registers input z output) weights

def readWeight (next : Bool → Block 10) : Block 10 :=
  .branch 9 .skip (.seq (.action (.pop 9)) (next false)) (.seq (.action (.pop 9)) (next true))
theorem readWeight_exec (r : Registers) (weights : BitString) (b : Bool)
    (next : Bool → Block 10) (used : Nat) (after : Store 10)
    (checked : Exec (next b) (full r weights) used after) :
    Exec (readWeight next) (full r (b :: weights)) (2 + used) after := by
  have popped : Exec (.action (.pop (9 : Fin 10))) (full r (b :: weights)) 1 (full r weights) := .action _ _
  rw [show 2 + used = 1 + (1 + used) by omega]
  cases b with
  | false => exact Exec.zero rfl (Exec.seq popped checked)
  | true => exact Exec.one rfl (Exec.seq popped checked)

def readOutput (next : Bool → Block 10) : Block 10 :=
  .branch 8 .skip (.seq (.action (.pop 8)) (next false)) (.seq (.action (.pop 8)) (next true))
theorem readOutput_exec (r : Registers) (weights : BitString) (b : Bool)
    (next : Bool → Block 10) (used : Nat) (after : Store 10)
    (checked : Exec (next b) (full r weights) used after) :
    Exec (readOutput next) (full {r with output := b :: r.output} weights) (2 + used) after := by
  have popped : Exec (.action (.pop (8 : Fin 10))) (full {r with output := b :: r.output} weights) 1
      (full r weights) := .action _ _
  rw [show 2 + used = 1 + (1 + used) by omega]
  cases b with
  | false => exact Exec.zero rfl (Exec.seq popped checked)
  | true => exact Exec.one rfl (Exec.seq popped checked)

def absorb : Block 10 := readWeight fun w => readOutput fun right =>
  readOutput fun left => readOutput fun acc => .action (.push 8 (Bool.xor (w && (left && right)) acc))
theorem absorb_exec (r : Registers) (weights : BitString) (w left right acc : Bool) :
    Exec absorb (full {r with output := right :: left :: acc :: r.output} (w :: weights)) 9
      (full {r with output := Bool.xor (w && (left && right)) acc :: r.output} weights) := by
  unfold absorb
  refine readWeight_exec {r with output := right :: left :: acc :: r.output} weights w _ 7 _ ?_
  refine readOutput_exec {r with output := left :: acc :: r.output} weights right _ 5 _ ?_
  refine readOutput_exec {r with output := acc :: r.output} weights left _ 3 _ ?_
  refine readOutput_exec r weights acc _ 1 _ ?_
  exact .action _ _

def row : Block 10 := .seq (.action (.pop 0))
  (.seq (core SourceReplayAffine.block) (.seq (core SourceReplayAffine.block) absorb))
def rowFuel (n : Nat) : Nat := 18 * n + 30

theorem row_exec {n : Nat} (r : Row n) (z : Point n) (w acc : Bool)
    (suffix weights output : BitString) :
    Exec row (work (rowWord r ++ suffix) z (w :: weights) (acc :: output)) (rowFuel n)
      (work suffix z weights (Bool.xor (w && r.eval z) acc :: output)) := by
  have words : rowWord r ++ suffix =
      r.selected :: (affineWord r.left ++ (affineWord r.right ++ suffix)) := by
    simp only [rowWord,List.cons_append,List.append_assoc]
  have popped : Exec (.action (.pop (0 : Fin 10)))
      (work (rowWord r ++ suffix) z (w :: weights) (acc :: output)) 1
      (work (affineWord r.left ++ (affineWord r.right ++ suffix)) z (w :: weights) (acc :: output)) := by
    rw [words]
    exact .action _ _
  have left := core_exec
    (SourceReplayAffine.block_exec (registers [] z (acc :: output)) r.left z (affineWord r.right ++ suffix))
    (w :: weights)
  have right := core_exec
    (SourceReplayAffine.block_exec (registers [] z (aEval r.left z :: acc :: output)) r.right z suffix)
    (w :: weights)
  have last := absorb_exec (registers suffix z output) weights w (aEval r.left z) (aEval r.right z) acc
  have cost : rowFuel n = 1 + (SourceReplayAffine.fuel n + (SourceReplayAffine.fuel n + 9)) := by
    unfold rowFuel SourceReplayAffine.fuel
    omega
  simpa only [row,cost,work,registers,Row.eval] using Exec.seq popped (Exec.seq left (Exec.seq right last))

private theorem xor_fold (a b c : Bool) : Bool.xor b (Bool.xor a c) = Bool.xor (Bool.xor a b) c := by
  cases a <;> cases b <;> cases c <;> rfl
def loop : Block 10 := .loop 0 row
def loopFuel (n rows : Nat) : Nat := (18 * n + 31) * rows + 1

theorem loop_exec {n : Nat} (F : Family n) (w : Point F.length) (z : Point n)
    (suffix : BitString) (acc : Bool) (output : BitString) :
    Exec loop (work (familyBits F) z ((SourceEncoding.pointCodec F.length).encode w ++ suffix) (acc :: output))
      (loopFuel n F.length)
      (work [] z suffix (Bool.xor (weightedValue F w z) acc :: output)) := by
  induction F generalizing acc with
  | nil =>
    simp only [weightedValue,Bool.false_xor]
    exact Exec.loopStop rfl
  | cons r F ih =>
    rcases w with ⟨b,w⟩
    let remaining := (SourceEncoding.pointCodec F.length).encode w ++ suffix
    have first := row_exec r z b acc (familyBits F) remaining output
    have rest := ih w (Bool.xor (b && r.eval z) acc)
    have checked := Exec.loopStep (source := (0 : Fin 10)) rfl first rest
    have cost : loopFuel n (F.length + 1) = 1 + (rowFuel n + loopFuel n F.length) := by
      simp only [loopFuel,rowFuel,Nat.mul_add,Nat.mul_one]
      omega
    simpa only [loop,cost,familyBits,weightedValue,xor_fold,remaining,List.length_cons,
      SourceLinearMap.point_bits_cons,List.cons_append] using checked

def block : Block 10 := .seq (.action (.push 8 false)) loop
def fuel (n rows : Nat) : Nat := (18 * n + 31) * rows + 2

theorem block_exec {n : Nat} (F : Family n) (w : Point F.length) (z : Point n) (output : BitString) :
    Exec block (work (familyBits F) z ((SourceEncoding.pointCodec F.length).encode w) output)
      (fuel n F.length) (work [] z [] (weightedValue F w z :: output)) := by
  have seed : Exec (.action (.push (8 : Fin 10) false))
      (work (familyBits F) z ((SourceEncoding.pointCodec F.length).encode w) output) 1
      (work (familyBits F) z ((SourceEncoding.pointCodec F.length).encode w) (false :: output)) := .action _ _
  have body := loop_exec F w z [] false output
  simp only [List.append_nil,Bool.xor_false] at body
  have cost : fuel n F.length = 1 + loopFuel n F.length := by unfold fuel loopFuel; omega
  simpa only [block,cost] using Exec.seq seed body

theorem fuel_mono {n rows N R : Nat} (hn : n ≤ N) (hr : rows ≤ R) : fuel n rows ≤ fuel N R :=
  Nat.add_le_add_right (Nat.mul_le_mul (show 18 * n + 31 ≤ 18 * N + 31 by omega) hr) 2

end PNP.Concrete.ResidualReduction.SourceReplayValue
