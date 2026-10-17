import PNP.Concrete.ResidualReduction.MatrixLinearCombinationInstructions
import PNP.Concrete.ResidualReduction.MatrixSolutionEncoding

/-! Literal evaluation of one homogeneous coefficient row on an arbitrary
encoded parameter vector. Every coefficient and vector bit is read. The affine
constant is consumed but excluded from the direction, including width zero. -/

namespace PNP.Concrete.ResidualReduction.SourceLinearMap
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.MatrixLinearCombinationInstructions (readInput readInput_exec readMode readMode_exec)

def value {k : Nat} (f : Affine k) (z : Point k) : Bool := Bool.xor (aEval f z) (aConstant f)
theorem value_zero (b : Bool) : value (k := 0) b () = false := by cases b <;> rfl
theorem value_cons {k : Nat} (b c : Bool) (f : Affine k) (z : Point k) :
    value (k := k + 1) (b, f) (c, z) = Bool.xor (b && c) (value f z) := by
  simp only [value, aEval, aConstant, Bool.xor_assoc]
theorem point_bits_cons {k : Nat} (b : Bool) (z : Point k) :
    (SourceEncoding.pointCodec (k + 1)).encode (b, z) = b :: (SourceEncoding.pointCodec k).encode z := rfl
theorem linearMap_cons {n k : Nat} (f : Affine k) (fs : AffineMap n k) (z : Point k) :
    linearMapEval (n := n + 1) (f, fs) z = (value f z, linearMapEval fs z) := by
  simp only [linearMapEval, mapEval, pXor, eval_zero_constant, value]

def readSign (next : Bool → Block 9) : Block 9 :=
  .branch 4 .skip (.seq (.action (.pop 4)) (next false))
    (.seq (.action (.pop 4)) (next true))
theorem readSign_exec (r : Registers) (b : Bool) (next : Bool → Block 9)
    (fuel : Nat) (after : Registers) (checked : Exec (next b) r.store fuel after.store) :
    Exec (readSign next) ({r with sign := b :: r.sign}).store (2 + fuel) after.store := by
  have popped : Exec (.action (.pop (4 : Fin 9))) ({r with sign := b :: r.sign}).store 1 r.store := .action _ _
  rw [show 2 + fuel = 1 + (1 + fuel) by omega]
  cases b with
  | false => exact Exec.zero (source := (4 : Fin 9)) rfl (Exec.seq popped checked)
  | true => exact Exec.one (source := (4 : Fin 9)) rfl (Exec.seq popped checked)

def accumulate : Block 9 := readInput fun x => readMode fun y => readSign fun acc =>
  .action (.push 4 (Bool.xor (x && y) acc))
theorem accumulate_exec (r : Registers) (x y acc : Bool) :
    Exec accumulate ({r with input := x :: r.input, mode := y :: r.mode, sign := [acc]}).store 7
      ({r with sign := [Bool.xor (x && y) acc]}).store := by
  unfold accumulate
  refine readInput_exec {r with mode := y :: r.mode, sign := [acc]} x _ 5 _ ?_
  refine readMode_exec {r with sign := [acc]} y _ 3 _ ?_
  refine readSign_exec {r with sign := []} acc _ 1 _ ?_
  exact .action _ _
def dotStep : Block 9 := .seq accumulate (.action (.pop 2))
theorem dotStep_exec (r : Registers) (x y acc tick : Bool) :
    Exec dotStep ({r with input := x :: r.input, mode := y :: r.mode, sign := [acc], remaining := tick :: r.remaining}).store 8
      ({r with sign := [Bool.xor (x && y) acc]}).store :=
  Exec.seq (accumulate_exec {r with remaining := tick :: r.remaining} x y acc) (.action _ _)

private theorem xor_acc (a b c : Bool) : Bool.xor b (Bool.xor a c) = Bool.xor (Bool.xor a b) c := by
  cases a <;> cases b <;> cases c <;> rfl
def dotLoop : Block 9 := .loop 2 dotStep
theorem dotLoop_exec (r : Registers) {k : Nat} (f : Affine k) (z : Point k)
    (acc : Bool) (suffix : BitString) :
    Exec dotLoop ({r with input := affineWord f ++ suffix, mode := (SourceEncoding.pointCodec k).encode z, sign := [acc], remaining := List.replicate k true}).store (9 * k + 1)
      ({r with input := aConstant f :: suffix, mode := [], sign := [Bool.xor (value f z) acc], remaining := []}).store := by
  induction k generalizing r acc with
  | zero =>
    cases z
    simp only [value_zero, Bool.false_xor]
    exact Exec.loopStop rfl
  | succ k ih =>
    rcases f with ⟨b, f⟩
    rcases z with ⟨c, z⟩
    let tail := {r with input := affineWord f ++ suffix, mode := (SourceEncoding.pointCodec k).encode z, sign := [acc], remaining := List.replicate k true}
    have first := dotStep_exec tail b c acc true
    have rest := ih r f z (Bool.xor (b && c) acc)
    have checked := Exec.loopStep (source := (2 : Fin 9)) rfl first rest
    have cost : 9 * (k + 1) + 1 = 1 + (8 + (9 * k + 1)) := by omega
    simpa only [dotLoop, cost, tail, affineWord_cons, point_bits_cons, List.cons_append,
      List.replicate_succ, aConstant, value_cons, xor_acc] using checked

def rowPrepare : Block 9 := .seq (.action (.copy 2 1)) <|
  .seq (.action (.copy 5 7)) <| .seq (.action (.clear 4)) (.action (.push 4 false))
def rowFinish : Block 9 := .seq (.action (.pop 0)) (readSign fun b => .action (.push 8 b))
theorem rowFinish_exec (r : Registers) (constant bit : Bool) :
    Exec rowFinish ({r with input := constant :: r.input, sign := [bit]}).store 4
      ({r with sign := [], output := bit :: r.output}).store := by
  have popped : Exec (.action (.pop (0 : Fin 9)))
      ({r with input := constant :: r.input, sign := [bit]}).store 1 ({r with sign := [bit]}).store := .action _ _
  have emitted := readSign_exec {r with sign := []} bit (fun b => .action (.push 8 b)) 1
    {r with sign := [], output := bit :: r.output} (.action _ _)
  exact Exec.seq popped emitted
def row : Block 9 := .seq rowPrepare (.seq dotLoop rowFinish)
def rowFuel (k : Nat) : Nat := 9 * k + 9
theorem row_exec (r : Registers) {k : Nat} (f : Affine k) (z : Point k) (suffix : BitString) :
    Exec row ({r with input := affineWord f ++ suffix, target := List.replicate k true, reserved := (SourceEncoding.pointCodec k).encode z}).store (rowFuel k)
      ({r with input := suffix, target := List.replicate k true, reserved := (SourceEncoding.pointCodec k).encode z, remaining := [], mode := [], sign := [], output := value f z :: r.output}).store := by
  let before := {r with input := affineWord f ++ suffix, target := List.replicate k true, reserved := (SourceEncoding.pointCodec k).encode z}
  let prepared := {before with remaining := List.replicate k true, mode := (SourceEncoding.pointCodec k).encode z, sign := [false]}
  let done := {before with input := aConstant f :: suffix, remaining := [], mode := [], sign := [value f z]}
  have prepare : Exec rowPrepare before.store 4 prepared.store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
  have dot : Exec dotLoop prepared.store (9 * k + 1) done.store := by
    simpa only [prepared, done, before, Bool.xor_false] using dotLoop_exec before f z false suffix
  have finish := rowFinish_exec
    {before with input := suffix, remaining := [], mode := [], sign := []} (aConstant f) (value f z)
  have cost : rowFuel k = 4 + ((9 * k + 1) + 4) := by unfold rowFuel; omega
  simpa only [row, cost, before] using Exec.seq prepare (Exec.seq dot finish)

end PNP.Concrete.ResidualReduction.SourceLinearMap
