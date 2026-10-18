import PNP.Concrete.ResidualReduction.SourcePolarRowAlgebra

/-! Literal homogeneous linear-combination rows. Both variable words are
read in full, both constants are consumed without using them, and a false
constant is emitted. Boolean parameters select among four finite blocks;
there is no semantic evaluator in the instruction set. -/

namespace PNP.Concrete.ResidualReduction.MatrixLinearCombinationInstructions
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixPullbackAlgebra
open PNP.Concrete.ResidualReduction.SourcePolarRowAlgebra

def readInput (next : Bool → Block 9) : Block 9 :=
  .branch 0 .skip (.seq (.action (.pop 0)) (next false))
    (.seq (.action (.pop 0)) (next true))
theorem readInput_exec (r : Registers) (b : Bool) (next : Bool → Block 9)
    (fuel : Nat) (after : Registers) (checked : Exec (next b) r.store fuel after.store) :
    Exec (readInput next) ({r with input := b :: r.input}).store (2 + fuel) after.store := by
  have popped : Exec (.action (.pop (0 : Fin 9)))
      ({r with input := b :: r.input}).store 1 r.store := .action _ _
  rw [show 2 + fuel = 1 + (1 + fuel) by omega]
  cases b with
  | false => exact Exec.zero (source := (0 : Fin 9)) rfl (Exec.seq popped checked)
  | true => exact Exec.one (source := (0 : Fin 9)) rfl (Exec.seq popped checked)

def readMode (next : Bool → Block 9) : Block 9 :=
  .branch 5 .skip (.seq (.action (.pop 5)) (next false))
    (.seq (.action (.pop 5)) (next true))
theorem readMode_exec (r : Registers) (b : Bool) (next : Bool → Block 9)
    (fuel : Nat) (after : Registers) (checked : Exec (next b) r.store fuel after.store) :
    Exec (readMode next) ({r with mode := b :: r.mode}).store (2 + fuel) after.store := by
  have popped : Exec (.action (.pop (5 : Fin 9)))
      ({r with mode := b :: r.mode}).store 1 r.store := .action _ _
  rw [show 2 + fuel = 1 + (1 + fuel) by omega]
  cases b with
  | false => exact Exec.zero (source := (5 : Fin 9)) rfl (Exec.seq popped checked)
  | true => exact Exec.one (source := (5 : Fin 9)) rfl (Exec.seq popped checked)

def emit (a b : Bool) : Block 9 :=
  readInput fun x => readMode fun y => .action (.push 8 (Bool.xor (a && x) (b && y)))
theorem emit_exec (r : Registers) (a b x y : Bool) :
    Exec (emit a b) ({r with input := x :: r.input, mode := y :: r.mode}).store 5
      ({r with output := Bool.xor (a && x) (b && y) :: r.output}).store := by
  unfold emit
  refine readInput_exec {r with mode := y :: r.mode} x _ 3 _ ?_
  refine readMode_exec r y _ 1 _ ?_
  exact .action _ _

def body (a b : Bool) : Block 9 := .seq (emit a b) (.action (.pop 2))
theorem body_exec (r : Registers) (a b x y tick : Bool) :
    Exec (body a b)
      ({r with input := x :: r.input, mode := y :: r.mode, remaining := tick :: r.remaining}).store 6
      ({r with output := Bool.xor (a && x) (b && y) :: r.output}).store :=
  Exec.seq (emit_exec {r with remaining := tick :: r.remaining} a b x y) (.action _ _)

def loop (a b : Bool) : Block 9 := .loop 2 (body a b)
theorem loop_exec (r : Registers) {n : Nat} (a b : Bool) (f g : Affine n)
    (leftSuffix rightSuffix : BitString) :
    Exec (loop a b)
      ({r with input := affineWord f ++ leftSuffix, mode := affineWord g ++ rightSuffix, remaining := List.replicate n true}).store
      (7 * n + 1)
      ({r with input := aConstant f :: leftSuffix, mode := aConstant g :: rightSuffix, remaining := [], output := (normalWord (combine a b f g)).reverse ++ r.output}).store := by
  induction n generalizing r with
  | zero => exact Exec.loopStop rfl
  | succ n ih =>
    rcases f with ⟨x, f⟩; rcases g with ⟨y, g⟩
    let tail := {r with input := affineWord f ++ leftSuffix, mode := affineWord g ++ rightSuffix, remaining := List.replicate n true}
    have first := body_exec tail a b x y true
    have rest := ih {r with output := Bool.xor (a && x) (b && y) :: r.output} f g
    have checked := Exec.loopStep (source := (2 : Fin 9)) rfl first rest
    have cost : 7 * (n + 1) + 1 = 1 + (6 + (7 * n + 1)) := by omega
    simpa only [loop, cost, tail, affineWord_cons, List.cons_append, List.replicate_succ,
      combine, normalWord, aConstant, List.reverse_cons, List.append_assoc,
      List.singleton_append, List.nil_append] using checked

def finish : Block 9 := .seq (.action (.pop 0)) <|
  .seq (.action (.pop 5)) (.action (.push 8 false))
def block (a b : Bool) : Block 9 := .seq (loop a b) finish
def fuel (n : Nat) : Nat := 7 * n + 4

theorem block_exec (r : Registers) {n : Nat} (a b : Bool) (f g : Affine n)
    (leftSuffix rightSuffix : BitString) :
    Exec (block a b)
      ({r with input := affineWord f ++ leftSuffix, mode := affineWord g ++ rightSuffix, remaining := List.replicate n true}).store
      (fuel n)
      ({r with input := leftSuffix, mode := rightSuffix, remaining := [], output := (affineWord (combine a b f g)).reverse ++ r.output}).store := by
  let middle := {r with input := aConstant f :: leftSuffix, mode := aConstant g :: rightSuffix, remaining := [], output := (normalWord (combine a b f g)).reverse ++ r.output}
  have finished : Exec finish middle.store 3
      ({r with input := leftSuffix, mode := rightSuffix, remaining := [], output := (affineWord (combine a b f g)).reverse ++ r.output}).store := by
    rw [combine_word, List.reverse_append]
    exact Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have cost : fuel n = (7 * n + 1) + 3 := by unfold fuel; omega
  simpa only [block, cost] using Exec.seq (loop_exec r a b f g leftSuffix rightSuffix) finished

end PNP.Concrete.ResidualReduction.MatrixLinearCombinationInstructions
