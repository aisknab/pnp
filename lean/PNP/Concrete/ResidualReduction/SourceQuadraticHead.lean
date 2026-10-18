import PNP.Concrete.ResidualReduction.SourceQuadraticEncoding
import PNP.Concrete.ResidualReduction.MatrixLinearCombinationInstructions

/-! One literal triangular head of an affine-factor product. The variable
coefficients use the existing linear-combination loop. Both affine constants
and the Boolean diagonal correction are read and emitted explicitly. -/

namespace PNP.Concrete.ResidualReduction.SourceQuadraticHead
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixPullbackAlgebra
open PNP.Concrete.ResidualReduction.SourcePolarRowAlgebra
open PNP.Concrete.ResidualReduction.MatrixLinearCombinationInstructions

def head {n : Nat} (d e : Bool) (f g : Affine n) : Affine n :=
  aAdd (aScale d g) (aAdd (aScale e f) (aConst n (d && e)))

theorem head_normal {n : Nat} (d e : Bool) (f g : Affine n) :
    normalWord (head d e f g) = normalWord (combine e d f g) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases f with ⟨x,f⟩
    rcases g with ⟨y,g⟩
    change Bool.xor (d && y) (Bool.xor (e && x) false) :: normalWord (head d e f g) =
      Bool.xor (e && x) (d && y) :: normalWord (combine e d f g)
    rw [Bool.xor_false,Bool.xor_comm (d && y) (e && x),ih]

theorem head_constant {n : Nat} (d e : Bool) (f g : Affine n) :
    aConstant (head d e f g) =
      Bool.xor (d && aConstant g) (Bool.xor (e && aConstant f) (d && e)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases f with ⟨x,f⟩
    rcases g with ⟨y,g⟩
    exact ih f g

theorem head_word {n : Nat} (d e : Bool) (f g : Affine n) :
    affineWord (head d e f g) = normalWord (combine e d f g) ++
      [Bool.xor (d && aConstant g) (Bool.xor (e && aConstant f) (d && e))] := by
  rw [word_split,head_normal,head_constant]

theorem product_word {n : Nat} (d e : Bool) (f g : Affine n) :
    SourceQuadraticEncoding.word (qProduct (n := n + 1) (d,f) (e,g)) =
      affineWord (head d e f g) ++ SourceQuadraticEncoding.word (qProduct f g) := rfl

def finish (d e : Bool) : Block 9 :=
  readInput fun x => readMode fun y =>
    .action (.push 8 (Bool.xor (d && y) (Bool.xor (e && x) (d && e))))

theorem finish_exec (r : Registers) (d e x y : Bool) :
    Exec (finish d e) ({r with input := x :: r.input,mode := y :: r.mode}).store 5
      ({r with output := Bool.xor (d && y) (Bool.xor (e && x) (d && e)) :: r.output}).store := by
  unfold finish
  refine readInput_exec {r with mode := y :: r.mode} x _ 3 _ ?_
  refine readMode_exec r y _ 1 _ ?_
  exact .action _ _

def block (d e : Bool) : Block 9 := .seq (loop e d) (finish d e)
def fuel (n : Nat) : Nat := 7 * n + 6

theorem block_exec (r : Registers) {n : Nat} (d e : Bool) (f g : Affine n)
    (leftSuffix rightSuffix : BitString) :
    Exec (block d e)
      ({r with input := affineWord f ++ leftSuffix,mode := affineWord g ++ rightSuffix,remaining := List.replicate n true}).store
      (fuel n)
      ({r with input := leftSuffix,mode := rightSuffix,remaining := [],output := (affineWord (head d e f g)).reverse ++ r.output}).store := by
  let middle := {r with input := aConstant f :: leftSuffix,mode := aConstant g :: rightSuffix,remaining := [],output := (normalWord (combine e d f g)).reverse ++ r.output}
  have last : Exec (finish d e) middle.store 5
      ({r with input := leftSuffix,mode := rightSuffix,remaining := [],output := (affineWord (head d e f g)).reverse ++ r.output}).store := by
    have checked := finish_exec
      {r with input := leftSuffix,mode := rightSuffix,remaining := [],output := (normalWord (combine e d f g)).reverse ++ r.output}
      d e (aConstant f) (aConstant g)
    simpa only [middle,head_word,List.reverse_append,List.reverse_singleton,List.singleton_append,List.cons_append,List.nil_append,List.append_assoc] using checked
  have cost : fuel n = (7 * n + 1) + 5 := by unfold fuel; omega
  simpa only [block,cost] using Exec.seq (loop_exec r e d f g leftSuffix rightSuffix) last

end PNP.Concrete.ResidualReduction.SourceQuadraticHead
