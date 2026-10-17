import PNP.Concrete.ResidualReduction.SourceQuadraticDiagonalAlgebra

/-! Literal diagonal/constant extraction from the triangular quadratic word.
Every discarded interaction coefficient and retained affine coefficient is read.
Both reversed accumulation and canonical forward output preserve an arbitrary
following input suffix; costs are linear in the encoded quadratic width. -/

namespace PNP.Concrete.ResidualReduction.SourceQuadraticDiagonal
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceClosure
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixPullbackAlgebra
open PNP.Concrete.ResidualReduction.SourceQuadraticDiagonalAlgebra

def take : Block 9 := MatrixLinearCombinationInstructions.readInput fun b => .action (.push 8 b)
theorem take_exec (r : Registers) (b : Bool) :
    Exec take ({r with input := b :: r.input}).store 3 ({r with output := b :: r.output}).store :=
  MatrixLinearCombinationInstructions.readInput_exec r b _ 1 _ (.action _ _)

def body : Block 9 := .seq (.action (.pop 1)) <| .seq (.action (.copy 2 1)) <| .seq dropLoop take
theorem body_exec (r : Registers) {n : Nat} (a : Affine n) (suffix : BitString) :
    Exec body ({r with input := affineWord a ++ suffix,target := List.replicate (n + 1) true,remaining := []}).store
      (3 * n + 6)
      ({r with input := suffix,target := List.replicate n true,remaining := [],output := aConstant a :: r.output}).store := by
  let before := {r with input := affineWord a ++ suffix,target := List.replicate (n + 1) true,remaining := []}
  let reduced := {before with target := List.replicate n true}
  let loaded := {reduced with remaining := List.replicate n true}
  let dropped := {r with input := aConstant a :: suffix,target := List.replicate n true,remaining := []}
  have pop : Exec (.action (.pop (1 : Fin 9))) before.store 1 reduced.store := .action _ _
  have load : Exec (.action (.copy (2 : Fin 9) 1)) reduced.store 1 loaded.store := .action _ _
  have discard : Exec dropLoop loaded.store (3 * n + 1) dropped.store := by
    simpa only [loaded,reduced,before,dropped,word_split,normalWord_length,List.append_assoc,List.singleton_append] using
      drop_exec {r with target := List.replicate n true} (normalWord a) (aConstant a :: suffix)
  have retain := take_exec {r with input := suffix,target := List.replicate n true,remaining := []} (aConstant a)
  have cost : 3 * n + 6 = 1 + (1 + ((3 * n + 1) + 3)) := by omega
  simpa only [body,cost,before] using Exec.seq pop (Exec.seq load (Exec.seq discard retain))

def ready (r : Registers) {n : Nat} (q : Quadratic n) (suffix : BitString) : Registers :=
  {r with input := SourceQuadraticEncoding.word q ++ suffix,target := List.replicate n true,remaining := []}
def loop : Block 9 := .loop 1 body
def loopFuel : Nat → Nat
  | 0 => 1
  | n + 1 => 1 + ((3 * n + 6) + loopFuel n)

theorem loop_exec (r : Registers) {n : Nat} (q : Quadratic n) (suffix : BitString) :
    Exec loop (ready r q suffix).store (loopFuel n)
      ({r with input := constant q :: suffix,target := [],remaining := [],output := (normalWord (diagonal q)).reverse ++ r.output}).store := by
  induction n generalizing r with
  | zero => exact Exec.loopStop rfl
  | succ n ih =>
    rcases q with ⟨a,q⟩
    have first := body_exec r a (SourceQuadraticEncoding.word q ++ suffix)
    have rest := ih {r with output := aConstant a :: r.output} q
    have checked := Exec.loopStep (source := (1 : Fin 9)) rfl first rest
    simpa only [loop,loopFuel,ready,SourceQuadraticEncoding.word_cons,constant,normal_cons,
      List.reverse_cons,List.append_assoc,List.singleton_append] using checked

def block : Block 9 := .seq loop take
def fuel (n : Nat) : Nat := loopFuel n + 3

theorem block_exec (r : Registers) {n : Nat} (q : Quadratic n) (suffix : BitString) :
    Exec block (ready r q suffix).store (fuel n)
      ({r with input := suffix,target := [],remaining := [],output := (affineWord (affinePart q)).reverse ++ r.output}).store := by
  have first := loop_exec r q suffix
  have last : Exec take
      ({r with input := constant q :: suffix,target := [],remaining := [],output := (normalWord (diagonal q)).reverse ++ r.output}).store 3
      ({r with input := suffix,target := [],remaining := [],output := (affineWord (affinePart q)).reverse ++ r.output}).store := by
    have checked := take_exec {r with input := suffix,target := [],remaining := [],output := (normalWord (diagonal q)).reverse ++ r.output} (constant q)
    simpa only [output_split,List.reverse_append,List.reverse_singleton,List.singleton_append,List.cons_append,List.nil_append,List.append_assoc] using checked
  exact Exec.seq first last

theorem loopFuel_exact (n : Nat) : loopFuel n + 2 = 3 * quadraticBits n + 4 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [loopFuel,quadraticBits,affineBits,Nat.mul_add,Nat.mul_one]
    omega
theorem fuel_exact (n : Nat) : fuel n = 3 * quadraticBits n + 4 * n + 1 := by
  have count := loopFuel_exact n
  unfold fuel
  omega

def forwardFinish : Block 9 := .seq (.action (.copy 3 8)) <| .seq (.action (.clear 8)) ClauseQuery.reverseLoop
def forwardBlock : Block 9 := .seq block forwardFinish
def forwardFuel (n : Nat) : Nat := fuel n + (4 * (n + 1) + 3)

theorem forward_exec (r : Registers) {n : Nat} (q : Quadratic n) (suffix : BitString) :
    Exec forwardBlock (ready {r with output := []} q suffix).store (forwardFuel n)
      ({r with input := suffix,target := [],remaining := [],excess := [],output := affineWord (affinePart q)}).store := by
  have first := block_exec {r with output := []} q suffix
  let reversed := {r with input := suffix,target := [],remaining := [],output := (affineWord (affinePart q)).reverse}
  let copied := {reversed with excess := (affineWord (affinePart q)).reverse}
  let prepared := {copied with output := []}
  let final := {r with input := suffix,target := [],remaining := [],excess := [],output := affineWord (affinePart q)}
  have copy : Exec (.action (.copy (3 : Fin 9) 8)) reversed.store 1 copied.store := .action _ _
  have clear : Exec (.action (.clear (8 : Fin 9))) copied.store 1 prepared.store := .action _ _
  have reverse : Exec ClauseQuery.reverseLoop prepared.store (4 * (n + 1) + 1) final.store := by
    simpa only [prepared,copied,reversed,final,List.length_reverse,affineWord_length,List.reverse_reverse,List.append_nil] using
      ClauseQuery.reverse_exec {r with input := suffix,target := [],remaining := [],output := []}
        (affineWord (affinePart q)).reverse
  have last : Exec forwardFinish reversed.store (4 * (n + 1) + 3) final.store := by
    have cost : 4 * (n + 1) + 3 = 1 + (1 + (4 * (n + 1) + 1)) := by omega
    simpa only [forwardFinish,cost] using Exec.seq copy (Exec.seq clear reverse)
  have start : Exec block (ready {r with output := []} q suffix).store (fuel n) reversed.store := by
    simpa only [reversed,List.append_nil] using first
  exact Exec.seq start last

theorem forwardFuel_exact (n : Nat) : forwardFuel n = 3 * quadraticBits n + 8 * n + 8 := by
  rw [forwardFuel,fuel_exact]
  omega
theorem forwardFuel_source_bound {n : Nat} (q : Quadratic n) :
    forwardFuel n ≤ 11 * (SourceQuadraticEncoding.word q).length := by
  rw [forwardFuel_exact,SourceQuadraticEncoding.word_length]
  have width := SourceQuadraticDiagonalAlgebra.dimension_bound n
  omega

end PNP.Concrete.ResidualReduction.SourceQuadraticDiagonal
