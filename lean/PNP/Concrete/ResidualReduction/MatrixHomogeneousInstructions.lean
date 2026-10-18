import PNP.Concrete.ResidualReduction.MatrixInputPreparation

/-! Literal homogenization of a parsed coefficient matrix. Every linear
coefficient is copied and each affine constant is replaced by false. The pass
restores exactly the existing solver's input layout; no matrix operation or
semantic callback is added to the machine instruction set. -/

namespace PNP.Concrete.ResidualReduction.MatrixHomogeneous
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixInstructions

def linearBits : {n : Nat} → Affine n → BitString
  | 0, _ => []
  | _ + 1, (b, a) => b :: linearBits a
theorem linearBits_length {n : Nat} (a : Affine n) : (linearBits a).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => rcases a with ⟨b, a⟩; exact congrArg Nat.succ (ih a)
theorem affineWord_split {n : Nat} (a : Affine n) :
    affineWord a = linearBits a ++ [aConstant a] := by
  induction n with
  | zero => rfl
  | succ n ih => rcases a with ⟨b, a⟩; exact congrArg (List.cons b) (ih a)
theorem homogeneous_bits {n : Nat} (a : Affine n) :
    affineWord (homogeneousRow a) = linearBits a ++ [false] := by
  induction n with
  | zero => cases a <;> rfl
  | succ n ih =>
    rcases a with ⟨b, a⟩
    change Bool.xor b false :: affineWord (homogeneousRow a) = b :: (linearBits a ++ [false])
    rw [Bool.xor_false, ih]

def row : Block 9 := .seq (.action (.copy 2 1)) <|
  .seq copyLoop (.seq (.action (.pop 0)) (.action (.push 3 false)))

theorem row_exec (r : Registers) {n : Nat} (a : Affine n) (suffix : BitString) :
    Exec row ({r with input := affineWord a ++ suffix, target := List.replicate n true, remaining := []}).store
      (5 * n + 4)
      ({r with input := suffix, target := List.replicate n true, remaining := [], excess := (affineWord (homogeneousRow a)).reverse ++ r.excess}).store := by
  let before := {r with input := affineWord a ++ suffix, target := List.replicate n true, remaining := []}
  let seeded := {before with remaining := List.replicate n true}
  let copied := {r with input := aConstant a :: suffix, target := List.replicate n true, remaining := [], excess := (linearBits a).reverse ++ r.excess}
  let popped := {copied with input := suffix}
  have seed : Exec (.action (.copy (2 : Fin 9) 1)) before.store 1 seeded.store := .action _ _
  have copy : Exec copyLoop seeded.store (5 * n + 1) copied.store := by
    simpa only [seeded, before, copied, affineWord_split, List.append_assoc,
      List.cons_append, List.nil_append, linearBits_length] using
      copy_exec {r with target := List.replicate n true} (linearBits a) (aConstant a :: suffix)
  have pop : Exec (.action (.pop (0 : Fin 9))) copied.store 1 popped.store := .action _ _
  have push : Exec (.action (.push (3 : Fin 9) false)) popped.store 1
      ({r with input := suffix, target := List.replicate n true, remaining := [], excess := (affineWord (homogeneousRow a)).reverse ++ r.excess}).store := by
    rw [homogeneous_bits, List.reverse_append]
    exact .action _ _
  have checked := Exec.seq seed (Exec.seq copy (Exec.seq pop push))
  have cost : 5 * n + 4 = 1 + ((5 * n + 1) + (1 + 1)) := by omega
  simpa only [row, cost] using checked

def loop : Block 9 := .loop 0 row
theorem loop_exec (r : Registers) (n : Nat) (rows : System n) :
    Exec loop ({r with input := matrixBits rows, target := List.replicate n true, remaining := []}).store
      ((5 * n + 5) * rows.length + 1)
      ({r with input := [], target := List.replicate n true, remaining := [], excess := (matrixBits (homogeneous rows)).reverse ++ r.excess}).store := by
  induction rows generalizing r with
  | nil => exact Exec.loopStop rfl
  | cons a rows ih =>
    obtain ⟨bit, rest, head⟩ := MatrixSolutionEncoding.affineWord_nonempty a
    have read : ({r with input := matrixBits (a :: rows), target := List.replicate n true, remaining := []}).store.get 0 =
        bit :: (rest ++ matrixBits rows) := by
      change affineWord a ++ matrixBits rows = _
      rw [head]
      rfl
    have checked := Exec.loopStep read (row_exec r a (matrixBits rows))
      (ih {r with excess := (affineWord (homogeneousRow a)).reverse ++ r.excess})
    have cost : (5 * n + 5) * (a :: rows).length + 1 =
        1 + ((5 * n + 4) + ((5 * n + 5) * rows.length + 1)) := by
      simp only [List.length_cons, Nat.mul_succ]
      omega
    simpa only [loop, cost, homogeneous, List.map_cons, matrixBits,
      List.reverse_append, List.append_assoc] using checked

def restore : Block 9 := .seq (.action (.copy 0 8)) <|
  .seq (.action (.copy 7 8)) (.action (.clear 8))
def coreBlock : Block 9 := .seq loop (.seq ClauseQuery.reverseLoop restore)
def fuel (n : Nat) (rows : System n) : Nat := 9 * (matrixBits rows).length + 5

theorem core_exec (n : Nat) (rows : System n) :
    Exec coreBlock (MatrixSolutionInstructions.start n rows).core.store (fuel n rows)
      (MatrixSolutionInstructions.start n (homogeneous rows)).core.store := by
  let bits := matrixBits (homogeneous rows)
  let before := {base n (matrixBits rows) with input := matrixBits rows}
  let copied := {base n (matrixBits rows) with excess := bits.reverse}
  let reversed := {base n (matrixBits rows) with output := bits}
  have first : Exec loop before.store ((5 * n + 5) * rows.length + 1) copied.store := by
    simpa only [before, copied, bits, base, List.append_nil] using loop_exec (base n (matrixBits rows)) n rows
  have second : Exec ClauseQuery.reverseLoop copied.store (4 * bits.length + 1) reversed.store := by
    simpa only [copied, reversed, base, List.length_reverse, List.reverse_reverse, List.append_nil] using
      ClauseQuery.reverse_exec (base n (matrixBits rows)) bits.reverse
  have third : Exec restore reversed.store 3 (MatrixSolutionInstructions.start n (homogeneous rows)).core.store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have checked := Exec.seq first (Exec.seq second third)
  have size : bits.length = (n + 1) * rows.length := by
    simp only [bits, matrixBits_length, homogeneous, List.length_map]
  have cost : fuel n rows = ((5 * n + 5) * rows.length + 1) + (4 * bits.length + 1 + 3) := by
    rw [fuel, matrixBits_length, size]
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_assoc]
    omega
  simpa only [coreBlock, cost, before, MatrixSolutionInstructions.start,
    MatrixSolutionInstructions.fromSweep, MatrixSweep.start] using checked

def block : Block 12 := MatrixReconstruction.lift coreBlock
theorem block_exec (n : Nat) (rows : System n) :
    Exec block (MatrixSolutionInstructions.start n rows).store (fuel n rows)
      (MatrixSolutionInstructions.start n (homogeneous rows)).store :=
  MatrixReconstruction.lift_exec coreBlock (MatrixSolutionInstructions.start n rows)
    (fuel n rows) _ (core_exec n rows)
theorem fuel_bound (n : Nat) (rows : System n) :
    fuel n rows ≤ 9 * (MatrixInputEncoding.codec.encode ⟨n, rows⟩).length + 5 :=
  Nat.add_le_add_right (Nat.mul_le_mul_left 9 (MatrixInputEncoding.payload_bound n rows)) 5

end PNP.Concrete.ResidualReduction.MatrixHomogeneous
