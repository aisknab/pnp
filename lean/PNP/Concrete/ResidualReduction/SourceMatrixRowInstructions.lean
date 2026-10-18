import PNP.Concrete.ResidualReduction.SourcePolarInstructions

/-! One complete affine-mask equation is constructed from every encoded source
row. The loop is unbounded in family size and consumes the actual row bytes.
It emits coefficients in reverse accumulation order, followed by the equation's
zero constant; the outer matrix constructor must restore final byte order. -/

namespace PNP.Concrete.ResidualReduction.SourceMatrixRowInstructions
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.SourcePolarInstructions

def loop : Block 12 := .loop 0 rowBlock
def loopFuel (n i j count : Nat) : Nat := (6 * i + 6 * j + 12 * (n + 1) + 50) * count + 1

theorem loop_exec {n : Nat} (F : Family n) (i j : Fin n) (stack output : BitString) :
    Exec loop (working n i.val j.val [] (familyBits F) stack output).store
      (loopFuel n i.val j.val F.length)
      (working n i.val j.val [] [] stack ((F.map (fun r => polarBit r i.val j.val)).reverse ++ output)).store := by
  induction F generalizing output with
  | nil => exact Exec.loopStop rfl
  | cons r F ih =>
    have step := rowBlock_exec r i j (familyBits F) stack output
    have checked := Exec.loopStep (source := (0 : Fin 12)) rfl step
      (ih (polarBit r i.val j.val :: output))
    have cost : loopFuel n i.val j.val (r :: F).length =
        1 + ((6 * i.val + 6 * j.val + 12 * (n + 1) + 49) + loopFuel n i.val j.val F.length) := by
      simp only [loopFuel, List.length_cons, Nat.mul_add, Nat.mul_one]
      omega
    simpa only [loop, cost, familyBits, List.map_cons, List.reverse_cons,
      List.append_assoc, List.cons_append, List.nil_append] using checked

def matrixRow : Block 12 := .seq loop (.action (.push 8 false))

theorem matrixRow_exec {n : Nat} (F : Family n) (i j : Fin n) (stack output : BitString) :
    Exec matrixRow (working n i.val j.val [] (familyBits F) stack output).store
      (loopFuel n i.val j.val F.length + 1)
      (working n i.val j.val [] [] stack
        ((F.map (fun r => polarBit r i.val j.val) ++ [false]).reverse ++ output)).store := by
  have last : Exec (.action (.push (8 : Fin 12) false))
      (working n i.val j.val [] [] stack ((F.map (fun r => polarBit r i.val j.val)).reverse ++ output)).store 1
      (working n i.val j.val [] [] stack
        (false :: ((F.map (fun r => polarBit r i.val j.val)).reverse ++ output))).store := .action _ _
  simpa only [matrixRow, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append] using Exec.seq (loop_exec F i j stack output) last

/-- This is the exact encoded equation expected by the existing solver, not
a separately supplied or merely equisatisfiable row. -/
theorem exact_equation_exec {n : Nat} (F : Family n) (i j : Fin n) (output : BitString) :
    Exec matrixRow (working n i.val j.val [] (familyBits F) [] output).store
      (loopFuel n i.val j.val F.length + 1)
      (working n i.val j.val [] [] []
        ((MatrixInstructions.affineWord
          (SourcePlane.planeConstraint F (aConst n false) (aConst n false)
            (ConstrainedBilinear.unitPoint n i) (ConstrainedBilinear.unitPoint n j))).reverse ++ output)).store := by
  rw [planeConstraint_word]
  exact matrixRow_exec F i j [] output

theorem matrixRowFuel_bound {n : Nat} (F : Family n) (i j : Fin n) :
    loopFuel n i.val j.val F.length + 1 ≤ (24 * n + 62) * F.length + 2 := by
  have one := rowFuel_bound i j
  have all := Nat.mul_le_mul_right F.length (show
    6 * i.val + 6 * j.val + 12 * (n + 1) + 50 ≤ 24 * n + 62 by omega)
  unfold loopFuel
  omega

end PNP.Concrete.ResidualReduction.SourceMatrixRowInstructions
