import PNP.Concrete.ResidualReduction.SourcePlaneMatrixEncoding

/-! Copy each complete affine equation, including its constant, and discard
only its extra padding bit. Both the counted copy and final output reversal
are literal instructions. The source-derived caller establishes the padding
identity; this pass does not assume an external equation certificate. -/

namespace PNP.Concrete.ResidualReduction.SourcePlaneMatrixProjection
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourcePlaneMatrix

def row : Block 9 := .seq (.action (.copy 2 1)) <|
  .seq copyLoop (.action (.pop 0))
theorem row_exec (r : Registers) {m : Nat} (a : Affine m) (suffix : BitString) :
    Exec row ({r with input := affineWord a ++ false :: suffix, target := List.replicate (m + 1) true, remaining := []}).store
      (5 * (m + 1) + 3)
      ({r with input := suffix, target := List.replicate (m + 1) true, remaining := [], excess := (affineWord a).reverse ++ r.excess}).store := by
  let before := {r with input := affineWord a ++ false :: suffix, target := List.replicate (m + 1) true, remaining := []}
  let seeded := {before with remaining := List.replicate (m + 1) true}
  let copied := {r with input := false :: suffix, target := List.replicate (m + 1) true, remaining := [], excess := (affineWord a).reverse ++ r.excess}
  have seed : Exec (.action (.copy (2 : Fin 9) 1)) before.store 1 seeded.store := .action _ _
  have copy : Exec copyLoop seeded.store (5 * (m + 1) + 1) copied.store := by
    simpa only [seeded, before, copied, affineWord_length] using
      copy_exec {r with target := List.replicate (m + 1) true} (affineWord a) (false :: suffix)
  have pop : Exec (.action (.pop (0 : Fin 9))) copied.store 1
      ({r with input := suffix, target := List.replicate (m + 1) true, remaining := [], excess := (affineWord a).reverse ++ r.excess}).store := .action _ _
  have cost : 5 * (m + 1) + 3 = 1 + ((5 * (m + 1) + 1) + 1) := by omega
  simpa only [row, cost] using Exec.seq seed (Exec.seq copy pop)

def loop : Block 9 := .loop 0 row
theorem loop_exec (r : Registers) (m : Nat) (rows : System m) :
    Exec loop ({r with input := paddedRows rows, target := List.replicate (m + 1) true, remaining := []}).store
      ((5 * (m + 1) + 4) * rows.length + 1)
      ({r with input := [], target := List.replicate (m + 1) true, remaining := [], excess := (matrixBits rows).reverse ++ r.excess}).store := by
  induction rows generalizing r with
  | nil => exact Exec.loopStop rfl
  | cons a rows ih =>
    obtain ⟨bit, rest, head⟩ := MatrixSolutionEncoding.affineWord_nonempty a
    have read : ({r with input := affineWord a ++ false :: paddedRows rows, target := List.replicate (m + 1) true, remaining := []}).store.get 0 =
          bit :: (rest ++ false :: paddedRows rows) := by
      change affineWord a ++ false :: paddedRows rows = _
      rw [head]
      rfl
    have checked := Exec.loopStep read (row_exec r a (paddedRows rows))
      (ih {r with excess := (affineWord a).reverse ++ r.excess})
    have cost : (5 * (m + 1) + 4) * (a :: rows).length + 1 =
        1 + ((5 * (m + 1) + 3) + ((5 * (m + 1) + 4) * rows.length + 1)) := by
      simp only [List.length_cons, Nat.mul_succ]
      omega
    simpa only [loop, cost, paddedRows, matrixBits, List.reverse_append, List.append_assoc,
      List.cons_append, List.nil_append] using checked

def block : Block 9 := .seq loop ClauseQuery.reverseLoop
def fuel (m : Nat) (rows : System m) : Nat := (9 * (m + 1) + 4) * rows.length + 2
theorem block_exec (r : Registers) (m : Nat) (rows : System m) :
    Exec block ({r with input := paddedRows rows, target := List.replicate (m + 1) true, remaining := [], excess := [], output := []}).store (fuel m rows)
      ({r with input := [], target := List.replicate (m + 1) true, remaining := [], excess := [], output := matrixBits rows}).store := by
  let clean := {r with target := List.replicate (m + 1) true, remaining := [], excess := [], output := []}
  let copied := {clean with input := [], excess := (matrixBits rows).reverse}
  let after := {clean with input := [], output := matrixBits rows}
  have copiedCore : Exec loop ({clean with input := paddedRows rows}).store
      ((5 * (m + 1) + 4) * rows.length + 1) copied.store := by
    simpa only [clean, copied, List.append_nil] using loop_exec clean m rows
  have reversed : Exec ClauseQuery.reverseLoop copied.store (4 * (matrixBits rows).length + 1) after.store := by
    simpa only [clean, copied, after, List.length_reverse, List.reverse_reverse, List.append_nil] using
      ClauseQuery.reverse_exec {clean with input := []} (matrixBits rows).reverse
  have cost : fuel m rows = ((5 * (m + 1) + 4) * rows.length + 1) + (4 * (matrixBits rows).length + 1) := by
    rw [fuel, matrixBits_length]
    simp only [Nat.add_mul, Nat.mul_assoc]
    omega
  simpa only [block, cost, clean, after] using Exec.seq copiedCore reversed

end PNP.Concrete.ResidualReduction.SourcePlaneMatrixProjection
