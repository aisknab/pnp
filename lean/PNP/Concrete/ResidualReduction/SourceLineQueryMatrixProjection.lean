import PNP.Concrete.ResidualReduction.SourceLineQueryMatrixAlgebra

/-! Project every affine-map row to its linear coefficients using the
existing counted-copy instructions. The discarded constant may be true or
false. The loop still consumes one constant when the parameter count is zero,
so empty coefficient rows cannot make the program stall. -/

namespace PNP.Concrete.ResidualReduction.SourceLineQueryMatrixProjection
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.MatrixPullbackAlgebra
open PNP.Concrete.ResidualReduction.SourceLineQueryMatrixAlgebra

abbrev row : Block 9 := SourcePlaneMatrixProjection.row
abbrev loop : Block 9 := SourcePlaneMatrixProjection.loop
abbrev block : Block 9 := SourcePlaneMatrixProjection.block

theorem row_exec (r : Registers) {k : Nat} (f : Affine k) (suffix : BitString) :
    Exec row ({r with input := affineWord f ++ suffix, target := List.replicate k true, remaining := []}).store
      (5 * k + 3)
      ({r with input := suffix, target := List.replicate k true, remaining := [], excess := (normalWord f).reverse ++ r.excess}).store := by
  let before := {r with input := normalWord f ++ aConstant f :: suffix, target := List.replicate k true, remaining := []}
  let staged := {before with remaining := List.replicate k true}
  let copied := {r with input := aConstant f :: suffix, target := List.replicate k true, remaining := [], excess := (normalWord f).reverse ++ r.excess}
  have seed : Exec (.action (.copy (2 : Fin 9) 1)) before.store 1 staged.store := .action _ _
  have copy : Exec copyLoop staged.store (5 * k + 1) copied.store := by
    simpa only [staged, before, copied, normalWord_length] using
      copy_exec {r with target := List.replicate k true} (normalWord f) (aConstant f :: suffix)
  have pop : Exec (.action (.pop (0 : Fin 9))) copied.store 1
      ({r with input := suffix, target := List.replicate k true, remaining := [], excess := (normalWord f).reverse ++ r.excess}).store := .action _ _
  have cost : 5 * k + 3 = 1 + ((5 * k + 1) + 1) := by omega
  simpa only [row, SourcePlaneMatrixProjection.row, cost, before, word_split,
    List.append_assoc, List.singleton_append] using Exec.seq seed (Exec.seq copy pop)

theorem loop_exec (r : Registers) {n k : Nat} (fs : AffineMap n k) :
    Exec loop ({r with input := mapBits fs, target := List.replicate k true, remaining := []}).store
      ((5 * k + 4) * n + 1)
      ({r with input := [], target := List.replicate k true, remaining := [], excess := (linearBits fs).reverse ++ r.excess}).store := by
  induction n generalizing r with
  | zero => exact Exec.loopStop rfl
  | succ n ih =>
    rcases fs with ⟨f, fs⟩
    obtain ⟨bit, rest, head⟩ := affineWord_nonempty f
    have read : ({r with input := affineWord f ++ mapBits fs, target := List.replicate k true, remaining := []}).store.get 0 =
        bit :: (rest ++ mapBits fs) := by
      change affineWord f ++ mapBits fs = _
      rw [head]
      rfl
    have checked := Exec.loopStep read (row_exec r f (mapBits fs))
      (ih {r with excess := (normalWord f).reverse ++ r.excess} fs)
    have cost : (5 * k + 4) * (n + 1) + 1 =
        1 + ((5 * k + 3) + ((5 * k + 4) * n + 1)) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    simpa only [loop, SourcePlaneMatrixProjection.loop, cost, mapBits_cons, linearBits,
      List.reverse_append, List.append_assoc] using checked

def fuel (n k padding : Nat) : Nat := ((5 * k + 4) * n + 1) + (4 * (padding + n * k) + 1)
theorem block_exec (r : Registers) {n k : Nat} (fs : AffineMap n k) (padding : BitString) :
    Exec block ({r with input := mapBits fs, target := List.replicate k true, remaining := [], excess := padding.reverse, output := []}).store
      (fuel n k padding.length)
      ({r with input := [], target := List.replicate k true, remaining := [], excess := [], output := padding ++ linearBits fs}).store := by
  let clean := {r with target := List.replicate k true, remaining := [], excess := padding.reverse, output := []}
  let copied := {clean with input := [], excess := (padding ++ linearBits fs).reverse}
  let after := {clean with input := [], excess := [], output := padding ++ linearBits fs}
  have rows : Exec loop ({clean with input := mapBits fs}).store ((5 * k + 4) * n + 1) copied.store := by
    simpa only [clean, copied, List.reverse_append] using loop_exec clean fs
  have reversed : Exec ClauseQuery.reverseLoop copied.store
      (4 * (padding ++ linearBits fs).length + 1) after.store := by
    simpa only [clean, copied, after, List.length_reverse, List.reverse_reverse, List.append_nil] using
      ClauseQuery.reverse_exec {clean with input := []} (padding ++ linearBits fs).reverse
  have cost : fuel n k padding.length =
      ((5 * k + 4) * n + 1) + (4 * (padding ++ linearBits fs).length + 1) := by
    rw [List.length_append, linearBits_length]
    rfl
  simpa only [block, SourcePlaneMatrixProjection.block, cost, clean, after] using Exec.seq rows reversed

end PNP.Concrete.ResidualReduction.SourceLineQueryMatrixProjection
