import PNP.Concrete.ResidualReduction.SourceBilinearRowInstructions

/-! Complete counted conversion of a row-major matrix into linear source rows.
The row counter, not the input's nonemptiness, controls iteration: a matrix
with zero columns and nonzero rows must still emit every row. -/

namespace PNP.Concrete.ResidualReduction.SourceBilinearMatrixInstructions
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.SourceActivityMapAlgebra
open PNP.Concrete.ResidualReduction.SourceBilinearFamily

theorem coefficient_bits_succ {m n : Nat} (M : Matrix (m + 1) n) :
    coefficientMatrixBits M =
      (List.finRange n).map (M 0) ++ coefficientMatrixBits (fun i => M i.succ) := by
  simp only [coefficientMatrixBits, List.finRange_succ, List.flatMap_cons,
    List.flatMap_map]

def step : Block 9 := .seq SourceBilinearRowInstructions.row (.action (.pop 4))
def loop : Block 9 := .loop 4 step

theorem loop_exec (r : Registers) {m n : Nat} (M : Matrix m n) :
    Exec loop ({r with input := coefficientMatrixBits M, target := List.replicate n true, remaining := [], sign := List.replicate m true}).store
      ((8 * n + 9) * m + 1)
      ({r with input := [], target := List.replicate n true, remaining := [], sign := [], excess := (familyBits (family M)).reverse ++ r.excess}).store := by
  induction m generalizing r with
  | zero => exact Exec.loopStop rfl
  | succ m ih =>
    let tail : Matrix m n := fun i => M i.succ
    let before := {r with input := coefficientMatrixBits M, target := List.replicate n true, remaining := [], sign := List.replicate (m + 1) true}
    let copied := {before with input := coefficientMatrixBits tail, excess := (rowWord (row (M 0))).reverse ++ r.excess}
    let after := {copied with sign := List.replicate m true}
    have one : Exec SourceBilinearRowInstructions.row before.store (8 * n + 7) copied.store := by
      simpa only [before, copied, tail, coefficient_bits_succ] using
        SourceBilinearRowInstructions.coefficient_row_exec
          {r with sign := List.replicate (m + 1) true} (M 0) (coefficientMatrixBits tail)
    have pop : Exec (.action (.pop (4 : Fin 9))) copied.store 1 after.store := .action _ _
    have first : Exec step before.store (8 * n + 8) after.store := by
      have cost : 8 * n + 8 = (8 * n + 7) + 1 := by omega
      simpa only [step, cost] using Exec.seq one pop
    have rest := ih {r with excess := (rowWord (row (M 0))).reverse ++ r.excess} tail
    have checked := Exec.loopStep (source := (4 : Fin 9)) rfl first rest
    have cost : (8 * n + 9) * (m + 1) + 1 = 1 + ((8 * n + 8) + ((8 * n + 9) * m + 1)) := by
      simp only [Nat.mul_succ]
      omega
    simpa only [loop, cost, before, after, copied, tail, family, familyBits,
      List.reverse_append, List.append_assoc] using checked

def block : Block 9 := .seq loop ClauseQuery.reverseLoop
def fuel (m n : Nat) : Nat := (16 * n + 21) * m + 2

theorem block_exec (r : Registers) {m n : Nat} (M : Matrix m n) :
    Exec block ({r with input := coefficientMatrixBits M, target := List.replicate n true, remaining := [], sign := List.replicate m true, excess := [], output := []}).store
      (fuel m n)
      ({r with input := [], target := List.replicate n true, remaining := [], sign := [], excess := [], output := familyBits (family M)}).store := by
  let clean := {r with target := List.replicate n true, remaining := [], sign := [], excess := [], output := []}
  let copied := {clean with input := [], excess := (familyBits (family M)).reverse}
  let after := {clean with input := [], output := familyBits (family M)}
  have converted : Exec loop ({clean with input := coefficientMatrixBits M, sign := List.replicate m true}).store
      ((8 * n + 9) * m + 1) copied.store := by
    simpa only [clean, copied, List.append_nil] using loop_exec clean M
  have reversed : Exec ClauseQuery.reverseLoop copied.store (4 * (familyBits (family M)).length + 1) after.store := by
    simpa only [clean, copied, after, List.length_reverse, List.reverse_reverse, List.append_nil] using
      ClauseQuery.reverse_exec {clean with input := []} (familyBits (family M)).reverse
  have cost : fuel m n = ((8 * n + 9) * m + 1) + (4 * (familyBits (family M)).length + 1) := by
    rw [fuel, family_bits_length]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc]
    omega
  simpa only [block, cost, clean, copied, after] using Exec.seq converted reversed

theorem fuel_mono (m n M N : Nat) (hm : m ≤ M) (hn : n ≤ N) : fuel m n ≤ fuel M N := by
  have factor : 16 * n + 21 ≤ 16 * N + 21 := by omega
  exact Nat.add_le_add_right (Nat.mul_le_mul factor hm) 2

end PNP.Concrete.ResidualReduction.SourceBilinearMatrixInstructions
