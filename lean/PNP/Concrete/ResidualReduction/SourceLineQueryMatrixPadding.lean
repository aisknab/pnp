import PNP.Concrete.ResidualReduction.SourceLineQueryMatrixProjection

/-! Literal zero-row construction for the two line-query matrices. Row
counters remain explicit even at zero width. The activity suffix is appended
by counted reversals, so matrix order is preserved without an oracle. -/

namespace PNP.Concrete.ResidualReduction.SourceLineQueryMatrixPadding
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.SourceLineQueryMatrixAlgebra

def innerStep : Block 9 := .seq (.action (.push 3 false)) (.action (.pop 2))
def innerLoop : Block 9 := .loop 2 innerStep
theorem inner_exec (r : Registers) (k : Nat) :
    Exec innerLoop ({r with remaining := List.replicate k true}).store (3 * k + 1)
      ({r with remaining := [], excess := List.replicate k false ++ r.excess}).store := by
  induction k generalizing r with
  | zero => exact Exec.loopStop rfl
  | succ k ih =>
    have step : Exec innerStep ({r with remaining := List.replicate (k + 1) true}).store 2
        ({r with remaining := List.replicate k true, excess := false :: r.excess}).store :=
      Exec.seq (.action _ _) (.action _ _)
    have checked := Exec.loopStep (source := (2 : Fin 9)) rfl step (ih {r with excess := false :: r.excess})
    have words : List.replicate k false ++ false :: r.excess =
        List.replicate (k + 1) false ++ r.excess := by
      calc
        _ = (List.replicate k false ++ List.replicate 1 false) ++ r.excess := by
          rw [List.append_assoc]
          rfl
        _ = _ := by rw [replicate_join]
    have cost : 3 * (k + 1) + 1 = 1 + (2 + (3 * k + 1)) := by omega
    simpa only [innerLoop, cost, words] using checked

def zeroStep : Block 9 := .seq (.action (.copy 2 1)) <| .seq innerLoop (.action (.pop 4))
theorem zeroStep_exec (r : Registers) (rows k : Nat) :
    Exec zeroStep ({r with target := List.replicate k true, remaining := [], sign := List.replicate (rows + 1) true}).store
      (3 * k + 3)
      ({r with target := List.replicate k true, remaining := [], sign := List.replicate rows true, excess := List.replicate k false ++ r.excess}).store := by
  let before := {r with target := List.replicate k true, remaining := [], sign := List.replicate (rows + 1) true}
  let seeded := {before with remaining := List.replicate k true}
  let filled := {before with remaining := [], excess := List.replicate k false ++ r.excess}
  have seed : Exec (.action (.copy (2 : Fin 9) 1)) before.store 1 seeded.store := .action _ _
  have fill : Exec innerLoop seeded.store (3 * k + 1) filled.store := inner_exec before k
  have pop : Exec (.action (.pop (4 : Fin 9))) filled.store 1
      ({r with target := List.replicate k true, remaining := [], sign := List.replicate rows true, excess := List.replicate k false ++ r.excess}).store := .action _ _
  have cost : 3 * k + 3 = 1 + ((3 * k + 1) + 1) := by omega
  simpa only [zeroStep, cost] using Exec.seq seed (Exec.seq fill pop)

def zeroLoop : Block 9 := .loop 4 zeroStep
def zeroFuel (rows k : Nat) : Nat := (3 * k + 4) * rows + 1
theorem zero_exec (r : Registers) (rows k : Nat) :
    Exec zeroLoop ({r with target := List.replicate k true, remaining := [], sign := List.replicate rows true}).store
      (zeroFuel rows k)
      ({r with target := List.replicate k true, remaining := [], sign := [], excess := List.replicate (rows * k) false ++ r.excess}).store := by
  induction rows generalizing r with
  | zero =>
    simp only [Nat.zero_mul]
    exact Exec.loopStop rfl
  | succ rows ih =>
    have checked := Exec.loopStep (source := (4 : Fin 9)) rfl (zeroStep_exec r rows k)
      (ih {r with excess := List.replicate k false ++ r.excess})
    have words : List.replicate (rows * k) false ++ (List.replicate k false ++ r.excess) =
        List.replicate ((rows + 1) * k) false ++ r.excess := by
      rw [← List.append_assoc, replicate_join]
      simp only [Nat.add_mul, Nat.one_mul]
    have cost : zeroFuel (rows + 1) k = 1 + ((3 * k + 3) + zeroFuel rows k) := by
      unfold zeroFuel
      rw [Nat.mul_add, Nat.mul_one]
      omega
    simpa only [zeroLoop, cost, words] using checked

def reverseOutput : Block 9 := .seq (.action (.copy 3 8)) <|
  .seq (.action (.clear 8)) ClauseQuery.reverseLoop
theorem reverse_output_exec (r : Registers) (word : BitString) :
    Exec reverseOutput ({r with excess := [], output := word}).store (4 * word.length + 3)
      ({r with excess := [], output := word.reverse}).store := by
  let before := {r with excess := [], output := word}
  let staged := {r with excess := word, output := []}
  have reverse : Exec ClauseQuery.reverseLoop staged.store (4 * word.length + 1)
      ({r with excess := [], output := word.reverse}).store := by
    simpa only [staged, List.append_nil] using ClauseQuery.reverse_exec {r with output := []} word
  have first : Exec (.action (.copy (3 : Fin 9) 8)) before.store 1 ({before with excess := word}).store := .action _ _
  have second : Exec (.action (.clear (8 : Fin 9))) ({before with excess := word}).store 1 staged.store := .action _ _
  have cost : 4 * word.length + 3 = 1 + (1 + (4 * word.length + 1)) := by omega
  simpa only [reverseOutput, cost] using Exec.seq first (Exec.seq second reverse)

def appendBlock : Block 9 := .seq reverseOutput <| .seq (.action (.copy 3 8)) <|
  .seq (.action (.clear 8)) <| .seq zeroLoop ClauseQuery.reverseLoop
def appendFuel (rows k bytes : Nat) : Nat :=
  (4 * bytes + 3) + (1 + (1 + (zeroFuel rows k + (4 * (bytes + rows * k) + 1))))
theorem append_exec (r : Registers) (rows k : Nat) (word : BitString) :
    Exec appendBlock
      ({r with target := List.replicate k true, remaining := [], sign := List.replicate rows true, excess := [], output := word}).store
      (appendFuel rows k word.length)
      ({r with target := List.replicate k true, remaining := [], sign := [], excess := [], output := word ++ List.replicate (rows * k) false}).store := by
  let clean := {r with target := List.replicate k true, remaining := [], sign := List.replicate rows true}
  let reversed := {clean with excess := [], output := word.reverse}
  let staged := {clean with excess := word.reverse, output := []}
  let filled := {clean with sign := [], excess := List.replicate (rows * k) false ++ word.reverse, output := []}
  let after := {clean with sign := [], excess := [], output := word ++ List.replicate (rows * k) false}
  have reverse : Exec reverseOutput ({clean with excess := [], output := word}).store
      (4 * word.length + 3) reversed.store := reverse_output_exec clean word
  have copy : Exec (.action (.copy (3 : Fin 9) 8)) reversed.store 1
      ({reversed with excess := word.reverse}).store := .action _ _
  have clear : Exec (.action (.clear (8 : Fin 9))) ({reversed with excess := word.reverse}).store 1 staged.store := .action _ _
  have fill : Exec zeroLoop staged.store (zeroFuel rows k) filled.store := zero_exec {clean with excess := word.reverse, output := []} rows k
  have finish : Exec ClauseQuery.reverseLoop filled.store
      (4 * (word.length + rows * k) + 1) after.store := by
    simpa only [filled, after, clean, List.length_append, List.length_reverse, List.length_replicate,
      List.reverse_append, List.reverse_reverse, List.reverse_replicate, List.append_nil,
      Nat.add_comm (rows * k) word.length] using
      ClauseQuery.reverse_exec {clean with sign := [], output := []} (List.replicate (rows * k) false ++ word.reverse)
  simpa only [appendBlock, appendFuel, clean, after] using
    Exec.seq reverse (Exec.seq copy (Exec.seq clear (Exec.seq fill finish)))

def normalBlock : Block 9 := .seq zeroLoop SourceLineQueryMatrixProjection.block
def normalFuel (n rows k : Nat) : Nat := zeroFuel rows k + SourceLineQueryMatrixProjection.fuel n k (rows * k)
theorem normal_exec (r : Registers) {n k : Nat} (fs : AffineMap n k) (rows : Nat) :
    Exec normalBlock
      ({r with input := mapBits fs, target := List.replicate k true, remaining := [], sign := List.replicate rows true, excess := [], output := []}).store
      (normalFuel n rows k)
      ({r with input := [], target := List.replicate k true, remaining := [], sign := [], excess := [], output := List.replicate (rows * k) false ++ linearBits fs}).store := by
  let clean := {r with input := mapBits fs, target := List.replicate k true, remaining := [], excess := [], output := []}
  let padded := {clean with sign := [], excess := List.replicate (rows * k) false}
  let after := {clean with input := [], sign := [], excess := [], output := List.replicate (rows * k) false ++ linearBits fs}
  have pad : Exec zeroLoop ({clean with sign := List.replicate rows true}).store (zeroFuel rows k) padded.store := by
    simpa only [clean, padded, List.append_nil] using zero_exec clean rows k
  have project : Exec SourceLineQueryMatrixProjection.block padded.store
      (SourceLineQueryMatrixProjection.fuel n k (rows * k)) after.store := by
    simpa only [clean, padded, after, List.length_replicate, List.reverse_replicate] using
      SourceLineQueryMatrixProjection.block_exec {clean with sign := []} fs (List.replicate (rows * k) false)
  simpa only [normalBlock, normalFuel, clean, after] using Exec.seq pad project

end PNP.Concrete.ResidualReduction.SourceLineQueryMatrixPadding
