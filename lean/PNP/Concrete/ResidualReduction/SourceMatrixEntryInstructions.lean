import PNP.Concrete.ResidualReduction.SourceOrderedScanCoordinate

/-! Literal arbitrary matrix-entry access. The unary row-major address is
constructed by loops, then every skipped bit is consumed. Matrix lookup and
multiplication are specifications, not source-machine instructions. -/

namespace PNP.Concrete.ResidualReduction.SourceMatrixEntry
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceActivityMapAlgebra
open PNP.Concrete.ResidualReduction.MatrixInstructions

def addStep : Block 9 := .seq (.action (.push 3 true)) (.action (.pop 2))
def addLoop : Block 9 := .loop 2 addStep
theorem add_exec (r : Registers) (count : Nat) :
    Exec addLoop ({r with remaining := List.replicate count true}).store (3 * count + 1)
      ({r with remaining := [], excess := List.replicate count true ++ r.excess}).store := by
  induction count generalizing r with
  | zero => exact Exec.loopStop rfl
  | succ count ih =>
    have first : Exec addStep ({r with remaining := List.replicate (count + 1) true}).store 2
        ({r with remaining := List.replicate count true, excess := true :: r.excess}).store :=
      Exec.seq (.action _ _) (.action _ _)
    have checked := Exec.loopStep (source := (2 : Fin 9)) rfl first (ih {r with excess := true :: r.excess})
    have snoc : List.replicate count true ++ true :: r.excess = List.replicate (count + 1) true ++ r.excess := by
      rw [List.replicate_succ']
      simp only [List.append_assoc, List.singleton_append]
    have cost : 3 * (count + 1) + 1 = 1 + (2 + (3 * count + 1)) := by omega
    simpa only [addLoop, cost, snoc] using checked

def rowStep : Block 9 :=
  .seq (.action (.copy 2 1)) (.seq addLoop (.action (.pop 5)))
def rowLoop : Block 9 := .loop 5 rowStep
theorem row_step_exec (r : Registers) (width : Nat) :
    Exec rowStep ({r with target := List.replicate width true, remaining := [], mode := true :: r.mode}).store
      (3 * width + 3)
      ({r with target := List.replicate width true, remaining := [], excess := List.replicate width true ++ r.excess}).store := by
  let copied := {r with target := List.replicate width true, remaining := List.replicate width true, mode := true :: r.mode}
  have a : Exec (.action (.copy (2 : Fin 9) 1))
      ({r with target := List.replicate width true, remaining := [], mode := true :: r.mode}).store 1 copied.store := .action _ _
  have b := add_exec {r with target := List.replicate width true, mode := true :: r.mode} width
  have c : Exec (.action (.pop (5 : Fin 9)))
      ({r with
        target := List.replicate width true, remaining := [], mode := true :: r.mode,
        excess := List.replicate width true ++ r.excess}).store 1
      ({r with target := List.replicate width true, remaining := [], excess := List.replicate width true ++ r.excess}).store := .action _ _
  have checked := Exec.seq a (Exec.seq b c)
  have cost : 3 * width + 3 = 1 + ((3 * width + 1) + 1) := by omega
  simpa only [rowStep, cost, copied] using checked

theorem row_loop_exec (r : Registers) (width rows : Nat) :
    Exec rowLoop ({r with target := List.replicate width true, remaining := [], mode := List.replicate rows true}).store
      ((3 * width + 4) * rows + 1)
      ({r with
        target := List.replicate width true, remaining := [], mode := [],
        excess := List.replicate (rows * width) true ++ r.excess}).store := by
  induction rows generalizing r with
  | zero =>
    simp only [Nat.zero_mul, Nat.mul_zero, List.replicate_zero, List.nil_append]
    exact Exec.loopStop rfl
  | succ rows ih =>
    have first := row_step_exec {r with mode := List.replicate rows true} width
    have rest := ih {r with excess := List.replicate width true ++ r.excess}
    have checked := Exec.loopStep (source := (5 : Fin 9)) rfl first rest
    have words : List.replicate (rows * width) true ++ (List.replicate width true ++ r.excess) =
        List.replicate ((rows + 1) * width) true ++ r.excess := by
      rw [Nat.add_mul, Nat.one_mul, ← List.append_assoc, List.replicate_append_replicate]
    have cost : (3 * width + 4) * (rows + 1) + 1 =
        1 + ((3 * width + 3) + ((3 * width + 4) * rows + 1)) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    simpa only [rowLoop, cost, words, List.replicate_succ] using checked

def seek : Block 9 :=
  .seq (.action (.copy 2 3)) (.seq (.action (.clear 3)) dropLoop)
theorem seek_exec (r : Registers) (front suffix : BitString) :
    Exec seek ({r with input := front ++ suffix, remaining := [], excess := List.replicate front.length true}).store
      (3 * front.length + 3)
      ({r with input := suffix, remaining := [], excess := []}).store := by
  have first : Exec (.action (.copy (2 : Fin 9) 3))
      ({r with input := front ++ suffix, remaining := [], excess := List.replicate front.length true}).store 1
      ({r with input := front ++ suffix, remaining := List.replicate front.length true, excess := List.replicate front.length true}).store := .action _ _
  have second : Exec (.action (.clear (3 : Fin 9)))
      ({r with input := front ++ suffix, remaining := List.replicate front.length true, excess := List.replicate front.length true}).store 1
      ({r with input := front ++ suffix, remaining := List.replicate front.length true, excess := []}).store := .action _ _
  have checked := Exec.seq first (Exec.seq second (drop_exec {r with excess := []} front suffix))
  have cost : 3 * front.length + 3 = 1 + (1 + (3 * front.length + 1)) := by omega
  simpa only [seek, cost] using checked

def read : Block 9 :=
  .seq (.branch 0 .skip (.action (.push 8 false)) (.action (.push 8 true))) (.action (.clear 0))
theorem read_exec (r : Registers) (bit : Bool) :
    Exec read ({r with input := bit :: r.input}).store 3
      ({r with input := [], output := bit :: r.output}).store := by
  cases bit
  · exact Exec.seq (Exec.zero rfl (.action _ _)) (.action _ _)
  · exact Exec.seq (Exec.one rfl (.action _ _)) (.action _ _)

def block : Block 9 := .seq rowLoop (.seq seek read)
def fuel (width row column : Nat) : Nat :=
  (3 * width + 4) * row + 3 * (row * width + column) + 7
def start (r : Registers) (bits : BitString) (width row column : Nat) : Registers :=
  {r with
    input := bits, target := List.replicate width true, remaining := [],
    mode := List.replicate row true, excess := List.replicate column true}
def result (r : Registers) (width : Nat) (bit : Bool) : Registers :=
  {r with input := [], target := List.replicate width true, remaining := [], mode := [], excess := [], output := bit :: r.output}

theorem block_exec (r : Registers) (bits : BitString) (width row column : Nat) (bit : Bool)
    (h : bits[row * width + column]? = some bit) :
    Exec block (start r bits width row column).store (fuel width row column) (result r width bit).store := by
  let offset := row * width + column
  obtain ⟨bound, value⟩ := List.getElem?_eq_some_iff.mp h
  have prefixLength : (bits.take offset).length = offset := by
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt bound)]
  have split : bits = bits.take offset ++ bit :: bits.drop (offset + 1) := by
    calc
      bits = bits.take offset ++ bits.drop offset := (List.take_append_drop offset bits).symm
      _ = bits.take offset ++ bit :: bits.drop (offset + 1) := by rw [List.drop_eq_getElem_cons bound, value]
  let afterAddress := {r with input := bits, target := List.replicate width true, remaining := [], mode := [], excess := List.replicate offset true}
  have address : Exec rowLoop (start r bits width row column).store ((3 * width + 4) * row + 1) afterAddress.store := by
    simpa only [start, afterAddress, offset, List.replicate_append_replicate, List.append_nil] using
      row_loop_exec {r with input := bits, excess := List.replicate column true} width row
  let afterSeek := {r with input := bit :: bits.drop (offset + 1), target := List.replicate width true, remaining := [], mode := [], excess := []}
  have skipped : Exec seek afterAddress.store (3 * offset + 3) afterSeek.store := by
    have checked := seek_exec {r with target := List.replicate width true, mode := []}
      (bits.take offset) (bit :: bits.drop (offset + 1))
    simpa only [prefixLength, ← split, afterAddress, afterSeek] using checked
  have final := read_exec {r with input := bits.drop (offset + 1), target := List.replicate width true, remaining := [], mode := [], excess := []} bit
  have checked := Exec.seq address (Exec.seq skipped final)
  have cost : fuel width row column = ((3 * width + 4) * row + 1) + ((3 * offset + 3) + 3) := by
    unfold fuel offset
    omega
  simpa only [block, cost, afterSeek, result] using checked

theorem matrix_bit {m n : Nat} (M : Matrix m n) (i : Fin m) (j : Fin n) :
    (coefficientMatrixBits M)[i.val * n + j.val]? = some (M i j) := by
  rw [SourceOrderedScan.matrix_bits_entries, List.getElem?_map, SourceOrderedScan.entries_get]
  rfl

theorem matrix_exec (r : Registers) {m n : Nat} (M : Matrix m n) (i : Fin m) (j : Fin n) :
    Exec block (start r (coefficientMatrixBits M) n i.val j.val).store (fuel n i.val j.val)
      (result r n (M i j)).store :=
  block_exec r _ n i.val j.val (M i j) (matrix_bit M i j)

def budget (rows width : Nat) : Nat :=
  (3 * width + 4) * rows + 3 * (rows * width + width) + 7
theorem fuel_bound {m n : Nat} (i : Fin m) (j : Fin n) : fuel n i.val j.val ≤ budget m n := by
  have rows := Nat.mul_le_mul_left (3 * n + 4) (Nat.le_of_lt i.isLt)
  have offset := Nat.add_le_add (Nat.mul_le_mul_right n (Nat.le_of_lt i.isLt)) (Nat.le_of_lt j.isLt)
  have skipped := Nat.mul_le_mul_left 3 offset
  exact Nat.add_le_add_right (Nat.add_le_add rows skipped) 7

def program : Program 9 := block.program 0 8
theorem program_run (r : Registers) {m n : Nat} (M : Matrix m n) (i : Fin m) (j : Fin n) :
    BitRegister.run program (fuel n i.val j.val + 1) ⟨.running 0, (start r (coefficientMatrixBits M) n i.val j.val).store⟩ =
      ⟨.accepted, (result r n (M i j)).store⟩ := (matrix_exec r M i j).program_run 0 8

end PNP.Concrete.ResidualReduction.SourceMatrixEntry
