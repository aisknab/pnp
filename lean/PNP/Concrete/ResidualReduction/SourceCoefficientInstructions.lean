import PNP.Concrete.ResidualReduction.SourceMatrixEncoding

/-! Literal counted reads and the fixed four-bit polar operation. The read
loop has a uniform cost even at end of input. Bounds here count source
instructions; the finite-machine compiler accounts for word-copy cost. -/

namespace PNP.Concrete.ResidualReduction.SourceCoefficientInstructions
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding

theorem drop_all (r : Registers) (bits : BitString) (k : Nat) :
    Exec dropLoop ({r with input := bits, remaining := List.replicate k true}).store
      (3 * k + 1) ({r with input := bits.drop k, remaining := []}).store := by
  induction k generalizing bits with
  | zero => exact Exec.loopStop rfl
  | succ k ih =>
    have cost : 3 * (k + 1) + 1 = 1 + (2 + (3 * k + 1)) := by omega
    cases bits with
    | nil =>
      have step : Exec dropBody
          ({r with input := [], remaining := List.replicate (k + 1) true}).store 2
          ({r with input := [], remaining := List.replicate k true}).store :=
        Exec.seq (.action _ _) (.action _ _)
      simpa only [dropLoop, cost, List.drop_nil] using
        Exec.loopStep (source := (2 : Fin 9)) rfl step (ih [])
    | cons b rest =>
      have step : Exec dropBody
          ({r with input := b :: rest, remaining := List.replicate (k + 1) true}).store 2
          ({r with input := rest, remaining := List.replicate k true}).store :=
        Exec.seq (.action _ _) (.action _ _)
      simpa only [dropLoop, cost, List.drop_succ_cons] using
        Exec.loopStep (source := (2 : Fin 9)) rfl step (ih rest)

def readHead : Block 9 := .branch 0 (.action (.push 3 false))
  (.action (.push 3 false)) (.action (.push 3 true))

theorem readHead_exec (r : Registers) :
    Exec readHead r.store 2 ({r with excess := r.input.headD false :: r.excess}).store := by
  cases r with
  | mk input target remaining excess sign mode active reserved output =>
    cases input with
    | nil => exact Exec.empty rfl (.action _ _)
    | cons bit rest => cases bit with
      | false => exact Exec.zero rfl (.action _ _)
      | true => exact Exec.one rfl (.action _ _)

def read : Block 9 := .seq dropLoop readHead

theorem read_exec (r : Registers) (k : Nat) :
    Exec read ({r with remaining := List.replicate k true}).store (3 * k + 3)
      ({r with input := r.input.drop k, remaining := [], excess := bitAt r.input k :: r.excess}).store := by
  have checked := Exec.seq (drop_all r r.input k)
    (readHead_exec {r with input := r.input.drop k, remaining := []})
  have cost : 3 * k + 3 = (3 * k + 1) + 2 := by omega
  simpa only [read, cost, bitAt_drop] using checked

theorem bitAt_append (front suffix : BitString) (k : Nat) (inside : k < front.length) :
    bitAt (front ++ suffix) k = bitAt front k := by
  induction front generalizing k with
  | nil => exact False.elim (Nat.not_lt_zero k inside)
  | cons b rest ih =>
    cases k with
    | zero => rfl
    | succ k => exact ih k (Nat.lt_of_succ_lt_succ inside)

/-- Both Boolean alternatives become literal branches. No function remains
in the resulting instruction set. The empty arm is unreachable for four
successfully read bits and does not manufacture an extra operand. -/
def readBit (next : Bool → Block 9) : Block 9 :=
  .branch 3 .skip (.seq (.action (.pop 3)) (next false))
    (.seq (.action (.pop 3)) (next true))

theorem readBit_exec (r : Registers) (b : Bool) (next : Bool → Block 9)
    (fuel : Nat) (after : Registers)
    (checked : Exec (next b) r.store fuel after.store) :
    Exec (readBit next) ({r with excess := b :: r.excess}).store (2 + fuel) after.store := by
  have popped : Exec (.action (.pop (3 : Fin 9)))
      ({r with excess := b :: r.excess}).store 1 r.store := .action _ _
  rw [show 2 + fuel = 1 + (1 + fuel) by omega]
  cases b with
  | false => exact Exec.zero (source := (3 : Fin 9)) rfl (Exec.seq popped checked)
  | true => exact Exec.one (source := (3 : Fin 9)) rfl (Exec.seq popped checked)

def emitPolar : Block 9 :=
  readBit fun d => readBit fun c => readBit fun b => readBit fun a =>
    .action (.push 8 (Bool.xor (a && b) (c && d)))

theorem emitPolar_exec (r : Registers) (a b c d : Bool) :
    Exec emitPolar ({r with excess := d :: c :: b :: a :: r.excess}).store 9
      ({r with output := Bool.xor (a && b) (c && d) :: r.output}).store := by
  unfold emitPolar
  refine readBit_exec {r with excess := c :: b :: a :: r.excess} d _ 7 _ ?_
  refine readBit_exec {r with excess := b :: a :: r.excess} c _ 5 _ ?_
  refine readBit_exec {r with excess := a :: r.excess} b _ 3 _ ?_
  refine readBit_exec r a _ 1 _ ?_
  exact .action _ _

end PNP.Concrete.ResidualReduction.SourceCoefficientInstructions
