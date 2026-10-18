import PNP.Concrete.ResidualReduction.MatrixStrictHeader

/-! A fail-closed counted payload copy on every input. Empty input clears the
validity flag; it never manufactures a coefficient bit. The exact cost includes
all remaining countdown iterations even after truncation has been detected. -/

namespace PNP.Concrete.ResidualReduction.MatrixCountedPayload
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.MatrixInstructions

def body : Block 9 :=
  .seq (.branch 0 (.action (.clear 5)) (.action (.push 3 false)) (.action (.push 3 true))) dropBody
def loop : Block 9 := .loop 2 body

def result (count : Nat) (input : BitString) (r : Registers) : Registers :=
  {r with input := input.drop count, remaining := [], excess := (input.take count).reverse ++ r.excess, mode := if count ≤ input.length then r.mode else []}

theorem empty_step (r : Registers) (tick : Bool) (ticks : BitString) :
    Exec body ({r with input := [], remaining := tick :: ticks}).store 4
      ({r with input := [], remaining := ticks, mode := []}).store :=
  Exec.seq (Exec.empty rfl (.action _ _)) (Exec.seq (.action _ _) (.action _ _))

theorem bit_step (r : Registers) (bit tick : Bool) (rest ticks : BitString) :
    Exec body ({r with input := bit :: rest, remaining := tick :: ticks}).store 4
      ({r with input := rest, remaining := ticks, excess := bit :: r.excess}).store := by
  cases bit
  · exact Exec.seq (Exec.zero rfl (.action _ _)) (Exec.seq (.action _ _) (.action _ _))
  · exact Exec.seq (Exec.one rfl (.action _ _)) (Exec.seq (.action _ _) (.action _ _))

theorem loop_exec (count : Nat) (input : BitString) (r : Registers) :
    Exec loop ({r with input := input, remaining := List.replicate count true}).store
      (5 * count + 1) (result count input r).store := by
  induction count generalizing input r with
  | zero =>
    have stopped : Exec loop ({r with input := input, remaining := []}).store 1
        ({r with input := input, remaining := []}).store := Exec.loopStop rfl
    simpa only [result, List.replicate_zero, Nat.mul_zero, Nat.zero_add,
      List.drop_zero, List.take_zero, List.reverse_nil, List.nil_append,
      if_pos (Nat.zero_le input.length)] using stopped
  | succ count ih =>
    have cost : 5 * (count + 1) + 1 = 1 + (4 + (5 * count + 1)) := by omega
    rw [cost]
    cases input with
    | nil =>
      have step := empty_step r true (List.replicate count true)
      have checked := Exec.loopStep (source := (2 : Fin 9)) rfl step (ih [] {r with mode := []})
      have insufficient : ¬ count + 1 ≤ ([] : BitString).length := by
        simp only [List.length_nil]
        omega
      simpa only [loop, result, List.replicate_succ, List.drop_nil, List.take_nil, List.reverse_nil,
        List.nil_append, ite_self, if_neg insufficient] using checked
    | cons bit rest =>
      have step := bit_step r bit true rest (List.replicate count true)
      have checked := Exec.loopStep (source := (2 : Fin 9)) rfl step
        (ih rest {r with excess := bit :: r.excess})
      have enough : count + 1 ≤ (bit :: rest).length ↔ count ≤ rest.length := by
        simp only [List.length_cons]
        constructor
        · exact Nat.le_of_succ_le_succ
        · exact Nat.succ_le_succ
      simpa only [loop, result, List.replicate_succ, List.drop_succ_cons, List.take_succ_cons,
        List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append,
        enough] using checked

theorem complete_exec (input : BitString) (r : Registers) :
    Exec loop ({r with input := input, remaining := List.replicate input.length true}).store
      (5 * input.length + 1)
      ({r with input := [], remaining := [], excess := input.reverse ++ r.excess}).store := by
  simpa only [result, List.drop_length, List.take_length, if_pos (Nat.le_refl input.length)] using
    loop_exec input.length input r

theorem success_iff (count : Nat) (input : BitString) (r : Registers) :
    (result count input {r with mode := [true]}).mode = [true] ↔ count ≤ input.length := by
  by_cases enough : count ≤ input.length
  · simp only [result, enough, if_true]
  · change (if count ≤ input.length then [true] else []) = [true] ↔ count ≤ input.length
    rw [if_neg enough]
    constructor
    · intro impossible; cases impossible
    · intro impossible; exact (enough impossible).elim

theorem exact_payload_iff (count : Nat) (input : BitString) (r : Registers) :
    (result count input {r with mode := [true]}).mode = [true] ∧
      (result count input r).input = [] ↔ input.length = count := by
  rw [success_iff]
  change count ≤ input.length ∧ input.drop count = [] ↔ input.length = count
  rw [List.drop_eq_nil_iff]
  omega

theorem copied_length_bound (count : Nat) (input : BitString) :
    (input.take count).length ≤ input.length := by
  rw [List.length_take]
  exact Nat.min_le_right _ _

end PNP.Concrete.ResidualReduction.MatrixCountedPayload
