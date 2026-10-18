import PNP.Concrete.ResidualReduction.MatrixInputPayload

/-! A successful exact-length payload is reversed into the solver's initial
register layout. The copy, reversal, and register resets are actual instructions,
and the execution theorem connects precisely to the complete prepared solver. -/

namespace PNP.Concrete.ResidualReduction.MatrixInputPreparation
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixReconstruction

def start (n : Nat) (input : BitString) : State :=
  ⟨{base (n + 1) [] with excess := input.reverse, mode := [true]},
    List.replicate n true, [], []⟩

def reversed (n : Nat) (input : BitString) : State :=
  ⟨{base (n + 1) [] with output := input, mode := [true]},
    List.replicate n true, [], []⟩

def result (n : Nat) (input : BitString) : State :=
  ⟨{base n input with input := input}, List.replicate n true, [], []⟩

def reset : Block 12 :=
  .seq (.action (.copy 0 8)) <| .seq (.action (.copy 7 8)) <|
    .seq (.action (.clear 8)) <| .seq (.action (.clear 5)) (.action (.pop 1))
def block : Block 12 := .seq (lift ClauseQuery.reverseLoop) reset

theorem reverse_exec (n : Nat) (input : BitString) :
    Exec (lift ClauseQuery.reverseLoop) (start n input).store (4 * input.length + 1)
      (reversed n input).store := by
  have core : Exec ClauseQuery.reverseLoop (start n input).core.store
      (4 * input.length + 1) (reversed n input).core.store := by
    simpa only [start, reversed, base, List.length_reverse, List.reverse_reverse,
      List.append_nil] using
      ClauseQuery.reverse_exec {base (n + 1) [] with mode := [true]} input.reverse
  exact lift_exec _ (start n input) _ (reversed n input).core core

theorem reset_exec (n : Nat) (input : BitString) :
    Exec reset (reversed n input).store 5 (result n input).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _)
    (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))))

theorem block_exec (n : Nat) (input : BitString) :
    Exec block (start n input).store (4 * input.length + 6) (result n input).store := by
  have cost : 4 * input.length + 6 = (4 * input.length + 1) + 5 := by omega
  rw [cost]
  exact Exec.seq (reverse_exec n input) (reset_exec n input)

theorem matrix_exec (n : Nat) (rows : System n) :
    Exec block (MatrixInputPayload.result n rows.length (matrixBits rows)).store
      (4 * (matrixBits rows).length + 6) (MatrixSolutionInstructions.start n rows).store := by
  have complete := MatrixInputPayload.result_complete n rows.length (matrixBits rows)
    (matrixBits_length rows)
  rw [complete]
  exact block_exec n (matrixBits rows)

end PNP.Concrete.ResidualReduction.MatrixInputPreparation
