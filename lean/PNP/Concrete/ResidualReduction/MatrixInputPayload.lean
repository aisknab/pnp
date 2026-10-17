import PNP.Concrete.ResidualReduction.MatrixInputHeaders
import PNP.Concrete.ResidualReduction.MatrixPayloadCounter

/-! The complete counted matrix-payload reader, including rejected inputs.
Both header counts are retained as unary words bounded by the original input.
The product counter and every copy iteration have explicit source costs. -/

namespace PNP.Concrete.ResidualReduction.MatrixInputPayload
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixReconstruction
open PNP.Concrete.ResidualReduction.MatrixInputFields

def start (n count : Nat) (input : BitString) : State :=
  ⟨{base (n + 1) [] with input := input, mode := [true]},
    List.replicate n true, [], List.replicate count true⟩

def seed : Block 12 :=
  .seq (.action (.copy 11 1)) <| .seq (.action (.copy 1 9)) <|
    .seq (.action (.push 1 true)) <| .seq (.action (.copy 5 4)) (.action (.clear 4))

theorem seed_exec (input : BitString) (success : (fields input).terminated = true) :
    Exec seed (MatrixInputHeaders.result input).store 5
      (start (fields input).dimension (fields input).rows (fields input).payload).store := by
  simp only [MatrixInputHeaders.result, success, if_true]
  exact Exec.seq (.action _ _) (Exec.seq (.action _ _)
    (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))))

def counted (n count : Nat) (input : BitString) : State :=
  ⟨{base (n + 1) [] with input := input, mode := [true], remaining := List.replicate ((n + 1) * count) true},
    List.replicate n true, [], []⟩

def result (n count : Nat) (input : BitString) : State :=
  ⟨{base (n + 1) [] with input := input.drop ((n + 1) * count), excess := (input.take ((n + 1) * count)).reverse, mode := if (n + 1) * count ≤ input.length then [true] else []},
    List.replicate n true, [], []⟩

def block : Block 12 :=
  .seq MatrixPayloadCounter.loop (lift MatrixCountedPayload.loop)

def fuel (n count : Nat) : Nat :=
  ((3 * (n + 1) + 4) * count + 1) + (5 * ((n + 1) * count) + 1)

theorem counter_exec (n count : Nat) (input : BitString) :
    Exec MatrixPayloadCounter.loop (start n count input).store
      ((3 * (n + 1) + 4) * count + 1) (counted n count input).store := by
  simpa only [start, counted, MatrixPayloadCounter.counted, base, Nat.add_zero,
    List.replicate_zero] using
    MatrixPayloadCounter.loop_exec (n + 1) count 0 (start n count input)

theorem copy_exec (n count : Nat) (input : BitString) :
    Exec (lift MatrixCountedPayload.loop) (counted n count input).store
      (5 * ((n + 1) * count) + 1) (result n count input).store := by
  have core : Exec MatrixCountedPayload.loop (counted n count input).core.store
      (5 * ((n + 1) * count) + 1) (result n count input).core.store := by
    simpa only [counted, result, start, MatrixCountedPayload.result, base,
      List.append_nil] using
      MatrixCountedPayload.loop_exec ((n + 1) * count) input (start n count input).core
  exact lift_exec _ (counted n count input) _ (result n count input).core core

theorem block_exec (n count : Nat) (input : BitString) :
    Exec block (start n count input).store (fuel n count) (result n count input).store :=
  Exec.seq (counter_exec n count input) (copy_exec n count input)

theorem fuel_input_bound (n count inputLength : Nat)
    (dimension : n ≤ inputLength) (rows : count ≤ inputLength) :
    fuel n count ≤ fuel inputLength inputLength := by
  have counter := MatrixPayloadCounter.counterFuel_input_bound n count inputLength dimension rows
  have size := MatrixPayloadCounter.counter_input_bound n count inputLength dimension rows
  unfold fuel
  omega

theorem valid_iff (n count : Nat) (input : BitString) :
    (result n count input).core.mode = [true] ∧ (result n count input).core.input = [] ↔
      input.length = (n + 1) * count := by
  exact MatrixCountedPayload.exact_payload_iff ((n + 1) * count) input (base (n + 1) [])

theorem result_complete (n count : Nat) (input : BitString)
    (length : input.length = (n + 1) * count) :
    result n count input =
      ⟨{base (n + 1) [] with excess := input.reverse, mode := [true]},
        List.replicate n true, [], []⟩ := by
  simp only [result, ← length, List.drop_length, List.take_length,
    if_pos (Nat.le_refl input.length)]
  rfl

end PNP.Concrete.ResidualReduction.MatrixInputPayload
