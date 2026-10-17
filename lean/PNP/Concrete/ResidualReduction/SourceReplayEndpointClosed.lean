import PNP.Concrete.ResidualReduction.SourceReplayEndpointOutput

/-! Complete raw-request to canonical optional-witness block. The observed
answer is now serialized into output register8. The theorems below establish
literal instruction execution, exact bytes and encoded-size bounds; physical
finite-machine refinement/runtime and source-generated linkage remain separate. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayEndpointClosed
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.SourceReplayEndpointExecute (parameters data good)

def replayed (input : BitString) : SourceReplayLoopFields.Result :=
  SourceReplayEndpointRun.iteration (parameters input) (SourceReplayEndpointFields.count (data input))
    (SourceReplayEndpointFields.stream (parameters input).recover (data input))
    (parameters input).witness (SourceReplayEndpointRun.firstGood (parameters input) (parameters input).witness (good input))
def accepted (input : BitString) : Bool := SourceReplayEndpointRun.finalGood (parameters input) (replayed input)
def result (input : BitString) : Store 40 :=
  SourceReplayEndpointOutput.result (replayed input).input (replayed input).point (parameters input)
    (replayed input).valid (accepted input)
def block : Block 40 := .seq SourceReplayEndpointExecute.block SourceReplayEndpointOutput.block
def fuel (input : BitString) : Nat :=
  SourceReplayEndpointExecute.fuel input + SourceReplayEndpointOutput.fuel (parameters input) (accepted input)
def program : Program 40 := block.program 0 8

theorem program_ports : program.input = 0 ∧ program.output = 8 ∧ program.entry = 0 := ⟨rfl,rfl,rfl⟩

theorem block_exec (input : BitString) :
    Exec block (SourceReplayEndpointState.initial input) (fuel input) (result input) :=
  Exec.seq (SourceReplayEndpointExecute.block_exec input)
    (SourceReplayEndpointOutput.block_exec (replayed input).input (replayed input).point (parameters input)
      (replayed input).valid (accepted input))

theorem accepted_width (input : BitString) (checked : accepted input = true) :
    (replayed input).point.length = SourceReplayEndpointOutput.width (parameters input) := by
  change ((replayed input).valid &&
    SourceReplayEndpointCheck.valid true (parameters input) (replayed input).point) = true at checked
  simp only [Bool.and_eq_true] at checked
  exact (SourceReplayWitness.valid_iff_width
    (SourceReplayEndpointCheck.width true (parameters input)) (replayed input).point).mp checked.2

theorem answer_view (input : BitString) :
    (if accepted input then some (replayed input).point else none) = SourceReplayRequest.answer input := by
  have checked := SourceReplayEndpointExecute.answer_eq input
  rw [SourceReplayEndpointExecute.result,SourceReplayEndpointRun.observed_result] at checked
  exact checked

theorem output_eq (input : BitString) :
    (result input).get 8 = SourceReplayEndpointOutput.codec.encode (SourceReplayRequest.answer input) := by
  calc
    (result input).get 8 =
        SourceReplayEndpointOutput.bytes (parameters input) (replayed input).point (accepted input) :=
      SourceReplayEndpointOutput.result_output _ _ _ _ _
    _ = SourceReplayEndpointOutput.codec.encode (if accepted input then some (replayed input).point else none) :=
      SourceReplayEndpointOutput.bytes_codec _ _ _ (accepted_width input)
    _ = SourceReplayEndpointOutput.codec.encode (SourceReplayRequest.answer input) :=
      congrArg SourceReplayEndpointOutput.codec.encode (answer_view input)

theorem decode_output (input : BitString) :
    SourceReplayEndpointOutput.codec.decode ((result input).get 8) = some (SourceReplayRequest.answer input) := by
  rw [output_eq]
  exact decode_encode _ _

theorem output_size_bound (input : BitString) : ((result input).get 8).length ≤ 2 * input.length + 2 := by
  rw [result,SourceReplayEndpointOutput.result_output]
  obtain ⟨_,_,original,terminal,_⟩ := SourceReplayEndpointExecute.input_bounds input
  have width := SourceReplayEndpointOutput.width_bound (parameters input) input.length original terminal
  cases flag : accepted input with
  | false =>
    simp only [SourceReplayEndpointOutput.bytes,Bool.false_eq_true,↓reduceIte,List.length_cons,List.length_nil]
    omega
  | true =>
    have size := accepted_width input flag
    simp only [SourceReplayEndpointOutput.bytes,↓reduceIte,List.length_cons,List.length_append,List.length_replicate]
    omega

theorem fuel_bound (input : BitString) :
    fuel input ≤ input.length * (SourceReplayHistoryStack.allowance input.length +
      SourceReplayLoopMachine.allowance input.length (2 * input.length)) +
      (16 * input.length + 36) * input.length + 80 * input.length + 380 := by
  have execution := SourceReplayEndpointExecute.fuel_bound input
  obtain ⟨_,_,original,terminal,_⟩ := SourceReplayEndpointExecute.input_bounds input
  have output := SourceReplayEndpointOutput.fuel_bound (parameters input) (accepted input) input.length original terminal
  unfold fuel
  omega

theorem all_input (input : BitString) :
    ∃ after, Exec block (SourceReplayEndpointState.initial input) (fuel input) after ∧
      after.get 8 = SourceReplayEndpointOutput.codec.encode (SourceReplayRequest.answer input) ∧
      fuel input ≤ input.length * (SourceReplayHistoryStack.allowance input.length +
        SourceReplayLoopMachine.allowance input.length (2 * input.length)) +
        (16 * input.length + 36) * input.length + 80 * input.length + 380 ∧
      (after.get 8).length ≤ 2 * input.length + 2 :=
  ⟨result input,block_exec input,output_eq input,fuel_bound input,output_size_bound input⟩

end PNP.Concrete.ResidualReduction.SourceReplayEndpointClosed
