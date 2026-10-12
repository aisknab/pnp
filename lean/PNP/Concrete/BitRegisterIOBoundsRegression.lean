import PNP.Concrete.BitRegisterIOBounds

namespace PNP.Concrete.BitRegister

open IOAdapter

private def first : Program 3 := ⟨[.accept], 0, 0, 2⟩
private def last : Program 3 := ⟨[.accept], 0, 2, 0⟩
private def sample : Store 3 := .cons [] (.cons [true, false, true] (.cons [false, true] .nil))

example : (inputRawBound 3).eval 0 = 183 := rfl
example : (inputRawBound 3).eval 1 = 240 := rfl
example : outputRawBound.eval 0 = 54 := rfl
example : outputRawBound.eval 1 = 120 := rfl
example : outputRawBound.eval 8 = 1590 := rfl

example (input : BitString) :
    boundedDecide (compileWorkMachine (inputAdapter first))
      ((inputRawBound 3).eval input.length) input = .accept :=
  inputAdapter_accepts first input

example :
    boundedDecide (compileWorkMachine (inputAdapter last))
      ((inputRawBound 3).eval 0) [] = .accept :=
  inputAdapter_accepts last []

example :
    boundedDecide (compileWorkMachine (inputAdapter last))
      ((inputRawBound 3).eval 3) [true, false, true] = .accept :=
  inputAdapter_accepts last [true, false, true]

example (outside : List WorkSymbol) (slack : Nat) :
    (PNP.Concrete.run (compileWorkMachine (outputAt 0))
      (outputRawBound.eval sample.span)
      (encodeWorkConfiguration ⟨(outputAt 0).startState, sample.tape outside slack⟩)).tape.outputBits = [] :=
  outputAt_output_budget sample 0 outside slack

example (outside : List WorkSymbol) (slack : Nat) :
    (PNP.Concrete.run (compileWorkMachine (outputAt 1))
      (outputRawBound.eval sample.span)
      (encodeWorkConfiguration ⟨(outputAt 1).startState, sample.tape outside slack⟩)).tape.outputBits =
      [true, false, true] :=
  outputAt_output_budget sample 1 outside slack

example {count : Nat} (store : Store count) (index : Fin count) :
    6 * outputAtSteps store index ≤ 18 * store.span * store.span + 48 * store.span + 54 := by
  rw [← outputRawBound_eval]
  exact outputAt_rawSteps_le store index

#print axioms IOAdapter.inputAdapter_rawSteps_le
#print axioms IOAdapter.accept_isHalted
#print axioms IOAdapter.inputAdapter_run_budget
#print axioms IOAdapter.inputAdapter_start_run
#print axioms IOAdapter.inputAdapter_accepts
#print axioms IOAdapter.outputRawBound_eval
#print axioms IOAdapter.get_length_le_span
#print axioms IOAdapter.seekSteps_le_span
#print axioms IOAdapter.outputAt_rawSteps_le
#print axioms IOAdapter.outputAt_run_budget
#print axioms IOAdapter.outputAt_output_budget

end PNP.Concrete.BitRegister
