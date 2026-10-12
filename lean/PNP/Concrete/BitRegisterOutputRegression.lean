import PNP.Concrete.BitRegisterOutput

namespace PNP.Concrete.BitRegister

open IOAdapter TapePrimitive

private def sample : Store 3 := .cons [] (.cons [true, false, true] (.cons [false, true] .nil))

example : frameWordSteps [] = 4 := rfl
example : frameWordSteps [false] = 2 := rfl
example : frameWordSteps [true, false] = 2 := rfl
example : frameRight [] [WorkSymbol.oneOne, WorkSymbol.zeroZero] = [WorkSymbol.zeroZero] := rfl
example : frameRight [true] [WorkSymbol.oneOne, WorkSymbol.zeroZero] =
    [WorkSymbol.oneOne, WorkSymbol.zeroZero] := rfl
example : workStep? frameWord ⟨0, ⟨[], WorkSymbol.blank, []⟩⟩ = none := rfl

example (left right : List WorkSymbol) :
    workRunExact? frameWord 4 ⟨0, focus left (Store.separator :: right)⟩ =
      some ⟨5, TerminalOutputPacker.terminalOutputPackerInputTape [] left.tail right.tail⟩ :=
  frameWord_nil_run left right

example (left right : List WorkSymbol) :
    workRunExact? frameWord 2 ⟨0, focus left ([true, false].map Store.bitSymbol ++ Store.separator :: right)⟩ =
      some ⟨5, TerminalOutputPacker.terminalOutputPackerInputTape [true, false] left.tail right⟩ :=
  frameWord_cons_run true [false] left right

example (outside : List WorkSymbol) (slack : Nat) :
    (encodeWorkTape (outputTape sample 0 outside slack)).outputBits = [] :=
  outputTape_output sample 0 outside slack

example (outside : List WorkSymbol) (slack : Nat) :
    (encodeWorkTape (outputTape sample 1 outside slack)).outputBits = [true, false, true] :=
  outputTape_output sample 1 outside slack

example (outside : List WorkSymbol) (slack : Nat) :
    (encodeWorkTape (outputTape sample 2 outside slack)).outputBits = [false, true] :=
  outputTape_output sample 2 outside slack

example {count : Nat} (store : Store count) (index : Fin count)
    (outside : List WorkSymbol) (slack : Nat) :
    workRunExact? (outputAt index.val) (outputAtSteps store index)
      ⟨(outputAt index.val).startState, store.tape outside slack⟩ =
      some ⟨(outputAt index.val).acceptState, outputTape store index outside slack⟩ :=
  outputAt_run store index outside slack

#print axioms IOAdapter.packerInput_nil
#print axioms IOAdapter.packerInput_cons
#print axioms IOAdapter.frameWord_wellFormed
#print axioms IOAdapter.frameWord_bit_step
#print axioms IOAdapter.frameWord_empty_step
#print axioms IOAdapter.frameWord_accept_left_step
#print axioms IOAdapter.frameWord_continue_left_step
#print axioms IOAdapter.frameWord_blank_step
#print axioms IOAdapter.frameWord_right_step
#print axioms IOAdapter.frameWord_cons_run
#print axioms IOAdapter.frameWord_empty_prepare_run
#print axioms IOAdapter.frameWord_empty_finish_run
#print axioms IOAdapter.frameWord_nil_run
#print axioms IOAdapter.frameWord_run
#print axioms IOAdapter.frameWordSteps_le
#print axioms IOAdapter.outputAt_wellFormed
#print axioms IOAdapter.outputAt_run
#print axioms IOAdapter.outputAt_raw_run
#print axioms IOAdapter.outputTape_output

end PNP.Concrete.BitRegister
