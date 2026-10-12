import PNP.Concrete.BitRegisterIOPrimitives

namespace PNP.Concrete.BitRegister

open IOAdapter Operation TapePrimitive Mutation

example : ProgramWellFormed PipelineInputFramer.pairedInputFramer := inputFramer_wellFormed
example : ProgramWellFormed TerminalOutputPacker.terminalOutputPacker := outputPacker_wellFormed
example (count : Nat) : ProgramWellFormed (prependFields count) := prependFields_wellFormed count
example (count : Nat) : ProgramWellFormed (appendFields count) := appendFields_wellFormed count

example (right : List WorkSymbol) :
    workRunExact? (prependFields 2) 5
      ⟨(prependFields 2).startState, ⟨[], WorkSymbol.blankZero, right⟩⟩ =
      some ⟨(prependFields 2).acceptState,
        ⟨[], WorkSymbol.blankZero, [Store.separator, Store.separator] ++ right⟩⟩ :=
  prependFields_run 2 [] WorkSymbol.blankZero right

example (head a b c : WorkSymbol) (right : List WorkSymbol) :
    workRunExact? (prependFields 2) 5
      ⟨(prependFields 2).startState, ⟨[a, b, c], head, right⟩⟩ =
      some ⟨(prependFields 2).acceptState,
        ⟨[c], WorkSymbol.blankZero, [Store.separator, Store.separator] ++ right⟩⟩ :=
  prependFields_run 2 [a, b, c] head right

example (left : List WorkSymbol) (head : WorkSymbol) :
    workRunExact? (appendFields 0) 1
      ⟨(appendFields 0).startState, ⟨left, head, []⟩⟩ =
      some ⟨(appendFields 0).acceptState, focusLeft left [rightBoundary]⟩ :=
  appendFields_run 0 left head

example (outside : List WorkSymbol) :
    workRunExact? scanInput 1 ⟨0, ⟨WorkSymbol.blankZero :: outside, WorkSymbol.blank, [Store.separator]⟩⟩ =
      some ⟨1, ⟨Store.separator :: WorkSymbol.blankZero :: outside, Store.separator, []⟩⟩ := rfl

example (left right : List WorkSymbol) :
    workRunExact? scanInput 4
      ⟨0, focus left ([true, false, true].map Store.bitSymbol ++ Store.separator :: right)⟩ =
      some ⟨1, focus (Store.separator :: reverseOnto ([true, false, true].map Store.bitSymbol) left) right⟩ :=
  scanInput_word_run [true, false, true] left right

#print axioms IOAdapter.inputFramer_wellFormed
#print axioms IOAdapter.outputPacker_wellFormed
#print axioms IOAdapter.writeAny_wellFormed
#print axioms IOAdapter.writeAny_run
#print axioms IOAdapter.writeAny_left_run
#print axioms IOAdapter.prependFields_wellFormed
#print axioms IOAdapter.prependFields_run
#print axioms IOAdapter.appendFields_wellFormed
#print axioms IOAdapter.appendFields_run
#print axioms IOAdapter.scanInput_wellFormed
#print axioms IOAdapter.scanInput_bit_step
#print axioms IOAdapter.scanInput_separator_step
#print axioms IOAdapter.scanInput_word_run

end PNP.Concrete.BitRegister
