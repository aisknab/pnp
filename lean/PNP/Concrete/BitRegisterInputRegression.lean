import PNP.Concrete.BitRegisterInput

namespace PNP.Concrete.BitRegister

open IOAdapter

private def firstInput : Program 3 := ⟨[.accept], 0, 0, 2⟩
private def lastInput : Program 3 := ⟨[.accept], 0, 2, 0⟩

example : loadProgramSteps firstInput 0 = 16 := rfl
example : loadProgramSteps lastInput 0 = 14 := rfl
example : loadProgramSteps firstInput 3 = 22 := rfl
example : loadProgramSteps lastInput 3 = 20 := rfl
example : (Compiler.scratchStore (initial firstInput [true, false]).store).encode =
    [Store.separator, Store.bitSymbol true, Store.bitSymbol false,
      Store.separator, Store.separator, Store.separator] := rfl
example : (Compiler.scratchStore (initial lastInput [true, false]).store).encode =
    [Store.separator, Store.separator, Store.separator,
      Store.bitSymbol true, Store.bitSymbol false, Store.separator] := rfl

example (input : BitString) (outside : List WorkSymbol) :
    workRunExact? (loadProgram lastInput) (loadProgramSteps lastInput input.length)
      ⟨(loadProgram lastInput).startState, PipelineTape.frameWithGarbage (Tape.ofInput input) outside []⟩ =
      some ⟨(loadProgram lastInput).acceptState,
        (Compiler.scratchStore (initial lastInput input).store).tape (outside.drop 3) 0⟩ :=
  loadProgram_run lastInput input outside

example {count : Nat} (program : Program count) (input : BitString) :
    workRunExact? (inputAdapter program) (inputAdapterSteps program input)
      ⟨(inputAdapter program).startState, rawInputWorkTape input⟩ =
      some ⟨(inputAdapter program).acceptState,
        (Compiler.scratchStore (initial program input).store).tape (inputOutside program input) 0⟩ :=
  inputAdapter_run program input

example (outside : List WorkSymbol) :
    scanFinalTape [] outside =
      ⟨Store.separator :: WorkSymbol.blankZero :: outside, Store.separator, []⟩ := rfl
example (outside : List WorkSymbol) :
    scanFinalTape [true] outside =
      ⟨Store.separator :: Store.bitSymbol true :: WorkSymbol.blankZero :: outside, WorkSymbol.blank, []⟩ := rfl

#print axioms IOAdapter.replicate_cons
#print axioms IOAdapter.reverseOnto_replicate
#print axioms IOAdapter.scanInput_framed_run
#print axioms IOAdapter.appendFields_framed_run
#print axioms IOAdapter.home_suffix_run
#print axioms IOAdapter.loadFields_wellFormed
#print axioms IOAdapter.loadFields_run
#print axioms IOAdapter.empty_encode
#print axioms IOAdapter.initial_encode
#print axioms IOAdapter.loadedTape_initial
#print axioms IOAdapter.loadProgram_wellFormed
#print axioms IOAdapter.loadProgram_run
#print axioms IOAdapter.loadProgramSteps_le
#print axioms IOAdapter.inputAdapter_wellFormed
#print axioms IOAdapter.inputAdapter_run
#print axioms IOAdapter.inputAdapter_raw_run

end PNP.Concrete.BitRegister
