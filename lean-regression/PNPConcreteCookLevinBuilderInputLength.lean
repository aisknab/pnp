import PNP

namespace PNP.Concrete.CookLevinBuilderInputLengthRegression

open PipelineTape
open CookLevin.BuilderInputLength

def arbitraryOutsideLeft : List WorkSymbol :=
  [WorkSymbol.zeroOne, WorkSymbol.blank, WorkSymbol.oneOne]

example : rules.length = 19 := rules_length

example : workSteps 0 = 2 := rfl
example : workSteps 1 = 8 := rfl
example : workSteps 3 = 32 := rfl
example : workSteps 4 = 50 := rfl

example : rawTimeBound.eval 0 = 12 := rfl
example : rawTimeBound.eval 1 = 48 := rfl
example : rawTimeBound.eval 3 = 192 := rfl
example : rawTimeBound.eval 4 = 300 := rfl

example : tallySizeBound.eval 0 = 0 := rfl
example : tallySizeBound.eval 4 = 4 := rfl

example : finalTape ([] : BitString) arbitraryOutsideLeft =
    frameWithGarbage (Tape.ofInput []) arbitraryOutsideLeft [] := rfl

example : finalTape ([false] : BitString) arbitraryOutsideLeft =
    frameWithGarbage (Tape.ofInput [false]) arbitraryOutsideLeft
      [tallySymbol] := rfl

example : finalTape ([true] : BitString) arbitraryOutsideLeft =
    frameWithGarbage (Tape.ofInput [true]) arbitraryOutsideLeft
      [tallySymbol] := rfl

example : finalTape ([true, false, true] : BitString) arbitraryOutsideLeft =
    frameWithGarbage (Tape.ofInput [true, false, true]) arbitraryOutsideLeft
      [tallySymbol, tallySymbol, tallySymbol] := rfl

example : finalTape ([true, true, false, false] : BitString)
    arbitraryOutsideLeft =
    frameWithGarbage (Tape.ofInput [true, true, false, false])
      arbitraryOutsideLeft
      [tallySymbol, tallySymbol, tallySymbol, tallySymbol] := rfl

example : finalTape ([false, false, false, false] : BitString)
    arbitraryOutsideLeft =
    frameWithGarbage (Tape.ofInput [false, false, false, false])
      arbitraryOutsideLeft
      [tallySymbol, tallySymbol, tallySymbol, tallySymbol] := rfl

example : finalTape ([true, true, true, true] : BitString)
    arbitraryOutsideLeft =
    frameWithGarbage (Tape.ofInput [true, true, true, true])
      arbitraryOutsideLeft
      [tallySymbol, tallySymbol, tallySymbol, tallySymbol] := rfl

example : finalTape ([false, true, false, true] : BitString)
    arbitraryOutsideLeft =
    frameWithGarbage (Tape.ofInput [false, true, false, true])
      arbitraryOutsideLeft
      [tallySymbol, tallySymbol, tallySymbol, tallySymbol] := rfl

example (input : BitString) :
    (List.replicate input.length tallySymbol).length = input.length :=
  finalTape_tally_length input arbitraryOutsideLeft

example (input : BitString) :
    Represents (Tape.ofInput input) (finalTape input arbitraryOutsideLeft) :=
  finalTape_represents input arbitraryOutsideLeft

example (input : BitString) :
    workRunExact? machine (workSteps input.length)
        (workStartConfiguration machine (inputTape input arbitraryOutsideLeft)) =
      some (finalConfiguration input arbitraryOutsideLeft) :=
  workRunExact input arbitraryOutsideLeft

example (input : BitString) :
    run (compileWorkMachine machine)
        (rawTimeBound.eval (BitString.size input))
        (encodeWorkConfiguration
          (workStartConfiguration machine
            (inputTape input arbitraryOutsideLeft))) =
      encodeWorkConfiguration (finalConfiguration input arbitraryOutsideLeft) :=
  run_compile input arbitraryOutsideLeft

example (input : BitString) :
    workBoundedDecide machine (workSteps input.length)
        (inputTape input arbitraryOutsideLeft) = .accept :=
  workBoundedDecide_accept input arbitraryOutsideLeft

example (input : BitString) :
    workBoundedDecide machine (workSteps input.length - 1)
        (inputTape input arbitraryOutsideLeft) = .timeout :=
  work_one_step_short_timeout input arbitraryOutsideLeft

example (fuel : Nat) :
    workBoundedDecide machine fuel
        { left := arbitraryOutsideLeft
          head := WorkSymbol.zeroOne
          right := [WorkSymbol.zeroBlank, rightMarker] } = .timeout :=
  malformedScanSymbol_timeout fuel _ _

example (input : BitString) :
    inputTape input (PipelineInputFramer.totalInputFramerOutsideLeft input) =
      PipelineInputFramer.totalInputFramerFinalTape input :=
  inputTape_eq_totalInputFramerFinalTape input

example (input : BitString) :
    workRunExact? machine (workSteps input.length)
        (workStartConfiguration machine
          (PipelineInputFramer.totalInputFramerFinalTape input)) =
      some (finalConfiguration input
        (PipelineInputFramer.totalInputFramerOutsideLeft input)) :=
  workRunExact_after_totalInputFramer input

end PNP.Concrete.CookLevinBuilderInputLengthRegression
