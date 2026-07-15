import PNP

namespace PNP.Concrete.CookLevinBuilderInputPrefixRegression

open CookLevin.BuilderInputPrefix
open PipelineStateNamespace

example : workSteps ([] : BitString) = 7 := rfl
example : workSteps ([false] : BitString) = 27 := rfl
example : workSteps ([true, false, true] : BitString) = 72 := rfl
example : workSteps ([true, true, false, false] : BitString) = 92 := rfl

example : rawTimeBound.eval 0 = 93 := rfl
example : rawTimeBound.eval 1 = 174 := rfl
example : rawTimeBound.eval 3 = 444 := rfl
example : rawTimeBound.eval 4 = 633 := rfl

example : 6 * workSteps ([] : BitString) = 42 := rfl
example : 6 * workSteps ([false] : BitString) = 162 := rfl
example : 6 * workSteps ([true, false, true] : BitString) = 432 := rfl
example : 6 * workSteps ([true, true, false, false] : BitString) = 552 := rfl

example : finalTape ([] : BitString) =
    PipelineTape.frameWithGarbage (Tape.ofInput []) [] [] := rfl

example : finalTape ([false] : BitString) =
    PipelineTape.frameWithGarbage (Tape.ofInput [false])
      [WorkSymbol.blank, PipelineTape.rightMarker]
      [CookLevin.BuilderInputLength.tallySymbol] := rfl

example : finalTape ([true] : BitString) =
    PipelineTape.frameWithGarbage (Tape.ofInput [true])
      [WorkSymbol.blank, PipelineTape.rightMarker]
      [CookLevin.BuilderInputLength.tallySymbol] := rfl

example : finalTape ([true, false, true] : BitString) =
    PipelineTape.frameWithGarbage (Tape.ofInput [true, false, true])
      [WorkSymbol.blank, WorkSymbol.blank, PipelineTape.rightMarker]
      [CookLevin.BuilderInputLength.tallySymbol,
       CookLevin.BuilderInputLength.tallySymbol,
       CookLevin.BuilderInputLength.tallySymbol] := rfl

example : finalTape ([false, false, false, false] : BitString) =
    PipelineTape.frameWithGarbage (Tape.ofInput [false, false, false, false])
      [WorkSymbol.blank, WorkSymbol.blank, PipelineTape.rightMarker]
      (List.replicate 4 CookLevin.BuilderInputLength.tallySymbol) := rfl

example : finalTape ([true, true, true, true] : BitString) =
    PipelineTape.frameWithGarbage (Tape.ofInput [true, true, true, true])
      [WorkSymbol.blank, WorkSymbol.blank, PipelineTape.rightMarker]
      (List.replicate 4 CookLevin.BuilderInputLength.tallySymbol) := rfl

example : finalTape ([false, true, false, true] : BitString) =
    PipelineTape.frameWithGarbage (Tape.ofInput [false, true, false, true])
      [WorkSymbol.blank, WorkSymbol.blank, PipelineTape.rightMarker]
      (List.replicate 4 CookLevin.BuilderInputLength.tallySymbol) := rfl

example (input : BitString) :
    PipelineTape.Represents (Tape.ofInput input) (finalTape input) :=
  finalTape_represents input

example (input : BitString) :
    (List.replicate input.length
      CookLevin.BuilderInputLength.tallySymbol).length = input.length :=
  finalTape_tally_length input

example (input : BitString) :
    workRunExact? machine (workSteps input)
        (workStartConfiguration machine (rawInputWorkTape input)) =
      some (finalConfiguration input) :=
  workRunExact input

example (input : BitString) :
    run (compileWorkMachine machine) (6 * workSteps input)
        (encodeWorkConfiguration
          (workStartConfiguration machine (rawInputWorkTape input))) =
      encodeWorkConfiguration (finalConfiguration input) :=
  run_compile_exact input

example (input : BitString) :
    run (compileWorkMachine machine)
        (rawTimeBound.eval (BitString.size input))
        (encodeWorkConfiguration
          (workStartConfiguration machine (rawInputWorkTape input))) =
      encodeWorkConfiguration (finalConfiguration input) :=
  run_compile_rawTimeBound input

example (input : BitString) :
    boundedDecide (compileWorkMachine machine)
        (rawTimeBound.eval (BitString.size input)) input = .accept :=
  boundedDecide_compile_accept input

example (input : BitString) :
    boundedDecide (compileWorkMachine machine)
        (rawTimeBound.eval (BitString.size input)) input ≠ .timeout :=
  boundedDecide_compile_ne_timeout input

example (input : BitString) :
    workBoundedDecide machine (workSteps input - 1)
        (rawInputWorkTape input) = .timeout :=
  work_one_step_short_timeout input

def arbitraryLeft : List WorkSymbol :=
  [WorkSymbol.oneOne, WorkSymbol.blank, WorkSymbol.zeroBlank]

def arbitraryRight : List WorkSymbol :=
  [WorkSymbol.oneBlank, WorkSymbol.zeroZero, WorkSymbol.blank]

example (fuel : Nat) :
    (let result := workRun machine fuel
        (malformedTallyConfiguration arbitraryLeft arbitraryRight)
     if result.state == machine.acceptState then WorkVerdict.accept
     else if result.state == machine.rejectState then WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  malformedTallyScanSymbol_timeout fuel arbitraryLeft arbitraryRight

example (input : BitString) :
    machine.isHalted
      (renameConfiguration framerState
        (PipelineInputFramer.totalInputFramerFinalConfiguration input)) =
      false :=
  machine_isHalted_framer_false _

example (input : BitString) :
    workStep? machine
        (renameConfiguration framerState
          (PipelineInputFramer.totalInputFramerFinalConfiguration input)) =
      some (renameConfiguration tallyState
        (workStartConfiguration CookLevin.BuilderInputLength.machine
          (PipelineInputFramer.totalInputFramerFinalTape input))) :=
  launch_workStep input

end PNP.Concrete.CookLevinBuilderInputPrefixRegression
