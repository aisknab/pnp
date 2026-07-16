import PNP

namespace PNP.Concrete.CookLevinBuilderFirstTokenPrefixRegression

open PipelineTape
open PipelineStateNamespace
open CookLevin
open CookLevin.BuilderFirstTokenPrefix

def arbitraryOutsideLeft : List WorkSymbol :=
  [WorkSymbol.zeroOne, WorkSymbol.blank, WorkSymbol.oneOne]

def arbitraryLeft : List WorkSymbol :=
  [WorkSymbol.oneOne, WorkSymbol.blank, WorkSymbol.zeroBlank]

def arbitraryRight : List WorkSymbol :=
  [WorkSymbol.oneBlank, WorkSymbol.zeroZero, WorkSymbol.blank]

example : rules.length = 184 := rules_length

example : workSteps ([] : BitString) = 16 := rfl
example : workSteps ([false] : BitString) = 38 := rfl
example : workSteps ([true] : BitString) = 38 := rfl
example : workSteps ([true, false, true] : BitString) = 91 := rfl
example : workSteps ([true, true, false, false] : BitString) = 115 := rfl
example : workSteps ([false, false, false, false] : BitString) = 115 := rfl
example : workSteps ([true, true, true, true] : BitString) = 115 := rfl

example : rawTimeBound.eval 0 = 147 := rfl
example : rawTimeBound.eval 1 = 252 := rfl
example : rawTimeBound.eval 3 = 570 := rfl
example : rawTimeBound.eval 4 = 783 := rfl

example : 6 * workSteps ([] : BitString) = 96 := rfl
example : 6 * workSteps ([false] : BitString) = 228 := rfl
example : 6 * workSteps ([true, false, true] : BitString) = 546 := rfl
example : 6 * workSteps ([true, true, false, false] : BitString) = 690 := rfl

example : finalTape ([] : BitString) =
    frameWithGarbage (Tape.ofInput []) []
      [CookLevin.BuilderTokenAppender.outputBoundarySymbol,
       CookLevin.BuilderTokenAppender.tokenSymbol .t] := rfl

example : finalTape ([false] : BitString) =
    frameWithGarbage (Tape.ofInput [false])
      [WorkSymbol.blank, rightMarker]
      [CookLevin.BuilderInputLength.tallySymbol,
       CookLevin.BuilderTokenAppender.outputBoundarySymbol,
       CookLevin.BuilderTokenAppender.tokenSymbol .t] := rfl

example : finalTape ([true] : BitString) =
    frameWithGarbage (Tape.ofInput [true])
      [WorkSymbol.blank, rightMarker]
      [CookLevin.BuilderInputLength.tallySymbol,
       CookLevin.BuilderTokenAppender.outputBoundarySymbol,
       CookLevin.BuilderTokenAppender.tokenSymbol .t] := rfl

example : finalTape ([true, false, true] : BitString) =
    frameWithGarbage (Tape.ofInput [true, false, true])
      [WorkSymbol.blank, WorkSymbol.blank, rightMarker]
      [CookLevin.BuilderInputLength.tallySymbol,
       CookLevin.BuilderInputLength.tallySymbol,
       CookLevin.BuilderInputLength.tallySymbol,
       CookLevin.BuilderTokenAppender.outputBoundarySymbol,
       CookLevin.BuilderTokenAppender.tokenSymbol .t] := rfl

example (input : BitString) :
    Represents (Tape.ofInput input) (finalTape input) :=
  finalTape_represents input

example (left right : Nat) : prefixState left ≠ appenderState right :=
  prefixState_ne_appenderState left right

example (input : BitString) :
    workStep? machine
        (renameConfiguration prefixState
          (CookLevin.BuilderInputPrefix.finalConfiguration input)) =
      some (renameConfiguration appenderState
        (workStartConfiguration CookLevin.BuilderTokenAppender.machine
          (CookLevin.BuilderInputPrefix.finalTape input))) :=
  launch_workStep input

example (input : BitString) :
    workRunExact? machine (workSteps input)
        (workStartConfiguration machine (rawInputWorkTape input)) =
      some (finalConfiguration input) :=
  workRunExact input

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
    workBoundedDecide machine
        (CookLevin.BuilderInputPrefix.workSteps input)
        (rawInputWorkTape input) = .timeout :=
  prefixEndpoint_before_launch_timeout input

example (input : BitString) :
    workBoundedDecide machine (workSteps input - 1)
        (rawInputWorkTape input) = .timeout :=
  work_one_step_short_timeout input

example (fuel : Nat) :
    (let config := renameConfiguration prefixState
        (CookLevin.BuilderInputPrefix.malformedTallyConfiguration
          arbitraryLeft arbitraryRight)
     let result := workRun machine fuel config
     if result.state == machine.acceptState then WorkVerdict.accept
     else if result.state == machine.rejectState then WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  malformedPrefixTally_timeout fuel arbitraryLeft arbitraryRight

example (fuel : Nat) (request : CNFToken) :
    (let config := renameConfiguration appenderState
        (CookLevin.BuilderTokenAppender.malformedTallyConfiguration
          request arbitraryLeft arbitraryRight)
     let result := workRun machine fuel config
     if result.state == machine.acceptState then WorkVerdict.accept
     else if result.state == machine.rejectState then WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  malformedAppenderTally_timeout fuel request arbitraryLeft arbitraryRight

example (fuel : Nat) (request : CNFToken) :
    (let config := renameConfiguration appenderState
        (CookLevin.BuilderTokenAppender.malformedOutputConfiguration
          request arbitraryLeft arbitraryRight)
     let result := workRun machine fuel config
     if result.state == machine.acceptState then WorkVerdict.accept
     else if result.state == machine.rejectState then WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  malformedAppenderOutput_timeout fuel request arbitraryLeft arbitraryRight

example : machine.isHalted
    { state := prefixState CookLevin.BuilderInputPrefix.machine.rejectState
      tape := rawInputWorkTape [] } = false := rfl

example : workStep? machine
    { state := prefixState CookLevin.BuilderInputPrefix.machine.rejectState
      tape := rawInputWorkTape [] } = none := rfl

def inputOnlyVerifier : PolynomialTimeVerifier (fun _ => True) :=
  verifierFromDecider
    (PolynomialTimeDecider.ofMachine acceptAllPolynomialTime)

def inputOnlyProblem : VerifierTableauProblem (fun _ => True) :=
  { verifier := inputOnlyVerifier, input := [false, true, false] }

example : CNFToken.t.bits = inputOnlyProblem.encodedFormula.take 2 :=
  finalTokenBits_eq_encodedFormula_take_two inputOnlyProblem

example : CookLevin.BuilderTokenAppender.tokenSymbol .t = WorkSymbol.oneOne :=
  rfl

end PNP.Concrete.CookLevinBuilderFirstTokenPrefixRegression
