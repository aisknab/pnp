import PNP

namespace PNP.Concrete.CookLevinBuilderCompleteHeaderRegression

open PipelineTape PipelineStateNamespace
open CookLevin
open CookLevin.BuilderCompleteHeader

def inputOnlyVerifier : PolynomialTimeVerifier (fun _ => True) :=
  verifierFromDecider
    (PolynomialTimeDecider.ofMachine acceptAllPolynomialTime)

def inputOnlyProblem (input : BitString) :
    VerifierTableauProblem (fun _ => True) :=
  { verifier := inputOnlyVerifier, input := input }

example : width (inputOnlyProblem []) = 6 := rfl
example : width (inputOnlyProblem [false]) = 10 := rfl
example : width (inputOnlyProblem [true]) = 10 := rfl
example : width (inputOnlyProblem [true, false, true]) = 18 := rfl

example : BuilderUnaryPolynomial.ruleCount
    (widthPolynomial (inputOnlyProblem [])) = 3465 := rfl
example : (rules (inputOnlyProblem [])).length = 3828 := by
  rw [rules_length]
  rfl
example (input : BitString) :
    (rules (inputOnlyProblem input)).length =
      363 + BuilderUnaryPolynomial.ruleCount
        (widthPolynomial (inputOnlyProblem input)) :=
  rules_length (inputOnlyProblem input)

example : workSteps (inputOnlyProblem []) = 2379 := rfl
example : workSteps (inputOnlyProblem [false]) = 4303 := rfl
example : workSteps (inputOnlyProblem [true]) = 4303 := rfl
example : workSteps (inputOnlyProblem [true, false, true]) = 9864 := rfl
example : workSteps
    (inputOnlyProblem [false, false, false, false]) = 13482 := rfl
example : workSteps
    (inputOnlyProblem [true, true, true, true]) = 13482 := rfl

example : (rawTimeBound inputOnlyVerifier).eval 0 = 14481 := rfl
example : (rawTimeBound inputOnlyVerifier).eval 1 = 26214 := rfl
example : (rawTimeBound inputOnlyVerifier).eval 3 = 59868 := rfl
example : (rawTimeBound inputOnlyVerifier).eval 4 = 81789 := rfl

example : headerTokens (inputOnlyProblem []) =
    [.t, .t, .t, .t, .t, .t, .f] := rfl

example (input : BitString) :
    headerTokens (inputOnlyProblem input) =
      encodeUnaryTokens (inputOnlyProblem input).FormulaWidth :=
  headerTokens_eq_encodeUnaryTokens (inputOnlyProblem input)

example (input : BitString) :
    Represents (Tape.ofInput input)
      (finalTape (inputOnlyProblem input)) :=
  finalTape_represents (inputOnlyProblem input)

example (input : BitString) :
    encodeTokenPairs (headerTokens (inputOnlyProblem input)) =
      (inputOnlyProblem input).encodedFormula.take
        (2 * ((inputOnlyProblem input).FormulaWidth + 1)) :=
  finalTokenBits_eq_encodedFormula_header (inputOnlyProblem input)

example (left right : Nat) : prefixState left ≠ evaluatorState right := by
  simp [prefixState, evaluatorState]
  omega

example (left right : Nat) : evaluatorState left ≠ controllerState right := by
  simp [evaluatorState, controllerState]
  omega

example (left right : Nat) : controllerState left ≠ tAppenderState right := by
  simp [controllerState, tAppenderState]
  omega

example (left right : Nat) : tAppenderState left ≠ fAppenderState right := by
  simp [tAppenderState, fAppenderState]
  omega

example : workRunExact? HeaderController.machine
      (HeaderController.steps 0 0)
      (HeaderController.initialConfiguration [] [] 0 [] []) =
    some (HeaderController.finalConfiguration [] [] 0 [] []) :=
  HeaderController.workRunExact [] [] 0 [] [] (by simp)

example : workRunExact? HeaderController.machine
      (HeaderController.steps 0 2)
      (HeaderController.initialConfiguration [] [] 2 [] []) =
    some (HeaderController.finalConfiguration [] [] 2 [] []) :=
  HeaderController.workRunExact [] [] 2 [] [] (by simp)

example (input : BitString) :
    workRunExact? (machine (inputOnlyProblem input))
        (workSteps (inputOnlyProblem input))
        (workStartConfiguration (machine (inputOnlyProblem input))
          (rawInputWorkTape input)) =
      some (finalConfiguration (inputOnlyProblem input)) :=
  workRunExact (inputOnlyProblem input)

example (input : BitString) :
    run (compileWorkMachine (machine (inputOnlyProblem input)))
        ((rawTimeBound inputOnlyVerifier).eval input.length)
        (encodeWorkConfiguration
          (workStartConfiguration (machine (inputOnlyProblem input))
            (rawInputWorkTape input))) =
      encodeWorkConfiguration (finalConfiguration (inputOnlyProblem input)) :=
  run_compile_rawTimeBound (inputOnlyProblem input)

example (input : BitString) :
    boundedDecide (compileWorkMachine (machine (inputOnlyProblem input)))
        ((rawTimeBound inputOnlyVerifier).eval input.length) input = .accept :=
  boundedDecide_compile_accept (inputOnlyProblem input)

example (input : BitString) :
    workBoundedDecide (machine (inputOnlyProblem input))
        (BuilderFirstTokenPrefix.workSteps input)
        (rawInputWorkTape input) = .timeout :=
  prefixEndpoint_before_launch_timeout (inputOnlyProblem input)

example (input : BitString) :
    workBoundedDecide (machine (inputOnlyProblem input))
        (workSteps (inputOnlyProblem input) - 1)
        (rawInputWorkTape input) = .timeout :=
  work_one_step_short_timeout (inputOnlyProblem input)

end PNP.Concrete.CookLevinBuilderCompleteHeaderRegression
