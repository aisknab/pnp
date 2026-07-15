import PNP

namespace PNP.Concrete.CookLevinBuilderTokenAppenderRegression

open PipelineTape
open CookLevin
open CookLevin.BuilderTokenAppender

def arbitraryOutsideLeft : List WorkSymbol :=
  [WorkSymbol.zeroOne, WorkSymbol.blank, WorkSymbol.oneOne]

example : rules.length = 59 := rules_length
example : allTokens = [.f, .t, .sep, .finish] := rfl

example : tokenSymbol .f = WorkSymbol.zeroZero := rfl
example : tokenSymbol .t = WorkSymbol.oneOne := rfl
example : tokenSymbol .sep = WorkSymbol.zeroOne := rfl
example : tokenSymbol .finish = WorkSymbol.oneZero := rfl

example : workSteps ([] : BitString) [] = 8 := rfl
example : workSteps ([false] : BitString) [] = 10 := rfl
example : workSteps ([true, false, true] : BitString) [] = 18 := rfl
example : workSteps ([true, true, false, false] : BitString) [] = 22 := rfl
example : workSteps ([true, false] : BitString) [.t, .sep, .f] = 20 := rfl

example : firstTokenRawTimeBound.eval 0 = 48 := rfl
example : firstTokenRawTimeBound.eval 1 = 72 := rfl
example : firstTokenRawTimeBound.eval 3 = 120 := rfl
example : firstTokenRawTimeBound.eval 4 = 144 := rfl

example (input : BitString) (output : List CNFToken)
    (request : CNFToken) :
    workRunExact? machine (workSteps input output)
        (entryConfiguration request
          (workspaceTape input arbitraryOutsideLeft output)) =
      some (finalConfiguration input arbitraryOutsideLeft
        (output ++ [request])) :=
  appendToken_workRunExact input arbitraryOutsideLeft output request

example (input : BitString) :
    workRunExact? machine (workSteps input [])
        (workStartConfiguration machine
          (CookLevin.BuilderInputLength.finalTape input arbitraryOutsideLeft)) =
      some (firstHeaderFinalConfiguration input arbitraryOutsideLeft) :=
  firstHeaderToken_workRunExact input arbitraryOutsideLeft

example (input : BitString) :
    run (compileWorkMachine machine)
        (firstTokenRawTimeBound.eval (BitString.size input))
        (encodeWorkConfiguration
          (workStartConfiguration machine
            (CookLevin.BuilderInputLength.finalTape input arbitraryOutsideLeft))) =
      encodeWorkConfiguration
        (firstHeaderFinalConfiguration input arbitraryOutsideLeft) :=
  run_compile_firstHeaderToken_rawTimeBound input arbitraryOutsideLeft

example (input : BitString) :
    workBoundedDecide machine (workSteps input [] - 1)
        (CookLevin.BuilderInputLength.finalTape input arbitraryOutsideLeft) =
      .timeout :=
  firstHeaderToken_one_step_short_timeout input arbitraryOutsideLeft

example (fuel : Nat) (request : CNFToken) :
    (let result := workRun machine fuel
        (malformedTallyConfiguration request arbitraryOutsideLeft [])
     if result.state == machine.acceptState then WorkVerdict.accept
     else if result.state == machine.rejectState then WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  malformedTallySymbol_timeout fuel request arbitraryOutsideLeft []

example (fuel : Nat) (request : CNFToken) :
    (let result := workRun machine fuel
        (malformedOutputConfiguration request arbitraryOutsideLeft [])
     if result.state == machine.acceptState then WorkVerdict.accept
     else if result.state == machine.rejectState then WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  malformedOutputSymbol_timeout fuel request arbitraryOutsideLeft []

def inputOnlyVerifier : PolynomialTimeVerifier (fun _ => True) :=
  verifierFromDecider
    (PolynomialTimeDecider.ofMachine acceptAllPolynomialTime)

def pairedVerifier : PolynomialTimeVerifier (fun _ => True) :=
  { program :=
      { inputMode := .paired
        decision := .machine immediateAcceptMachine (.constant 0) }
    certificateBound := .linear 1 1
    runtimeBound := .constant 0
    haltsWithin := by
      intro input certificate hCertificate
      exact Verdict.noConfusion
    runtime_le := by
      intro input certificate hCertificate
      exact Nat.le_refl 0
    accepts_iff := by
      intro input
      constructor
      · intro member
        exact ⟨[], Nat.zero_le _, rfl⟩
      · intro witness
        exact True.intro }

def inputOnlyProblem : VerifierTableauProblem (fun _ => True) :=
  { verifier := inputOnlyVerifier, input := [false] }

def pairedProblem : VerifierTableauProblem (fun _ => True) :=
  { verifier := pairedVerifier, input := [true, false, true] }

example : inputOnlyProblem.formulaBitSlotDirect 0 = some (some true) :=
  formulaBitSlotDirect_zero inputOnlyProblem

example : inputOnlyProblem.formulaBitSlotDirect 1 = some (some true) :=
  formulaBitSlotDirect_one inputOnlyProblem

example : CNFToken.t.bits = inputOnlyProblem.encodedFormula.take 2 :=
  firstHeaderToken_bits_eq_encodedFormula_take_two inputOnlyProblem

example : CNFToken.t.bits = pairedProblem.encodedFormula.take 2 :=
  firstHeaderToken_bits_eq_encodedFormula_take_two pairedProblem

end PNP.Concrete.CookLevinBuilderTokenAppenderRegression
