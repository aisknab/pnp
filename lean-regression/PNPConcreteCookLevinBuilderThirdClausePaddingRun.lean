import PNP

namespace PNP.Concrete.CookLevinBuilderThirdClausePaddingRunRegression

open PipelineTape PipelineStateNamespace
open CookLevin
open CookLevin.BuilderThirdClausePaddingRun

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

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

def inputOnlyProblem (input : BitString) :
    VerifierTableauProblem (fun _ => True) :=
  { verifier := inputOnlyVerifier, input := input }

def pairedProblem (input : BitString) :
    VerifierTableauProblem (fun _ => True) :=
  { verifier := pairedVerifier, input := input }

example : BuilderFirstClausePaddingRun.PaddingCountdown.rules.length = 25 :=
  BuilderFirstClausePaddingRun.PaddingCountdown.rules_length

example (input : BitString) :
    (machine (inputOnlyProblem input)).rules.length =
      3178 +
        BuilderUnaryPolynomial.ruleCount
          (BuilderCompleteHeader.widthPolynomial (inputOnlyProblem input)) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderBodyStartPrefix.nextTokenSlotPolynomial inputOnlyVerifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderFirstLiteralPrefix.nextTokenSlotPolynomial inputOnlyVerifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderFirstClausePrefix.nextTokenSlotPolynomial inputOnlyVerifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderFirstClausePaddingRun.remainingPaddingPolynomial
            inputOnlyVerifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderFirstClausePaddingRun.secondClauseStartPolynomial
            inputOnlyVerifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderSecondClausePaddingRun.remainingPaddingPolynomial
            inputOnlyVerifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderSecondClausePaddingRun.thirdClauseStartPolynomial
            inputOnlyVerifier) +
        BuilderUnaryPolynomial.ruleCount
          (remainingPaddingPolynomial inputOnlyVerifier) +
        BuilderUnaryPolynomial.ruleCount
          (fourthClauseStartPolynomial inputOnlyVerifier) :=
  rules_length (inputOnlyProblem input)

example : remainingPaddingCount (inputOnlyProblem []) = 82 := rfl
example : remainingPaddingCount (inputOnlyProblem [false]) = 174 := rfl
example : remainingPaddingCount (inputOnlyProblem [true]) = 174 := rfl
example : remainingPaddingCount
    (inputOnlyProblem [true, false, true]) = 454 := rfl
example : remainingPaddingCount
    (pairedProblem [true, false, true]) = 6634 := rfl
example : remainingPaddingCount
    (inputOnlyProblem [false, false, false, false]) = 642 := rfl
example : remainingPaddingCount
    (inputOnlyProblem [true, true, true, true]) = 642 := rfl

example : fourthClauseStart (inputOnlyProblem []) = 278 := rfl
example : fourthClauseStart (inputOnlyProblem [false]) = 558 := rfl
example : fourthClauseStart
    (inputOnlyProblem [true, false, true]) = 1406 := rfl
example : fourthClauseStart
    (pairedProblem [true, false, true]) = 20006 := rfl
example : fourthClauseStart
    (inputOnlyProblem [false, false, false, false]) = 1974 := rfl
example : fourthClauseStart
    (inputOnlyProblem [true, true, true, true]) = 1974 := rfl

example (input : BitString) :
    (rawTimeBound inputOnlyVerifier).eval input.length =
      (BuilderThirdClausePrefix.rawTimeBound inputOnlyVerifier).eval
          input.length + 18 +
        6 * BuilderUnaryPolynomial.workSteps
          (remainingPaddingPolynomial inputOnlyVerifier) input +
        6 *
          (remainingPaddingCount (inputOnlyProblem input) *
              (2 * countRootPrefixLength (inputOnlyProblem input) + 8) +
            remainingPaddingCount (inputOnlyProblem input) *
              remainingPaddingCount (inputOnlyProblem input)) +
        6 * BuilderUnaryPolynomial.workSteps
          (fourthClauseStartPolynomial inputOnlyVerifier) input :=
  rawTimeBound_eval (inputOnlyProblem input)

example (input : BitString) :
    remainingPaddingCount (inputOnlyProblem input) =
      (inputOnlyProblem input).formulaTokensPerClause - 8 :=
  remainingPaddingCount_eq_formulaTokensPerClause_sub_eight
    (inputOnlyProblem input)

example (input : BitString) :
    BuilderThirdClausePrefix.finalTokenSlot (inputOnlyProblem input) +
        remainingPaddingCount (inputOnlyProblem input) =
      fourthClauseStart (inputOnlyProblem input) :=
  predecessorSlot_add_remainingPaddingCount (inputOnlyProblem input)

example (input : BitString) (offset : Nat)
    (hOffset : offset < remainingPaddingCount (inputOnlyProblem input)) :
    (inputOnlyProblem input).formulaTokenSlotDirect
        (BuilderThirdClausePrefix.finalTokenSlot
          (inputOnlyProblem input) + offset) = some none :=
  paddingSlot_direct_eq_padding (inputOnlyProblem input) offset hOffset

example (input : BitString) :
    (inputOnlyProblem input).formulaTokenSlotDirect
        (fourthClauseStart (inputOnlyProblem input)) =
      some (some CNFToken.sep) :=
  fourthClauseStart_direct_eq_sep (inputOnlyProblem input)

example (input : BitString) :
    specificationRun (inputOnlyProblem input)
        (remainingPaddingCount (inputOnlyProblem input))
        ⟨BuilderThirdClausePrefix.finalTokenSlot
          (inputOnlyProblem input)⟩ =
      some ([], ⟨fourthClauseStart (inputOnlyProblem input)⟩) :=
  specification_padding_run (inputOnlyProblem input)

example (input : BitString) :
    VerifierTableauProblem.FormulaTokenCursor.step
        (inputOnlyProblem input)
        ⟨fourthClauseStart (inputOnlyProblem input)⟩ =
      some (some CNFToken.sep,
        ⟨fourthClauseStart (inputOnlyProblem input) + 1⟩) :=
  specification_target_step (inputOnlyProblem input)

example (input : BitString) :
    Represents (Tape.ofInput input) (finalTape (inputOnlyProblem input)) :=
  finalTape_represents (inputOnlyProblem input)

example (input : BitString) :
    encodeTokenPairs
        (BuilderThirdClausePrefix.thirdClauseTokens
          (inputOnlyProblem input)) =
      (inputOnlyProblem input).encodedFormula.take
        (2 * ((inputOnlyProblem input).FormulaWidth + 27)) :=
  finalTokenBits_eq_encodedFormula_thirdClause (inputOnlyProblem input)

example (input : BitString) :
    workStep? (machine (inputOnlyProblem input))
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (BuilderThirdClausePrefix.finalConfiguration
            (inputOnlyProblem input))) =
      some (renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration
          (paddingSuffixMachine (inputOnlyProblem input))
          (BuilderThirdClausePrefix.finalTape
            (inputOnlyProblem input)))) :=
  launch_workStep (inputOnlyProblem input)

example (input : BitString) :
    workRunExact? (machine (inputOnlyProblem input))
        (workSteps (inputOnlyProblem input))
        (workStartConfiguration (machine (inputOnlyProblem input))
          (rawInputWorkTape input)) =
      some (finalConfiguration (inputOnlyProblem input)) :=
  workRunExact (inputOnlyProblem input)

example (input : BitString) :
    workRunExact? (machine (pairedProblem input))
        (workSteps (pairedProblem input))
        (workStartConfiguration (machine (pairedProblem input))
          (rawInputWorkTape input)) =
      some (finalConfiguration (pairedProblem input)) :=
  workRunExact (pairedProblem input)

example (input : BitString) :
    boundedDecide (compileWorkMachine (machine (inputOnlyProblem input)))
        ((rawTimeBound inputOnlyVerifier).eval input.length) input = .accept :=
  boundedDecide_compile_accept (inputOnlyProblem input)

example (input : BitString) :
    workBoundedDecide (machine (inputOnlyProblem input))
        (BuilderThirdClausePrefix.workSteps (inputOnlyProblem input))
        (rawInputWorkTape input) = .timeout :=
  prefixEndpoint_before_launch_timeout (inputOnlyProblem input)

example (input : BitString) :
    workBoundedDecide (machine (inputOnlyProblem input))
        (workSteps (inputOnlyProblem input) - 1)
        (rawInputWorkTape input) = .timeout :=
  work_one_step_short_timeout (inputOnlyProblem input)

example (fuel : Nat) (left right : List WorkSymbol) :
    (let config := malformedCountdownScratchConfiguration left right
     let result := workRun BuilderFirstClausePaddingRun.PaddingCountdown.machine fuel config
     if result.state == BuilderFirstClausePaddingRun.PaddingCountdown.machine.acceptState then
       WorkVerdict.accept
     else if result.state == BuilderFirstClausePaddingRun.PaddingCountdown.machine.rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  malformedCountdownScratch_timeout fuel left right

example (fuel : Nat) (left right : List WorkSymbol) :
    (let config := malformedCountdownRootConfiguration left right
     let result := workRun BuilderFirstClausePaddingRun.PaddingCountdown.machine fuel config
     if result.state == BuilderFirstClausePaddingRun.PaddingCountdown.machine.acceptState then
       WorkVerdict.accept
     else if result.state == BuilderFirstClausePaddingRun.PaddingCountdown.machine.rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  malformedCountdownRoot_timeout fuel left right

end PNP.Concrete.CookLevinBuilderThirdClausePaddingRunRegression
