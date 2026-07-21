import PNP

namespace PNP.Concrete.CookLevinBuilderFifthClausePaddingRunRegression

open PipelineTape PipelineStateNamespace
open CookLevin
open CookLevin.BuilderFifthClausePaddingRun

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
      4380 +
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
          (BuilderThirdClausePaddingRun.remainingPaddingPolynomial
            inputOnlyVerifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderThirdClausePaddingRun.fourthClauseStartPolynomial
            inputOnlyVerifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderFourthClausePaddingRun.remainingPaddingPolynomial
            inputOnlyVerifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderFourthClausePaddingRun.fifthClauseSlotStartPolynomial
            inputOnlyVerifier) +
        BuilderUnaryPolynomial.ruleCount
          (paddingPolynomial inputOnlyVerifier) +
        BuilderUnaryPolynomial.ruleCount
          (sixthClauseSlotStartPolynomial inputOnlyVerifier) :=
  rules_length (inputOnlyProblem input)

example : paddingCount (inputOnlyProblem []) = 90 := rfl
example : paddingCount (inputOnlyProblem [false]) = 182 := rfl
example : paddingCount (inputOnlyProblem [true]) = 182 := rfl
example : paddingCount
    (inputOnlyProblem [true, false, true]) = 462 := rfl
example : paddingCount
    (pairedProblem [true, false, true]) = 6642 := rfl
example : paddingCount
    (inputOnlyProblem [false, false, false, false]) = 650 := rfl
example : paddingCount
    (inputOnlyProblem [true, true, true, true]) = 650 := rfl

example : sixthClauseSlotStart (inputOnlyProblem []) = 458 := rfl
example : sixthClauseSlotStart (inputOnlyProblem [false]) = 922 := rfl
example : sixthClauseSlotStart
    (inputOnlyProblem [true, false, true]) = 2330 := rfl
example : sixthClauseSlotStart
    (pairedProblem [true, false, true]) = 33290 := rfl
example : sixthClauseSlotStart
    (inputOnlyProblem [false, false, false, false]) = 3274 := rfl
example : sixthClauseSlotStart
    (inputOnlyProblem [true, true, true, true]) = 3274 := rfl

example (input : BitString) :
    (rawTimeBound inputOnlyVerifier).eval input.length =
      (BuilderFourthClausePaddingRun.rawTimeBound inputOnlyVerifier).eval
          input.length + 18 +
        6 * BuilderUnaryPolynomial.workSteps
          (paddingPolynomial inputOnlyVerifier) input +
        6 *
          (paddingCount (inputOnlyProblem input) *
              (2 * countRootPrefixLength (inputOnlyProblem input) + 8) +
            paddingCount (inputOnlyProblem input) *
              paddingCount (inputOnlyProblem input)) +
        6 * BuilderUnaryPolynomial.workSteps
          (sixthClauseSlotStartPolynomial inputOnlyVerifier) input :=
  rawTimeBound_eval (inputOnlyProblem input)

example (input : BitString) :
    paddingCount (inputOnlyProblem input) =
      (inputOnlyProblem input).formulaTokensPerClause :=
  paddingCount_eq_formulaTokensPerClause
    (inputOnlyProblem input)

example (input : BitString) :
    BuilderFourthClausePaddingRun.finalTokenSlot (inputOnlyProblem input) +
        paddingCount (inputOnlyProblem input) =
      sixthClauseSlotStart (inputOnlyProblem input) :=
  predecessorSlot_add_paddingCount (inputOnlyProblem input)

example (input : BitString) (offset : Nat)
    (hOffset : offset < paddingCount (inputOnlyProblem input)) :
    (inputOnlyProblem input).formulaTokenSlotDirect
        (BuilderFourthClausePaddingRun.finalTokenSlot
          (inputOnlyProblem input) + offset) = some none :=
  paddingSlot_direct_eq_padding (inputOnlyProblem input) offset hOffset

example (input : BitString) :
    (inputOnlyProblem input).formulaTokenSlotDirect
        (sixthClauseSlotStart (inputOnlyProblem input)) =
      some none :=
  sixthClauseSlotStart_direct_eq_padding (inputOnlyProblem input)

example (input : BitString) :
    specificationRun (inputOnlyProblem input)
        (paddingCount (inputOnlyProblem input))
        ⟨BuilderFourthClausePaddingRun.finalTokenSlot
          (inputOnlyProblem input)⟩ =
      some ([], ⟨sixthClauseSlotStart (inputOnlyProblem input)⟩) :=
  specification_padding_run (inputOnlyProblem input)

example (input : BitString) :
    VerifierTableauProblem.FormulaTokenCursor.step
        (inputOnlyProblem input)
        ⟨sixthClauseSlotStart (inputOnlyProblem input)⟩ =
      some (none,
        ⟨sixthClauseSlotStart (inputOnlyProblem input) + 1⟩) :=
  specification_target_step (inputOnlyProblem input)

example (input : BitString) :
    Represents (Tape.ofInput input) (finalTape (inputOnlyProblem input)) :=
  finalTape_represents (inputOnlyProblem input)

example (input : BitString) :
    encodeTokenPairs
        (BuilderFourthClausePrefix.fourthClauseTokens
          (inputOnlyProblem input)) =
      (inputOnlyProblem input).encodedFormula.take
        (2 * ((inputOnlyProblem input).FormulaWidth + 36)) :=
  finalTokenBits_eq_encodedFormula_fourthClause (inputOnlyProblem input)

example (input : BitString) :
    workStep? (machine (inputOnlyProblem input))
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (BuilderFourthClausePaddingRun.finalConfiguration
            (inputOnlyProblem input))) =
      some (renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration
          (paddingSuffixMachine (inputOnlyProblem input))
          (BuilderFourthClausePaddingRun.finalTape
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
        (BuilderFourthClausePaddingRun.workSteps (inputOnlyProblem input))
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

end PNP.Concrete.CookLevinBuilderFifthClausePaddingRunRegression
