import PNP

namespace PNP.Concrete.CookLevinBuilderSecondConstraintFirstLiteralSuccessorTokenStepRegression

open PipelineTape PipelineStateNamespace
open CookLevin
open CookLevin.BuilderSecondConstraintFirstLiteralSuccessorTokenStep

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

example :
    WidthBranchAppender.machine.rules.length = 93 :=
  WidthBranchAppender.rules_length

example (input : BitString) :
    (machine (inputOnlyProblem input)).rules.length =
      5284 +
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
          (BuilderFifthClausePaddingRun.paddingPolynomial inputOnlyVerifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderFifthClausePaddingRun.sixthClauseSlotStartPolynomial
            inputOnlyVerifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderFirstConstraintPaddingRun.paddingPolynomial
            inputOnlyVerifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderFirstConstraintPaddingRun.secondConstraintStartPolynomial
            inputOnlyVerifier) +
        BuilderUnaryPolynomial.ruleCount
          (widthPolynomial (inputOnlyProblem input)) +
        BuilderUnaryPolynomial.ruleCount
          (successorTokenSlotPolynomial inputOnlyVerifier) :=
  rules_length (inputOnlyProblem input)

example : finalTokenSlot (inputOnlyProblem []) = 4515 := rfl
example : finalTokenSlot (inputOnlyProblem [false]) = 22223 := rfl
example : finalTokenSlot (inputOnlyProblem [true]) = 22223 := rfl
example : finalTokenSlot
    (inputOnlyProblem [true, false, true]) = 167271 := rfl
example : finalTokenSlot
    (pairedProblem [true, false, true]) = 41459451 := rfl
example : finalTokenSlot
    (inputOnlyProblem [false, false, false, false]) = 344531 := rfl
example : finalTokenSlot
    (inputOnlyProblem [true, true, true, true]) = 344531 := rfl

example (input : BitString) :
    secondConstraintFirstLiteralSuccessorTokens (inputOnlyProblem input) =
      BuilderSecondConstraintFirstLiteralTerminatorStep.secondConstraintFirstLiteralTerminatorTokens
          (inputOnlyProblem input) ++
        [successorToken (inputOnlyProblem input)] := rfl

example (input : BitString) :
    ∃ rest, encodeCNFTokens (inputOnlyProblem input).formula =
      secondConstraintFirstLiteralSuccessorTokens
        (inputOnlyProblem input) ++ rest :=
  secondConstraintFirstLiteralSuccessorTokens_eq_canonical_formula_prefix
    (inputOnlyProblem input)

example (input : BitString) :
    encodeTokenPairs
        (secondConstraintFirstLiteralSuccessorTokens
          (inputOnlyProblem input)) =
      (inputOnlyProblem input).encodedFormula.take
        (2 * ((inputOnlyProblem input).FormulaWidth + 43)) :=
  finalTokenBits_eq_encodedFormula_secondConstraintFirstLiteralSuccessor
    (inputOnlyProblem input)

example (input : BitString) :
    Represents (Tape.ofInput input) (finalTape (inputOnlyProblem input)) :=
  finalTape_represents (inputOnlyProblem input)

example :
    successorToken (inputOnlyProblem []) = CNFToken.finish := by
  rw [successorToken_eq_finish_or_t]
  rfl

example :
    successorToken (inputOnlyProblem [false]) = CNFToken.t := by
  rw [successorToken_eq_finish_or_t]
  rfl

example :
    successorToken (inputOnlyProblem [true]) = CNFToken.t := by
  rw [successorToken_eq_finish_or_t]
  rfl

example :
    successorToken (pairedProblem []) = CNFToken.t := by
  rw [successorToken_eq_finish_or_t]
  rfl

example :
    (inputOnlyProblem []).formulaTokenSlotDirect
        (finalTokenSlot (inputOnlyProblem [])) = some none := by
  rw [followingTokenSlot_direct_eq_padding_or_t]
  rfl

example :
    (inputOnlyProblem [false]).formulaTokenSlotDirect
        (finalTokenSlot (inputOnlyProblem [false])) =
      some (some CNFToken.t) := by
  rw [followingTokenSlot_direct_eq_padding_or_t]
  rfl

example :
    (pairedProblem []).formulaTokenSlotDirect
        (finalTokenSlot (pairedProblem [])) =
      some (some CNFToken.t) := by
  rw [followingTokenSlot_direct_eq_padding_or_t]
  rfl

example (tape : WorkTape) :
    workStep? WidthBranchAppender.machine
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          { state :=
              BuilderCompleteHeader.HeaderController.doneExitState
            tape := tape }) =
      some
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
          (BuilderTokenAppender.entryConfiguration .finish tape)) :=
  WidthBranchAppender.controller_done_launch_workStep tape

example (tape : WorkTape) :
    workStep? WidthBranchAppender.machine
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          { state :=
              BuilderCompleteHeader.HeaderController.moreExitState
            tape := tape }) =
      some
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
          (BuilderTokenAppender.entryConfiguration .t tape)) :=
  WidthBranchAppender.controller_more_launch_workStep tape

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
        (workSteps (inputOnlyProblem input) - 1)
        (rawInputWorkTape input) = .timeout :=
  work_one_step_short_timeout (inputOnlyProblem input)

example (input : BitString) :
    (rawTimeBound inputOnlyVerifier).eval input.length =
      (BuilderSecondConstraintFirstLiteralTerminatorStep.rawTimeBound
        inputOnlyVerifier).eval input.length +
      600 + 24 * input.length +
      12 * (inputOnlyProblem input).FormulaWidth +
      12 * width (inputOnlyProblem input) +
      12 * widthRootPrefixLength (inputOnlyProblem input) +
      6 * widthWorkSteps (inputOnlyProblem input) +
      6 * targetWorkSteps (inputOnlyProblem input) :=
  rawTimeBound_eval (inputOnlyProblem input)

end PNP.Concrete.CookLevinBuilderSecondConstraintFirstLiteralSuccessorTokenStepRegression
