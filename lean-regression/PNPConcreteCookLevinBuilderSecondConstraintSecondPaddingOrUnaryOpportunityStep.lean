import PNP

namespace PNP.Concrete.CookLevinBuilderSecondConstraintSecondPaddingOrUnaryOpportunityStepRegression

open PipelineTape PipelineStateNamespace
open CookLevin
open CookLevin.BuilderSecondConstraintSecondPaddingOrUnaryOpportunityStep

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
    BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.machine.rules.length =
      93 :=
  BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.rules_length

example (input : BitString) :
    (machine (inputOnlyProblem input)).rules.length =
      5524 +
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
          (BuilderSecondConstraintFirstLiteralSuccessorTokenStep.widthPolynomial
            (inputOnlyProblem input)) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderSecondConstraintFirstLiteralSuccessorTokenStep.successorTokenSlotPolynomial
            inputOnlyVerifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderSecondConstraintPaddingOrUnaryOpportunityStep.widthPolynomial
            (inputOnlyProblem input)) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderSecondConstraintPaddingOrUnaryOpportunityStep.opportunitySlotPolynomial
            inputOnlyVerifier) +
        BuilderUnaryPolynomial.ruleCount
          (widthPolynomial (inputOnlyProblem input)) +
        BuilderUnaryPolynomial.ruleCount
          (opportunitySlotPolynomial inputOnlyVerifier) :=
  rules_length (inputOnlyProblem input)

example : finalTokenSlot (inputOnlyProblem []) = 4517 := rfl
example : finalTokenSlot (inputOnlyProblem [false]) = 22225 := rfl
example : finalTokenSlot (inputOnlyProblem [true]) = 22225 := rfl
example : finalTokenSlot
    (inputOnlyProblem [true, false, true]) = 167273 := rfl
example : finalTokenSlot
    (pairedProblem [true, false, true]) = 41459453 := rfl
example : finalTokenSlot
    (inputOnlyProblem [false, false, false, false]) = 344533 := rfl
example : finalTokenSlot
    (inputOnlyProblem [true, true, true, true]) = 344533 := rfl

example (input : BitString) :
    secondConstraintSecondPaddingOrUnaryTokens (inputOnlyProblem input) =
      BuilderSecondConstraintPaddingOrUnaryOpportunityStep.secondConstraintPaddingOrUnaryTokens
          (inputOnlyProblem input) ++
        opportunityOutput (inputOnlyProblem input) := rfl

example (input : BitString) :
    ∃ rest, encodeCNFTokens (inputOnlyProblem input).formula =
      secondConstraintSecondPaddingOrUnaryTokens
        (inputOnlyProblem input) ++ rest :=
  secondConstraintSecondPaddingOrUnaryTokens_eq_canonical_formula_prefix
    (inputOnlyProblem input)

example (input : BitString) :
    encodeTokenPairs
        (secondConstraintSecondPaddingOrUnaryTokens
          (inputOnlyProblem input)) =
      (inputOnlyProblem input).encodedFormula.take
        (2 * ((inputOnlyProblem input).FormulaWidth + 43 +
          if (inputOnlyProblem input).dimensions.tapeWidth
              (inputOnlyProblem input).tableauInputMode = 1
            then 0 else 2)) :=
  finalTokenBits_eq_encodedFormula_secondConstraintSecondPaddingOrUnary
    (inputOnlyProblem input)

example (input : BitString) :
    Represents (Tape.ofInput input) (finalTape (inputOnlyProblem input)) :=
  finalTape_represents (inputOnlyProblem input)

example :
    opportunityOutput (inputOnlyProblem []) = [] := by
  rw [opportunityOutput_eq_nil_or_t]
  rfl

example :
    opportunityOutput (inputOnlyProblem [false]) = [CNFToken.t] := by
  rw [opportunityOutput_eq_nil_or_t]
  rfl

example :
    opportunityOutput (inputOnlyProblem [true]) = [CNFToken.t] := by
  rw [opportunityOutput_eq_nil_or_t]
  rfl

example :
    opportunityOutput (pairedProblem []) = [CNFToken.t] := by
  rw [opportunityOutput_eq_nil_or_t]
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
    workStep?
        BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.machine
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          { state :=
              BuilderCompleteHeader.HeaderController.doneExitState
            tape := tape }) =
      some
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
          { state := BuilderTokenAppender.machine.acceptState
            tape := tape }) :=
  BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.controller_done_skip_workStep
    tape

example (tape : WorkTape) :
    workStep?
        BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.machine
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          { state :=
              BuilderCompleteHeader.HeaderController.moreExitState
            tape := tape }) =
      some
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
          (BuilderTokenAppender.entryConfiguration .t tape)) :=
  BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.controller_more_launch_workStep
    tape

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
      (BuilderSecondConstraintPaddingOrUnaryOpportunityStep.rawTimeBound
        inputOnlyVerifier).eval input.length +
      624 + 24 * input.length +
      12 * (inputOnlyProblem input).FormulaWidth +
      12 * width (inputOnlyProblem input) +
      12 * widthRootPrefixLength (inputOnlyProblem input) +
      6 * widthWorkSteps (inputOnlyProblem input) +
      6 * targetWorkSteps (inputOnlyProblem input) :=
  rawTimeBound_eval (inputOnlyProblem input)

end PNP.Concrete.CookLevinBuilderSecondConstraintSecondPaddingOrUnaryOpportunityStepRegression
