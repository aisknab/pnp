import PNP

namespace PNP.Concrete.CookLevinBuilderSecondConstraintFirstLiteralSignStepRegression

open PipelineTape PipelineStateNamespace
open CookLevin
open CookLevin.BuilderSecondConstraintFirstLiteralSignStep

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
    BuilderSecondClauseSecondLiteralPrefix.TrueTokenCursor.machine.rules.length =
      113 :=
  BuilderSecondClauseSecondLiteralPrefix.TrueTokenCursor.rules_length

example (input : BitString) :
    (machine (inputOnlyProblem input)).rules.length =
      4676 +
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
          (BuilderFifthClausePaddingRun.paddingPolynomial
            inputOnlyVerifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderFifthClausePaddingRun.sixthClauseSlotStartPolynomial
            inputOnlyVerifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderFirstConstraintPaddingRun.paddingPolynomial
            inputOnlyVerifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderFirstConstraintPaddingRun.secondConstraintStartPolynomial
            inputOnlyVerifier) :=
  rules_length (inputOnlyProblem input)

example : finalTokenSlot (inputOnlyProblem []) = 4510 := rfl
example : finalTokenSlot (inputOnlyProblem [false]) = 22218 := rfl
example : finalTokenSlot (inputOnlyProblem [true]) = 22218 := rfl
example : finalTokenSlot
    (inputOnlyProblem [true, false, true]) = 167266 := rfl
example : finalTokenSlot
    (pairedProblem [true, false, true]) = 41459446 := rfl
example : finalTokenSlot
    (inputOnlyProblem [false, false, false, false]) = 344526 := rfl
example : finalTokenSlot
    (inputOnlyProblem [true, true, true, true]) = 344526 := rfl

example (input : BitString) :
    workSteps (inputOnlyProblem input) =
      BuilderSecondConstraintSeparatorStep.workSteps
          (inputOnlyProblem input) + 1 +
        appenderWorkSteps (inputOnlyProblem input) + 1 +
        cursorWorkSteps (inputOnlyProblem input) := by
  simp [workSteps, suffixWorkSteps, Nat.add_assoc]

example (input : BitString) :
    (rawTimeBound inputOnlyVerifier).eval input.length =
      (BuilderSecondConstraintSeparatorStep.rawTimeBound inputOnlyVerifier).eval
          input.length + 546 +
        24 * input.length + 12 * (inputOnlyProblem input).FormulaWidth +
        12 * (cursorWord (inputOnlyProblem input)).length :=
  rawTimeBound_eval (inputOnlyProblem input)

example (input : BitString) :
    secondConstraintFirstLiteralSignTokens (inputOnlyProblem input) =
      BuilderSecondConstraintSeparatorStep.secondConstraintStartTokens
          (inputOnlyProblem input) ++ [CNFToken.t] := rfl

example (input : BitString) :
    ∃ rest, encodeCNFTokens (inputOnlyProblem input).formula =
      secondConstraintFirstLiteralSignTokens (inputOnlyProblem input) ++ rest :=
  secondConstraintFirstLiteralSignTokens_eq_canonical_formula_prefix
    (inputOnlyProblem input)

example (input : BitString) :
    encodeTokenPairs (secondConstraintFirstLiteralSignTokens (inputOnlyProblem input)) =
      (inputOnlyProblem input).encodedFormula.take
        (2 * ((inputOnlyProblem input).FormulaWidth + 38)) :=
  finalTokenBits_eq_encodedFormula_secondConstraintFirstLiteralSign
    (inputOnlyProblem input)

example (input : BitString) :
    Represents (Tape.ofInput input) (finalTape (inputOnlyProblem input)) :=
  finalTape_represents (inputOnlyProblem input)

example (input : BitString) :
    finalTape (inputOnlyProblem input) =
      BuilderTokenAppender.workspaceTape input
        (finalOutside (inputOnlyProblem input))
        (BuilderSecondConstraintSeparatorStep.secondConstraintStartTokens
          (inputOnlyProblem input) ++ [CNFToken.t]) := rfl

example (input : BitString) :
    VerifierTableauProblem.FormulaTokenCursor.step
        (inputOnlyProblem input)
        ⟨BuilderSecondConstraintSeparatorStep.finalTokenSlot
          (inputOnlyProblem input)⟩ =
      some (some CNFToken.t,
        ⟨BuilderSecondConstraintSeparatorStep.finalTokenSlot
          (inputOnlyProblem input) + 1⟩) :=
  specification_sign_step (inputOnlyProblem input)

example (input : BitString) :
    (inputOnlyProblem input).formulaTokenSlotDirect
        (finalTokenSlot (inputOnlyProblem input)) =
      some (some CNFToken.t) :=
  nextTokenSlot_direct_eq_t (inputOnlyProblem input)

example (input : BitString) :
    VerifierTableauProblem.FormulaTokenCursor.step
        (inputOnlyProblem input) ⟨finalTokenSlot (inputOnlyProblem input)⟩ =
      some (some CNFToken.t,
        ⟨finalTokenSlot (inputOnlyProblem input) + 1⟩) :=
  specification_next_step (inputOnlyProblem input)

example (input : BitString) :
    workStep? (machine (inputOnlyProblem input))
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (BuilderSecondConstraintSeparatorStep.finalConfiguration
            (inputOnlyProblem input))) =
      some (renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration
          BuilderSecondClauseSecondLiteralPrefix.TrueTokenCursor.machine
          (BuilderSecondConstraintSeparatorStep.finalTape
            (inputOnlyProblem input)))) :=
  prefixSign_launch_workStep (inputOnlyProblem input)

example (input : BitString) :
    workStep? BuilderSecondClauseSecondLiteralPrefix.TrueTokenCursor.machine
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (appenderFinalConfiguration (inputOnlyProblem input))) =
      some (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration
          BuilderDynamicTokenCursorStep.CursorAdvance.machine
          (appenderFinalConfiguration (inputOnlyProblem input)).tape)) :=
  trueTokenCursor_launch_workStep (inputOnlyProblem input)

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
        (BuilderSecondConstraintSeparatorStep.workSteps
          (inputOnlyProblem input))
        (rawInputWorkTape input) = .timeout :=
  prefixEndpoint_before_launch_timeout (inputOnlyProblem input)

example (input : BitString) :
    workBoundedDecide (machine (inputOnlyProblem input))
        (BuilderSecondConstraintSeparatorStep.workSteps
          (inputOnlyProblem input) + 1 +
          appenderWorkSteps (inputOnlyProblem input))
        (rawInputWorkTape input) = .timeout :=
  appenderEndpoint_before_cursor_launch_timeout (inputOnlyProblem input)

example (input : BitString) :
    workBoundedDecide (machine (inputOnlyProblem input))
        (workSteps (inputOnlyProblem input) - 1)
        (rawInputWorkTape input) = .timeout :=
  work_one_step_short_timeout (inputOnlyProblem input)

example (fuel : Nat) (request : CNFToken)
    (left right : List WorkSymbol) :
    (let config := renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (BuilderTokenAppender.malformedTallyConfiguration
            request left right))
     let result := workRun (machine (inputOnlyProblem [])) fuel config
     if result.state == (machine (inputOnlyProblem [])).acceptState then
       WorkVerdict.accept
     else if result.state == (machine (inputOnlyProblem [])).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  malformedAppenderTally_timeout (inputOnlyProblem []) fuel request left right

example (fuel : Nat) (request : CNFToken)
    (left right : List WorkSymbol) :
    (let config := renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (BuilderTokenAppender.malformedOutputConfiguration
            request left right))
     let result := workRun (machine (inputOnlyProblem [])) fuel config
     if result.state == (machine (inputOnlyProblem [])).acceptState then
       WorkVerdict.accept
     else if result.state == (machine (inputOnlyProblem [])).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  malformedAppenderOutput_timeout (inputOnlyProblem []) fuel request left right

example (fuel : Nat) (left right : List WorkSymbol) :
    (let config := renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
          (BuilderDynamicTokenCursorStep.CursorAdvance.malformedScratchConfiguration
            left right))
     let result := workRun (machine (inputOnlyProblem [])) fuel config
     if result.state == (machine (inputOnlyProblem [])).acceptState then
       WorkVerdict.accept
     else if result.state == (machine (inputOnlyProblem [])).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  malformedCursorScratch_timeout (inputOnlyProblem []) fuel left right

end PNP.Concrete.CookLevinBuilderSecondConstraintFirstLiteralSignStepRegression
