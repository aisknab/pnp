import PNP

namespace PNP.Concrete.CookLevinBuilderSecondConstraintFirstLiteralTerminatorStepRegression

open PipelineTape PipelineStateNamespace
open CookLevin
open CookLevin.BuilderSecondConstraintFirstLiteralTerminatorStep

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
    BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine.rules.length =
      113 :=
  BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.rules_length

example (input : BitString) :
    (machine (inputOnlyProblem input)).rules.length =
      5164 +
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

example : finalTokenSlot (inputOnlyProblem []) = 4514 := rfl
example : finalTokenSlot (inputOnlyProblem [false]) = 22222 := rfl
example : finalTokenSlot (inputOnlyProblem [true]) = 22222 := rfl
example : finalTokenSlot
    (inputOnlyProblem [true, false, true]) = 167270 := rfl
example : finalTokenSlot
    (pairedProblem [true, false, true]) = 41459450 := rfl
example : finalTokenSlot
    (inputOnlyProblem [false, false, false, false]) = 344530 := rfl
example : finalTokenSlot
    (inputOnlyProblem [true, true, true, true]) = 344530 := rfl

example (input : BitString) :
    workSteps (inputOnlyProblem input) =
      BuilderSecondConstraintFirstLiteralThirdUnaryUnitStep.workSteps
          (inputOnlyProblem input) + 1 +
        appenderWorkSteps (inputOnlyProblem input) + 1 +
        cursorWorkSteps (inputOnlyProblem input) := by
  simp [workSteps, suffixWorkSteps, Nat.add_assoc]

example (input : BitString) :
    (rawTimeBound inputOnlyVerifier).eval input.length =
      (BuilderSecondConstraintFirstLiteralThirdUnaryUnitStep.rawTimeBound inputOnlyVerifier).eval
          input.length + 594 +
        24 * input.length + 12 * (inputOnlyProblem input).FormulaWidth +
        12 * (cursorWord (inputOnlyProblem input)).length :=
  rawTimeBound_eval (inputOnlyProblem input)

example (input : BitString) :
    secondConstraintFirstLiteralTerminatorTokens (inputOnlyProblem input) =
      BuilderSecondConstraintFirstLiteralThirdUnaryUnitStep.secondConstraintFirstLiteralThirdUnaryTokens
          (inputOnlyProblem input) ++ [CNFToken.f] := rfl

example (input : BitString) :
    ∃ rest, encodeCNFTokens (inputOnlyProblem input).formula =
      secondConstraintFirstLiteralTerminatorTokens (inputOnlyProblem input) ++ rest :=
  secondConstraintFirstLiteralTerminatorTokens_eq_canonical_formula_prefix
    (inputOnlyProblem input)

example (input : BitString) :
    encodeTokenPairs (secondConstraintFirstLiteralTerminatorTokens (inputOnlyProblem input)) =
      (inputOnlyProblem input).encodedFormula.take
        (2 * ((inputOnlyProblem input).FormulaWidth + 42)) :=
  finalTokenBits_eq_encodedFormula_secondConstraintFirstLiteralTerminator
    (inputOnlyProblem input)

example (input : BitString) :
    Represents (Tape.ofInput input) (finalTape (inputOnlyProblem input)) :=
  finalTape_represents (inputOnlyProblem input)

example (input : BitString) :
    finalTape (inputOnlyProblem input) =
      BuilderTokenAppender.workspaceTape input
        (finalOutside (inputOnlyProblem input))
        (BuilderSecondConstraintFirstLiteralThirdUnaryUnitStep.secondConstraintFirstLiteralThirdUnaryTokens
          (inputOnlyProblem input) ++ [CNFToken.f]) := rfl

example (input : BitString) :
    VerifierTableauProblem.FormulaTokenCursor.step
        (inputOnlyProblem input)
        ⟨BuilderSecondConstraintFirstLiteralThirdUnaryUnitStep.finalTokenSlot
          (inputOnlyProblem input)⟩ =
      some (some CNFToken.f,
        ⟨BuilderSecondConstraintFirstLiteralThirdUnaryUnitStep.finalTokenSlot
          (inputOnlyProblem input) + 1⟩) :=
  specification_terminator_step (inputOnlyProblem input)

example (input : BitString) :
    (inputOnlyProblem input).formulaTokenSlotDirect
        (finalTokenSlot (inputOnlyProblem input)) =
      some (some
        (if (inputOnlyProblem input).dimensions.tapeWidth
              (inputOnlyProblem input).tableauInputMode = 1
          then CNFToken.finish else CNFToken.t)) :=
  nextTokenSlot_direct_eq_finish_or_t (inputOnlyProblem input)

example :
    (inputOnlyProblem []).formulaTokenSlotDirect
        (finalTokenSlot (inputOnlyProblem [])) =
      some (some CNFToken.finish) := by
  have hWidth :
      (inputOnlyProblem []).dimensions.tapeWidth
          (inputOnlyProblem []).tableauInputMode = 1 := by
    rfl
  rw [nextTokenSlot_direct_eq_finish_or_t, hWidth]
  rfl

example :
    (inputOnlyProblem [false]).formulaTokenSlotDirect
        (finalTokenSlot (inputOnlyProblem [false])) =
      some (some CNFToken.t) := by
  have hWidth :
      (inputOnlyProblem [false]).dimensions.tapeWidth
          (inputOnlyProblem [false]).tableauInputMode = 2 := by
    rfl
  rw [nextTokenSlot_direct_eq_finish_or_t, hWidth]
  rfl

example :
    (inputOnlyProblem [true]).formulaTokenSlotDirect
        (finalTokenSlot (inputOnlyProblem [true])) =
      some (some CNFToken.t) := by
  have hWidth :
      (inputOnlyProblem [true]).dimensions.tapeWidth
          (inputOnlyProblem [true]).tableauInputMode = 2 := by
    rfl
  rw [nextTokenSlot_direct_eq_finish_or_t, hWidth]
  rfl

example :
    (pairedProblem []).formulaTokenSlotDirect
        (finalTokenSlot (pairedProblem [])) =
      some (some CNFToken.t) := by
  have hWidth :
      (pairedProblem []).dimensions.tapeWidth
          (pairedProblem []).tableauInputMode = 5 := by
    rfl
  rw [nextTokenSlot_direct_eq_finish_or_t, hWidth]
  rfl

example :
    (pairedProblem [true]).formulaTokenSlotDirect
        (finalTokenSlot (pairedProblem [true])) =
      some (some CNFToken.t) := by
  have hWidth :
      (pairedProblem [true]).dimensions.tapeWidth
          (pairedProblem [true]).tableauInputMode = 9 := by
    rfl
  rw [nextTokenSlot_direct_eq_finish_or_t, hWidth]
  rfl

example (input : BitString) :
    VerifierTableauProblem.FormulaTokenCursor.step
        (inputOnlyProblem input) ⟨finalTokenSlot (inputOnlyProblem input)⟩ =
      some (some
        (if (inputOnlyProblem input).dimensions.tapeWidth
              (inputOnlyProblem input).tableauInputMode = 1
          then CNFToken.finish else CNFToken.t),
        ⟨finalTokenSlot (inputOnlyProblem input) + 1⟩) :=
  specification_next_step (inputOnlyProblem input)

example (input : BitString) :
    workStep? (machine (inputOnlyProblem input))
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (BuilderSecondConstraintFirstLiteralThirdUnaryUnitStep.finalConfiguration
            (inputOnlyProblem input))) =
      some (renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration
          BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine
          (BuilderSecondConstraintFirstLiteralThirdUnaryUnitStep.finalTape
            (inputOnlyProblem input)))) :=
  prefixTerminator_launch_workStep (inputOnlyProblem input)

example (input : BitString) :
    workStep? BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (appenderFinalConfiguration (inputOnlyProblem input))) =
      some (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration
          BuilderDynamicTokenCursorStep.CursorAdvance.machine
          (appenderFinalConfiguration (inputOnlyProblem input)).tape)) :=
  falseTokenCursor_launch_workStep (inputOnlyProblem input)

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
        (BuilderSecondConstraintFirstLiteralThirdUnaryUnitStep.workSteps
          (inputOnlyProblem input))
        (rawInputWorkTape input) = .timeout :=
  prefixEndpoint_before_launch_timeout (inputOnlyProblem input)

example (input : BitString) :
    workBoundedDecide (machine (inputOnlyProblem input))
        (BuilderSecondConstraintFirstLiteralThirdUnaryUnitStep.workSteps
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

end PNP.Concrete.CookLevinBuilderSecondConstraintFirstLiteralTerminatorStepRegression
