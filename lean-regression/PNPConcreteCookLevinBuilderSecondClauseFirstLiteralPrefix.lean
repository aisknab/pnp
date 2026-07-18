import PNP

namespace PNP.Concrete.CookLevinBuilderSecondClauseFirstLiteralPrefixRegression

open PipelineTape PipelineStateNamespace
open CookLevin
open CookLevin.BuilderSecondClauseFirstLiteralPrefix

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

example : FalseTokenCursor.machine.rules.length = 113 :=
  FalseTokenCursor.rules_length

example : FirstLiteralSuffix.machine.rules.length = 235 :=
  FirstLiteralSuffix.rules_length

example (input : BitString) :
    (machine (inputOnlyProblem input)).rules.length =
      1610 +
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
            inputOnlyVerifier) :=
  rules_length (inputOnlyProblem input)

example : finalTokenSlot (inputOnlyProblem []) = 101 := rfl
example : finalTokenSlot (inputOnlyProblem [false]) = 197 := rfl
example : finalTokenSlot (inputOnlyProblem [true]) = 197 := rfl
example : finalTokenSlot
    (inputOnlyProblem [true, false, true]) = 485 := rfl
example : finalTokenSlot
    (pairedProblem [true, false, true]) = 6725 := rfl

example (input : BitString) :
    secondClauseFirstLiteralTokens (inputOnlyProblem input) =
      BuilderSecondClauseSeparatorStep.secondClauseStartTokens
          (inputOnlyProblem input) ++ [CNFToken.f, CNFToken.f] := by
  simp [secondClauseFirstLiteralTokens, firstTokenOutput, List.append_assoc]

example (input : BitString) :
    ∃ rest, encodeCNFTokens (inputOnlyProblem input).formula =
      secondClauseFirstLiteralTokens (inputOnlyProblem input) ++ rest :=
  secondClauseFirstLiteralTokens_eq_canonical_formula_prefix
    (inputOnlyProblem input)

example (input : BitString) :
    encodeTokenPairs
        (secondClauseFirstLiteralTokens (inputOnlyProblem input)) =
      (inputOnlyProblem input).encodedFormula.take
        (2 * ((inputOnlyProblem input).FormulaWidth + 15)) :=
  finalTokenBits_eq_encodedFormula_secondClauseFirstLiteral
    (inputOnlyProblem input)

example (input : BitString) :
    Represents (Tape.ofInput input) (finalTape (inputOnlyProblem input)) :=
  finalTape_represents (inputOnlyProblem input)

example (input : BitString) :
    (inputOnlyProblem input).formulaTokenSlotDirect
        (BuilderFirstClausePaddingRun.secondClauseStart
          (inputOnlyProblem input) + 1) = some (some CNFToken.f) :=
  firstLiteralSignSlot_direct_eq_f (inputOnlyProblem input)

example (input : BitString) :
    (inputOnlyProblem input).formulaTokenSlotDirect
        (BuilderFirstClausePaddingRun.secondClauseStart
          (inputOnlyProblem input) + 2) = some (some CNFToken.f) :=
  firstLiteralZeroTerminatorSlot_direct_eq_f (inputOnlyProblem input)

example (input : BitString) :
    (inputOnlyProblem input).formulaTokenSlotDirect
        (finalTokenSlot (inputOnlyProblem input)) = some (some CNFToken.f) :=
  nextTokenSlot_direct_eq_f (inputOnlyProblem input)

example (input : BitString) :
    workStep? (machine (inputOnlyProblem input))
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (BuilderSecondClauseSeparatorStep.finalConfiguration
            (inputOnlyProblem input))) =
      some (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration FirstLiteralSuffix.machine
          (BuilderSecondClauseSeparatorStep.finalTape
            (inputOnlyProblem input)))) :=
  prefixFirstLiteral_launch_workStep (inputOnlyProblem input)

example (input : BitString) :
    workStep? FalseTokenCursor.machine
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (firstAppenderFinalConfiguration (inputOnlyProblem input))) =
      some (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration
          BuilderDynamicTokenCursorStep.CursorAdvance.machine
          (firstAppenderFinalConfiguration (inputOnlyProblem input)).tape)) :=
  firstFalseTokenCursor_launch_workStep (inputOnlyProblem input)

example (input : BitString) :
    workStep? FirstLiteralSuffix.machine
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (firstFalseTokenCursorFinalConfiguration
            (inputOnlyProblem input))) =
      some (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration FalseTokenCursor.machine
          (firstFalseTokenCursorFinalConfiguration
            (inputOnlyProblem input)).tape)) :=
  firstLiteralSuffix_launch_workStep (inputOnlyProblem input)

example (input : BitString) :
    workStep? FalseTokenCursor.machine
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (secondAppenderFinalConfiguration (inputOnlyProblem input))) =
      some (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration
          BuilderDynamicTokenCursorStep.CursorAdvance.machine
          (secondAppenderFinalConfiguration (inputOnlyProblem input)).tape)) :=
  secondFalseTokenCursor_launch_workStep (inputOnlyProblem input)

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
    (rawTimeBound inputOnlyVerifier).eval input.length =
      (BuilderSecondClauseSeparatorStep.rawTimeBound inputOnlyVerifier).eval
          input.length + 564 + 48 * input.length +
        24 * (inputOnlyProblem input).FormulaWidth +
        24 * (BuilderSecondClauseSeparatorStep.cursorWord
          (inputOnlyProblem input)).length :=
  rawTimeBound_eval (inputOnlyProblem input)

example (input : BitString) :
    boundedDecide (compileWorkMachine (machine (inputOnlyProblem input)))
        ((rawTimeBound inputOnlyVerifier).eval input.length) input = .accept :=
  boundedDecide_compile_accept (inputOnlyProblem input)

example (input : BitString) :
    workBoundedDecide (machine (inputOnlyProblem input))
        (BuilderSecondClauseSeparatorStep.workSteps (inputOnlyProblem input))
        (rawInputWorkTape input) = .timeout :=
  prefixEndpoint_before_launch_timeout (inputOnlyProblem input)

example (input : BitString) :
    workBoundedDecide (machine (inputOnlyProblem input))
        (BuilderSecondClauseSeparatorStep.workSteps (inputOnlyProblem input) +
          1 + firstAppenderWorkSteps (inputOnlyProblem input))
        (rawInputWorkTape input) = .timeout :=
  firstAppenderEndpoint_before_cursor_launch_timeout (inputOnlyProblem input)

example (input : BitString) :
    workBoundedDecide (machine (inputOnlyProblem input))
        (BuilderSecondClauseSeparatorStep.workSteps (inputOnlyProblem input) +
          1 + firstAppenderWorkSteps (inputOnlyProblem input) + 1 +
          firstCursorWorkSteps (inputOnlyProblem input))
        (rawInputWorkTape input) = .timeout :=
  firstCursorEndpoint_before_secondAppender_launch_timeout
    (inputOnlyProblem input)

example (input : BitString) :
    workBoundedDecide (machine (inputOnlyProblem input))
        (BuilderSecondClauseSeparatorStep.workSteps (inputOnlyProblem input) +
          1 + firstFalseTokenCursorWorkSteps (inputOnlyProblem input) + 1 +
          secondAppenderWorkSteps (inputOnlyProblem input))
        (rawInputWorkTape input) = .timeout :=
  secondAppenderEndpoint_before_cursor_launch_timeout (inputOnlyProblem input)

example (input : BitString) :
    workBoundedDecide (machine (inputOnlyProblem input))
        (workSteps (inputOnlyProblem input) - 1)
        (rawInputWorkTape input) = .timeout :=
  work_one_step_short_timeout (inputOnlyProblem input)

example (fuel : Nat) (request : CNFToken)
    (left right : List WorkSymbol) :
    (let bad := BuilderTokenAppender.malformedTallyConfiguration
        request left right
     let component := renameConfiguration
        BuilderFirstClausePrefix.WorkChain.firstState bad
     let suffix := renameConfiguration
        BuilderFirstClausePrefix.WorkChain.firstState component
     let global := renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState suffix
     let result := workRun (machine (inputOnlyProblem [])) fuel global
     if result.state == (machine (inputOnlyProblem [])).acceptState then
       WorkVerdict.accept
     else if result.state == (machine (inputOnlyProblem [])).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  malformedFirstAppenderTally_timeout
    (inputOnlyProblem []) fuel request left right

example (fuel : Nat) (request : CNFToken)
    (left right : List WorkSymbol) :
    (let bad := BuilderTokenAppender.malformedOutputConfiguration
        request left right
     let component := renameConfiguration
        BuilderFirstClausePrefix.WorkChain.firstState bad
     let suffix := renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState component
     let global := renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState suffix
     let result := workRun (machine (inputOnlyProblem [])) fuel global
     if result.state == (machine (inputOnlyProblem [])).acceptState then
       WorkVerdict.accept
     else if result.state == (machine (inputOnlyProblem [])).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  malformedSecondAppenderOutput_timeout
    (inputOnlyProblem []) fuel request left right

example (fuel : Nat) (left right : List WorkSymbol) :
    (let bad := firstCursorGlobalConfiguration (inputOnlyProblem [])
        (BuilderDynamicTokenCursorStep.CursorAdvance.malformedScratchConfiguration
          left right)
     let result := workRun (machine (inputOnlyProblem [])) fuel bad
     if result.state == (machine (inputOnlyProblem [])).acceptState then
       WorkVerdict.accept
     else if result.state == (machine (inputOnlyProblem [])).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  malformedFirstCursorScratch_timeout (inputOnlyProblem []) fuel left right

example (fuel : Nat) (left right : List WorkSymbol) :
    (let bad := secondCursorGlobalConfiguration (inputOnlyProblem [])
        (BuilderDynamicTokenCursorStep.CursorAdvance.malformedScratchConfiguration
          left right)
     let result := workRun (machine (inputOnlyProblem [])) fuel bad
     if result.state == (machine (inputOnlyProblem [])).acceptState then
       WorkVerdict.accept
     else if result.state == (machine (inputOnlyProblem [])).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  malformedSecondCursorScratch_timeout (inputOnlyProblem []) fuel left right

end PNP.Concrete.CookLevinBuilderSecondClauseFirstLiteralPrefixRegression
