import PNP

namespace PNP.Concrete.CookLevinBuilderSecondClauseSecondLiteralPrefixRegression

open PipelineTape PipelineStateNamespace
open CookLevin
open CookLevin.BuilderSecondClauseSecondLiteralPrefix

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

example : TrueTokenCursor.machine.rules.length = 113 :=
  TrueTokenCursor.rules_length

example : TrueFalseSuffix.machine.rules.length = 235 :=
  TrueFalseSuffix.rules_length

example : SecondLiteralSuffix.machine.rules.length = 357 :=
  SecondLiteralSuffix.rules_length

example (input : BitString) :
    (machine (inputOnlyProblem input)).rules.length =
      1976 +
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

example : finalTokenSlot (inputOnlyProblem []) = 104 := rfl
example : finalTokenSlot (inputOnlyProblem [false]) = 200 := rfl
example : finalTokenSlot (inputOnlyProblem [true]) = 200 := rfl
example : finalTokenSlot
    (inputOnlyProblem [true, false, true]) = 488 := rfl
example : finalTokenSlot
    (inputOnlyProblem [false, false, false, false]) =
      finalTokenSlot (inputOnlyProblem [true, true, true, true]) := rfl
example : finalTokenSlot
    (pairedProblem [true, false, true]) = 6728 := rfl

example (input : BitString) :
    secondClauseSecondLiteralTokens (inputOnlyProblem input) =
      BuilderSecondClauseFirstLiteralPrefix.secondClauseFirstLiteralTokens
          (inputOnlyProblem input) ++
        [CNFToken.f, CNFToken.t, CNFToken.f] := by
  simp [secondClauseSecondLiteralTokens, unaryTokenOutput, signTokenOutput,
    List.append_assoc]

example (input : BitString) :
    ∃ rest, encodeCNFTokens (inputOnlyProblem input).formula =
      secondClauseSecondLiteralTokens (inputOnlyProblem input) ++ rest :=
  secondClauseSecondLiteralTokens_eq_canonical_formula_prefix
    (inputOnlyProblem input)

example (input : BitString) :
    encodeTokenPairs
        (secondClauseSecondLiteralTokens (inputOnlyProblem input)) =
      (inputOnlyProblem input).encodedFormula.take
        (2 * ((inputOnlyProblem input).FormulaWidth + 18)) :=
  finalTokenBits_eq_encodedFormula_secondClauseSecondLiteral
    (inputOnlyProblem input)

example (input : BitString) :
    Represents (Tape.ofInput input) (finalTape (inputOnlyProblem input)) :=
  finalTape_represents (inputOnlyProblem input)

example (input : BitString) :
    (inputOnlyProblem input).formulaTokenSlotDirect
        (BuilderFirstClausePaddingRun.secondClauseStart
          (inputOnlyProblem input) + 3) = some (some CNFToken.f) :=
  secondLiteralSignSlot_direct_eq_f (inputOnlyProblem input)

example (input : BitString) :
    (inputOnlyProblem input).formulaTokenSlotDirect
        (BuilderFirstClausePaddingRun.secondClauseStart
          (inputOnlyProblem input) + 4) = some (some CNFToken.t) :=
  secondLiteralUnaryUnitSlot_direct_eq_t (inputOnlyProblem input)

example (input : BitString) :
    (inputOnlyProblem input).formulaTokenSlotDirect
        (BuilderFirstClausePaddingRun.secondClauseStart
          (inputOnlyProblem input) + 5) = some (some CNFToken.f) :=
  secondLiteralTerminatorSlot_direct_eq_f (inputOnlyProblem input)

example (input : BitString) :
    (inputOnlyProblem input).formulaTokenSlotDirect
        (finalTokenSlot (inputOnlyProblem input)) =
      some (some CNFToken.finish) :=
  nextTokenSlot_direct_eq_finish (inputOnlyProblem input)

example (input : BitString) :
    workStep? (machine (inputOnlyProblem input))
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (BuilderSecondClauseFirstLiteralPrefix.finalConfiguration
            (inputOnlyProblem input))) =
      some (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration SecondLiteralSuffix.machine
          (BuilderSecondClauseFirstLiteralPrefix.finalTape
            (inputOnlyProblem input)))) :=
  prefixSecondLiteral_launch_workStep (inputOnlyProblem input)

example (input : BitString) :
    workStep?
        BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (firstAppenderFinalConfiguration (inputOnlyProblem input))) =
      some (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration
          BuilderDynamicTokenCursorStep.CursorAdvance.machine
          (firstAppenderFinalConfiguration (inputOnlyProblem input)).tape)) :=
  signAppenderCursor_launch_workStep (inputOnlyProblem input)

example (input : BitString) :
    workStep? SecondLiteralSuffix.machine
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (signTokenCursorFinalConfiguration (inputOnlyProblem input))) =
      some (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration TrueFalseSuffix.machine
          (signTokenCursorFinalConfiguration (inputOnlyProblem input)).tape)) :=
  secondLiteralSuffix_launch_workStep (inputOnlyProblem input)

example (input : BitString) :
    workStep? TrueTokenCursor.machine
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (secondAppenderFinalConfiguration (inputOnlyProblem input))) =
      some (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration
          BuilderDynamicTokenCursorStep.CursorAdvance.machine
          (secondAppenderFinalConfiguration (inputOnlyProblem input)).tape)) :=
  unaryAppenderCursor_launch_workStep (inputOnlyProblem input)

example (input : BitString) :
    workStep? TrueFalseSuffix.machine
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (unaryTokenCursorFinalConfiguration (inputOnlyProblem input))) =
      some (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration
          BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine
          (unaryTokenCursorFinalConfiguration (inputOnlyProblem input)).tape)) :=
  trueFalseSuffix_launch_workStep (inputOnlyProblem input)

example (input : BitString) :
    workStep?
        BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (thirdAppenderFinalConfiguration (inputOnlyProblem input))) =
      some (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration
          BuilderDynamicTokenCursorStep.CursorAdvance.machine
          (thirdAppenderFinalConfiguration (inputOnlyProblem input)).tape)) :=
  terminatorAppenderCursor_launch_workStep (inputOnlyProblem input)

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
      (BuilderSecondClauseFirstLiteralPrefix.rawTimeBound
          inputOnlyVerifier).eval input.length + 1026 + 72 * input.length +
        36 * (inputOnlyProblem input).FormulaWidth +
        36 * (BuilderSecondClauseSeparatorStep.cursorWord
          (inputOnlyProblem input)).length :=
  rawTimeBound_eval (inputOnlyProblem input)

example (input : BitString) :
    boundedDecide (compileWorkMachine (machine (inputOnlyProblem input)))
        ((rawTimeBound inputOnlyVerifier).eval input.length) input = .accept :=
  boundedDecide_compile_accept (inputOnlyProblem input)

example (input : BitString) :
    workBoundedDecide (machine (inputOnlyProblem input))
        (BuilderSecondClauseFirstLiteralPrefix.workSteps
          (inputOnlyProblem input))
        (rawInputWorkTape input) = .timeout :=
  prefixEndpoint_before_launch_timeout (inputOnlyProblem input)

example (input : BitString) :
    workBoundedDecide (machine (inputOnlyProblem input))
        (BuilderSecondClauseFirstLiteralPrefix.workSteps
            (inputOnlyProblem input) + 1 +
          firstAppenderWorkSteps (inputOnlyProblem input))
        (rawInputWorkTape input) = .timeout :=
  signAppenderEndpoint_before_cursor_launch_timeout (inputOnlyProblem input)

example (input : BitString) :
    workBoundedDecide (machine (inputOnlyProblem input))
        (BuilderSecondClauseFirstLiteralPrefix.workSteps
            (inputOnlyProblem input) + 1 +
          firstAppenderWorkSteps (inputOnlyProblem input) + 1 +
          firstCursorWorkSteps (inputOnlyProblem input))
        (rawInputWorkTape input) = .timeout :=
  signCursorEndpoint_before_unary_launch_timeout (inputOnlyProblem input)

example (input : BitString) :
    workBoundedDecide (machine (inputOnlyProblem input))
        (BuilderSecondClauseFirstLiteralPrefix.workSteps
            (inputOnlyProblem input) + 1 +
          firstAppenderWorkSteps (inputOnlyProblem input) + 1 +
          firstCursorWorkSteps (inputOnlyProblem input) + 1 +
          secondAppenderWorkSteps (inputOnlyProblem input))
        (rawInputWorkTape input) = .timeout :=
  unaryAppenderEndpoint_before_cursor_launch_timeout (inputOnlyProblem input)

example (input : BitString) :
    workBoundedDecide (machine (inputOnlyProblem input))
        (BuilderSecondClauseFirstLiteralPrefix.workSteps
            (inputOnlyProblem input) + 1 +
          firstAppenderWorkSteps (inputOnlyProblem input) + 1 +
          firstCursorWorkSteps (inputOnlyProblem input) + 1 +
          secondAppenderWorkSteps (inputOnlyProblem input) + 1 +
          secondCursorWorkSteps (inputOnlyProblem input))
        (rawInputWorkTape input) = .timeout :=
  unaryCursorEndpoint_before_terminator_launch_timeout
    (inputOnlyProblem input)

example (input : BitString) :
    workBoundedDecide (machine (inputOnlyProblem input))
        (BuilderSecondClauseFirstLiteralPrefix.workSteps
            (inputOnlyProblem input) + 1 +
          firstAppenderWorkSteps (inputOnlyProblem input) + 1 +
          firstCursorWorkSteps (inputOnlyProblem input) + 1 +
          secondAppenderWorkSteps (inputOnlyProblem input) + 1 +
          secondCursorWorkSteps (inputOnlyProblem input) + 1 +
          thirdAppenderWorkSteps (inputOnlyProblem input))
        (rawInputWorkTape input) = .timeout :=
  terminatorAppenderEndpoint_before_cursor_launch_timeout
    (inputOnlyProblem input)

example (input : BitString) :
    workBoundedDecide (machine (inputOnlyProblem input))
        (workSteps (inputOnlyProblem input) - 1)
        (rawInputWorkTape input) = .timeout :=
  work_one_step_short_timeout (inputOnlyProblem input)

example (fuel : Nat) (left right : List WorkSymbol) :
    (let bad := signCursorGlobalConfiguration (inputOnlyProblem [])
        (BuilderDynamicTokenCursorStep.CursorAdvance.malformedScratchConfiguration
          left right)
     let result := workRun (machine (inputOnlyProblem [])) fuel bad
     if result.state == (machine (inputOnlyProblem [])).acceptState then
       WorkVerdict.accept
     else if result.state == (machine (inputOnlyProblem [])).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  malformedSignCursorScratch_timeout (inputOnlyProblem []) fuel left right

example (fuel : Nat) (left right : List WorkSymbol) :
    (let bad := unaryCursorGlobalConfiguration (inputOnlyProblem [])
        (BuilderDynamicTokenCursorStep.CursorAdvance.malformedScratchConfiguration
          left right)
     let result := workRun (machine (inputOnlyProblem [])) fuel bad
     if result.state == (machine (inputOnlyProblem [])).acceptState then
       WorkVerdict.accept
     else if result.state == (machine (inputOnlyProblem [])).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  malformedUnaryCursorScratch_timeout (inputOnlyProblem []) fuel left right

example (fuel : Nat) (left right : List WorkSymbol) :
    (let bad := terminatorCursorGlobalConfiguration (inputOnlyProblem [])
        (BuilderDynamicTokenCursorStep.CursorAdvance.malformedScratchConfiguration
          left right)
     let result := workRun (machine (inputOnlyProblem [])) fuel bad
     if result.state == (machine (inputOnlyProblem [])).acceptState then
       WorkVerdict.accept
     else if result.state == (machine (inputOnlyProblem [])).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  malformedTerminatorCursorScratch_timeout
    (inputOnlyProblem []) fuel left right

#check malformedSignAppenderTally_timeout
#check malformedUnaryAppenderTally_timeout
#check malformedTerminatorAppenderTally_timeout
#check malformedSignAppenderOutput_timeout
#check malformedUnaryAppenderOutput_timeout
#check malformedTerminatorAppenderOutput_timeout

end PNP.Concrete.CookLevinBuilderSecondClauseSecondLiteralPrefixRegression
