import PNP

namespace PNP.Concrete.CookLevinBuilderThirdClauseSecondLiteralPrefixRegression

open PipelineTape PipelineStateNamespace
open CookLevin
open CookLevin.BuilderThirdClauseSecondLiteralPrefix

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

example : TrueTrueFalseSuffix.machine.rules.length = 357 :=
  TrueTrueFalseSuffix.rules_length

example : SecondLiteralSuffix.machine.rules.length = 479 :=
  SecondLiteralSuffix.rules_length

example (input : BitString) :
    (machine (inputOnlyProblem input)).rules.length =
      3004 +
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
            inputOnlyVerifier) :=
  rules_length (inputOnlyProblem input)

example : finalTokenSlot (inputOnlyProblem []) = 195 := rfl
example : finalTokenSlot (inputOnlyProblem [false]) = 383 := rfl
example : finalTokenSlot (inputOnlyProblem [true]) = 383 := rfl
example : finalTokenSlot
    (inputOnlyProblem [true, false, true]) = 951 := rfl
example : finalTokenSlot
    (pairedProblem [true, false, true]) = 13371 := rfl
example : finalTokenSlot
    (inputOnlyProblem [false, false, false, false]) = 1331 := rfl
example : finalTokenSlot
    (inputOnlyProblem [true, true, true, true]) = 1331 := rfl

example : workSteps (inputOnlyProblem []) = 479754 := rfl
example : workSteps (inputOnlyProblem [false]) = 1562946 := rfl
example : workSteps (inputOnlyProblem [true]) = 1562946 := rfl
example : workSteps
    (inputOnlyProblem [true, false, true]) = 8413543 := rfl

example : (rawTimeBound inputOnlyVerifier).eval 0 = 2880675 := rfl
example : (rawTimeBound inputOnlyVerifier).eval 1 = 9382524 := rfl
example : (rawTimeBound inputOnlyVerifier).eval 3 = 50493114 := rfl
example : (rawTimeBound inputOnlyVerifier).eval 4 = 95695647 := rfl
example : (rawTimeBound pairedVerifier).eval 3 = 8715970440 := rfl

example (input : BitString) :
    thirdClauseSecondLiteralTokens (inputOnlyProblem input) =
      BuilderThirdClauseFirstLiteralPrefix.thirdClauseFirstLiteralTokens
          (inputOnlyProblem input) ++
        [CNFToken.f, CNFToken.t, CNFToken.t, CNFToken.f] := by
  simp [thirdClauseSecondLiteralTokens, secondUnaryTokenOutput,
    firstUnaryTokenOutput, signTokenOutput, List.append_assoc]

example (input : BitString) :
    ∃ rest, encodeCNFTokens (inputOnlyProblem input).formula =
      thirdClauseSecondLiteralTokens (inputOnlyProblem input) ++ rest :=
  thirdClauseSecondLiteralTokens_eq_canonical_formula_prefix
    (inputOnlyProblem input)

example (input : BitString) :
    encodeTokenPairs
        (thirdClauseSecondLiteralTokens (inputOnlyProblem input)) =
      (inputOnlyProblem input).encodedFormula.take
        (2 * ((inputOnlyProblem input).FormulaWidth + 26)) :=
  finalTokenBits_eq_encodedFormula_thirdClauseSecondLiteral
    (inputOnlyProblem input)

example (input : BitString) :
    Represents (Tape.ofInput input) (finalTape (inputOnlyProblem input)) :=
  finalTape_represents (inputOnlyProblem input)

example (input : BitString) :
    (inputOnlyProblem input).formulaTokenSlotDirect
        (BuilderSecondClausePaddingRun.thirdClauseStart
          (inputOnlyProblem input) + 3) = some (some CNFToken.f) :=
  secondLiteralSignSlot_direct_eq_f (inputOnlyProblem input)

example (input : BitString) :
    (inputOnlyProblem input).formulaTokenSlotDirect
        (BuilderSecondClausePaddingRun.thirdClauseStart
          (inputOnlyProblem input) + 4) = some (some CNFToken.t) :=
  secondLiteralFirstUnaryUnitSlot_direct_eq_t (inputOnlyProblem input)

example (input : BitString) :
    (inputOnlyProblem input).formulaTokenSlotDirect
        (BuilderSecondClausePaddingRun.thirdClauseStart
          (inputOnlyProblem input) + 5) = some (some CNFToken.t) :=
  secondLiteralSecondUnaryUnitSlot_direct_eq_t (inputOnlyProblem input)

example (input : BitString) :
    (inputOnlyProblem input).formulaTokenSlotDirect
        (BuilderSecondClausePaddingRun.thirdClauseStart
          (inputOnlyProblem input) + 6) = some (some CNFToken.f) :=
  secondLiteralTerminatorSlot_direct_eq_f (inputOnlyProblem input)

example (input : BitString) :
    (inputOnlyProblem input).formulaTokenSlotDirect
        (finalTokenSlot (inputOnlyProblem input)) =
      some (some CNFToken.finish) :=
  nextTokenSlot_direct_eq_finish (inputOnlyProblem input)

example (input : BitString) :
    workStep? (machine (inputOnlyProblem input))
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (BuilderThirdClauseFirstLiteralPrefix.finalConfiguration
            (inputOnlyProblem input))) =
      some (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration SecondLiteralSuffix.machine
          (BuilderThirdClauseFirstLiteralPrefix.finalTape
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
    workStep? TrueTokenCursor.machine
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (secondAppenderFinalConfiguration (inputOnlyProblem input))) =
      some (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration
          BuilderDynamicTokenCursorStep.CursorAdvance.machine
          (secondAppenderFinalConfiguration (inputOnlyProblem input)).tape)) :=
  unaryAppenderCursor_launch_workStep (inputOnlyProblem input)

example (input : BitString) :
    workStep? TrueTokenCursor.machine
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (thirdAppenderFinalConfiguration (inputOnlyProblem input))) =
      some (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration
          BuilderDynamicTokenCursorStep.CursorAdvance.machine
          (thirdAppenderFinalConfiguration (inputOnlyProblem input)).tape)) :=
  secondUnaryAppenderCursor_launch_workStep (inputOnlyProblem input)

example (input : BitString) :
    workStep?
        BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (fourthAppenderFinalConfiguration (inputOnlyProblem input))) =
      some (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration
          BuilderDynamicTokenCursorStep.CursorAdvance.machine
          (fourthAppenderFinalConfiguration (inputOnlyProblem input)).tape)) :=
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
      (BuilderThirdClauseFirstLiteralPrefix.rawTimeBound
          inputOnlyVerifier).eval input.length + 1752 +
        96 * input.length + 48 * (inputOnlyProblem input).FormulaWidth +
        48 * (BuilderThirdClauseSeparatorStep.cursorWord
          (inputOnlyProblem input)).length :=
  rawTimeBound_eval (inputOnlyProblem input)

example (input : BitString) :
    boundedDecide (compileWorkMachine (machine (inputOnlyProblem input)))
        ((rawTimeBound inputOnlyVerifier).eval input.length) input = .accept :=
  boundedDecide_compile_accept (inputOnlyProblem input)

example (input : BitString) :
    workBoundedDecide (machine (inputOnlyProblem input))
        (BuilderThirdClauseFirstLiteralPrefix.workSteps
          (inputOnlyProblem input))
        (rawInputWorkTape input) = .timeout :=
  prefixEndpoint_before_launch_timeout (inputOnlyProblem input)

example (input : BitString) :
    workBoundedDecide (machine (inputOnlyProblem input))
        (BuilderThirdClauseFirstLiteralPrefix.workSteps
          (inputOnlyProblem input) + 1 +
          signTokenCursorWorkSteps (inputOnlyProblem input) + 1 +
          unaryTokenCursorWorkSteps (inputOnlyProblem input) + 1 +
          secondUnaryTokenCursorWorkSteps (inputOnlyProblem input))
        (rawInputWorkTape input) = .timeout :=
  secondUnaryCursorEndpoint_before_terminator_launch_timeout
    (inputOnlyProblem input)

example (input : BitString) :
    workBoundedDecide (machine (inputOnlyProblem input))
        (workSteps (inputOnlyProblem input) - 1)
        (rawInputWorkTape input) = .timeout :=
  work_one_step_short_timeout (inputOnlyProblem input)

example (fuel : Nat) (request : CNFToken)
    (left right : List WorkSymbol) :
    (let bad := BuilderTokenAppender.malformedTallyConfiguration
        request left right
     let global := signAppenderGlobalConfiguration (inputOnlyProblem []) bad
     let result := workRun (machine (inputOnlyProblem [])) fuel global
     if result.state == (machine (inputOnlyProblem [])).acceptState then
       WorkVerdict.accept
     else if result.state == (machine (inputOnlyProblem [])).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  malformedSignAppenderTally_timeout
    (inputOnlyProblem []) fuel request left right

example (fuel : Nat) (request : CNFToken)
    (left right : List WorkSymbol) :
    (let bad := BuilderTokenAppender.malformedTallyConfiguration
        request left right
     let global := secondUnaryAppenderGlobalConfiguration
        (inputOnlyProblem []) bad
     let result := workRun (machine (inputOnlyProblem [])) fuel global
     if result.state == (machine (inputOnlyProblem [])).acceptState then
       WorkVerdict.accept
     else if result.state == (machine (inputOnlyProblem [])).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  malformedSecondUnaryAppenderTally_timeout
    (inputOnlyProblem []) fuel request left right

example (fuel : Nat) (request : CNFToken)
    (left right : List WorkSymbol) :
    (let bad := BuilderTokenAppender.malformedOutputConfiguration
        request left right
     let global := firstUnaryAppenderGlobalConfiguration
        (inputOnlyProblem []) bad
     let result := workRun (machine (inputOnlyProblem [])) fuel global
     if result.state == (machine (inputOnlyProblem [])).acceptState then
       WorkVerdict.accept
     else if result.state == (machine (inputOnlyProblem [])).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  malformedFirstUnaryAppenderOutput_timeout
    (inputOnlyProblem []) fuel request left right

example (fuel : Nat) (request : CNFToken)
    (left right : List WorkSymbol) :
    (let bad := BuilderTokenAppender.malformedOutputConfiguration
        request left right
     let global := terminatorAppenderGlobalConfiguration
        (inputOnlyProblem []) bad
     let result := workRun (machine (inputOnlyProblem [])) fuel global
     if result.state == (machine (inputOnlyProblem [])).acceptState then
       WorkVerdict.accept
     else if result.state == (machine (inputOnlyProblem [])).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  malformedTerminatorAppenderOutput_timeout
    (inputOnlyProblem []) fuel request left right

example (fuel : Nat) (left right : List WorkSymbol) :
    (let bad := secondUnaryCursorGlobalConfiguration (inputOnlyProblem [])
        (BuilderDynamicTokenCursorStep.CursorAdvance.malformedScratchConfiguration
          left right)
     let result := workRun (machine (inputOnlyProblem [])) fuel bad
     if result.state == (machine (inputOnlyProblem [])).acceptState then
       WorkVerdict.accept
     else if result.state == (machine (inputOnlyProblem [])).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  malformedSecondUnaryCursorScratch_timeout
    (inputOnlyProblem []) fuel left right

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

end PNP.Concrete.CookLevinBuilderThirdClauseSecondLiteralPrefixRegression
