import PNP

namespace PNP.Concrete.CookLevinBuilderFirstClausePrefixRegression

open PipelineTape PipelineStateNamespace
open CookLevin
open CookLevin.BuilderFirstClausePrefix

set_option maxRecDepth 1000000

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

example : nextTokenSlot (inputOnlyProblem []) = 19 := rfl
example : nextTokenSlot (inputOnlyProblem [false]) = 23 := rfl
example : nextTokenSlot (inputOnlyProblem [true, false, true]) = 31 := rfl
example : nextTokenSlot (pairedProblem [true, false, true]) = 91 := rfl

example (input : BitString) :
    nextTokenSlot (inputOnlyProblem input) =
      (inputOnlyProblem input).formulaVariableSlotBound + 12 :=
  nextTokenSlot_eq_formulaVariableSlotBound_add_twelve
    (inputOnlyProblem input)

example (input : BitString) :
    (nextBitCursor (inputOnlyProblem input)).nextSlot =
      2 * ((inputOnlyProblem input).formulaVariableSlotBound + 12) :=
  nextBitCursor_nextSlot (inputOnlyProblem input)

example : BuilderUnaryPolynomial.ruleCount
    (nextTokenSlotPolynomial inputOnlyVerifier) = 4473 := rfl

example : (machine (inputOnlyProblem [])).rules.length = 17698 := by
  rw [rules_length]
  rfl

example (input : BitString) :
    (machine (inputOnlyProblem input)).rules.length =
      1138 +
        BuilderUnaryPolynomial.ruleCount
          (BuilderCompleteHeader.widthPolynomial (inputOnlyProblem input)) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderBodyStartPrefix.nextTokenSlotPolynomial inputOnlyVerifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderFirstLiteralPrefix.nextTokenSlotPolynomial
            inputOnlyVerifier) +
        BuilderUnaryPolynomial.ruleCount
          (nextTokenSlotPolynomial inputOnlyVerifier) :=
  rules_length (inputOnlyProblem input)

example : workSteps (inputOnlyProblem []) = 10192 := rfl
example : workSteps (inputOnlyProblem [false]) = 17056 := rfl
example : workSteps (inputOnlyProblem [true]) = 17056 := rfl
example : workSteps (inputOnlyProblem [true, false, true]) = 36429 := rfl
example : workSteps
    (inputOnlyProblem [false, false, false, false]) = 48897 := rfl
example : workSteps
    (inputOnlyProblem [true, true, true, true]) = 48897 := rfl
example : workSteps (pairedProblem [true, false, true]) = 510860 := rfl

example : (rawTimeBound inputOnlyVerifier).eval 0 = 61359 := rfl
example : (rawTimeBound inputOnlyVerifier).eval 1 = 102864 := rfl
example : (rawTimeBound inputOnlyVerifier).eval 3 = 219390 := rfl
example : (rawTimeBound inputOnlyVerifier).eval 4 = 294411 := rfl
example : (rawTimeBound pairedVerifier).eval 3 = 3068172 := rfl

example : firstClauseTokens (inputOnlyProblem []) =
    [.t, .t, .t, .t, .t, .t, .f,
     .sep, .t, .f, .t, .t, .f, .t, .t, .t, .f, .finish] := rfl

example (input : BitString) :
    firstClauseTokens (inputOnlyProblem input) =
      encodeUnaryTokens (inputOnlyProblem input).FormulaWidth ++
        [.sep, .t, .f, .t, .t, .f, .t, .t, .t, .f, .finish] :=
  firstClauseTokens_eq_canonical_prefix (inputOnlyProblem input)

example (input : BitString) :
    Represents (Tape.ofInput input) (finalTape (inputOnlyProblem input)) :=
  finalTape_represents (inputOnlyProblem input)

example (input : BitString) :
    ∃ rest, encodeCNFTokens (inputOnlyProblem input).formula =
      firstClauseTokens (inputOnlyProblem input) ++ rest :=
  firstClauseTokens_eq_canonical_formula_prefix (inputOnlyProblem input)

example (input : BitString) :
    encodeTokenPairs (firstClauseTokens (inputOnlyProblem input)) =
      (inputOnlyProblem input).encodedFormula.take
        (2 * ((inputOnlyProblem input).FormulaWidth + 12)) :=
  finalTokenBits_eq_encodedFormula_firstClause (inputOnlyProblem input)

example (input : BitString) :
    encodeTokenPairs (firstClauseTokens (pairedProblem input)) =
      (pairedProblem input).encodedFormula.take
        (2 * ((pairedProblem input).FormulaWidth + 12)) :=
  finalTokenBits_eq_encodedFormula_firstClause (pairedProblem input)

example (left right : Nat) :
    WorkChain.firstState left ≠ WorkChain.secondState right :=
  WorkChain.firstState_ne_secondState left right

example (input : BitString) :
    (machine (inputOnlyProblem input)).rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) :=
  rules_pairwise_query_distinct (inputOnlyProblem input)

example (input : BitString) :
    workStep? (machine (inputOnlyProblem input))
        (renameConfiguration WorkChain.firstState
          (BuilderFirstLiteralPrefix.finalConfiguration
            (inputOnlyProblem input))) =
      some (renameConfiguration WorkChain.secondState
        (workStartConfiguration
          (evaluatorTailMachine (inputOnlyProblem input))
          (BuilderFirstLiteralPrefix.finalTape
            (inputOnlyProblem input)))) :=
  launch_workStep (inputOnlyProblem input)

example (input : BitString) :
    workStep? (evaluatorTailMachine (inputOnlyProblem input))
        (renameConfiguration WorkChain.firstState
          (BuilderUnaryPolynomial.finalConfiguration
            (nextTokenSlotPolynomial inputOnlyVerifier) input
            (BuilderFirstLiteralPrefix.finalOutside
              (inputOnlyProblem input))
            (BuilderFirstLiteralPrefix.firstLiteralTokens
              (inputOnlyProblem input)))) =
      some (renameConfiguration WorkChain.secondState
        (workStartConfiguration FirstClauseTailAppender.machine
          (BuilderTokenAppender.workspaceTape input
            (finalOutside (inputOnlyProblem input))
            (BuilderFirstLiteralPrefix.firstLiteralTokens
              (inputOnlyProblem input))))) :=
  evaluatorTail_launch_workStep (inputOnlyProblem input)

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
        (BuilderFirstLiteralPrefix.workSteps (inputOnlyProblem input))
        (rawInputWorkTape input) = .timeout :=
  prefixEndpoint_before_launch_timeout (inputOnlyProblem input)

example (input : BitString) :
    workBoundedDecide (machine (inputOnlyProblem input))
        (BuilderFirstLiteralPrefix.workSteps (inputOnlyProblem input) + 1 +
          BuilderUnaryPolynomial.workSteps
            (nextTokenSlotPolynomial inputOnlyVerifier) input)
        (rawInputWorkTape input) = .timeout :=
  evaluatorEndpoint_before_launch_timeout (inputOnlyProblem input)

example (input : BitString) :
    workBoundedDecide (machine (inputOnlyProblem input))
        (workSteps (inputOnlyProblem input) - 1)
        (rawInputWorkTape input) = .timeout :=
  work_one_step_short_timeout (inputOnlyProblem input)

example (fuel : Nat) (request : CNFToken)
    (left right : List WorkSymbol) :
    (let config := renameConfiguration WorkChain.secondState
        (renameConfiguration WorkChain.secondState
          (renameConfiguration WorkChain.firstState
            (BuilderTokenAppender.malformedTallyConfiguration
              request left right)))
     let result := workRun (machine (inputOnlyProblem [])) fuel config
     if result.state == (machine (inputOnlyProblem [])).acceptState then
       WorkVerdict.accept
     else if result.state == (machine (inputOnlyProblem [])).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  malformedAppenderTally_timeout (inputOnlyProblem []) fuel request left right

example (fuel : Nat) (request : CNFToken)
    (left right : List WorkSymbol) :
    (let config := renameConfiguration WorkChain.secondState
        (renameConfiguration WorkChain.secondState
          (renameConfiguration WorkChain.firstState
            (BuilderTokenAppender.malformedOutputConfiguration
              request left right)))
     let result := workRun (machine (inputOnlyProblem [])) fuel config
     if result.state == (machine (inputOnlyProblem [])).acceptState then
       WorkVerdict.accept
     else if result.state == (machine (inputOnlyProblem [])).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  malformedAppenderOutput_timeout (inputOnlyProblem []) fuel request left right

end PNP.Concrete.CookLevinBuilderFirstClausePrefixRegression
