import PNP

namespace PNP.Concrete.CookLevinBuilderFirstLiteralPrefixRegression

open PipelineTape PipelineStateNamespace
open CookLevin
open CookLevin.BuilderFirstLiteralPrefix

set_option maxRecDepth 10000

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

example : nextTokenSlot (inputOnlyProblem []) = 11 := rfl
example : nextTokenSlot (inputOnlyProblem [false]) = 15 := rfl
example : nextTokenSlot (inputOnlyProblem [true, false, true]) = 23 := rfl
example : nextTokenSlot (pairedProblem [true, false, true]) = 83 := rfl

example (input : BitString) :
    nextTokenSlot (inputOnlyProblem input) =
      (inputOnlyProblem input).formulaVariableSlotBound + 4 :=
  nextTokenSlot_eq_formulaVariableSlotBound_add_four (inputOnlyProblem input)

example (input : BitString) :
    (nextBitCursor (inputOnlyProblem input)).nextSlot =
      2 * ((inputOnlyProblem input).formulaVariableSlotBound + 4) :=
  nextBitCursor_nextSlot (inputOnlyProblem input)

example : BuilderUnaryPolynomial.ruleCount
    (nextTokenSlotPolynomial inputOnlyVerifier) = 4329 := rfl

example : (rules (inputOnlyProblem [])).length = 12672 := by
  rw [rules_length]
  rfl

example (input : BitString) :
    (rules (inputOnlyProblem input)).length =
      585 +
        BuilderUnaryPolynomial.ruleCount
          (BuilderCompleteHeader.widthPolynomial (inputOnlyProblem input)) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderBodyStartPrefix.nextTokenSlotPolynomial inputOnlyVerifier) +
        BuilderUnaryPolynomial.ruleCount
          (nextTokenSlotPolynomial inputOnlyVerifier) :=
  rules_length (inputOnlyProblem input)

example : workSteps (inputOnlyProblem []) = 6984 := rfl
example : workSteps (inputOnlyProblem [false]) = 12062 := rfl
example : workSteps (inputOnlyProblem [true]) = 12062 := rfl
example : workSteps (inputOnlyProblem [true, false, true]) = 26535 := rfl
example : workSteps
    (inputOnlyProblem [false, false, false, false]) = 35905 := rfl
example : workSteps
    (inputOnlyProblem [true, true, true, true]) = 35905 := rfl
example : workSteps (pairedProblem [true, false, true]) = 398032 := rfl

example : (rawTimeBound inputOnlyVerifier).eval 0 = 42111 := rfl
example : (rawTimeBound inputOnlyVerifier).eval 1 = 72804 := rfl
example : (rawTimeBound inputOnlyVerifier).eval 3 = 159930 := rfl
example : (rawTimeBound inputOnlyVerifier).eval 4 = 216363 := rfl
example : (rawTimeBound pairedVerifier).eval 3 = 2391108 := rfl

example : firstLiteralTokens (inputOnlyProblem []) =
    [.t, .t, .t, .t, .t, .t, .f, .sep, .t, .f] := rfl

example (input : BitString) :
    firstLiteralTokens (inputOnlyProblem input) =
      encodeUnaryTokens (inputOnlyProblem input).FormulaWidth ++
        [.sep, .t, .f] :=
  firstLiteralTokens_eq_canonical_prefix (inputOnlyProblem input)

example (input : BitString) :
    Represents (Tape.ofInput input) (finalTape (inputOnlyProblem input)) :=
  finalTape_represents (inputOnlyProblem input)

example (input : BitString) :
    ∃ wordPrefix tail,
      finalOutside (inputOnlyProblem input) =
        wordPrefix ++ BuilderUnaryPolynomial.separatorSymbol ::
          List.replicate (nextTokenSlot (inputOnlyProblem input))
            BuilderUnaryPolynomial.unitSymbol ++
          BuilderUnaryPolynomial.scratchEndSymbol :: tail :=
  finalOutside_contains_nextTokenSlot (inputOnlyProblem input)

example (input : BitString) :
    (inputOnlyProblem input).formulaTokenSlotDirect
        ((inputOnlyProblem input).formulaVariableSlotBound + 2) =
      some (some CNFToken.t) :=
  firstLiteralSignSlotDirect_eq_t (inputOnlyProblem input)

example (input : BitString) :
    (inputOnlyProblem input).formulaTokenSlotDirect
        ((inputOnlyProblem input).formulaVariableSlotBound + 3) =
      some (some CNFToken.f) :=
  firstLiteralZeroTerminatorSlotDirect_eq_f (inputOnlyProblem input)

example (input : BitString) :
    (pairedProblem input).formulaTokenSlotDirect
        ((pairedProblem input).formulaVariableSlotBound + 2) =
      some (some CNFToken.t) :=
  firstLiteralSignSlotDirect_eq_t (pairedProblem input)

example (input : BitString) :
    (pairedProblem input).formulaTokenSlotDirect
        ((pairedProblem input).formulaVariableSlotBound + 3) =
      some (some CNFToken.f) :=
  firstLiteralZeroTerminatorSlotDirect_eq_f (pairedProblem input)

example (input : BitString) :
    encodeTokenPairs (firstLiteralTokens (inputOnlyProblem input)) =
      (inputOnlyProblem input).encodedFormula.take
        (2 * ((inputOnlyProblem input).FormulaWidth + 4)) :=
  finalTokenBits_eq_encodedFormula_firstLiteral (inputOnlyProblem input)

example (input : BitString) :
    encodeTokenPairs (firstLiteralTokens (pairedProblem input)) =
      (pairedProblem input).encodedFormula.take
        (2 * ((pairedProblem input).FormulaWidth + 4)) :=
  finalTokenBits_eq_encodedFormula_firstLiteral (pairedProblem input)

example (left right : Nat) : prefixState left ≠ evaluatorState right :=
  prefixState_ne_evaluatorState left right

example (left right : Nat) : prefixState left ≠ tAppenderState right :=
  prefixState_ne_tAppenderState left right

example (left right : Nat) : evaluatorState left ≠ tAppenderState right :=
  evaluatorState_ne_tAppenderState left right

example (left right : Nat) : prefixState left ≠ fAppenderState right :=
  prefixState_ne_fAppenderState left right

example (left right : Nat) : evaluatorState left ≠ fAppenderState right :=
  evaluatorState_ne_fAppenderState left right

example (left right : Nat) : tAppenderState left ≠ fAppenderState right :=
  tAppenderState_ne_fAppenderState left right

example (input : BitString) :
    workStep? (machine (inputOnlyProblem input))
        (renameConfiguration prefixState
          (BuilderBodyStartPrefix.finalConfiguration
            (inputOnlyProblem input))) =
      some (renameConfiguration evaluatorState
        (BuilderUnaryPolynomial.initialConfiguration
          (nextTokenSlotPolynomial inputOnlyVerifier) input
          (BuilderBodyStartPrefix.finalOutside (inputOnlyProblem input))
          (BuilderBodyStartPrefix.bodyStartTokens (inputOnlyProblem input)))) :=
  prefixEvaluator_launch_workStep (inputOnlyProblem input)

example (input : BitString) :
    workStep? (machine (inputOnlyProblem input))
        (renameConfiguration evaluatorState
          (BuilderUnaryPolynomial.finalConfiguration
            (nextTokenSlotPolynomial inputOnlyVerifier) input
            (BuilderBodyStartPrefix.finalOutside (inputOnlyProblem input))
            (BuilderBodyStartPrefix.bodyStartTokens (inputOnlyProblem input)))) =
      some (renameConfiguration tAppenderState
        (BuilderTokenAppender.entryConfiguration .t
          (BuilderTokenAppender.workspaceTape input
            (finalOutside (inputOnlyProblem input))
            (BuilderBodyStartPrefix.bodyStartTokens
              (inputOnlyProblem input))))) :=
  evaluatorT_launch_workStep (inputOnlyProblem input)

example (input : BitString) :
    workStep? (machine (inputOnlyProblem input))
        (renameConfiguration tAppenderState
          (BuilderTokenAppender.finalConfiguration input
            (finalOutside (inputOnlyProblem input))
            (firstLiteralSignTokens (inputOnlyProblem input)))) =
      some (renameConfiguration fAppenderState
        (BuilderTokenAppender.entryConfiguration .f
          (BuilderTokenAppender.workspaceTape input
            (finalOutside (inputOnlyProblem input))
            (firstLiteralSignTokens (inputOnlyProblem input))))) :=
  tF_launch_workStep (inputOnlyProblem input)

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
        (BuilderBodyStartPrefix.workSteps (inputOnlyProblem input))
        (rawInputWorkTape input) = .timeout :=
  prefixEndpoint_before_launch_timeout (inputOnlyProblem input)

example (input : BitString) :
    workBoundedDecide (machine (inputOnlyProblem input))
        (BuilderBodyStartPrefix.workSteps (inputOnlyProblem input) + 1 +
          BuilderUnaryPolynomial.workSteps
            (nextTokenSlotPolynomial inputOnlyVerifier) input)
        (rawInputWorkTape input) = .timeout :=
  evaluatorEndpoint_before_launch_timeout (inputOnlyProblem input)

example (input : BitString) :
    workBoundedDecide (machine (inputOnlyProblem input))
        (BuilderBodyStartPrefix.workSteps (inputOnlyProblem input) + 1 +
          BuilderUnaryPolynomial.workSteps
            (nextTokenSlotPolynomial inputOnlyVerifier) input + 1 +
          BuilderTokenAppender.workSteps input
            (BuilderBodyStartPrefix.bodyStartTokens
              (inputOnlyProblem input)))
        (rawInputWorkTape input) = .timeout :=
  tAppenderEndpoint_before_launch_timeout (inputOnlyProblem input)

example (input : BitString) :
    workBoundedDecide (machine (inputOnlyProblem input))
        (workSteps (inputOnlyProblem input) - 1)
        (rawInputWorkTape input) = .timeout :=
  work_one_step_short_timeout (inputOnlyProblem input)

example (fuel : Nat) (tape : WorkTape) :
    (let config := renameConfiguration prefixState
        { state := (BuilderBodyStartPrefix.machine
            (inputOnlyProblem [])).rejectState
          tape := tape }
     let result := workRun (machine (inputOnlyProblem [])) fuel config
     if result.state == (machine (inputOnlyProblem [])).acceptState then
       WorkVerdict.accept
     else if result.state == (machine (inputOnlyProblem [])).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  prefixRejectEndpoint_timeout (inputOnlyProblem []) fuel tape

example (fuel : Nat) (tape : WorkTape) :
    (let config := renameConfiguration evaluatorState
        { state := BuilderUnaryPolynomial.deadState
            (nextTokenSlotPolynomial inputOnlyVerifier)
          tape := tape }
     let result := workRun (machine (inputOnlyProblem [])) fuel config
     if result.state == (machine (inputOnlyProblem [])).acceptState then
       WorkVerdict.accept
     else if result.state == (machine (inputOnlyProblem [])).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  evaluatorDeadState_timeout (inputOnlyProblem []) fuel tape

example (fuel : Nat) (left right : List WorkSymbol) :
    (let config := renameConfiguration tAppenderState
        (BuilderTokenAppender.malformedTallyConfiguration .t left right)
     let result := workRun (machine (inputOnlyProblem [])) fuel config
     if result.state == (machine (inputOnlyProblem [])).acceptState then
       WorkVerdict.accept
     else if result.state == (machine (inputOnlyProblem [])).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  malformedAppenderTally_timeout (inputOnlyProblem []) fuel .t left right

example (fuel : Nat) (left right : List WorkSymbol) :
    (let config := renameConfiguration tAppenderState
        (BuilderTokenAppender.malformedOutputConfiguration .t left right)
     let result := workRun (machine (inputOnlyProblem [])) fuel config
     if result.state == (machine (inputOnlyProblem [])).acceptState then
       WorkVerdict.accept
     else if result.state == (machine (inputOnlyProblem [])).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  malformedAppenderOutput_timeout (inputOnlyProblem []) fuel .t left right

example (fuel : Nat) (left right : List WorkSymbol) :
    (let config := renameConfiguration fAppenderState
        (BuilderTokenAppender.malformedTallyConfiguration .f left right)
     let result := workRun (machine (inputOnlyProblem [])) fuel config
     if result.state == (machine (inputOnlyProblem [])).acceptState then
       WorkVerdict.accept
     else if result.state == (machine (inputOnlyProblem [])).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  malformedFAppenderTally_timeout (inputOnlyProblem []) fuel .f left right

example (fuel : Nat) (left right : List WorkSymbol) :
    (let config := renameConfiguration fAppenderState
        (BuilderTokenAppender.malformedOutputConfiguration .f left right)
     let result := workRun (machine (inputOnlyProblem [])) fuel config
     if result.state == (machine (inputOnlyProblem [])).acceptState then
       WorkVerdict.accept
     else if result.state == (machine (inputOnlyProblem [])).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  malformedFAppenderOutput_timeout (inputOnlyProblem []) fuel .f left right

end PNP.Concrete.CookLevinBuilderFirstLiteralPrefixRegression
