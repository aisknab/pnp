import PNP

namespace PNP.Concrete.CookLevinBuilderBodyStartPrefixRegression

open PipelineTape PipelineStateNamespace
open CookLevin
open CookLevin.BuilderBodyStartPrefix

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

example : nextTokenSlot (inputOnlyProblem []) = 9 := rfl
example : nextTokenSlot (inputOnlyProblem [false]) = 13 := rfl
example : nextTokenSlot (inputOnlyProblem [true, false, true]) = 21 := rfl
example : nextTokenSlot (pairedProblem [true, false, true]) = 81 := rfl

example (input : BitString) :
    nextTokenSlot (inputOnlyProblem input) =
      (inputOnlyProblem input).formulaVariableSlotBound + 2 :=
  nextTokenSlot_eq_formulaVariableSlotBound_add_two (inputOnlyProblem input)

example (input : BitString) :
    (nextBitCursor (inputOnlyProblem input)).nextSlot =
      2 * ((inputOnlyProblem input).formulaVariableSlotBound + 2) :=
  nextBitCursor_nextSlot (inputOnlyProblem input)

example : BuilderUnaryPolynomial.ruleCount
    (nextTokenSlotPolynomial inputOnlyVerifier) = 4293 := rfl

example : (rules (inputOnlyProblem [])).length = 8198 := by
  rw [rules_length]
  rfl

example (input : BitString) :
    (rules (inputOnlyProblem input)).length =
      440 +
        BuilderUnaryPolynomial.ruleCount
          (BuilderCompleteHeader.widthPolynomial (inputOnlyProblem input)) +
        BuilderUnaryPolynomial.ruleCount
          (nextTokenSlotPolynomial inputOnlyVerifier) :=
  rules_length (inputOnlyProblem input)

example : workSteps (inputOnlyProblem []) = 4612 := rfl
example : workSteps (inputOnlyProblem [false]) = 8092 := rfl
example : workSteps (inputOnlyProblem [true]) = 8092 := rfl
example : workSteps (inputOnlyProblem [true, false, true]) = 18065 := rfl
example : workSteps
    (inputOnlyProblem [false, false, false, false]) = 24537 := rfl
example : workSteps
    (inputOnlyProblem [true, true, true, true]) = 24537 := rfl
example : workSteps (pairedProblem [true, false, true]) = 289280 := rfl

example : (rawTimeBound inputOnlyVerifier).eval 0 = 27879 := rfl
example : (rawTimeBound inputOnlyVerifier).eval 1 = 48960 := rfl
example : (rawTimeBound inputOnlyVerifier).eval 3 = 109086 := rfl
example : (rawTimeBound inputOnlyVerifier).eval 4 = 148131 := rfl
example : (rawTimeBound pairedVerifier).eval 3 = 1738572 := rfl

example : bodyStartTokens (inputOnlyProblem []) =
    [.t, .t, .t, .t, .t, .t, .f, .sep] := rfl

example (input : BitString) :
    bodyStartTokens (inputOnlyProblem input) =
      encodeUnaryTokens (inputOnlyProblem input).FormulaWidth ++ [.sep] :=
  bodyStartTokens_eq_canonical_prefix (inputOnlyProblem input)

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
        ((inputOnlyProblem input).formulaVariableSlotBound + 1) =
      some (some CNFToken.sep) :=
  firstBodyTokenSlotDirect_eq_separator (inputOnlyProblem input)

example (input : BitString) :
    (pairedProblem input).formulaTokenSlotDirect
        ((pairedProblem input).formulaVariableSlotBound + 1) =
      some (some CNFToken.sep) :=
  firstBodyTokenSlotDirect_eq_separator (pairedProblem input)

example (input : BitString) :
    encodeTokenPairs (bodyStartTokens (inputOnlyProblem input)) =
      (inputOnlyProblem input).encodedFormula.take
        (2 * ((inputOnlyProblem input).FormulaWidth + 2)) :=
  finalTokenBits_eq_encodedFormula_bodyStart (inputOnlyProblem input)

example (input : BitString) :
    encodeTokenPairs (bodyStartTokens (pairedProblem input)) =
      (pairedProblem input).encodedFormula.take
        (2 * ((pairedProblem input).FormulaWidth + 2)) :=
  finalTokenBits_eq_encodedFormula_bodyStart (pairedProblem input)

example (left right : Nat) : headerState left ≠ cursorState right :=
  headerState_ne_cursorState left right

example (left right : Nat) : headerState left ≠ appenderState right :=
  headerState_ne_appenderState left right

example (left right : Nat) : cursorState left ≠ appenderState right :=
  cursorState_ne_appenderState left right

example (input : BitString) :
    workStep? (machine (inputOnlyProblem input))
        (renameConfiguration headerState
          (BuilderCompleteHeader.finalConfiguration
            (inputOnlyProblem input))) =
      some (renameConfiguration cursorState
        (BuilderUnaryPolynomial.initialConfiguration
          (nextTokenSlotPolynomial inputOnlyVerifier) input
          (BuilderCompleteHeader.finalOutside (inputOnlyProblem input))
          (BuilderCompleteHeader.headerTokens (inputOnlyProblem input)))) :=
  headerCursor_launch_workStep (inputOnlyProblem input)

example (input : BitString) :
    workStep? (machine (inputOnlyProblem input))
        (renameConfiguration cursorState
          (BuilderUnaryPolynomial.finalConfiguration
            (nextTokenSlotPolynomial inputOnlyVerifier) input
            (BuilderCompleteHeader.finalOutside (inputOnlyProblem input))
            (BuilderCompleteHeader.headerTokens (inputOnlyProblem input)))) =
      some (renameConfiguration appenderState
        (BuilderTokenAppender.entryConfiguration .sep
          (BuilderTokenAppender.workspaceTape input
            (finalOutside (inputOnlyProblem input))
            (BuilderCompleteHeader.headerTokens (inputOnlyProblem input))))) :=
  cursorAppender_launch_workStep (inputOnlyProblem input)

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
        (BuilderCompleteHeader.workSteps (inputOnlyProblem input))
        (rawInputWorkTape input) = .timeout :=
  headerEndpoint_before_launch_timeout (inputOnlyProblem input)

example (input : BitString) :
    workBoundedDecide (machine (inputOnlyProblem input))
        (BuilderCompleteHeader.workSteps (inputOnlyProblem input) + 1 +
          BuilderUnaryPolynomial.workSteps
            (nextTokenSlotPolynomial inputOnlyVerifier) input)
        (rawInputWorkTape input) = .timeout :=
  cursorEndpoint_before_launch_timeout (inputOnlyProblem input)

example (input : BitString) :
    workBoundedDecide (machine (inputOnlyProblem input))
        (workSteps (inputOnlyProblem input) - 1)
        (rawInputWorkTape input) = .timeout :=
  work_one_step_short_timeout (inputOnlyProblem input)

example (fuel : Nat) (tape : WorkTape) :
    (let config := renameConfiguration headerState
        { state := (BuilderCompleteHeader.machine
            (inputOnlyProblem [])).rejectState
          tape := tape }
     let result := workRun (machine (inputOnlyProblem [])) fuel config
     if result.state == (machine (inputOnlyProblem [])).acceptState then
       WorkVerdict.accept
     else if result.state == (machine (inputOnlyProblem [])).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  headerRejectEndpoint_timeout (inputOnlyProblem []) fuel tape

example (fuel : Nat) (tape : WorkTape) :
    (let config := renameConfiguration cursorState
        { state := BuilderUnaryPolynomial.deadState
            (nextTokenSlotPolynomial inputOnlyVerifier)
          tape := tape }
     let result := workRun (machine (inputOnlyProblem [])) fuel config
     if result.state == (machine (inputOnlyProblem [])).acceptState then
       WorkVerdict.accept
     else if result.state == (machine (inputOnlyProblem [])).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  cursorDeadState_timeout (inputOnlyProblem []) fuel tape

example (fuel : Nat) (left right : List WorkSymbol) :
    (let config := renameConfiguration appenderState
        (BuilderTokenAppender.malformedTallyConfiguration .sep left right)
     let result := workRun (machine (inputOnlyProblem [])) fuel config
     if result.state == (machine (inputOnlyProblem [])).acceptState then
       WorkVerdict.accept
     else if result.state == (machine (inputOnlyProblem [])).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  malformedAppenderTally_timeout (inputOnlyProblem []) fuel .sep left right

example (fuel : Nat) (left right : List WorkSymbol) :
    (let config := renameConfiguration appenderState
        (BuilderTokenAppender.malformedOutputConfiguration .sep left right)
     let result := workRun (machine (inputOnlyProblem [])) fuel config
     if result.state == (machine (inputOnlyProblem [])).acceptState then
       WorkVerdict.accept
     else if result.state == (machine (inputOnlyProblem [])).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  malformedAppenderOutput_timeout (inputOnlyProblem []) fuel .sep left right

end PNP.Concrete.CookLevinBuilderBodyStartPrefixRegression
