import PNP

namespace PNP.Concrete.CookLevinBuilderThirdClauseSeparatorStepRegression

open PipelineTape PipelineStateNamespace
open CookLevin
open CookLevin.BuilderThirdClauseSeparatorStep

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
    BuilderSecondClauseSeparatorStep.SeparatorCursor.machine.rules.length =
      113 :=
  BuilderSecondClauseSeparatorStep.SeparatorCursor.rules_length

example : (machine (inputOnlyProblem [])).rules.length = 77530 := by
  rw [rules_length]
  rfl

example : finalTokenSlot (inputOnlyProblem []) = 189 := rfl
example : finalTokenSlot (inputOnlyProblem [false]) = 377 := rfl
example : finalTokenSlot (inputOnlyProblem [true]) = 377 := rfl
example : finalTokenSlot
    (inputOnlyProblem [true, false, true]) = 945 := rfl
example : finalTokenSlot
    (pairedProblem [true, false, true]) = 13365 := rfl
example : finalTokenSlot
    (inputOnlyProblem [false, false, false, false]) = 1325 := rfl
example : finalTokenSlot
    (inputOnlyProblem [true, true, true, true]) = 1325 := rfl

example : workSteps (inputOnlyProblem []) = 465216 := rfl
example : workSteps (inputOnlyProblem [false]) = 1538724 := rfl
example : workSteps (inputOnlyProblem [true]) = 1538724 := rfl
example : workSteps
    (inputOnlyProblem [true, false, true]) = 8361865 := rfl
example : workSteps
    (inputOnlyProblem [false, false, false, false]) = 15877073 := rfl
example : workSteps
    (inputOnlyProblem [true, true, true, true]) = 15877073 := rfl
example : workSteps
    (pairedProblem [true, false, true]) = 1452027628 := rfl

example : (rawTimeBound inputOnlyVerifier).eval 0 = 2793447 := rfl
example : (rawTimeBound inputOnlyVerifier).eval 1 = 9237120 := rfl
example : (rawTimeBound inputOnlyVerifier).eval 3 = 50182974 := rfl
example : (rawTimeBound inputOnlyVerifier).eval 4 = 95278947 := rfl
example : (rawTimeBound pairedVerifier).eval 3 = 8712328068 := rfl

example (input : BitString) :
    (rawTimeBound inputOnlyVerifier).eval input.length =
      (BuilderSecondClausePaddingRun.rawTimeBound inputOnlyVerifier).eval
          input.length + 330 +
        24 * input.length + 12 * (inputOnlyProblem input).FormulaWidth +
        12 * (cursorWord (inputOnlyProblem input)).length :=
  rawTimeBound_eval (inputOnlyProblem input)

example (input : BitString) :
    thirdClauseStartTokens (inputOnlyProblem input) =
      BuilderSecondClausePrefix.secondClauseTokens (inputOnlyProblem input) ++
        [CNFToken.sep] := rfl

example (input : BitString) :
    ∃ rest, encodeCNFTokens (inputOnlyProblem input).formula =
      thirdClauseStartTokens (inputOnlyProblem input) ++ rest :=
  thirdClauseStartTokens_eq_canonical_formula_prefix
    (inputOnlyProblem input)

example (input : BitString) :
    encodeTokenPairs (thirdClauseStartTokens (inputOnlyProblem input)) =
      (inputOnlyProblem input).encodedFormula.take
        (2 * ((inputOnlyProblem input).FormulaWidth + 20)) :=
  finalTokenBits_eq_encodedFormula_thirdClauseStart
    (inputOnlyProblem input)

example (input : BitString) :
    Represents (Tape.ofInput input) (finalTape (inputOnlyProblem input)) :=
  finalTape_represents (inputOnlyProblem input)

example (input : BitString) :
    VerifierTableauProblem.FormulaTokenCursor.step
        (inputOnlyProblem input)
        ⟨BuilderSecondClausePaddingRun.thirdClauseStart
          (inputOnlyProblem input)⟩ =
      some (some CNFToken.sep,
        ⟨BuilderSecondClausePaddingRun.thirdClauseStart
          (inputOnlyProblem input) + 1⟩) :=
  specification_separator_step (inputOnlyProblem input)

example (input : BitString) :
    (inputOnlyProblem input).formulaTokenSlotDirect
        (finalTokenSlot (inputOnlyProblem input)) =
      some (some CNFToken.f) :=
  nextTokenSlot_direct_eq_f (inputOnlyProblem input)

example (input : BitString) :
    VerifierTableauProblem.FormulaTokenCursor.step
        (inputOnlyProblem input) ⟨finalTokenSlot (inputOnlyProblem input)⟩ =
      some (some CNFToken.f,
        ⟨finalTokenSlot (inputOnlyProblem input) + 1⟩) :=
  specification_next_step (inputOnlyProblem input)

example (input : BitString) :
    workStep? (machine (inputOnlyProblem input))
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (BuilderSecondClausePaddingRun.finalConfiguration
            (inputOnlyProblem input))) =
      some (renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration
          BuilderSecondClauseSeparatorStep.SeparatorCursor.machine
          (BuilderSecondClausePaddingRun.finalTape
            (inputOnlyProblem input)))) :=
  prefixSeparator_launch_workStep (inputOnlyProblem input)

example (input : BitString) :
    workStep? BuilderSecondClauseSeparatorStep.SeparatorCursor.machine
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (appenderFinalConfiguration (inputOnlyProblem input))) =
      some (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration
          BuilderDynamicTokenCursorStep.CursorAdvance.machine
          (appenderFinalConfiguration (inputOnlyProblem input)).tape)) :=
  separatorCursor_launch_workStep (inputOnlyProblem input)

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
        (BuilderSecondClausePaddingRun.workSteps (inputOnlyProblem input))
        (rawInputWorkTape input) = .timeout :=
  prefixEndpoint_before_launch_timeout (inputOnlyProblem input)

example (input : BitString) :
    workBoundedDecide (machine (inputOnlyProblem input))
        (BuilderSecondClausePaddingRun.workSteps (inputOnlyProblem input) + 1 +
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

end PNP.Concrete.CookLevinBuilderThirdClauseSeparatorStepRegression
