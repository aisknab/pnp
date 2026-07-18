import PNP

namespace PNP.Concrete.CookLevinBuilderSecondClauseSeparatorStepRegression

open PipelineTape PipelineStateNamespace
open CookLevin
open CookLevin.BuilderSecondClauseSeparatorStep

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

example : SeparatorCursor.machine.rules.length = 113 :=
  SeparatorCursor.rules_length

example : (machine (inputOnlyProblem [])).rules.length = 41713 := by
  rw [rules_length]
  rfl

example : finalTokenSlot (inputOnlyProblem []) = 99 := rfl
example : finalTokenSlot (inputOnlyProblem [false]) = 195 := rfl
example : finalTokenSlot (inputOnlyProblem [true]) = 195 := rfl
example : finalTokenSlot
    (inputOnlyProblem [true, false, true]) = 483 := rfl
example : finalTokenSlot
    (pairedProblem [true, false, true]) = 6723 := rfl

example : workSteps (inputOnlyProblem []) = 130209 := rfl
example : workSteps (inputOnlyProblem [false]) = 403821 := rfl
example : workSteps (inputOnlyProblem [true]) = 403821 := rfl
example : workSteps
    (inputOnlyProblem [true, false, true]) = 2066502 := rfl
example : workSteps
    (inputOnlyProblem [false, false, false, false]) = 3862568 := rfl
example : workSteps
    (inputOnlyProblem [true, true, true, true]) = 3862568 := rfl

example : (rawTimeBound inputOnlyVerifier).eval 0 = 782403 := rfl
example : (rawTimeBound inputOnlyVerifier).eval 1 = 2425512 := rfl
example : (rawTimeBound inputOnlyVerifier).eval 3 = 12405246 := rfl
example : (rawTimeBound inputOnlyVerifier).eval 4 = 23184111 := rfl
example : (rawTimeBound pairedVerifier).eval 3 = 2016350100 := rfl

example (input : BitString) :
    secondClauseStartTokens (inputOnlyProblem input) =
      BuilderFirstClausePrefix.firstClauseTokens (inputOnlyProblem input) ++
        [CNFToken.sep] := rfl

example (input : BitString) :
    ∃ rest, encodeCNFTokens (inputOnlyProblem input).formula =
      secondClauseStartTokens (inputOnlyProblem input) ++ rest :=
  secondClauseStartTokens_eq_canonical_formula_prefix
    (inputOnlyProblem input)

example (input : BitString) :
    encodeTokenPairs (secondClauseStartTokens (inputOnlyProblem input)) =
      (inputOnlyProblem input).encodedFormula.take
        (2 * ((inputOnlyProblem input).FormulaWidth + 13)) :=
  finalTokenBits_eq_encodedFormula_secondClauseStart
    (inputOnlyProblem input)

example (input : BitString) :
    Represents (Tape.ofInput input) (finalTape (inputOnlyProblem input)) :=
  finalTape_represents (inputOnlyProblem input)

example (input : BitString) :
    VerifierTableauProblem.FormulaTokenCursor.step
        (inputOnlyProblem input)
        ⟨BuilderFirstClausePaddingRun.secondClauseStart
          (inputOnlyProblem input)⟩ =
      some (some CNFToken.sep,
        ⟨BuilderFirstClausePaddingRun.secondClauseStart
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
          (BuilderFirstClausePaddingRun.finalConfiguration
            (inputOnlyProblem input))) =
      some (renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration SeparatorCursor.machine
          (BuilderFirstClausePaddingRun.finalTape
            (inputOnlyProblem input)))) :=
  prefixSeparator_launch_workStep (inputOnlyProblem input)

example (input : BitString) :
    workStep? SeparatorCursor.machine
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
        (BuilderFirstClausePaddingRun.workSteps (inputOnlyProblem input))
        (rawInputWorkTape input) = .timeout :=
  prefixEndpoint_before_launch_timeout (inputOnlyProblem input)

example (input : BitString) :
    workBoundedDecide (machine (inputOnlyProblem input))
        (BuilderFirstClausePaddingRun.workSteps (inputOnlyProblem input) + 1 +
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

end PNP.Concrete.CookLevinBuilderSecondClauseSeparatorStepRegression
