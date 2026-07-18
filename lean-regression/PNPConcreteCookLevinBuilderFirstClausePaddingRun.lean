import PNP

namespace PNP.Concrete.CookLevinBuilderFirstClausePaddingRunRegression

open PipelineTape PipelineStateNamespace
open CookLevin
open CookLevin.BuilderFirstClausePaddingRun

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

example : PaddingCountdown.rules.length = 25 :=
  PaddingCountdown.rules_length

example : (machine (inputOnlyProblem [])).rules.length = 41591 := by
  rw [rules_length]
  rfl

example : remainingPaddingCount (inputOnlyProblem []) = 78 := rfl
example : remainingPaddingCount (inputOnlyProblem [false]) = 170 := rfl
example : remainingPaddingCount (inputOnlyProblem [true]) = 170 := rfl
example : remainingPaddingCount
    (inputOnlyProblem [true, false, true]) = 450 := rfl
example : remainingPaddingCount
    (pairedProblem [true, false, true]) = 6630 := rfl

example : secondClauseStart (inputOnlyProblem []) = 98 := rfl
example : secondClauseStart (inputOnlyProblem [false]) = 194 := rfl
example : secondClauseStart
    (inputOnlyProblem [true, false, true]) = 482 := rfl
example : secondClauseStart
    (pairedProblem [true, false, true]) = 6722 := rfl

example : workSteps (inputOnlyProblem []) = 128974 := rfl
example : workSteps (inputOnlyProblem [false]) = 401836 := rfl
example : workSteps (inputOnlyProblem [true]) = 401836 := rfl
example : workSteps
    (inputOnlyProblem [true, false, true]) = 2062437 := rfl
example : workSteps
    (inputOnlyProblem [false, false, false, false]) = 3857175 := rfl
example : workSteps
    (inputOnlyProblem [true, true, true, true]) = 3857175 := rfl
example : (rawTimeBound inputOnlyVerifier).eval 0 = 774993 := rfl
example : (rawTimeBound inputOnlyVerifier).eval 1 = 2413590 := rfl
example : (rawTimeBound inputOnlyVerifier).eval 3 = 12380844 := rfl
example : (rawTimeBound inputOnlyVerifier).eval 4 = 23151741 := rfl
example : (rawTimeBound pairedVerifier).eval 3 = 2016081318 := rfl

example (input : BitString) :
    remainingPaddingCount (inputOnlyProblem input) =
      (inputOnlyProblem input).formulaTokensPerClause - 12 :=
  remainingPaddingCount_eq_formulaTokensPerClause_sub_twelve
    (inputOnlyProblem input)

example (input : BitString) :
    BuilderDynamicTokenCursorStep.finalTokenSlot (inputOnlyProblem input) +
        remainingPaddingCount (inputOnlyProblem input) =
      secondClauseStart (inputOnlyProblem input) :=
  predecessorSlot_add_remainingPaddingCount (inputOnlyProblem input)

example (input : BitString) (offset : Nat)
    (hOffset : offset < remainingPaddingCount (inputOnlyProblem input)) :
    (inputOnlyProblem input).formulaTokenSlotDirect
        (BuilderDynamicTokenCursorStep.finalTokenSlot
          (inputOnlyProblem input) + offset) = some none :=
  paddingSlot_direct_eq_padding (inputOnlyProblem input) offset hOffset

example (input : BitString) :
    (inputOnlyProblem input).formulaTokenSlotDirect
        (secondClauseStart (inputOnlyProblem input)) =
      some (some CNFToken.sep) :=
  secondClauseStart_direct_eq_sep (inputOnlyProblem input)

example (input : BitString) :
    specificationRun (inputOnlyProblem input)
        (remainingPaddingCount (inputOnlyProblem input))
        ⟨BuilderDynamicTokenCursorStep.finalTokenSlot
          (inputOnlyProblem input)⟩ =
      some ([], ⟨secondClauseStart (inputOnlyProblem input)⟩) :=
  specification_padding_run (inputOnlyProblem input)

example (input : BitString) :
    VerifierTableauProblem.FormulaTokenCursor.step
        (inputOnlyProblem input)
        ⟨secondClauseStart (inputOnlyProblem input)⟩ =
      some (some CNFToken.sep,
        ⟨secondClauseStart (inputOnlyProblem input) + 1⟩) :=
  specification_target_step (inputOnlyProblem input)

example (input : BitString) :
    Represents (Tape.ofInput input) (finalTape (inputOnlyProblem input)) :=
  finalTape_represents (inputOnlyProblem input)

example (input : BitString) :
    encodeTokenPairs
        (BuilderFirstClausePrefix.firstClauseTokens
          (inputOnlyProblem input)) =
      (inputOnlyProblem input).encodedFormula.take
        (2 * ((inputOnlyProblem input).FormulaWidth + 12)) :=
  finalTokenBits_eq_encodedFormula_firstClause (inputOnlyProblem input)

example (input : BitString) :
    workStep? (machine (inputOnlyProblem input))
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (BuilderDynamicTokenCursorStep.finalConfiguration
            (inputOnlyProblem input))) =
      some (renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration
          (paddingSuffixMachine (inputOnlyProblem input))
          (BuilderDynamicTokenCursorStep.finalTape
            (inputOnlyProblem input)))) :=
  launch_workStep (inputOnlyProblem input)

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
        (BuilderDynamicTokenCursorStep.workSteps (inputOnlyProblem input))
        (rawInputWorkTape input) = .timeout :=
  prefixEndpoint_before_launch_timeout (inputOnlyProblem input)

example (input : BitString) :
    workBoundedDecide (machine (inputOnlyProblem input))
        (workSteps (inputOnlyProblem input) - 1)
        (rawInputWorkTape input) = .timeout :=
  work_one_step_short_timeout (inputOnlyProblem input)

example (fuel : Nat) (left right : List WorkSymbol) :
    (let config := malformedCountdownScratchConfiguration left right
     let result := workRun PaddingCountdown.machine fuel config
     if result.state == PaddingCountdown.machine.acceptState then
       WorkVerdict.accept
     else if result.state == PaddingCountdown.machine.rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  malformedCountdownScratch_timeout fuel left right

example (fuel : Nat) (left right : List WorkSymbol) :
    (let config := malformedCountdownRootConfiguration left right
     let result := workRun PaddingCountdown.machine fuel config
     if result.state == PaddingCountdown.machine.acceptState then
       WorkVerdict.accept
     else if result.state == PaddingCountdown.machine.rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  malformedCountdownRoot_timeout fuel left right

end PNP.Concrete.CookLevinBuilderFirstClausePaddingRunRegression
