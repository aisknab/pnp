import PNP

namespace PNP.Concrete.CookLevinBuilderSecondClausePaddingRunRegression

open PipelineTape PipelineStateNamespace
open CookLevin
open CookLevin.BuilderSecondClausePaddingRun

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

example : BuilderFirstClausePaddingRun.PaddingCountdown.rules.length = 25 :=
  BuilderFirstClausePaddingRun.PaddingCountdown.rules_length

example : (machine (inputOnlyProblem [])).rules.length = 77408 := by
  rw [rules_length]
  rfl

example : remainingPaddingCount (inputOnlyProblem []) = 83 := rfl
example : remainingPaddingCount (inputOnlyProblem [false]) = 175 := rfl
example : remainingPaddingCount (inputOnlyProblem [true]) = 175 := rfl
example : remainingPaddingCount
    (inputOnlyProblem [true, false, true]) = 455 := rfl
example : remainingPaddingCount
    (pairedProblem [true, false, true]) = 6635 := rfl
example : remainingPaddingCount
    (inputOnlyProblem [false, false, false, false]) = 643 := rfl
example : remainingPaddingCount
    (inputOnlyProblem [true, true, true, true]) = 643 := rfl

example : thirdClauseStart (inputOnlyProblem []) = 188 := rfl
example : thirdClauseStart (inputOnlyProblem [false]) = 376 := rfl
example : thirdClauseStart
    (inputOnlyProblem [true, false, true]) = 944 := rfl
example : thirdClauseStart
    (pairedProblem [true, false, true]) = 13364 := rfl
example : thirdClauseStart
    (inputOnlyProblem [false, false, false, false]) = 1324 := rfl
example : thirdClauseStart
    (inputOnlyProblem [true, true, true, true]) = 1324 := rfl

example : workSteps (inputOnlyProblem []) = 462807 := rfl
example : workSteps (inputOnlyProblem [false]) = 1534701 := rfl
example : workSteps (inputOnlyProblem [true]) = 1534701 := rfl
example : (rawTimeBound inputOnlyVerifier).eval 0 = 2778993 := rfl
example : (rawTimeBound inputOnlyVerifier).eval 1 = 9212970 := rfl
example : (rawTimeBound inputOnlyVerifier).eval 3 = 50131368 := rfl
example : (rawTimeBound inputOnlyVerifier).eval 4 = 95209581 := rfl
example : (rawTimeBound pairedVerifier).eval 3 = 8711721090 := rfl

example (input : BitString) :
    remainingPaddingCount (inputOnlyProblem input) =
      (inputOnlyProblem input).formulaTokensPerClause - 7 :=
  remainingPaddingCount_eq_formulaTokensPerClause_sub_seven
    (inputOnlyProblem input)

example (input : BitString) :
    BuilderSecondClausePrefix.finalTokenSlot (inputOnlyProblem input) +
        remainingPaddingCount (inputOnlyProblem input) =
      thirdClauseStart (inputOnlyProblem input) :=
  predecessorSlot_add_remainingPaddingCount (inputOnlyProblem input)

example (input : BitString) (offset : Nat)
    (hOffset : offset < remainingPaddingCount (inputOnlyProblem input)) :
    (inputOnlyProblem input).formulaTokenSlotDirect
        (BuilderSecondClausePrefix.finalTokenSlot
          (inputOnlyProblem input) + offset) = some none :=
  paddingSlot_direct_eq_padding (inputOnlyProblem input) offset hOffset

example (input : BitString) :
    (inputOnlyProblem input).formulaTokenSlotDirect
        (thirdClauseStart (inputOnlyProblem input)) =
      some (some CNFToken.sep) :=
  thirdClauseStart_direct_eq_sep (inputOnlyProblem input)

example (input : BitString) :
    specificationRun (inputOnlyProblem input)
        (remainingPaddingCount (inputOnlyProblem input))
        ⟨BuilderSecondClausePrefix.finalTokenSlot
          (inputOnlyProblem input)⟩ =
      some ([], ⟨thirdClauseStart (inputOnlyProblem input)⟩) :=
  specification_padding_run (inputOnlyProblem input)

example (input : BitString) :
    VerifierTableauProblem.FormulaTokenCursor.step
        (inputOnlyProblem input)
        ⟨thirdClauseStart (inputOnlyProblem input)⟩ =
      some (some CNFToken.sep,
        ⟨thirdClauseStart (inputOnlyProblem input) + 1⟩) :=
  specification_target_step (inputOnlyProblem input)

example (input : BitString) :
    Represents (Tape.ofInput input) (finalTape (inputOnlyProblem input)) :=
  finalTape_represents (inputOnlyProblem input)

example (input : BitString) :
    encodeTokenPairs
        (BuilderSecondClausePrefix.secondClauseTokens
          (inputOnlyProblem input)) =
      (inputOnlyProblem input).encodedFormula.take
        (2 * ((inputOnlyProblem input).FormulaWidth + 19)) :=
  finalTokenBits_eq_encodedFormula_secondClause (inputOnlyProblem input)

example (input : BitString) :
    workStep? (machine (inputOnlyProblem input))
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (BuilderSecondClausePrefix.finalConfiguration
            (inputOnlyProblem input))) =
      some (renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration
          (paddingSuffixMachine (inputOnlyProblem input))
          (BuilderSecondClausePrefix.finalTape
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
        (BuilderSecondClausePrefix.workSteps (inputOnlyProblem input))
        (rawInputWorkTape input) = .timeout :=
  prefixEndpoint_before_launch_timeout (inputOnlyProblem input)

example (input : BitString) :
    workBoundedDecide (machine (inputOnlyProblem input))
        (workSteps (inputOnlyProblem input) - 1)
        (rawInputWorkTape input) = .timeout :=
  work_one_step_short_timeout (inputOnlyProblem input)

example (fuel : Nat) (left right : List WorkSymbol) :
    (let config := malformedCountdownScratchConfiguration left right
     let result := workRun BuilderFirstClausePaddingRun.PaddingCountdown.machine fuel config
     if result.state == BuilderFirstClausePaddingRun.PaddingCountdown.machine.acceptState then
       WorkVerdict.accept
     else if result.state == BuilderFirstClausePaddingRun.PaddingCountdown.machine.rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  malformedCountdownScratch_timeout fuel left right

example (fuel : Nat) (left right : List WorkSymbol) :
    (let config := malformedCountdownRootConfiguration left right
     let result := workRun BuilderFirstClausePaddingRun.PaddingCountdown.machine fuel config
     if result.state == BuilderFirstClausePaddingRun.PaddingCountdown.machine.acceptState then
       WorkVerdict.accept
     else if result.state == BuilderFirstClausePaddingRun.PaddingCountdown.machine.rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  malformedCountdownRoot_timeout fuel left right

end PNP.Concrete.CookLevinBuilderSecondClausePaddingRunRegression
