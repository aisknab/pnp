import PNP

namespace PNP.Concrete.CookLevinBuilderDynamicTokenCursorStepRegression

open PipelineTape PipelineStateNamespace
open CookLevin
open CookLevin.BuilderDynamicTokenCursorStep

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

example : CursorAdvance.rules.length = 45 := CursorAdvance.rules_length

example : (machine (inputOnlyProblem [])).rules.length = 17752 := by
  rw [rules_length]
  rfl

example : finalTokenSlot (inputOnlyProblem []) = 20 := rfl
example : finalTokenSlot (inputOnlyProblem [false]) = 24 := rfl
example : finalTokenSlot (inputOnlyProblem [true, false, true]) = 32 := rfl
example : finalTokenSlot (pairedProblem [true, false, true]) = 92 := rfl

example (input : BitString) :
    finalTokenSlot (inputOnlyProblem input) =
      (inputOnlyProblem input).formulaVariableSlotBound + 13 :=
  finalTokenSlot_eq_formulaVariableSlotBound_add_thirteen
    (inputOnlyProblem input)

example (input : BitString) :
    (inputOnlyProblem input).formulaTokenSlotDirect
        (CookLevin.BuilderFirstClausePrefix.nextTokenSlot
          (inputOnlyProblem input)) = some none :=
  directOutcome_is_padding (inputOnlyProblem input)

example (input : BitString) :
    VerifierTableauProblem.FormulaTokenCursor.step
        (inputOnlyProblem input)
        ⟨CookLevin.BuilderFirstClausePrefix.nextTokenSlot
          (inputOnlyProblem input)⟩ =
      some (none,
        ⟨CookLevin.BuilderFirstClausePrefix.nextTokenSlot
          (inputOnlyProblem input) + 1⟩) :=
  specification_step (inputOnlyProblem input)

example : (cursorWord (inputOnlyProblem [])).length = 123 := rfl
example : (cursorWord (inputOnlyProblem [false])).length = 153 := rfl
example : (cursorWord
    (inputOnlyProblem [true, false, true])).length = 213 := rfl
example : (cursorWord
    (pairedProblem [true, false, true])).length = 781 := rfl

example : workSteps (inputOnlyProblem []) = 10446 := rfl
example : workSteps (inputOnlyProblem [false]) = 17370 := rfl
example : workSteps (inputOnlyProblem [true]) = 17370 := rfl
example : workSteps (inputOnlyProblem [true, false, true]) = 36863 := rfl
example : workSteps
    (inputOnlyProblem [false, false, false, false]) = 49391 := rfl
example : workSteps
    (inputOnlyProblem [true, true, true, true]) = 49391 := rfl
example : workSteps (pairedProblem [true, false, true]) = 512430 := rfl

example : (rawTimeBound inputOnlyVerifier).eval 0 = 62883 := rfl
example : (rawTimeBound inputOnlyVerifier).eval 1 = 104748 := rfl
example : (rawTimeBound inputOnlyVerifier).eval 3 = 221994 := rfl
example : (rawTimeBound inputOnlyVerifier).eval 4 = 297375 := rfl
example : (rawTimeBound pairedVerifier).eval 3 = 3077592 := rfl

example (input : BitString) :
    Represents (Tape.ofInput input) (finalTape (inputOnlyProblem input)) :=
  finalTape_represents (inputOnlyProblem input)

example (input : BitString) :
    ∃ wordPrefix tail,
      finalOutside (inputOnlyProblem input) =
        wordPrefix ++ BuilderUnaryPolynomial.separatorSymbol ::
          List.replicate (finalTokenSlot (inputOnlyProblem input))
            BuilderUnaryPolynomial.unitSymbol ++
          BuilderUnaryPolynomial.scratchEndSymbol :: tail :=
  finalOutside_contains_finalTokenSlot (inputOnlyProblem input)

example (input : BitString) :
    encodeTokenPairs
        (CookLevin.BuilderFirstClausePrefix.firstClauseTokens
          (inputOnlyProblem input)) =
      (inputOnlyProblem input).encodedFormula.take
        (2 * ((inputOnlyProblem input).FormulaWidth + 12)) :=
  finalTokenBits_eq_encodedFormula_firstClause (inputOnlyProblem input)

example (input : BitString) :
    workStep? (machine (inputOnlyProblem input))
        (renameConfiguration
          CookLevin.BuilderFirstClausePrefix.WorkChain.firstState
          (CookLevin.BuilderFirstClausePrefix.finalConfiguration
            (inputOnlyProblem input))) =
      some (renameConfiguration
        CookLevin.BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration CursorAdvance.machine
          (CookLevin.BuilderFirstClausePrefix.finalTape
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
        (CookLevin.BuilderFirstClausePrefix.workSteps
          (inputOnlyProblem input))
        (rawInputWorkTape input) = .timeout :=
  prefixEndpoint_before_launch_timeout (inputOnlyProblem input)

example (input : BitString) :
    workBoundedDecide (machine (inputOnlyProblem input))
        (workSteps (inputOnlyProblem input) - 1)
        (rawInputWorkTape input) = .timeout :=
  work_one_step_short_timeout (inputOnlyProblem input)

example (fuel : Nat) (left right : List WorkSymbol) :
    (let config := renameConfiguration
        CookLevin.BuilderFirstClausePrefix.WorkChain.secondState
        (CursorAdvance.malformedScratchConfiguration left right)
     let result := workRun (machine (inputOnlyProblem [])) fuel config
     if result.state == (machine (inputOnlyProblem [])).acceptState then
       WorkVerdict.accept
     else if result.state == (machine (inputOnlyProblem [])).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  malformedCursorScratch_timeout (inputOnlyProblem []) fuel left right

end PNP.Concrete.CookLevinBuilderDynamicTokenCursorStepRegression
