import PNP

namespace PNP.Concrete.CookLevinBuilderFullScheduleCursorControllerRegression

open PipelineTape PipelineStateNamespace
open CookLevin
open CookLevin.BuilderFullScheduleCursorController

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

example (input : BitString) :
    firstBodySlot (inputOnlyProblem input) =
      (inputOnlyProblem input).formulaVariableSlotBound + 1 :=
  firstBodySlot_eq (inputOnlyProblem input)

example (input : BitString) :
    bodySlotCount (inputOnlyProblem input) =
      (inputOnlyProblem input).formulaClauseSlotCount *
        (inputOnlyProblem input).formulaTokensPerClause + 1 :=
  bodySlotCount_eq (inputOnlyProblem input)

example (input : BitString) :
    terminalSlot (inputOnlyProblem input) =
      (inputOnlyProblem input).formulaTokenSlotCountDirect :=
  terminalSlot_eq (inputOnlyProblem input)

example (input : BitString) :
    firstBodySlot (inputOnlyProblem input) +
        bodySlotCount (inputOnlyProblem input) =
      terminalSlot (inputOnlyProblem input) :=
  firstBodySlot_add_bodySlotCount (inputOnlyProblem input)

example (input : BitString) :
    TokenCursor.run (inputOnlyProblem input)
        (bodySlotCount (inputOnlyProblem input))
        ⟨firstBodySlot (inputOnlyProblem input)⟩ =
      ((inputOnlyProblem input).formulaTokenSchedule.drop
          (firstBodySlot (inputOnlyProblem input)),
        ⟨(inputOnlyProblem input).formulaTokenSlotCountDirect⟩) :=
  TokenCursor.run_body (inputOnlyProblem input)

example (input : BitString) :
    FormulaSchedule.emit
        (TokenCursor.run (inputOnlyProblem input)
          (inputOnlyProblem input).formulaTokenSlotCountDirect
          VerifierTableauProblem.FormulaTokenCursor.initial).1 =
      encodeCNFTokens (inputOnlyProblem input).formula :=
  TokenCursor.run_full_emit_eq_encodeCNFTokens (inputOnlyProblem input)

example (input : BitString) :
    (machine (inputOnlyProblem input)).rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) :=
  rules_pairwise_query_distinct (inputOnlyProblem input)

example (input : BitString) :
    Represents (Tape.ofInput input) (finalTape (inputOnlyProblem input)) :=
  finalTape_represents (inputOnlyProblem input)

example (input : BitString) :
    workRunExact? (machine (inputOnlyProblem input))
        (workSteps (inputOnlyProblem input))
        (workStartConfiguration (machine (inputOnlyProblem input))
          (rawInputWorkTape input)) =
      some (finalConfiguration (inputOnlyProblem input)) :=
  workRunExact (inputOnlyProblem input)

example (input : BitString) :
    terminalSlot (inputOnlyProblem input) =
      (inputOnlyProblem input).formulaTokenSchedule.length :=
  finalTokenSlot_eq_complete_schedule (inputOnlyProblem input)

example (input : BitString) :
    6 * workSteps (inputOnlyProblem input) ≤
      (rawTimeBound inputOnlyVerifier).eval input.length :=
  rawTimeBound_le (inputOnlyProblem input)

example (input : BitString) :
    boundedDecide
        (compileWorkMachine (machine (inputOnlyProblem input)))
        ((rawTimeBound inputOnlyVerifier).eval input.length) input =
      .accept :=
  boundedDecide_compile_accept (inputOnlyProblem input)

example (input : BitString) :
    workBoundedDecide (machine (inputOnlyProblem input))
        (BuilderCompleteHeader.workSteps (inputOnlyProblem input))
        (rawInputWorkTape input) = .timeout :=
  prefixEndpoint_before_launch_timeout (inputOnlyProblem input)

example (input : BitString) :
    workBoundedDecide (machine (inputOnlyProblem input))
        (workSteps (inputOnlyProblem input) - 1)
        (rawInputWorkTape input) = .timeout :=
  work_one_step_short_timeout (inputOnlyProblem input)

example (fuel : Nat) (left right : List WorkSymbol) :
    (let config := malformedCountdownScratchConfiguration left right
     let result := workRun
       BuilderFirstClausePaddingRun.PaddingCountdown.machine fuel config
     if result.state ==
        BuilderFirstClausePaddingRun.PaddingCountdown.machine.acceptState then
       WorkVerdict.accept
     else if result.state ==
        BuilderFirstClausePaddingRun.PaddingCountdown.machine.rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  malformedCountdownScratch_timeout fuel left right

example (input : BitString) :
    TokenCursor.run (pairedProblem input)
        (pairedProblem input).formulaTokenSlotCountDirect
        VerifierTableauProblem.FormulaTokenCursor.initial =
      ((pairedProblem input).formulaTokenSchedule,
        ⟨(pairedProblem input).formulaTokenSlotCountDirect⟩) ∧
    workRunExact? (machine (pairedProblem input))
        (workSteps (pairedProblem input))
        (workStartConfiguration (machine (pairedProblem input))
          (rawInputWorkTape input)) =
          some (finalConfiguration (pairedProblem input)) ∧
    terminalSlot (pairedProblem input) =
        (pairedProblem input).formulaTokenSchedule.length ∧
    6 * workSteps (pairedProblem input) ≤
      (rawTimeBound pairedVerifier).eval input.length ∧
    boundedDecide
        (compileWorkMachine (machine (pairedProblem input)))
        ((rawTimeBound pairedVerifier).eval input.length) input = .accept ∧
    workBoundedDecide (machine (pairedProblem input))
        (BuilderCompleteHeader.workSteps (pairedProblem input))
        (rawInputWorkTape input) = .timeout ∧
    workBoundedDecide (machine (pairedProblem input))
        (workSteps (pairedProblem input) - 1)
        (rawInputWorkTape input) = .timeout :=
  cook_levin_full_schedule_cursor_controller_checked_complete
    (pairedProblem input)

end PNP.Concrete.CookLevinBuilderFullScheduleCursorControllerRegression
