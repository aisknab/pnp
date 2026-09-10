/-
Copyright (c) 2026 PNP Labs.

One source-derived body iteration of the complete Cook-Levin builder:
actual token lookup, scratch recovery, optional output emission and balanced
cursor advancement. Padding emits nothing but still advances. A missing
lookup is a distinct error result, never padding. Only the original body
and balance invariants are premises.

The fixed finite continuation shares the existing appender and cursor rule
tables. Bounds charge the already-written output explicitly; closing the
whole loop and bounding that output in original input size remain separate
obligations, as do exact complete formula output and the packaged reduction.
-/
import PNP.Concrete.CookLevinBuilderCursorTokenRecovery

namespace PNP.Concrete.CookLevin.BuilderCursorOutputAdvance

open PipelineStateNamespace (renameConfiguration)
open BuilderDividerOperands (count inside)
open BuilderClauseDividerOperands (quotient)
open BuilderClauseDividerExecution (constraintIndex)
open BuilderRequestedPairLookup (storedCells)
open BuilderCursorTokenRecovery (encodeResult decodeState)

def nextOutput (output : List CNFToken) : Option CNFToken → List CNFToken
  | none => output
  | some token => output ++ [token]

def appendEntry : Option CNFToken → Nat
  | none => BuilderTokenAppender.machine.acceptState
  | some token => BuilderTokenAppender.seekInputState token

def appendSteps (input : BitString) (output : List CNFToken) : Option CNFToken → Nat
  | none => 0
  | some _ => BuilderTokenAppender.workSteps input output

def continuation : WorkMachine :=
  WorkMachineChain.machine BuilderTokenAppender.machine BuilderBalancedCursor.machine

/-- Entries are fixed when the finite table is assembled, not supplied at runtime. -/
def entry (outcome : Fin 6) : Nat :=
  match decodeState outcome.val with
  | none => WorkMachineChain.secondState BuilderBalancedCursor.machine.rejectState
  | some request => WorkMachineChain.firstState (appendEntry request)

def classify (state : Nat) : Fin 6 := encodeResult (decodeState state)

def observe (configuration : WorkConfiguration) : Option (Option CNFToken) :=
  decodeState configuration.state

def machine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineTerminalHandoff.machineWithEntries
    (BuilderCursorTokenRecovery.machine verifier) continuation entry classify

def initialConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  workStartConfiguration (machine problem.verifier)
    (BuilderCursorSource.cursorTape problem index remaining output)

def continuationSteps {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (request : Option CNFToken) : Nat :=
  appendSteps problem.input output request + 1 +
    BuilderBalancedCursor.steps (BuilderCursorSource.registerPrefix problem).length index (remaining + 1)

def rawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderCursorTokenRecovery.rawTimeBound verifier)
    (.add (BuilderCursorSource.rawTimeBound verifier) (.linear 24 66))

def spanBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderCursorTokenRecovery.spanBound verifier)
    (.add (BuilderCursorSource.rawTimeBound verifier) (.linear 24 54))

private theorem appender_noRuleAtAccept : WorkMachineChain.NoRuleAtAccept BuilderTokenAppender.machine := by
  have h : ∀ rule ∈ BuilderTokenAppender.rules,
      rule.sourceState ≠ BuilderTokenAppender.acceptState := by decide
  exact h

theorem entry_encode_some (request : Option CNFToken) :
    entry (encodeResult (some request)) = WorkMachineChain.firstState (appendEntry request) := by
  unfold entry
  rw [BuilderCursorTokenRecovery.decode_encode]

theorem continuation_rules_pairwise :
    continuation.rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineChain.rules_pairwise_query_distinct _ _
    BuilderTokenAppender.rules_pairwise_query_distinct
    BuilderBalancedCursor.rules_pairwise_query_distinct appender_noRuleAtAccept

theorem continuation_noRuleAtAccept : WorkMachineChain.NoRuleAtAccept continuation :=
  WorkMachineChain.noRuleAtAccept _ _ BuilderBalancedCursor.noRuleAtAccept

/-- The request is an internal continuation parameter, not a premise of the
source-derived body theorem below. All output prefixes and body positions work. -/
theorem append_workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (request : Option CNFToken) :
    workRunExact? BuilderTokenAppender.machine (appendSteps problem.input output request)
      {state := appendEntry request, tape := BuilderCursorSource.cursorTape problem index remaining output} =
      some {state := BuilderTokenAppender.machine.acceptState,
            tape := BuilderCursorSource.cursorTape problem index remaining (nextOutput output request)} := by
  cases request with
  | none => rfl
  | some token =>
      rw [BuilderCursorSource.cursorTape_eq_workspace, BuilderCursorSource.cursorTape_eq_workspace]
      exact BuilderTokenAppender.appendToken_workRunExact _ _ _ token

theorem continuation_workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (request : Option CNFToken) :
    workRunExact? continuation (continuationSteps problem index remaining output request)
      {state := entry (encodeResult (some request)),
        tape := BuilderCursorSource.cursorTape problem index (remaining + 1) output} =
      some {state := continuation.acceptState,
            tape := BuilderCursorSource.cursorTape problem (index + 1) remaining (nextOutput output request)} := by
  rw [entry_encode_some]
  exact WorkMachineChain.workRunExact BuilderTokenAppender.machine BuilderBalancedCursor.machine
    (appendSteps problem.input output request)
    (BuilderBalancedCursor.steps (BuilderCursorSource.registerPrefix problem).length index (remaining + 1))
    {state := appendEntry request, tape := BuilderCursorSource.cursorTape problem index (remaining + 1) output}
    {state := BuilderTokenAppender.machine.acceptState,
      tape := BuilderCursorSource.cursorTape problem index (remaining + 1) (nextOutput output request)}
    {state := BuilderBalancedCursor.machine.acceptState,
      tape := BuilderCursorSource.cursorTape problem (index + 1) remaining (nextOutput output request)}
    (append_workRunExact problem index (remaining + 1) output request) rfl
    (BuilderCursorSource.advance_workRunExact problem index remaining (nextOutput output request))

theorem append_rawTime_le (input : BitString) (output : List CNFToken) (request : Option CNFToken) :
    6 * appendSteps input output request ≤ 24 * input.length + 12 * output.length + 48 := by
  have hSource := BuilderTokenAppender.sourceCellCount_le input
  cases request with
  | none => simp only [appendSteps]; omega
  | some token =>
      simp only [appendSteps, BuilderTokenAppender.workSteps, BuilderTokenAppender.halfSteps]
      omega

theorem continuation_rawTime_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (request : Option CNFToken)
    (hBalance : index + (remaining + 1) = BuilderFullScheduleCursorController.bodySlotCount problem) :
    6 * continuationSteps problem index remaining output request ≤
      (BuilderCursorSource.rawTimeBound problem.verifier).eval problem.input.length +
        24 * problem.input.length + 12 * output.length + 54 := by
  have hAppend := append_rawTime_le problem.input output request
  have hAdvance := BuilderCursorSource.rawTimeBound_le problem index (remaining + 1) hBalance
  simp only [continuationSteps]
  omega

/-- Every in-body source coordinate has an optional emission. A missing
outer lookup cannot be silently treated as an empty/padding emission. -/
theorem canonical_some_of_body {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hBody : quotient problem index < count problem) :
    ∃ request, BuilderCursorTokenLookup.canonicalResult problem index = some request := by
  have hIndex := BuilderClauseDividerExecution.constraintIndex_lt problem index hBody
  rw [← problem.formulaConstraintSchedule_length] at hIndex
  rw [BuilderCursorTokenLookup.canonical_result_eq_emit,
    problem.formulaConstraintSlotDirect_eq, List.getElem?_eq_getElem hIndex]
  exact ⟨_, rfl⟩

theorem rules_pairwise_query_distinct {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineTerminalHandoff.rules_pairwise_with_entries _ _ _ _
    (BuilderCursorTokenRecovery.rules_pairwise_query_distinct verifier)
    continuation_rules_pairwise continuation_noRuleAtAccept

theorem noRuleAtResult {language : Language} (verifier : PolynomialTimeVerifier language) (result : Fin 6) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier) result.val :=
  WorkMachineTerminalHandoff.noRuleAt_outcome_with_entries _ _ _ _ result

theorem noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (machine verifier) :=
  noRuleAtResult verifier 0

theorem noRuleAtReject {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier) (machine verifier).rejectState :=
  noRuleAtResult verifier 1

theorem acceptState_ne_rejectState {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState :=
  Nat.zero_ne_one

theorem rawTimeBound_eval {language : Language} (verifier : PolynomialTimeVerifier language) (n : Nat) :
    (rawTimeBound verifier).eval n = (BuilderCursorTokenRecovery.rawTimeBound verifier).eval n +
      ((BuilderCursorSource.rawTimeBound verifier).eval n + (24 * n + 66)) := rfl

theorem spanBound_eval {language : Language} (verifier : PolynomialTimeVerifier language) (n : Nat) :
    (spanBound verifier).eval n = (BuilderCursorTokenRecovery.spanBound verifier).eval n +
      ((BuilderCursorSource.rawTimeBound verifier).eval n + (24 * n + 54)) := rfl

/-- Actual lookup, recovery, optional emission and advancement. No selected
request, lookup-success, workspace, execution or correctness certificate is a
supplied premise. Bounds explicitly include the already-written output. -/
theorem workRun_polynomial_output_advance {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken)
    (hBody : quotient problem index < count problem)
    (hBalance : index + (remaining + 1) = BuilderFullScheduleCursorController.bodySlotCount problem) :
    ∃ (steps : Nat) (request : Option CNFToken) (final : WorkConfiguration),
      BuilderCursorTokenLookup.canonicalResult problem index = some request ∧
      workRunExact? (machine problem.verifier) steps
        (initialConfiguration problem index (remaining + 1) output) = some final ∧
      final.state < 6 ∧
      WorkMachineProgramGraph.NoRuleAt (machine problem.verifier) final.state ∧
      observe final = some request ∧
      WorkTape.BlankEquivalent final.tape
        (BuilderCursorSource.cursorTape problem (index + 1) remaining (nextOutput output request)) ∧
      storedCells final.tape ≤ (inside problem.input output).length +
        (spanBound problem.verifier).eval problem.input.length + 12 * output.length ∧
      6 * steps ≤ (rawTimeBound problem.verifier).eval problem.input.length + 12 * output.length := by
  obtain ⟨request, hCanonical⟩ := canonical_some_of_body problem index hBody
  obtain ⟨lookupSteps, middle, hLookup, _, hNo, hObserve, hTape, hSpace, hTime⟩ :=
    BuilderCursorTokenRecovery.workRun_polynomial_lookup_recovered problem index (remaining + 1) output hBody hBalance
  have hSelected : classify middle.state = encodeResult (some request) :=
    congrArg encodeResult (hObserve.trans hCanonical)
  have hCanonicalAfter := continuation_workRunExact problem index remaining output request
  rw [← hSelected] at hCanonicalAfter
  have hEquivalent : WorkConfiguration.BlankEquivalent
      {state := entry (classify middle.state), tape := middle.tape}
      {state := entry (classify middle.state), tape := BuilderCursorSource.cursorTape problem index (remaining + 1) output} :=
    ⟨rfl, hTape⟩
  obtain ⟨advanced, hAfter, hAdvanced⟩ :=
    PNP.Concrete.workRunExact?_transport continuation
      (continuationSteps problem index remaining output request) hEquivalent hCanonicalAfter
  have hAdvancedState : advanced.state = continuation.acceptState := hAdvanced.state
  have hAdvancedConfiguration : advanced = {state := continuation.acceptState, tape := advanced.tape} := by
    rw [← hAdvancedState]
  have hAfterPrepared : workRunExact? continuation
      (continuationSteps problem index remaining output request)
      {state := entry (classify middle.state), tape := middle.tape} =
      some {state := continuation.acceptState, tape := advanced.tape} := by
    rw [← hAdvancedConfiguration]
    exact hAfter
  have hRun := WorkMachineTerminalHandoff.workRunExact_with_entries
    (BuilderCursorTokenRecovery.machine problem.verifier) continuation entry classify
    lookupSteps (continuationSteps problem index remaining output request)
    (BuilderCursorSource.cursorTape problem index (remaining + 1) output) middle advanced.tape
    (BuilderCursorTokenRecovery.rules_pairwise_query_distinct problem.verifier)
    continuation_rules_pairwise continuation_noRuleAtAccept hLookup hNo hAfterPrepared
  have hAfterTime := continuation_rawTime_le problem index remaining output request hBalance
  have hAfterSpace := BuilderRequestedPairLookup.workRun_storedCells _ _ _ _ hAfter
  dsimp only at hAfterSpace
  refine ⟨lookupSteps + 1 + continuationSteps problem index remaining output request + 1,
    request, {state := (classify middle.state).val, tape := advanced.tape},
    hCanonical, hRun, (classify middle.state).isLt, noRuleAtResult problem.verifier (classify middle.state),
    ?_, hAdvanced.tape, ?_, ?_⟩
  · change decodeState (classify middle.state).val = some request
    rw [hSelected, BuilderCursorTokenRecovery.decode_encode]
  · simp only [spanBound_eval]
    omega
  · simp only [rawTimeBound_eval]
    omega

theorem uniform_polynomial_output_advance {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken)
    (hBody : quotient problem index < count problem)
    (hBalance : index + (remaining + 1) = BuilderFullScheduleCursorController.bodySlotCount problem) :
    ∃ (rawSteps : Nat) (request : Option CNFToken) (final : WorkConfiguration),
      BuilderCursorTokenLookup.canonicalResult problem index = some request ∧
      rawSteps ≤ (rawTimeBound problem.verifier).eval problem.input.length + 12 * output.length ∧
      run (compileWorkMachine (machine problem.verifier)) rawSteps
        (encodeWorkConfiguration (initialConfiguration problem index (remaining + 1) output)) =
        encodeWorkConfiguration final ∧
      final.state < 6 ∧
      WorkMachineProgramGraph.NoRuleAt (machine problem.verifier) final.state ∧
      observe final = some request ∧
      WorkTape.BlankEquivalent final.tape
        (BuilderCursorSource.cursorTape problem (index + 1) remaining (nextOutput output request)) ∧
      storedCells final.tape ≤ (inside problem.input output).length +
        (spanBound problem.verifier).eval problem.input.length + 12 * output.length := by
  obtain ⟨steps, request, final, hCanonical, hRun, hTag, hNo, hObserve, hTape, hSpace, hTime⟩ :=
    workRun_polynomial_output_advance problem index remaining output hBody hBalance
  exact ⟨6 * steps, request, final, hCanonical, hTime,
    run_compileWorkMachine_mul_of_workRunExact _ _ _ _ hRun, hTag, hNo, hObserve, hTape, hSpace⟩

end PNP.Concrete.CookLevin.BuilderCursorOutputAdvance
