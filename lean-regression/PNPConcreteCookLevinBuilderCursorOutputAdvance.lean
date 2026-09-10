/- Exact source-derived output/advance contracts and independent emission boundaries. -/
import PNP.Concrete.CookLevinBuilderCursorOutputAdvance

namespace PNP.Concrete.CookLevin.BuilderCursorOutputAdvance
open BuilderDividerOperands (count inside)
open BuilderClauseDividerOperands (quotient)
open BuilderRequestedPairLookup (storedCells)
open BuilderCursorTokenRecovery (encodeResult decodeState)

example (request : Option CNFToken) :
    entry (encodeResult (some request)) = WorkMachineChain.firstState (appendEntry request) :=
  entry_encode_some request

example :
    continuation.rules.Pairwise WorkMachineChain.QueryDistinct :=
  continuation_rules_pairwise

example : WorkMachineChain.NoRuleAtAccept continuation :=
  continuation_noRuleAtAccept

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (request : Option CNFToken) :
    workRunExact? BuilderTokenAppender.machine (appendSteps problem.input output request)
      {state := appendEntry request, tape := BuilderCursorSource.cursorTape problem index remaining output} =
      some {state := BuilderTokenAppender.machine.acceptState,
            tape := BuilderCursorSource.cursorTape problem index remaining (nextOutput output request)} :=
  append_workRunExact problem index remaining output request

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (request : Option CNFToken) :
    workRunExact? continuation (continuationSteps problem index remaining output request)
      {state := entry (encodeResult (some request)),
        tape := BuilderCursorSource.cursorTape problem index (remaining + 1) output} =
      some {state := continuation.acceptState,
            tape := BuilderCursorSource.cursorTape problem (index + 1) remaining (nextOutput output request)} :=
  continuation_workRunExact problem index remaining output request

example (input : BitString) (output : List CNFToken) (request : Option CNFToken) :
    6 * appendSteps input output request ≤ 24 * input.length + 12 * output.length + 48 :=
  append_rawTime_le input output request

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (request : Option CNFToken)
    (hBalance : index + (remaining + 1) = BuilderFullScheduleCursorController.bodySlotCount problem) :
    6 * continuationSteps problem index remaining output request ≤
      (BuilderCursorSource.rawTimeBound problem.verifier).eval problem.input.length +
        24 * problem.input.length + 12 * output.length + 54 :=
  continuation_rawTime_le problem index remaining output request hBalance

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hBody : quotient problem index < count problem) :
    ∃ request, BuilderCursorTokenLookup.canonicalResult problem index = some request :=
  canonical_some_of_body problem index hBody

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct :=
  rules_pairwise_query_distinct verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) (result : Fin 6) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier) result.val :=
  noRuleAtResult verifier result

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (machine verifier) :=
  noRuleAtAccept verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier) (machine verifier).rejectState :=
  noRuleAtReject verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState :=
  acceptState_ne_rejectState verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) (n : Nat) :
    (rawTimeBound verifier).eval n = (BuilderCursorTokenRecovery.rawTimeBound verifier).eval n +
      ((BuilderCursorSource.rawTimeBound verifier).eval n + (24 * n + 66)) :=
  rawTimeBound_eval verifier n

example {language : Language} (verifier : PolynomialTimeVerifier language) (n : Nat) :
    (spanBound verifier).eval n = (BuilderCursorTokenRecovery.spanBound verifier).eval n +
      ((BuilderCursorSource.rawTimeBound verifier).eval n + (24 * n + 54)) :=
  spanBound_eval verifier n

example {language : Language} (problem : VerifierTableauProblem language)
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
      6 * steps ≤ (rawTimeBound problem.verifier).eval problem.input.length + 12 * output.length :=
  workRun_polynomial_output_advance problem index remaining output hBody hBalance

example {language : Language} (problem : VerifierTableauProblem language)
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
        (spanBound problem.verifier).eval problem.input.length + 12 * output.length :=
  uniform_polynomial_output_advance problem index remaining output hBody hBalance

-- Padding emits nothing for every output prefix.
example (output : List CNFToken) : nextOutput output none = output := rfl

-- A real token is appended exactly once and in order.
example (output : List CNFToken) (token : CNFToken) :
    nextOutput output (some token) = output ++ [token] := rfl

-- Padding skips emission, but the continuation theorem still charges advancement.
example (input : BitString) (output : List CNFToken) :
    appendSteps input output none = 0 := rfl

-- Missing lookup cannot enter the padding continuation.
example : entry 5 ≠ entry 2 := by decide

-- The complete static entry map follows the recovered result coding.
example :
    [entry 0, entry 1, entry 2, entry 3, entry 4, entry 5] =
      [WorkMachineChain.firstState (BuilderTokenAppender.seekInputState .t),
       WorkMachineChain.firstState (BuilderTokenAppender.seekInputState .f),
       WorkMachineChain.firstState BuilderTokenAppender.machine.acceptState,
       WorkMachineChain.firstState (BuilderTokenAppender.seekInputState .sep),
       WorkMachineChain.firstState (BuilderTokenAppender.seekInputState .finish),
       WorkMachineChain.secondState BuilderBalancedCursor.machine.rejectState] := by rfl

-- No tape content supplies or changes the observed result.
example (state : Nat) (first second : WorkTape) :
    observe {state := state, tape := first} = observe {state := state, tape := second} := rfl

-- Every iteration grows the canonical output by at most one token.
example (output : List CNFToken) (request : Option CNFToken) :
    (nextOutput output request).length ≤ output.length + 1 := by
  cases request with
  | none => simp only [nextOutput]; omega
  | some token =>
      simp only [nextOutput, List.length_append, List.length_cons, List.length_nil]
      omega

-- A general growing prefix really incurs linear scan cost, even on empty input.
example (n : Nat) :
    6 * appendSteps [] (List.replicate n .t) (some .f) = 12 * n + 48 := by
  simp only [appendSteps, BuilderTokenAppender.workSteps, BuilderTokenAppender.halfSteps,
    BuilderTokenAppender.sourceCellCount, List.length_nil, List.length_replicate]
  change 6 * (2 * (1 + 0 + n + 3)) = 12 * n + 48
  omega

end PNP.Concrete.CookLevin.BuilderCursorOutputAdvance
