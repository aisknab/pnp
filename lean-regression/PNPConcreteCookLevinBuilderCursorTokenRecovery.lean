/- Exact cursor-only interfaces and independent observation/clock contracts. -/
import PNP.Concrete.CookLevinBuilderCursorTokenRecovery

namespace PNP.Concrete.CookLevin.BuilderCursorTokenRecovery
open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape inside count)
open BuilderClauseDividerOperands (quotient)
open BuilderRequestedPairLookup (BlankExterior storedCells)

example (result : Option (Option CNFToken)) :
    decodeState (encodeResult result).val = result :=
  decode_encode result

example : Function.Injective encodeResult :=
  encodeResult_injective

example (configuration : WorkConfiguration) (tape : WorkTape) :
    observe {state := (classify configuration.state).val, tape := tape} =
      BuilderCursorTokenLookup.observe configuration :=
  classify_observe configuration tape

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

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (value : Nat) (scratch : List Nat)
    (outside : List WorkSymbol) (hBlank : BlankExterior outside) :
    WorkTape.BlankEquivalent
      (BuilderCursorRecovery.recoveredCursorTape problem index remaining output
        (BuilderCursorRecovery.clearedOutside value scratch outside))
      (BuilderCursorSource.cursorTape problem index remaining output) :=
  recovered_original_equivalent problem index remaining output value scratch outside hBlank

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken)
    (hBody : quotient problem index < count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    ∃ (steps : Nat) (final : WorkConfiguration),
      workRunExact? (machine problem.verifier) steps (initialConfiguration problem index remaining output) = some final ∧
      final.state < 6 ∧
      WorkMachineProgramGraph.NoRuleAt (machine problem.verifier) final.state ∧
      observe final = BuilderCursorTokenLookup.canonicalResult problem index ∧
      WorkTape.BlankEquivalent final.tape (BuilderCursorSource.cursorTape problem index remaining output) ∧
      storedCells final.tape ≤ (inside problem.input output).length + (spanBound problem.verifier).eval problem.input.length ∧
      6 * steps ≤ (rawTimeBound problem.verifier).eval problem.input.length :=
  workRun_polynomial_lookup_recovered problem index remaining output hBody hBalance

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken)
    (hBody : quotient problem index < count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    ∃ (rawSteps : Nat) (final : WorkConfiguration),
      rawSteps ≤ (rawTimeBound problem.verifier).eval problem.input.length ∧
      run (compileWorkMachine (machine problem.verifier)) rawSteps
        (encodeWorkConfiguration (initialConfiguration problem index remaining output)) = encodeWorkConfiguration final ∧
      final.state < 6 ∧
      WorkMachineProgramGraph.NoRuleAt (machine problem.verifier) final.state ∧
      observe final = BuilderCursorTokenLookup.canonicalResult problem index ∧
      WorkTape.BlankEquivalent final.tape (BuilderCursorSource.cursorTape problem index remaining output) ∧
      storedCells final.tape ≤ (inside problem.input output).length + (spanBound problem.verifier).eval problem.input.length :=
  uniform_polynomial_lookup_recovered problem index remaining output hBody hBalance

-- Stable public result codes independently fix the six-way distinction.
example :
    [(encodeResult (some (some .t))).val, (encodeResult (some (some .f))).val,
      (encodeResult (some none)).val, (encodeResult (some (some .sep))).val,
      (encodeResult (some (some .finish))).val, (encodeResult none).val] = [0, 1, 2, 3, 4, 5] := rfl

example : encodeResult none ≠ encodeResult (some none) := by decide

example : encodeResult (some (some .finish)) ≠ encodeResult none := by decide

example (first second : Option (Option CNFToken)) (h : first ≠ second) :
    encodeResult first ≠ encodeResult second := fun equality => h (encodeResult_injective equality)

-- Scratch contents cannot change a terminal observation.
example (state : Nat) (first second : WorkTape) :
    observe {state := state, tape := first} = observe {state := state, tape := second} := rfl

-- Both handoff steps are charged in raw time, independently of cleanup.
example {language : Language} (verifier : PolynomialTimeVerifier language) (input : Nat) :
    (rawTimeBound verifier).eval input =
      (BuilderCursorTokenLookup.rawTimeBound verifier).eval input + 12 +
        (recoveryRawTimeBound verifier).eval input := rfl

-- No source, recovery-run, scratch, family or blank certificate is supplied here.
example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken)
    (hBody : quotient problem index < count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    ∃ rawSteps final,
      rawSteps ≤ (rawTimeBound problem.verifier).eval problem.input.length ∧
      run (compileWorkMachine (machine problem.verifier)) rawSteps
        (encodeWorkConfiguration
          (workStartConfiguration (machine problem.verifier)
            (BuilderCursorSource.cursorTape problem index remaining output))) = encodeWorkConfiguration final ∧
      observe final = BuilderCursorTokenLookup.canonicalResult problem index ∧
      WorkTape.BlankEquivalent final.tape (BuilderCursorSource.cursorTape problem index remaining output) := by
  obtain ⟨steps, final, hTime, hRun, _, _, hObserve, hTape, _⟩ :=
    uniform_polynomial_lookup_recovered problem index remaining output hBody hBalance
  exact ⟨steps, final, hTime, hRun, hObserve, hTape⟩

end PNP.Concrete.CookLevin.BuilderCursorTokenRecovery
