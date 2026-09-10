/-
Copyright (c) 2026 PNP Labs.
Exact all-input cursor-root recovery-frame contracts. No source, request,
retained root, selected program, blank certificate or polynomial is supplied.
-/
import PNP.Concrete.CookLevinBuilderCursorTokenLookup

namespace PNP.Concrete.CookLevin.BuilderCursorTokenRecoveryFrameRegression

open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape inside count)
open BuilderClauseDividerOperands (quotient)
open BuilderRequestedPairLookup (BlankExterior)
open BuilderCursorTokenLookup

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (hBody : quotient problem index < count problem) :
    ∃ scratch, BuilderSourceTokenRequest.finalValues problem index remaining hBody =
      BuilderOperandRegisters.retainedValues problem index remaining ++ [count problem] ++ scratch :=
  BuilderCursorTokenLookup.source_retained_root problem index remaining hBody

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken)
    (hBody : quotient problem index < count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    ∃ (steps : Nat) (values : List Nat) (resultOutside : List WorkSymbol) (final : WorkConfiguration),
      workRunExact? (machine problem.verifier) steps (initialConfiguration problem index remaining output) = some final ∧
      final.state % 3 = 1 ∧
      WorkMachineProgramGraph.NoRuleAt (machine problem.verifier) final.state ∧
      observe final = canonicalResult problem index ∧
      (∃ scratch, values =
        BuilderOperandRegisters.retainedValues problem index remaining ++ [count problem] ++ scratch) ∧
      WorkTape.BlankEquivalent final.tape (endTape values (inside problem.input output) resultOutside) ∧
      BlankExterior resultOutside ∧
      (registerWord values).length + resultOutside.length ≤
        (canonicalSpanBound problem.verifier).eval problem.input.length ∧
      BuilderRequestedPairLookup.storedCells final.tape ≤
        (inside problem.input output).length + (spanBound problem.verifier).eval problem.input.length ∧
      6 * steps ≤ (rawTimeBound problem.verifier).eval problem.input.length :=
  BuilderCursorTokenLookup.workRun_polynomial_lookup_with_frame problem index remaining output hBody hBalance

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken)
    (hBody : quotient problem index < count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    ∃ (rawSteps : Nat) (values : List Nat) (resultOutside : List WorkSymbol) (final : WorkConfiguration),
      rawSteps ≤ (rawTimeBound problem.verifier).eval problem.input.length ∧
      run (compileWorkMachine (machine problem.verifier)) rawSteps
        (encodeWorkConfiguration (initialConfiguration problem index remaining output)) = encodeWorkConfiguration final ∧
      final.state % 3 = 1 ∧
      WorkMachineProgramGraph.NoRuleAt (machine problem.verifier) final.state ∧
      observe final = canonicalResult problem index ∧
      (∃ scratch, values =
        BuilderOperandRegisters.retainedValues problem index remaining ++ [count problem] ++ scratch) ∧
      WorkTape.BlankEquivalent final.tape (endTape values (inside problem.input output) resultOutside) ∧
      BlankExterior resultOutside ∧
      (registerWord values).length + resultOutside.length ≤
        (canonicalSpanBound problem.verifier).eval problem.input.length ∧
      BuilderRequestedPairLookup.storedCells final.tape ≤
        (inside problem.input output).length + (spanBound problem.verifier).eval problem.input.length :=
  BuilderCursorTokenLookup.uniform_polynomial_lookup_with_frame problem index remaining output hBody hBalance

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (hBody : quotient problem index < count problem) :
    (BuilderOperandRegisters.retainedValues problem index remaining).length <
      (BuilderSourceTokenRequest.finalValues problem index remaining hBody).length := by
  obtain ⟨scratch, hRoot⟩ := source_retained_root problem index remaining hBody
  rw [hRoot]
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

end PNP.Concrete.CookLevin.BuilderCursorTokenRecoveryFrameRegression
