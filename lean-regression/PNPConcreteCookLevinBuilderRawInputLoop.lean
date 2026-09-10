/-
Copyright (c) 2026 PNP Labs.

All-input entry and polynomial-bound contracts for the physical full builder
loop. No prepared header, scratch, selected request or execution is a premise.
-/
import PNP.Concrete.CookLevinBuilderRawInputLoop

open PNP.Concrete
open PNP.Concrete.CookLevin
open PipelineTape
open WorkMachineProgramGraph (NoRuleAt)
open BuilderFullScheduleCursorController (bodySlotCount bodySlotCountPolynomial)
open BuilderRawInputLoop

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct :=
  rules_pairwise_query_distinct verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    NoRuleAt (machine verifier) (machine verifier).acceptState :=
  noRuleAtAccept verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState :=
  acceptState_ne_rejectState verifier

example {language : Language} (problem : VerifierTableauProblem language) :
    (initialConfiguration problem).tape = rawInputWorkTape problem.input :=
  initialConfiguration_tape problem

example {language : Language} (problem : VerifierTableauProblem language) :
    (outputBound problem.verifier).eval problem.input.length =
      problem.FormulaWidth + 1 + bodySlotCount problem :=
  outputBound_eval problem

example {language : Language} (problem : VerifierTableauProblem language) :
    (rawTimeBound problem.verifier).eval problem.input.length =
      (BuilderInitialization.rawTimeBound problem.verifier).eval problem.input.length + 6 +
        bodySlotCount problem * ((BuilderCursorLoop.stepPolynomial problem.verifier).eval problem.input.length +
          12 * (problem.FormulaWidth + 1 + bodySlotCount problem)) :=
  rawTimeBound_eval problem

example {language : Language} (problem : VerifierTableauProblem language) :
    (outputTokens problem).length ≤ (outputBound problem.verifier).eval problem.input.length :=
  outputTokens_length_le problem

example {language : Language} (problem : VerifierTableauProblem language) :
    ∃ (steps : Nat) (final : WorkConfiguration),
      workRunExact? (machine problem.verifier) steps (initialConfiguration problem) = some final ∧
      final.state = (machine problem.verifier).acceptState ∧
      WorkTape.BlankEquivalent final.tape
        (BuilderCursorSource.cursorTape problem (bodySlotCount problem) 0 (outputTokens problem)) ∧
      6 * steps ≤ (rawTimeBound problem.verifier).eval problem.input.length :=
  workRun_from_raw problem

example {language : Language} (problem : VerifierTableauProblem language) :
    ∃ (rawSteps : Nat) (final : WorkConfiguration),
      rawSteps ≤ (rawTimeBound problem.verifier).eval problem.input.length ∧
      run (compileWorkMachine (machine problem.verifier)) rawSteps
        (encodeWorkConfiguration (initialConfiguration problem)) = encodeWorkConfiguration final ∧
      final.state = (machine problem.verifier).acceptState ∧
      WorkTape.BlankEquivalent final.tape
        (BuilderCursorSource.cursorTape problem (bodySlotCount problem) 0 (outputTokens problem)) ∧
      (outputTokens problem).length ≤ (outputBound problem.verifier).eval problem.input.length :=
  uniform_raw_from_input problem

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    machine verifier =
      WorkMachineChain.machine (BuilderInitialization.machine verifier) (BuilderCursorLoop.machine verifier) := rfl

example {language : Language} (verifier : PolynomialTimeVerifier language) (input : BitString) :
    initialConfiguration (VerifierTableauProblem.mk verifier input) =
      workStartConfiguration (machine verifier) (rawInputWorkTape input) := rfl

example {language : Language} (problem : VerifierTableauProblem language) :
    outputTokens problem = BuilderCursorLoop.completeOutput problem 0
      (bodySlotCount problem - 1) (encodeUnaryTokens problem.FormulaWidth) := rfl

example {language : Language} (problem : VerifierTableauProblem language) :
    (bodySlotCount problem - 1) + 1 = bodySlotCount problem := by
  have h := BuilderFullScheduleCursorController.bodySlotCount_positive problem
  omega

example {language : Language} (problem : VerifierTableauProblem language) :
    (encodeUnaryTokens problem.FormulaWidth).length ≤
      (outputBound problem.verifier).eval problem.input.length := by
  rw [encodeUnaryTokens_length, outputBound_eval]
  omega

example {language : Language} (problem : VerifierTableauProblem language) :
    (BuilderInitialization.rawTimeBound problem.verifier).eval problem.input.length + 6 ≤
      (rawTimeBound problem.verifier).eval problem.input.length := by
  rw [rawTimeBound_eval]
  omega
