/-
Copyright (c) 2026 PNP Labs.

Exact canonical-output contracts for every body coordinate and whole input.
Padding/missing separation and the trailing framing bit are checked independently.
-/
import PNP.Concrete.CookLevinBuilderCanonicalOutput

open PNP.Concrete
open PNP.Concrete.CookLevin
open BuilderDividerOperands (count width)
open BuilderClauseDividerOperands (quotient clauseWidth)
open BuilderFullScheduleCursorController (bodySlotCount)
open BuilderCanonicalOutput

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hBody : quotient problem index < count problem) :
    BuilderCursorTokenLookup.canonicalResult problem index = problem.formulaClauseTokenSlotDirect index :=
  canonical_result_eq_direct problem index hBody

example {language : Language} (problem : VerifierTableauProblem language) :
    (bodySchedule problem).length + 1 = bodySlotCount problem :=
  bodySchedule_length problem

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hBody : quotient problem index < count problem) :
    BuilderCursorTokenLookup.canonicalResult problem index = (bodySchedule problem)[index]? :=
  canonical_result_eq_getElem problem index hBody

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken)
    (hBalance : index + (remaining + 1) = bodySlotCount problem) :
    BuilderCursorLoop.completeOutput problem index remaining output =
      (output ++ FormulaSchedule.emit ((bodySchedule problem).drop index)) ++ [CNFToken.finish] :=
  completeOutput_eq_suffix problem index remaining output hBalance

example {language : Language} (problem : VerifierTableauProblem language) :
    BuilderRawInputLoop.outputTokens problem = encodeCNFTokens problem.formula :=
  outputTokens_eq_encodeCNFTokens problem

example {language : Language} (problem : VerifierTableauProblem language) :
    encodeTokenPairs (BuilderRawInputLoop.outputTokens problem) ++ [false] = problem.encodedFormula :=
  encoded_output_eq_encodedFormula problem

example {language : Language} (problem : VerifierTableauProblem language) :
    problem.encodedFormula.length ≤ (encodedSizeBound problem.verifier).eval problem.input.length :=
  encodedFormula_length_le problem

example {language : Language} (problem : VerifierTableauProblem language) :
    ∃ (steps : Nat) (final : WorkConfiguration),
      workRunExact? (BuilderRawInputLoop.machine problem.verifier) steps
        (BuilderRawInputLoop.initialConfiguration problem) = some final ∧
      final.state = (BuilderRawInputLoop.machine problem.verifier).acceptState ∧
      WorkTape.BlankEquivalent final.tape
        (BuilderCursorSource.cursorTape problem (bodySlotCount problem) 0 (encodeCNFTokens problem.formula)) ∧
      6 * steps ≤ (BuilderRawInputLoop.rawTimeBound problem.verifier).eval problem.input.length :=
  workRun_canonical_from_raw problem

example {language : Language} (problem : VerifierTableauProblem language) :
    ∃ (rawSteps : Nat) (final : WorkConfiguration),
      rawSteps ≤ (BuilderRawInputLoop.rawTimeBound problem.verifier).eval problem.input.length ∧
      run (compileWorkMachine (BuilderRawInputLoop.machine problem.verifier)) rawSteps
        (encodeWorkConfiguration (BuilderRawInputLoop.initialConfiguration problem)) = encodeWorkConfiguration final ∧
      final.state = (BuilderRawInputLoop.machine problem.verifier).acceptState ∧
      WorkTape.BlankEquivalent final.tape
        (BuilderCursorSource.cursorTape problem (bodySlotCount problem) 0 (encodeCNFTokens problem.formula)) ∧
      problem.encodedFormula.length ≤ (encodedSizeBound problem.verifier).eval problem.input.length :=
  uniform_raw_canonical_output problem

example : (none : Option (Option CNFToken)) ≠ some none := by decide

example (tokens : List (Option CNFToken)) :
    FormulaSchedule.emit (none :: tokens) = FormulaSchedule.emit tokens := rfl

example (token : CNFToken) (tokens : List (Option CNFToken)) :
    FormulaSchedule.emit (some token :: tokens) = token :: FormulaSchedule.emit tokens := rfl

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) (output : List CNFToken) :
    BuilderCursorLoop.completeOutput problem index 0 output = output ++ [CNFToken.finish] := rfl

example {language : Language} (problem : VerifierTableauProblem language) :
    problem.encodedFormula = encodeTokenPairs (encodeCNFTokens problem.formula) ++ [false] := rfl

example (tokens : List CNFToken) :
    (encodeTokenPairs tokens ++ [false]).length = 2 * tokens.length + 1 := by
  simp only [List.length_append, encodeTokenPairs_length, List.length_cons, List.length_nil]

example {language : Language} (problem : VerifierTableauProblem language) :
    (encodeCNFTokens problem.formula).length ≤
      (BuilderRawInputLoop.outputBound problem.verifier).eval problem.input.length := by
  rw [← outputTokens_eq_encodeCNFTokens]
  exact BuilderRawInputLoop.outputTokens_length_le problem
