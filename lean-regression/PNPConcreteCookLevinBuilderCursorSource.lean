import PNP.Concrete.CookLevinBuilderCursorSource

namespace PNP.Concrete.CookLevinBuilderCursorSourceRegression

open CookLevin CookLevin.BuilderCursorSource

example : prefixWord (.constant 0) (.constant 1) 0 =
    [BuilderUnaryPolynomial.separatorSymbol, BuilderUnaryPolynomial.separatorSymbol,
      BuilderUnaryPolynomial.separatorSymbol, BuilderUnaryPolynomial.unitSymbol] := by decide

example : (prefixWord (.constant 3) (.constant 2) 7).length = 8 := by decide

example (counter width : NatPolynomial) (inputLength : Nat) :
    BuilderUnaryPolynomial.scratchWord
        (BuilderDimensionRegisters.preparationPolynomial counter width) inputLength =
      BuilderBalancedCursor.word (prefixWord counter width inputLength) 0
        (counter.eval inputLength) :=
  prefixWord_layout counter width inputLength

example (counter width : NatPolynomial) (inputLength : Nat) :
    BuilderBalancedCursor.RegisterSymbols (prefixWord counter width inputLength) :=
  prefixWord_symbols counter width inputLength

example {language : Language} (problem : VerifierTableauProblem language) :
    BuilderUnaryPolynomial.scratchWord
        (BuilderDimensionRegisters.polynomial problem.verifier) problem.input.length =
      BuilderBalancedCursor.word (registerPrefix problem) 0
        (BuilderFullScheduleCursorController.bodySlotCount problem) := sourceWord_layout problem

example {language : Language} (problem : VerifierTableauProblem language) :
    BuilderBalancedCursor.RegisterSymbols (registerPrefix problem) := registerPrefix_symbols problem

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    cursorTape problem index remaining output =
      BuilderTokenAppender.workspaceTape problem.input
        (BuilderBalancedCursor.outside (registerPrefix problem) index remaining
          (preservedTail problem)) output := cursorTape_eq_workspace problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    PipelineTape.Represents (Tape.ofInput problem.input) (cursorTape problem index remaining output) :=
  cursorTape_represents problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language) :
    (BuilderInitialization.finalConfiguration problem).tape =
      cursorTape problem 0 (BuilderFullScheduleCursorController.bodySlotCount problem)
        (encodeUnaryTokens problem.FormulaWidth) := initializer_tape_handoff problem

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    workRunExact? BuilderBalancedCursor.machine
        (BuilderBalancedCursor.steps (registerPrefix problem).length index (remaining + 1))
        (initialConfiguration problem index (remaining + 1) output) =
      some (advancedConfiguration problem index remaining output) :=
  advance_workRunExact problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (output : List CNFToken) :
    workRunExact? BuilderBalancedCursor.machine
        (BuilderBalancedCursor.steps (registerPrefix problem).length index 0)
        (initialConfiguration problem index 0 output) =
      some (exhaustedConfiguration problem index output) := exhausted_workRunExact problem index output

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    run (compileWorkMachine BuilderBalancedCursor.machine)
        (6 * BuilderBalancedCursor.steps (registerPrefix problem).length index (remaining + 1))
        (encodeWorkConfiguration (initialConfiguration problem index (remaining + 1) output)) =
      encodeWorkConfiguration (advancedConfiguration problem index remaining output) :=
  compiled_advance problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language) :
    (rawTimeBound problem.verifier).eval problem.input.length =
      12 * (BuilderUnaryPolynomial.scratchWord
        (BuilderDimensionRegisters.polynomial problem.verifier) problem.input.length).length + 36 :=
  rawTimeBound_eval problem

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    (BuilderBalancedCursor.word (registerPrefix problem) index remaining).length =
      (BuilderUnaryPolynomial.scratchWord
        (BuilderDimensionRegisters.polynomial problem.verifier) problem.input.length).length :=
  invariant_span problem index remaining hBalance

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    6 * BuilderBalancedCursor.steps (registerPrefix problem).length index remaining ≤
      (rawTimeBound problem.verifier).eval problem.input.length :=
  rawTimeBound_le problem index remaining hBalance

end PNP.Concrete.CookLevinBuilderCursorSourceRegression
