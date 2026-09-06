import PNP.Concrete.CookLevinBuilderOperandRegisters

namespace PNP.Concrete.CookLevinBuilderOperandRegistersRegression

open CookLevin CookLevin.BuilderOperandRegisters

example : rootPrefix (.constant 0) 9 = [] := by decide

example : rootPrefix (.add (.constant 2) (.constant 3)) 0 = [2, 3] := by decide

example :
    prefixValues (.add (.mul (.constant 2) (.constant 3)) (.constant 1)) (.constant 5) 0 =
      [2, 3, 6, 1, 7, 0, 5] := by decide

example : Operand.tokenWidth ≠ Operand.clauseCount := by decide

example (polynomial : NatPolynomial) (input : Nat) :
    BuilderUnaryPolynomial.registerValues polynomial input =
      rootPrefix polynomial input ++ [polynomial.eval input] :=
  registerValues_rootPrefix polynomial input

example (counter width : NatPolynomial) (input : Nat) :
    BuilderCursorSource.prefixWord counter width input =
      BuilderUnaryPolynomial.registerWord (prefixValues counter width input) :=
  prefixWord_values counter width input

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    BuilderBalancedCursor.word (BuilderCursorSource.registerPrefix problem) index remaining =
      BuilderUnaryPolynomial.registerWord (retainedValues problem index remaining) :=
  cursorWord_values problem index remaining

example {language : Language} (problem : VerifierTableauProblem language)
    (operand : Operand) (index remaining : Nat) :
    (newerValues problem index remaining operand).length = newerCount problem.verifier operand :=
  newerValues_length problem operand index remaining

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    newerCount verifier .tokenWidth =
      BuilderUnaryPolynomial.nodeCount (BuilderDimensionRegisters.widthPolynomial verifier) + 6 := rfl

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    newerCount verifier .clauseCount =
      BuilderUnaryPolynomial.nodeCount (formulaClauseTokenPolynomial verifier) +
      BuilderUnaryPolynomial.nodeCount (BuilderDimensionRegisters.widthPolynomial verifier) + 6 := rfl

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    newerCount verifier .index = 1 := rfl

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    copiedValue problem index .tokenWidth = problem.formulaTokensPerClause :=
  tokenWidth_value problem index

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    copiedValue problem index .clauseCount = problem.formulaClauseSlotCount :=
  clauseCount_value problem index

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    copiedValue problem index .index = index := index_value problem index

example {language : Language} (problem : VerifierTableauProblem language)
    (operand : Operand) (index remaining : Nat) :
    retainedValues problem index remaining =
      olderValues problem operand ++ [copiedValue problem index operand] ++
        newerValues problem index remaining operand :=
  retainedValues_selection problem operand index remaining

example {language : Language} (problem : VerifierTableauProblem language)
    (operand : Operand) (index remaining : Nat) :
    BuilderBalancedCursor.word (BuilderCursorSource.registerPrefix problem) index remaining =
      BuilderRegisterAccess.encodedWord (BuilderUnaryPolynomial.registerWord (olderValues problem operand))
        (copiedValue problem index operand) (newerValues problem index remaining operand) :=
  cursorWord_selection problem operand index remaining

example {language : Language} (problem : VerifierTableauProblem language) (operand : Operand) :
    (BuilderInitialization.finalConfiguration problem).tape =
      (initialConfiguration problem operand 0 (BuilderFullScheduleCursorController.bodySlotCount problem)
        (encodeUnaryTokens problem.FormulaWidth)).tape := initializer_tape_handoff problem operand

example {language : Language} (problem : VerifierTableauProblem language)
    (operand : Operand) (index remaining : Nat) (output : List CNFToken) :
    workRunExact? (machine problem.verifier operand) (workSteps problem operand index remaining)
        (initialConfiguration problem operand index remaining output) =
      some (finalConfiguration problem operand index remaining output) :=
  workRunExact problem operand index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (operand : Operand) (index remaining : Nat) (output : List CNFToken) :
    run (compileWorkMachine (machine problem.verifier operand)) (6 * workSteps problem operand index remaining)
        (encodeWorkConfiguration (initialConfiguration problem operand index remaining output)) =
      encodeWorkConfiguration (finalConfiguration problem operand index remaining output) :=
  run_compile_exact problem operand index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (operand : Operand) (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem operand index remaining output).state =
      (machine problem.verifier operand).acceptState :=
  finalConfiguration_state problem operand index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (operand : Operand) (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    6 * workSteps problem operand index remaining ≤
      (rawTimeBound problem.verifier).eval problem.input.length :=
  rawTimeBound_le problem operand index remaining hBalance

example {language : Language} (problem : VerifierTableauProblem language) (operand : Operand) :
    workRunExact? (fromRawMachine problem.verifier operand) (fromRawSteps problem operand)
        (fromRawInitial problem operand) = some (fromRawFinal problem operand) :=
  fromRaw_workRunExact problem operand

example {language : Language} (problem : VerifierTableauProblem language) (operand : Operand) :
    run (compileWorkMachine (fromRawMachine problem.verifier operand))
        (6 * fromRawSteps problem operand) (encodeWorkConfiguration (fromRawInitial problem operand)) =
      encodeWorkConfiguration (fromRawFinal problem operand) := fromRaw_run_compile_exact problem operand

example {language : Language} (problem : VerifierTableauProblem language) (operand : Operand) :
    6 * fromRawSteps problem operand ≤ (fromRawTimeBound problem.verifier).eval problem.input.length :=
  fromRawTimeBound_le problem operand

example {language : Language} (problem : VerifierTableauProblem language) (operand : Operand) :
    (fromRawFinal problem operand).tape.head = BuilderUnaryPolynomial.scratchEndSymbol := rfl

end PNP.Concrete.CookLevinBuilderOperandRegistersRegression
