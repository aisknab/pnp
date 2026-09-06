import PNP.Concrete.CookLevinBuilderDividerOperands

namespace PNP.Concrete.CookLevinBuilderDividerOperandsRegression

open CookLevin CookLevin.BuilderDividerOperands
open PipelineTape

example : Delimiter.machine.rules.length = 18 := Delimiter.rules_length

example : Delimiter.machine.rules.Pairwise WorkMachineChain.QueryDistinct :=
  Delimiter.rules_pairwise_query_distinct

example : WorkMachineChain.NoRuleAtAccept Delimiter.machine := Delimiter.noRuleAtAccept

example : Delimiter.machine.acceptState ≠ Delimiter.machine.rejectState :=
  Delimiter.acceptState_ne_rejectState

example : workRunExact? Delimiter.machine 2
    (workStartConfiguration Delimiter.machine (endTape [] [] [])) =
  some { state := 2, tape := endTape [0] [] [] } := by decide

example : workRunExact? Delimiter.machine 2
    (workStartConfiguration Delimiter.machine (endTape [2, 0, 3]
      [leftMarker, .oneBlank, rightMarker] [rightMarker, .zeroOne])) =
  some {
    state := 2
    tape := endTape [2, 0, 3, 0] [leftMarker, .oneBlank, rightMarker] [.zeroOne]
  } := by decide

example : workRunExact? Delimiter.machine 2
    (workStartConfiguration Delimiter.machine
      { left := [], head := .blank, right := [] }) = none := by decide

example (values : List Nat) (inside tail : List WorkSymbol) :
    workRunExact? Delimiter.machine 2 (workStartConfiguration Delimiter.machine
      (endTape values inside tail)) =
    some {
      state := Delimiter.machine.acceptState
      tape := endTape (values ++ [0]) inside (tail.drop 1)
    } :=
  Delimiter.workRunExact values inside tail

example {language : Language} (problem : VerifierTableauProblem language) :
    count problem = problem.formulaClauseSlotCount := rfl

example {language : Language} (problem : VerifierTableauProblem language) :
    width problem = problem.formulaTokensPerClause := rfl

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    appended problem index =
      [problem.formulaClauseSlotCount, 0, index, problem.formulaTokensPerClause] := rfl

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    tokenOffset verifier = BuilderUnaryPolynomial.nodeCount
      (BuilderDimensionRegisters.widthPolynomial verifier) + 6 + 3 := rfl

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).tape =
      { left := (BuilderCursorSource.preservedTail problem).drop
          (count problem + index + width problem + 4),
        head := BuilderUnaryPolynomial.scratchEndSymbol,
        right := (BuilderUnaryPolynomial.registerWord
          (BuilderOperandRegisters.retainedValues problem index remaining ++
            [count problem, 0, index, width problem])).reverse ++ inside problem.input output } :=
  final_tape_layout problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
        (initialConfiguration problem index remaining output) =
      some (finalConfiguration problem index remaining output) :=
  workRunExact problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining)
        (encodeWorkConfiguration (initialConfiguration problem index remaining output)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining output) :=
  run_compile_exact problem index remaining output

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct :=
  rules_pairwise_query_distinct verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (machine verifier) := noRuleAtAccept verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState :=
  machine_acceptState_ne_rejectState verifier

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) :
    let span := (BuilderUnaryPolynomial.registerWord
      (BuilderOperandRegisters.retainedValues problem index remaining)).length
    workSteps problem index remaining ≤ span + 4 + quadratic span + 5 +
      2 * quadratic (3 * span + 3) := workSteps_le problem index remaining

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    6 * workSteps problem index remaining ≤
      (rawTimeBound problem.verifier).eval problem.input.length :=
  rawTimeBound_le problem index remaining hBalance

example {language : Language} (problem : VerifierTableauProblem language) :
    workRunExact? (fromRawMachine problem.verifier) (fromRawSteps problem)
      (fromRawInitial problem) = some (fromRawFinal problem) := fromRaw_workRunExact problem

example {language : Language} (problem : VerifierTableauProblem language) :
    run (compileWorkMachine (fromRawMachine problem.verifier)) (6 * fromRawSteps problem)
      (encodeWorkConfiguration (fromRawInitial problem)) =
      encodeWorkConfiguration (fromRawFinal problem) := fromRaw_run_compile_exact problem

example {language : Language} (problem : VerifierTableauProblem language) :
    6 * fromRawSteps problem ≤ (fromRawTimeBound problem.verifier).eval problem.input.length :=
  fromRawTimeBound_le problem

example {language : Language} (problem : VerifierTableauProblem language) :
    (fromRawFinal problem).tape.head = BuilderUnaryPolynomial.scratchEndSymbol := rfl

end PNP.Concrete.CookLevinBuilderDividerOperandsRegression
