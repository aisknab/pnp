import PNP.Concrete.CookLevinBuilderConstraintRegionAssembly

namespace PNP.Concrete.CookLevinBuilderConstraintRegionAssemblyRegression

open CookLevin CookLevin.BuilderConstraintRegionAssembly BuilderUnaryPolynomial
open BuilderDividerOperands (endTape inside count quadratic)
open BuilderClauseDividerOperands (quotient)
open BuilderClauseDividerExecution (constraintIndex)
open BuilderConstraintRegionRegisters (orderedLengths termValue regionLength)
open BuilderDividerSourceExecution (sourceSpan)

example : Increment.machine.rules.length = 18 := rfl

example (older : List Nat) (value : Nat) :
    (registerWord (older ++ [value + 1])).reverse =
      unitSymbol :: (registerWord (older ++ [value])).reverse :=
  Increment.reverse_word_increment older value

example (older : List Nat) (value : Nat) (workspace tail : List WorkSymbol) :
    workRunExact? Increment.machine 2
      (workStartConfiguration Increment.machine (endTape (older ++ [value]) workspace tail)) =
      some {
        state := Increment.machine.acceptState
        tape := endTape (older ++ [value + 1]) workspace (tail.drop 1)
      } := Increment.workRunExact older value workspace tail

example :
    workRunExact? Increment.machine 2
      (workStartConfiguration Increment.machine (endTape [2, 0] [.zeroBlank, .oneBlank] [.zeroZero, .oneOne])) =
      some { state := Increment.machine.acceptState, tape := endTape [2, 1] [.zeroBlank, .oneBlank] [.oneOne] } := by decide

example :
    workRunExact? Increment.machine 2
      (workStartConfiguration Increment.machine (endTape [0, 3] [.zeroZero] [])) =
      some { state := Increment.machine.acceptState, tape := endTape [0, 4] [.zeroZero] [] } := by decide

example :
    workRunExact? Increment.machine 1
      (workStartConfiguration Increment.machine (endTape [2, 0] [.zeroBlank] [])) ≠
      some { state := Increment.machine.acceptState, tape := endTape [2, 1] [.zeroBlank] [] } := by decide

example :
    workRunExact? Increment.machine 2
      { state := Increment.machine.startState, tape := { left := [], head := .blank, right := [] } } = none := by decide

example : Increment.machine.rules.Pairwise WorkMachineChain.QueryDistinct :=
  Increment.rules_pairwise_query_distinct

example : WorkMachineChain.NoRuleAtAccept Increment.machine := Increment.noRuleAtAccept

example : Increment.machine.acceptState ≠ Increment.machine.rejectState :=
  Increment.acceptState_ne_rejectState

example (values : List Nat) (workspace tail : List WorkSymbol) :
    workRunExact? oneMachine 5
      (workStartConfiguration oneMachine (endTape values workspace tail)) =
      some { state := oneMachine.acceptState, tape := endTape (values ++ [1]) workspace (tail.drop 2) } :=
  one_workRunExact values workspace tail

example :
    workRunExact? oneMachine 5
      (workStartConfiguration oneMachine (endTape [2, 0] [.zeroBlank, .oneBlank] [.zeroZero, .oneOne, .blankZero])) =
      some { state := oneMachine.acceptState, tape := endTape [2, 0, 1] [.zeroBlank, .oneBlank] [.blankZero] } := by decide

example :
    workRunExact? oneMachine 4
      (workStartConfiguration oneMachine (endTape [2, 0] [.zeroBlank] [])) ≠
      some { state := oneMachine.acceptState, tape := endTape [2, 0, 1] [.zeroBlank] [] } := by decide

example (older : List Nat) (value : Nat) (workspace tail : List WorkSymbol) :
    workRunExact? threeMachine 8
      (workStartConfiguration threeMachine (endTape (older ++ [value]) workspace tail)) =
      some { state := threeMachine.acceptState, tape := endTape (older ++ [value + 3]) workspace (tail.drop 3) } :=
  three_workRunExact older value workspace tail

example :
    workRunExact? threeMachine 8
      (workStartConfiguration threeMachine (endTape [2, 0] [.zeroZero, .blankOne] [.oneBlank, .zeroBlank, .oneOne, .zeroZero])) =
      some { state := threeMachine.acceptState, tape := endTape [2, 3] [.zeroZero, .blankOne] [.zeroZero] } := by decide

example :
    workRunExact? threeMachine 8
      (workStartConfiguration threeMachine (endTape [2, 4] [.blankOne] [.oneBlank])) =
      some { state := threeMachine.acceptState, tape := endTape [2, 7] [.blankOne] [] } := by decide

example :
    workRunExact? threeMachine 7
      (workStartConfiguration threeMachine (endTape [2, 0] [.zeroZero] [])) ≠
      some { state := threeMachine.acceptState, tape := endTape [2, 3] [.zeroZero] [] } := by decide

example {language : Language} (problem : VerifierTableauProblem language) :
    afterInitial problem =
      [1, termValue problem .preservation, termValue problem .control, 3 + termValue problem .initialTail] := rfl

example {language : Language} (problem : VerifierTableauProblem language) :
    lengthFrame problem =
      [1, termValue problem .preservation, termValue problem .control,
       3 + termValue problem .initialTail, termValue problem .shape] := rfl

example {language : Language} (problem : VerifierTableauProblem language) :
    (lengthFrame problem).reverse = orderedLengths problem := lengthFrame_reverse problem

example {language : Language} (problem : VerifierTableauProblem language) :
    (lengthFrame problem).sum = problem.formulaConstraintSlotCount := lengthFrame_sum problem

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    (preparedFrame problem index).reverse = constraintIndex problem index :: orderedLengths problem :=
  preparedFrame_reverse problem index

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    (preparedFrame problem index).length = 6 := preparedFrame_length problem index

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    (preparedFrame problem index).sum = problem.formulaConstraintSlotCount + constraintIndex problem index :=
  preparedFrame_sum problem index

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    finalValues problem index remaining =
      BuilderClauseCoordinateRegisters.finalValues problem index remaining ++
        [1, termValue problem .preservation, termValue problem .control,
         3 + termValue problem .initialTail, termValue problem .shape, constraintIndex problem index] := rfl

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    machine verifier =
      WorkMachineChain.machine oneMachine
        (WorkMachineChain.machine (BuilderConstraintRegionRegisters.copyMachine verifier .preservation 1)
          (WorkMachineChain.machine (BuilderConstraintRegionRegisters.copyMachine verifier .control 2)
            (WorkMachineChain.machine (BuilderConstraintRegionRegisters.copyMachine verifier .initialTail 3)
              (WorkMachineChain.machine threeMachine
                (WorkMachineChain.machine (BuilderConstraintRegionRegisters.copyMachine verifier .shape 4)
                  (RegisterCopy.machine 5)))))) := rfl

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    workSteps problem index remaining =
      BuilderConstraintRegionRegisters.copySteps problem index remaining [1] .preservation +
      BuilderConstraintRegionRegisters.copySteps problem index remaining (afterPreservation problem) .control +
      BuilderConstraintRegionRegisters.copySteps problem index remaining (afterControl problem) .initialTail +
      BuilderConstraintRegionRegisters.copySteps problem index remaining (afterInitial problem) .shape +
      RegisterCopy.steps (lengthFrame problem) (constraintIndex problem index) + 19 := rfl

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (workspace tail : List WorkSymbol) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
      (workStartConfiguration (machine problem.verifier)
        (endTape (BuilderClauseCoordinateRegisters.finalValues problem index remaining) workspace tail)) =
      some {
        state := (machine problem.verifier).acceptState
        tape := endTape (finalValues problem index remaining) workspace (tail.drop (consumedCells problem index))
      } := workRunExact problem index remaining workspace tail

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (workspace tail : List WorkSymbol) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining)
      (encodeWorkConfiguration (workStartConfiguration (machine problem.verifier)
        (endTape (BuilderClauseCoordinateRegisters.finalValues problem index remaining) workspace tail))) =
      encodeWorkConfiguration {
        state := (machine problem.verifier).acceptState
        tape := endTape (finalValues problem index remaining) workspace (tail.drop (consumedCells problem index))
      } := run_compile_exact problem index remaining workspace tail

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    consumedCells problem index = problem.formulaConstraintSlotCount + constraintIndex problem index + 6 := rfl

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    problem.formulaConstraintSlotCount ≤ (sourceSpan problem.verifier).eval problem.input.length :=
  constraintCount_le_sourceSpan problem index remaining hBalance

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    consumedCells problem index ≤ 2 * (sourceSpan problem.verifier).eval problem.input.length + 6 :=
  consumedCells_le problem index remaining hBalance

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    (registerWord (finalValues problem index remaining)).length ≤
      11 * (sourceSpan problem.verifier).eval problem.input.length + 17 :=
  final_register_span_le problem index remaining hBalance

example {language : Language} (verifier : PolynomialTimeVerifier language) (inputLength : Nat) :
    (copyBudget verifier).eval inputLength = 10 * (sourceSpan verifier).eval inputLength + 16 := rfl

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    workSteps problem index remaining ≤ 5 * quadratic ((copyBudget problem.verifier).eval problem.input.length) + 19 :=
  workSteps_le problem index remaining hBalance

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    6 * workSteps problem index remaining ≤ (rawTimeBound problem.verifier).eval problem.input.length :=
  rawTimeBound_le problem index remaining hBalance

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct := rules_pairwise_query_distinct verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (machine verifier) := noRuleAtAccept verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState := acceptState_ne_rejectState verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    bodyMachine verifier = WorkMachineChain.machine
      (BuilderClauseCoordinateRegisters.machine verifier) (machine verifier) := rfl

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    bodyInitial problem index remaining output =
      workStartConfiguration (bodyMachine problem.verifier)
        (BuilderCursorSource.cursorTape problem index remaining output) := rfl

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (bodyFinal problem index remaining output).tape =
      endTape (finalValues problem index remaining) (inside problem.input output) [] := rfl

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (hBody : quotient problem index < count problem) :
    workRunExact? (bodyMachine problem.verifier) (bodySteps problem index remaining)
      (bodyInitial problem index remaining output) = some (bodyFinal problem index remaining output) :=
  body_workRunExact problem index remaining output hBody

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (hBody : quotient problem index < count problem) :
    run (compileWorkMachine (bodyMachine problem.verifier)) (6 * bodySteps problem index remaining)
      (encodeWorkConfiguration (bodyInitial problem index remaining output)) =
      encodeWorkConfiguration (bodyFinal problem index remaining output) :=
  body_run_compile_exact problem index remaining output hBody

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hBody : quotient problem index < count problem) :
    constraintIndex problem index < (lengthFrame problem).sum := body_constraintIndex_valid problem index hBody

example {language : Language} (verifier : PolynomialTimeVerifier language) (inputLength : Nat) :
    (bodyRawTimeBound verifier).eval inputLength =
      (BuilderClauseCoordinateRegisters.rawTimeBound verifier).eval inputLength + 6 +
        (rawTimeBound verifier).eval inputLength := by
  simp only [bodyRawTimeBound, NatPolynomial.eval_add, NatPolynomial.eval_constant]
  omega

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    6 * bodySteps problem index remaining ≤ (bodyRawTimeBound problem.verifier).eval problem.input.length :=
  body_rawTimeBound_le problem index remaining hBalance

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (bodyMachine verifier).rules.Pairwise WorkMachineChain.QueryDistinct := body_rules_pairwise_query_distinct verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (bodyMachine verifier) := body_noRuleAtAccept verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (bodyMachine verifier).acceptState ≠ (bodyMachine verifier).rejectState := body_acceptState_ne_rejectState verifier

end PNP.Concrete.CookLevinBuilderConstraintRegionAssemblyRegression
