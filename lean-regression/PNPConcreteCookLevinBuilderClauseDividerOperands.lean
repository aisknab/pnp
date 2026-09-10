import PNP.Concrete.CookLevinBuilderClauseDividerOperands

namespace PNP.Concrete.CookLevinBuilderClauseDividerOperandsRegression

open CookLevin CookLevin.BuilderClauseDividerOperands PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape inside count width quadratic)
open BuilderDividerSourceExecution (sourceSpan)

example : QuotientPreparation.machine.rules.Pairwise WorkMachineChain.QueryDistinct :=
  QuotientPreparation.rules_pairwise_query_distinct
example : WorkMachineChain.NoRuleAtAccept QuotientPreparation.machine := QuotientPreparation.noRuleAtAccept
example : QuotientPreparation.machine.acceptState ≠ QuotientPreparation.machine.rejectState :=
  QuotientPreparation.acceptState_ne_rejectState

example :
    workRunExact? QuotientPreparation.machine (QuotientPreparation.steps 0 0)
        (workStartConfiguration QuotientPreparation.machine
          (endTape [2, 0, 0, 0] [leftMarker, separatorSymbol, scratchEndSymbol, .oneBlank, .blank] [])) =
      some {
        state := QuotientPreparation.machine.acceptState
        tape := endTape [2, 0, 0, 0, 0, 0]
          [leftMarker, separatorSymbol, scratchEndSymbol, .oneBlank, .blank] []
      } := by decide

example :
    workRunExact? QuotientPreparation.machine (QuotientPreparation.steps 2 1)
        (workStartConfiguration QuotientPreparation.machine (endTape [7, 0, 1, 2] [rightMarker] [])) =
      some {
        state := QuotientPreparation.machine.acceptState
        tape := endTape [7, 0, 1, 2, 0, 1] [rightMarker] []
      } := by decide

example :
    workRunExact? QuotientPreparation.machine (QuotientPreparation.steps 2 2)
        (workStartConfiguration QuotientPreparation.machine (endTape [0, 2, 2] [] [])) =
      some {
        state := QuotientPreparation.machine.acceptState
        tape := endTape [0, 2, 2, 0, 2] [] []
      } := by decide

example :
    workRunExact? QuotientPreparation.machine (QuotientPreparation.steps 2 3)
        (workStartConfiguration QuotientPreparation.machine (endTape [3, 2] [] [])) =
      some {
        state := QuotientPreparation.machine.acceptState
        tape := endTape [3, 2, 0, 3] [] []
      } := by decide

example :
    workRunExact? QuotientPreparation.machine (QuotientPreparation.steps 3 0)
        (workStartConfiguration QuotientPreparation.machine (endTape [1, 4, 0, 3] [.blank] [])) =
      some {
        state := QuotientPreparation.machine.acceptState
        tape := endTape [1, 4, 0, 3, 0, 0] [.blank] []
      } := by decide

example :
    workRunExact? QuotientPreparation.machine (QuotientPreparation.steps 2 1 - 1)
        (workStartConfiguration QuotientPreparation.machine (endTape [1, 2] [] [])) ≠
      some {
        state := QuotientPreparation.machine.acceptState
        tape := endTape [1, 2, 0, 1] [] []
      } := by decide

private def wrongOffsetMachine : WorkMachine :=
  WorkMachineChain.machine BuilderDividerOperands.Delimiter.machine (RegisterCopy.machine 1)

/-- Selecting the adjacent count register cannot masquerade as copying the quotient. -/
example :
    workRunExact? wrongOffsetMachine (QuotientPreparation.steps 2 1)
        (workStartConfiguration wrongOffsetMachine (endTape [1, 2] [] [])) ≠
      some {
        state := wrongOffsetMachine.acceptState
        tape := endTape [1, 2, 0, 1] [] []
      } := by decide

example (older : List Nat) (count quotient : Nat) (workspace : List WorkSymbol) :
    workRunExact? QuotientPreparation.machine (QuotientPreparation.steps count quotient)
        (workStartConfiguration QuotientPreparation.machine (endTape (older ++ [quotient, count]) workspace [])) =
      some {
        state := QuotientPreparation.machine.acceptState
        tape := endTape (older ++ [quotient, count, 0, quotient]) workspace []
      } := QuotientPreparation.workRunExact older count quotient workspace

example {language : Language} (problem : VerifierTableauProblem language) :
    clauseWidth problem = problem.formulaClauseSlotsPerConstraint := clauseWidth_value problem

example {language : Language} (problem : VerifierTableauProblem language) :
    0 < clauseWidth problem := clauseWidth_pos problem

example {language : Language} (problem : VerifierTableauProblem language) :
    count problem = problem.formulaConstraintSlotCount * clauseWidth problem := clauseCount_product problem

/-- The second divisor is not the token width used by the first division. -/
example {language : Language} (problem : VerifierTableauProblem language) :
    clauseWidth problem ≠ width problem := by
  let variables := (formulaVariableCountPolynomial problem.verifier).eval problem.input.length
  change 1 + variables * variables ≠ 2 + (variables + 4) * (variables + 1)
  have h : variables * variables ≤ (variables + 4) * (variables + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    (newerValues problem index remaining).length = newerCount problem.verifier :=
  newerValues_length problem index remaining

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    newerCount verifier = nodeCount (formulaClauseTokenPolynomial verifier) +
      nodeCount (BuilderDimensionRegisters.widthPolynomial verifier) + 7 := newerCount_eq verifier

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    BuilderOperandRegisters.retainedValues problem index remaining =
      olderValues problem ++ [clauseWidth problem] ++ newerValues problem index remaining :=
  retainedValues_selection problem index remaining

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    clauseWidth problem ≤ (sourceSpan problem.verifier).eval problem.input.length ∧
      (newerValues problem index remaining).length + (newerValues problem index remaining).sum ≤
        (sourceSpan problem.verifier).eval problem.input.length :=
  source_selection_bounds problem index remaining hBalance

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    copyOffset verifier = nodeCount (formulaClauseTokenPolynomial verifier) +
      nodeCount (BuilderDimensionRegisters.widthPolynomial verifier) + 15 := copyOffset_eq verifier

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    (newerForCopy problem index remaining).length = copyOffset problem.verifier :=
  newerForCopy_length problem index remaining

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (BuilderSourceRegisterRestore.restorationFinal problem index remaining output).tape =
      tapeAfter problem index remaining output [] := restored_tape_handoff problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
        (initialConfiguration problem index remaining output) =
      some (finalConfiguration problem index remaining output) := workRunExact problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining)
        (encodeWorkConfiguration (initialConfiguration problem index remaining output)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining output) :=
  run_compile_exact problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).tape =
      endTape (dividerOlder problem index remaining ++ [count problem, 0, quotient problem index, clauseWidth problem])
        (inside problem.input output) [] := final_tape_layout problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).state = (machine problem.verifier).acceptState :=
  finalConfiguration_state problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    (preparedExtra problem index).length = 9 := preparedExtra_length problem index

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    (registerWord (BuilderOperandRegisters.retainedValues problem index remaining ++ preparedExtra problem index)).length ≤
      8 * (sourceSpan problem.verifier).eval problem.input.length + 9 :=
  final_register_span_le problem index remaining hBalance

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    workSteps problem index remaining ≤
      4 + 2 * quadratic (7 * (sourceSpan problem.verifier).eval problem.input.length + 8) :=
  workSteps_le problem index remaining hBalance

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    6 * workSteps problem index remaining ≤ (rawTimeBound problem.verifier).eval problem.input.length :=
  rawTimeBound_le problem index remaining hBalance

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct := rules_pairwise_query_distinct verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (machine verifier) := noRuleAtAccept verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState := machine_acceptState_ne_rejectState verifier

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (hBody : index / width problem < count problem) :
    workRunExact? (bodyMachine problem.verifier) (bodySteps problem index remaining)
        (bodyInitial problem index remaining output) = some (bodyFinal problem index remaining output) :=
  body_workRunExact problem index remaining output hBody

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (hBody : index / width problem < count problem) :
    run (compileWorkMachine (bodyMachine problem.verifier)) (6 * bodySteps problem index remaining)
        (encodeWorkConfiguration (bodyInitial problem index remaining output)) =
      encodeWorkConfiguration (bodyFinal problem index remaining output) :=
  body_run_compile_exact problem index remaining output hBody

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (bodyFinal problem index remaining output).state = (bodyMachine problem.verifier).acceptState :=
  body_finalConfiguration_state problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (bodyFinal problem index remaining output).tape =
      endTape (dividerOlder problem index remaining ++ [count problem, 0, quotient problem index, clauseWidth problem])
        (inside problem.input output) [] := body_final_tape_layout problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    6 * bodySteps problem index remaining ≤ (bodyRawTimeBound problem.verifier).eval problem.input.length :=
  body_rawTimeBound_le problem index remaining hBalance

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (bodyMachine verifier).rules.Pairwise WorkMachineChain.QueryDistinct := body_rules_pairwise_query_distinct verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (bodyMachine verifier) := body_noRuleAtAccept verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (bodyMachine verifier).acceptState ≠ (bodyMachine verifier).rejectState := body_acceptState_ne_rejectState verifier

end PNP.Concrete.CookLevinBuilderClauseDividerOperandsRegression
