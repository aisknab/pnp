import PNP.Concrete.CookLevinBuilderClauseCoordinateRegisters

namespace PNP.Concrete.CookLevinBuilderClauseCoordinateRegistersRegression

open CookLevin CookLevin.BuilderClauseCoordinateRegisters BuilderUnaryPolynomial
open BuilderDividerOperands (count width inside endTape)
open BuilderClauseDividerOperands (clauseWidth quotient)
open BuilderDividerSourceExecution (sourceSpan)

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    (sourceView problem index).quotient = (index / width problem) / clauseWidth problem := rfl

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    (sourceView problem index).remainder = (index / width problem) % clauseWidth problem := rfl

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    (sourceView problem index).consumed =
      ((index / width problem) / clauseWidth problem) * clauseWidth problem := rfl

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    (sourceView problem index).sidecarCount = problem.formulaClauseSlotCount := rfl

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (BuilderClauseDividerExecution.finalConfiguration problem index remaining output).tape =
      (BuilderDividerCoordinateRegisters.initialConfiguration (sourceView problem index)
        (workspace problem index remaining output) []).tape :=
  input_tape_handoff problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (restorationFinal problem index remaining output).tape =
      endTape (finalValues problem index remaining) (inside problem.input output) [] :=
  restoration_final_tape problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    workRunExact? BuilderDividerCoordinateRegisters.machine (restorationSteps problem index)
      (workStartConfiguration BuilderDividerCoordinateRegisters.machine
        (BuilderClauseDividerExecution.finalConfiguration problem index remaining output).tape) =
      some (restorationFinal problem index remaining output) :=
  restoration_workRunExact problem index remaining output

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    machine verifier = WorkMachineChain.machine
      (BuilderClauseDividerExecution.bodyMachine verifier) BuilderDividerCoordinateRegisters.machine := rfl

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (hBody : quotient problem index < count problem) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
      (initialConfiguration problem index remaining output) =
      some (finalConfiguration problem index remaining output) :=
  workRunExact problem index remaining output hBody

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (hBody : quotient problem index < count problem) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining)
      (encodeWorkConfiguration (initialConfiguration problem index remaining output)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining output) :=
  run_compile_exact problem index remaining output hBody

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).state = (machine problem.verifier).acceptState :=
  finalConfiguration_state problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).tape =
      endTape (finalValues problem index remaining) (inside problem.input output) [] :=
  final_tape_layout problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) :
    finalValues problem index remaining =
      BuilderOperandRegisters.retainedValues problem index remaining ++
        [count problem, 0, index, width problem, quotient problem index,
         count problem, 0, BuilderClauseDividerExecution.constraintIndex problem index * clauseWidth problem,
         BuilderClauseDividerExecution.clauseIndex problem index, clauseWidth problem,
         BuilderClauseDividerExecution.constraintIndex problem index] :=
  finalValues_eq problem index remaining

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hBody : quotient problem index < count problem) :
    ClauseOccupancy.constraintSlot problem
      (sourceView problem index).quotient (sourceView problem index).remainder =
      (problem.formulaClauseSchedule[quotient problem index]?).map Option.isSome :=
  coordinates_match_schedule problem index hBody

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    let span := (sourceSpan problem.verifier).eval problem.input.length
    (sourceView problem index).quotient ≤ span ∧
    (sourceView problem index).width ≤ span ∧
    (sourceView problem index).remainder ≤ span ∧
    (sourceView problem index).consumed ≤ span ∧
    (sourceView problem index).sidecarCount ≤ span :=
  source_magnitudes_le problem index remaining hBalance

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    restorationSteps problem index ≤
      15 * (sourceSpan problem.verifier).eval problem.input.length + 19 :=
  restorationSteps_le problem index remaining hBalance

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    6 * workSteps problem index remaining ≤
      (rawTimeBound problem.verifier).eval problem.input.length :=
  rawTimeBound_le problem index remaining hBalance

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    (registerWord (finalValues problem index remaining)).length ≤
      9 * (sourceSpan problem.verifier).eval problem.input.length + 11 :=
  final_register_span_le problem index remaining hBalance

example {language : Language} (problem : VerifierTableauProblem language) :
    (rawTimeBound problem.verifier).eval problem.input.length =
      (BuilderClauseDividerExecution.bodyRawTimeBound problem.verifier).eval problem.input.length +
        6 * (15 * (sourceSpan problem.verifier).eval problem.input.length + 20) := rfl

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct := rules_pairwise_query_distinct verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (machine verifier) := noRuleAtAccept verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState := acceptState_ne_rejectState verifier

end PNP.Concrete.CookLevinBuilderClauseCoordinateRegistersRegression
