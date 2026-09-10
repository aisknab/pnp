/-
Copyright (c) 2026 PNP Labs.
Actual source cursor to complete-schedule occupancy. These universal contracts
supply no chosen family, payload, local coordinate, variable count or occupancy.
-/
import PNP.Concrete.CookLevinBuilderSourceClauseOccupancy

namespace PNP.Concrete.CookLevin.BuilderSourceClauseOccupancy.Regression
open BuilderSourceClauseOccupancy
open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape inside count)
open BuilderClauseDividerOperands (quotient)
open BuilderClauseDividerExecution (clauseIndex constraintIndex)

variable {language : Language} (verifier : PolynomialTimeVerifier language)
example : machine verifier =
    WorkMachineChain.machine (BuilderSourceClauseCoordinate.machine verifier) BuilderPayloadClauseOccupancy.machine := rfl
example : (machine verifier).acceptState = WorkMachineChain.secondState 0 := machine_acceptState verifier
example : (machine verifier).rejectState = WorkMachineChain.secondState 1 := machine_rejectState verifier
example (tape : WorkTape) : observe {state := (machine verifier).acceptState, tape := tape} = some true := rfl
example (tape : WorkTape) : observe {state := (machine verifier).rejectState, tape := tape} = some false := rfl
example : (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct := rules_pairwise_query_distinct verifier
example : WorkMachineChain.NoRuleAtAccept (machine verifier) := noRuleAtAccept verifier
example : WorkMachineProgramGraph.NoRuleAt (machine verifier) (machine verifier).rejectState := noRuleAtReject verifier
example : (machine verifier).acceptState ≠ (machine verifier).rejectState := acceptState_ne_rejectState verifier

variable (problem : VerifierTableauProblem language) (index remaining : Nat) (output : List CNFToken)
example : slot problem index = problem.formulaConstraintSlotDirect (constraintIndex problem index) := rfl
example : BuilderPayloadClauseOccupancy.result (slot problem index) (clauseIndex problem index) =
    ClauseOccupancy.constraintSlot problem (constraintIndex problem index) (clauseIndex problem index) :=
  source_slot_result problem index
example : occupancySteps problem index =
    BuilderPayloadClauseOccupancy.workSteps (slot problem index) (clauseIndex problem index) := rfl
example : (initialConfiguration problem index remaining output).tape =
    BuilderCursorSource.cursorTape problem index remaining output := rfl

variable (hBody : quotient problem index < count problem)
example : BuilderSourceClauseCoordinate.finalValues problem index remaining hBody =
    BuilderSourcePayload.history problem index remaining hBody ++
      BuilderLocalConstraintPayload.values (slot problem index) ++ [clauseIndex problem index] :=
  source_operand_layout problem index remaining hBody
example : workSteps problem index remaining hBody =
    BuilderSourceClauseCoordinate.workSteps problem index remaining hBody + 1 + occupancySteps problem index := rfl
example : workRunExact? BuilderPayloadClauseOccupancy.machine (occupancySteps problem index)
    (workStartConfiguration BuilderPayloadClauseOccupancy.machine
      (BuilderSourceClauseCoordinate.finalConfiguration problem index remaining output hBody).tape) =
    some (occupancyFinal problem index remaining output hBody) :=
  occupancy_workRunExact problem index remaining output hBody
example : workRunExact? (machine problem.verifier) (workSteps problem index remaining hBody)
    (initialConfiguration problem index remaining output) =
    some (finalConfiguration problem index remaining output hBody) := workRunExact problem index remaining output hBody
example : run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining hBody)
    (encodeWorkConfiguration (initialConfiguration problem index remaining output)) =
    encodeWorkConfiguration (finalConfiguration problem index remaining output hBody) :=
  run_compile_exact problem index remaining output hBody
example : (finalConfiguration problem index remaining output hBody).tape =
    endTape (finalValues problem index remaining hBody) (inside problem.input output) (exterior problem index remaining hBody) :=
  final_tape problem index remaining output hBody
example : (finalConfiguration problem index remaining output hBody).tape.right =
    (registerWord (finalValues problem index remaining hBody)).reverse ++ inside problem.input output := rfl
example : observe (finalConfiguration problem index remaining output hBody) =
    ClauseOccupancy.constraintSlot problem (constraintIndex problem index) (clauseIndex problem index) :=
  canonical_result problem index remaining output hBody
example : observe (finalConfiguration problem index remaining output hBody) =
    (problem.formulaClauseSchedule[quotient problem index]?).map Option.isSome :=
  final_observes_schedule problem index remaining output hBody
example : observe (workRun (machine problem.verifier) (workSteps problem index remaining hBody)
    (initialConfiguration problem index remaining output)) =
    (problem.formulaClauseSchedule[quotient problem index]?).map Option.isSome :=
  workRun_observes_schedule problem index remaining output hBody
example (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    (registerWord (finalValues problem index remaining hBody)).length + (exterior problem index remaining hBody).length ≤
        (spanBound problem.verifier).eval problem.input.length ∧
      6 * workSteps problem index remaining hBody ≤ (rawTimeBound problem.verifier).eval problem.input.length :=
  source_polynomial_bounds problem index remaining hBody hBalance

end PNP.Concrete.CookLevin.BuilderSourceClauseOccupancy.Regression
