/-
Copyright (c) 2026 PNP Labs.

One verifier-fixed finite machine obtains the actual source payload and local
clause coordinate, then dispatches occupancy from those physical cells. Its
observation equals the complete canonical clause schedule at the decoded
source coordinate. No family, payload, coordinate, count or occupancy premise
is supplied. The old payload and source/output interior remain intact.
Token emission, scratch recovery, the successor and Finish are still open.
-/
import PNP.Concrete.CookLevinBuilderSourceClauseCoordinate
import PNP.Concrete.CookLevinBuilderPayloadClauseOccupancy

namespace PNP.Concrete.CookLevin.BuilderSourceClauseOccupancy

open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape inside count)
open BuilderClauseDividerOperands (quotient)
open BuilderClauseDividerExecution (constraintIndex clauseIndex)

def slot {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :=
  problem.formulaConstraintSlotDirect (constraintIndex problem index)

def machine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineChain.machine (BuilderSourceClauseCoordinate.machine verifier) BuilderPayloadClauseOccupancy.machine

def observe (configuration : WorkConfiguration) : Option Bool :=
  if configuration.state = WorkMachineChain.secondState 0 then some true
  else if configuration.state = WorkMachineChain.secondState 1 then some false else none

theorem machine_acceptState {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState = WorkMachineChain.secondState 0 := rfl
theorem machine_rejectState {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rejectState = WorkMachineChain.secondState 1 := rfl

private theorem observe_renamed (configuration : WorkConfiguration) :
    observe (PipelineStateNamespace.renameConfiguration WorkMachineChain.secondState configuration) =
      BuilderPayloadClauseOccupancy.observe configuration := by
  have hZero : WorkMachineChain.secondState configuration.state = WorkMachineChain.secondState 0 ↔
      configuration.state = 0 :=
    ⟨fun h => WorkMachineChain.secondState_injective h, fun h => congrArg WorkMachineChain.secondState h⟩
  have hOne : WorkMachineChain.secondState configuration.state = WorkMachineChain.secondState 1 ↔
      configuration.state = 1 :=
    ⟨fun h => WorkMachineChain.secondState_injective h, fun h => congrArg WorkMachineChain.secondState h⟩
  simp only [observe, PipelineStateNamespace.renameConfiguration, hZero, hOne, BuilderPayloadClauseOccupancy.observe]

theorem source_operand_layout {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (hBody : quotient problem index < count problem) :
    BuilderSourceClauseCoordinate.finalValues problem index remaining hBody =
      BuilderSourcePayload.history problem index remaining hBody ++
        BuilderLocalConstraintPayload.values (slot problem index) ++ [clauseIndex problem index] := by
  rw [BuilderSourceClauseCoordinate.finalValues, BuilderSourcePayload.final_suffix, BuilderSourcePayload.payload_canonical]
  rfl

theorem source_slot_result {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    BuilderPayloadClauseOccupancy.result (slot problem index) (clauseIndex problem index) =
      ClauseOccupancy.constraintSlot problem (constraintIndex problem index) (clauseIndex problem index) := by
  unfold BuilderPayloadClauseOccupancy.result slot ClauseOccupancy.constraintSlot
  cases problem.formulaConstraintSlotDirect (constraintIndex problem index) with
  | none => rfl
  | some item =>
      simp only [Option.map_some, ClauseOccupancy.paddedSlot,
        if_pos (BuilderClauseDividerExecution.clauseIndex_lt problem index)]
      rfl

def occupancySteps {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : Nat :=
  BuilderPayloadClauseOccupancy.workSteps (slot problem index) (clauseIndex problem index)
def workSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : quotient problem index < count problem) : Nat :=
  BuilderSourceClauseCoordinate.workSteps problem index remaining hBody + 1 + occupancySteps problem index

def finalValues {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : quotient problem index < count problem) : List Nat :=
  BuilderPayloadClauseOccupancy.finalValues (slot problem index) (clauseIndex problem index)
    (BuilderSourcePayload.history problem index remaining hBody)
def exterior {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : quotient problem index < count problem) : List WorkSymbol :=
  BuilderPayloadClauseOccupancy.finalOutside (slot problem index) (clauseIndex problem index)
    (BuilderSourceClauseCoordinate.exterior problem index remaining hBody)
def occupancyFinal {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hBody : quotient problem index < count problem) : WorkConfiguration :=
  BuilderPayloadClauseOccupancy.finalConfiguration (slot problem index) (clauseIndex problem index)
    (BuilderSourcePayload.history problem index remaining hBody) (inside problem.input output)
    (BuilderSourceClauseCoordinate.exterior problem index remaining hBody)
def initialConfiguration {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) : WorkConfiguration :=
  workStartConfiguration (machine problem.verifier) (BuilderCursorSource.cursorTape problem index remaining output)
def finalConfiguration {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hBody : quotient problem index < count problem) : WorkConfiguration :=
  PipelineStateNamespace.renameConfiguration WorkMachineChain.secondState
    (occupancyFinal problem index remaining output hBody)

theorem occupancy_workRunExact {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hBody : quotient problem index < count problem) :
    workRunExact? BuilderPayloadClauseOccupancy.machine (occupancySteps problem index)
      (workStartConfiguration BuilderPayloadClauseOccupancy.machine
        (BuilderSourceClauseCoordinate.finalConfiguration problem index remaining output hBody).tape) =
      some (occupancyFinal problem index remaining output hBody) := by
  rw [BuilderSourceClauseCoordinate.final_tape_canonical]
  exact BuilderPayloadClauseOccupancy.workRunExact (slot problem index) (clauseIndex problem index)
    (BuilderSourcePayload.history problem index remaining hBody) (inside problem.input output)
    (BuilderSourceClauseCoordinate.exterior problem index remaining hBody)

private theorem chain_run_result (first second : WorkMachine) (n m : Nat)
    (initial middle : WorkTape) (final : WorkConfiguration)
    (hFirst : workRunExact? first n (workStartConfiguration first initial) =
      some {state := first.acceptState, tape := middle})
    (hSecond : workRunExact? second m (workStartConfiguration second middle) = some final) :
    workRunExact? (WorkMachineChain.machine first second) (n + 1 + m)
      (workStartConfiguration (WorkMachineChain.machine first second) initial) =
      some (PipelineStateNamespace.renameConfiguration WorkMachineChain.secondState final) :=
  WorkMachineChain.workRunExact first second n m _ _ _ hFirst rfl hSecond

theorem workRunExact {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hBody : quotient problem index < count problem) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining hBody)
      (initialConfiguration problem index remaining output) =
      some (finalConfiguration problem index remaining output hBody) := by
  have hSource := BuilderSourceClauseCoordinate.workRunExact problem index remaining output hBody
  have hOccupancy := occupancy_workRunExact problem index remaining output hBody
  simp only [BuilderSourceClauseCoordinate.initialConfiguration,
    BuilderSourceClauseCoordinate.finalConfiguration] at hSource hOccupancy
  have h := chain_run_result (BuilderSourceClauseCoordinate.machine problem.verifier)
    BuilderPayloadClauseOccupancy.machine (BuilderSourceClauseCoordinate.workSteps problem index remaining hBody)
    (occupancySteps problem index) _ _ _ hSource hOccupancy
  simpa only [machine, workSteps, initialConfiguration, finalConfiguration] using h

theorem run_compile_exact {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hBody : quotient problem index < count problem) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining hBody)
      (encodeWorkConfiguration (initialConfiguration problem index remaining output)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining output hBody) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact problem index remaining output hBody)

theorem final_tape {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hBody : quotient problem index < count problem) :
    (finalConfiguration problem index remaining output hBody).tape =
      endTape (finalValues problem index remaining hBody) (inside problem.input output) (exterior problem index remaining hBody) := rfl

theorem canonical_result {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hBody : quotient problem index < count problem) :
    observe (finalConfiguration problem index remaining output hBody) =
      ClauseOccupancy.constraintSlot problem (constraintIndex problem index) (clauseIndex problem index) := by
  rw [finalConfiguration, observe_renamed]
  exact (BuilderPayloadClauseOccupancy.canonical_result (slot problem index) (clauseIndex problem index)
    (BuilderSourcePayload.history problem index remaining hBody) (inside problem.input output)
    (BuilderSourceClauseCoordinate.exterior problem index remaining hBody)).trans (source_slot_result problem index)

theorem final_observes_schedule {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hBody : quotient problem index < count problem) :
    observe (finalConfiguration problem index remaining output hBody) =
      (problem.formulaClauseSchedule[quotient problem index]?).map Option.isSome := by
  rw [canonical_result]
  exact BuilderClauseCoordinateRegisters.coordinates_match_schedule problem index hBody

theorem workRun_observes_schedule {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (hBody : quotient problem index < count problem) :
    observe (workRun (machine problem.verifier) (workSteps problem index remaining hBody)
      (initialConfiguration problem index remaining output)) =
      (problem.formulaClauseSchedule[quotient problem index]?).map Option.isSome := by
  rw [workRun_eq_of_workRunExact _ _ _ _ (workRunExact problem index remaining output hBody)]
  exact final_observes_schedule problem index remaining output hBody

theorem rules_pairwise_query_distinct {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineChain.rules_pairwise_query_distinct _ _
    (BuilderSourceClauseCoordinate.rules_pairwise_query_distinct verifier)
    BuilderPayloadClauseOccupancy.rules_pairwise_query_distinct
    (BuilderSourceClauseCoordinate.noRuleAtAccept verifier)
theorem noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (machine verifier) :=
  WorkMachineChain.noRuleAtAccept _ _ BuilderPayloadClauseOccupancy.noRuleAtAccept
theorem noRuleAtReject {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier) (machine verifier).rejectState :=
  WorkMachineChain.noRuleAtAccept (BuilderSourceClauseCoordinate.machine verifier)
    {BuilderPayloadClauseOccupancy.machine with acceptState := BuilderPayloadClauseOccupancy.machine.rejectState}
    BuilderPayloadClauseOccupancy.noRuleAtReject
theorem acceptState_ne_rejectState {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState :=
  WorkMachineChain.machine_acceptState_ne_rejectState _ _ BuilderPayloadClauseOccupancy.acceptState_ne_rejectState

def spanBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  BuilderPayloadClauseOccupancy.spanPolynomial (BuilderSourceClauseCoordinate.spanBound verifier)
def rawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderSourceClauseCoordinate.rawTimeBound verifier)
    (.add (.constant 6) (BuilderPayloadClauseOccupancy.rawTimePolynomial (BuilderSourceClauseCoordinate.spanBound verifier)))

theorem source_polynomial_bounds {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hBody : quotient problem index < count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    (registerWord (finalValues problem index remaining hBody)).length + (exterior problem index remaining hBody).length ≤
        (spanBound problem.verifier).eval problem.input.length ∧
      6 * workSteps problem index remaining hBody ≤ (rawTimeBound problem.verifier).eval problem.input.length := by
  have hSource := BuilderSourceClauseCoordinate.source_polynomial_bounds problem index remaining hBody hBalance
  have hSpan := hSource.1
  rw [source_operand_layout] at hSpan
  have hOccupancy := BuilderPayloadClauseOccupancy.source_polynomial_bounds (slot problem index) (clauseIndex problem index)
    (BuilderSourcePayload.history problem index remaining hBody)
    (BuilderSourceClauseCoordinate.exterior problem index remaining hBody)
    (BuilderSourceClauseCoordinate.spanBound problem.verifier) problem.input.length hSpan
  constructor
  · exact hOccupancy.1
  · simp only [workSteps, occupancySteps, rawTimeBound, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

end PNP.Concrete.CookLevin.BuilderSourceClauseOccupancy
