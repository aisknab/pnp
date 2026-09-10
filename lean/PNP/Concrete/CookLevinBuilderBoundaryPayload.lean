/-
Copyright (c) 2026 PNP Labs.

Source-derived boundary requirements for every input tableau. The verifier fixes
three branch programs: initial state, initial head and final accepting state.
Runtime fuel, dimensions and canonical literal indices are read or constructed
from the actual source packet. The final packing reads the written index.
Initial-family routing and complete formula emission remain downstream.
-/

import PNP.Concrete.CookLevinBuilderInitialConstraintPayload
import PNP.Concrete.CookLevinBuilderLiteralArgumentSource

namespace PNP.Concrete.CookLevin.BuilderBoundaryPayload

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderConstraintRegionRegisters (Region)
open BuilderLiteralArgumentSource (Plan)

/-- The three semantic tableau boundaries, not runtime-supplied literal answers. -/
inductive Role where
  | initialState | initialHead | acceptingState
  deriving DecidableEq, Repr

def region : Role → Region
  | .initialState | .initialHead => .initial
  | .acceptingState => .accepting

def kind : Role → BuilderLiteralIndexExpression.Kind
  | .initialState | .acceptingState => .state
  | .initialHead => .head

def rawMachine {language : Language} (verifier : PolynomialTimeVerifier language) : Machine :=
  (DecisionProgram.RawRefinement.compile verifier.program.decision).machine

def plan {language : Language} (verifier : PolynomialTimeVerifier language) (role : Role) : Plan (region role) 0 :=
  fun field => match role, field.val with
  | .initialState, 2 => .constant (rawMachine verifier).startState
  | .initialHead, 1 | .acceptingState, 0 => .source .fuel
  | .acceptingState, 2 => .constant (rawMachine verifier).acceptState
  | _, _ => .constant 0

def request {language : Language} (problem : VerifierTableauProblem language) : Role →
    BuilderLiteralIndexExpression.Request problem.layout
  | .initialState => .state problem.initialTime problem.startState
  | .initialHead => .head problem.initialTime problem.initialHeadPosition
  | .acceptingState => .state problem.finalTime problem.acceptingState

def constraint {language : Language} (problem : VerifierTableauProblem language) : Role →
    LocalConstraint problem.FormulaWidth
  | .initialState => .require (problem.stateLiteral problem.initialTime problem.startState)
  | .initialHead => .require (problem.headLiteral problem.initialTime problem.initialHeadPosition)
  | .acceptingState => .require (problem.stateLiteral problem.finalTime problem.acceptingState)

theorem request_kind {language : Language} (problem : VerifierTableauProblem language) (role : Role) :
    (request problem role).kind = kind role := by cases role <;> rfl

theorem argument_environment {language : Language} (problem : VerifierTableauProblem language) (index : Nat) (role : Role) :
    BuilderLiteralArgumentSource.argumentEnvironment problem index (region role) [] (plan problem.verifier role) =
      (request problem role).environment := by
  funext field
  rcases field with ⟨field, hField⟩
  have hCases : field = 0 ∨ field = 1 ∨ field = 2 ∨ field = 3 ∨
      field = 4 ∨ field = 5 ∨ field = 6 ∨ field = 7 := by omega
  cases role <;> rcases hCases with h | h | h | h | h | h | h | h <;> subst field <;> rfl

def indexValue {language : Language} (problem : VerifierTableauProblem language) (index : Nat) (role : Role) : Nat :=
  BuilderRegisterExpression.eval (BuilderLiteralIndexExpression.expression (kind role))
    (BuilderLiteralArgumentSource.argumentEnvironment problem index (region role) [] (plan problem.verifier role))

theorem index_canonical {language : Language} (problem : VerifierTableauProblem language) (index : Nat) (role : Role) :
    indexValue problem index role = (request problem role).index := by
  rw [indexValue, argument_environment]
  simpa only [request_kind] using BuilderLiteralIndexExpression.eval_eq_index (request problem role)

def payloadValues {language : Language} (problem : VerifierTableauProblem language) (index : Nat) (role : Role) : List Nat :=
  [indexValue problem index role, 1, 2]

theorem payload_length {language : Language} (problem : VerifierTableauProblem language) (index : Nat) (role : Role) :
    (payloadValues problem index role).length = 3 := rfl

theorem payload_canonical {language : Language} (problem : VerifierTableauProblem language) (index : Nat) (role : Role) :
    payloadValues problem index role = BuilderLocalConstraintPayload.values (some (some (constraint problem role))) := by
  rw [payloadValues, index_canonical]
  cases role <;> rfl

theorem payload_decode {language : Language} (problem : VerifierTableauProblem language) (index : Nat) (role : Role) :
    BuilderLocalConstraintPayload.decode problem.FormulaWidth (payloadValues problem index role) =
      some (some (some (constraint problem role))) := by
  rw [payload_canonical, BuilderLocalConstraintPayload.decode_values]

theorem initial_state_payload {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    payloadValues problem index .initialState = BuilderInitialConstraintPayload.values problem 0 := by
  rw [BuilderInitialConstraintPayload.state_values, payloadValues, index_canonical]
  rfl

theorem initial_head_payload {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    payloadValues problem index .initialHead = BuilderInitialConstraintPayload.values problem 1 := by
  rw [BuilderInitialConstraintPayload.head_values, payloadValues, index_canonical]
  rfl

/-- The unique accepting coordinate follows from the source-selected region. -/
theorem accepting_coordinate {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .accepting) :
    BuilderConstraintRegionSource.localCoordinate problem index .accepting = 0 := by
  have h := BuilderConstraintRegionSource.localCoordinate_valid problem index .accepting hRegion
  change BuilderConstraintRegionSource.localCoordinate problem index .accepting < 1 at h
  omega

theorem accepting_source_payload {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .accepting) :
    payloadValues problem index .acceptingState = BuilderLocalConstraintPayload.values
      (problem.formulaConstraintSlotDirect (BuilderClauseDividerExecution.constraintIndex problem index)) := by
  rw [← BuilderConstraintRegionSource.regionSlot_eq problem index .accepting hRegion,
    accepting_coordinate problem index hRegion, payload_canonical]
  rfl

def literalValues {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) (role : Role) : List Nat :=
  BuilderLiteralArgumentSource.finalValues problem index remaining (region role) [] (plan problem.verifier role) (kind role)

def Arity {language : Language} (verifier : PolynomialTimeVerifier language) (role : Role) : Nat :=
  BuilderLiteralArgumentSource.inputCount verifier (region role) 0 + 8 +
    BuilderRegisterExpression.nodeCount (BuilderLiteralIndexExpression.expression (kind role))

theorem literalValues_length {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) (role : Role) :
    (literalValues problem index remaining role).length = Arity problem.verifier role := by
  simp only [literalValues, BuilderLiteralArgumentSource.finalValues, BuilderLiteralArgumentSource.writtenValues,
    List.length_append, List.length_ofFn, BuilderRegisterExpression.values_length,
    BuilderLiteralArgumentSource.inputValues_length problem index remaining (region role) 0 [] rfl, Arity, Nat.add_assoc]

private def view {arity : Nat} (values : List Nat) (index : Fin arity) : Nat := values.getD index.val 0
private theorem view_ofFn {arity : Nat} (values : List Nat) (hLength : values.length = arity) :
    List.ofFn (view values : Fin arity → Nat) = values := by
  subst arity
  have h : (view values : Fin values.length → Nat) = fun index => values[index.val] := by
    funext index
    simp only [view, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem index.isLt, Option.getD_some]
  rw [h]
  exact List.ofFn_getElem

private theorem getD_after (leading trailing : List Nat) (index : Nat) :
    (leading ++ trailing).getD (leading.length + index) 0 = trailing.getD index 0 := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]

def indexField {language : Language} (verifier : PolynomialTimeVerifier language) (role : Role) :
    BuilderRegisterPack.Field (Arity verifier role) :=
  .argument ⟨Arity verifier role - 1, by simp only [Arity]; omega⟩

theorem indexField_eval {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) (role : Role) :
    (indexField problem.verifier role).eval (view (literalValues problem index remaining role)) = indexValue problem index role := by
  let leading := BuilderLiteralArgumentSource.inputValues problem index remaining (region role) [] ++
    List.ofFn (BuilderLiteralArgumentSource.argumentEnvironment problem index (region role) [] (plan problem.verifier role)) ++
    BuilderRegisterExpression.prefixValues (BuilderLiteralIndexExpression.expression (kind role))
      (BuilderLiteralArgumentSource.argumentEnvironment problem index (region role) [] (plan problem.verifier role))
  have hValues : literalValues problem index remaining role = leading ++ [indexValue problem index role] :=
    BuilderLiteralArgumentSource.final_index_register problem index remaining (region role) [] (plan problem.verifier role) (kind role)
  have hLength := literalValues_length problem index remaining role
  rw [hValues, List.length_append] at hLength
  simp only [List.length_cons, List.length_nil] at hLength
  have hPosition : Arity problem.verifier role - 1 = leading.length + 0 := by omega
  change (literalValues problem index remaining role).getD (Arity problem.verifier role - 1) 0 = indexValue problem index role
  rw [hValues, hPosition, getD_after]
  rfl

def fields {language : Language} (verifier : PolynomialTimeVerifier language) (role : Role) :
    List (BuilderRegisterPack.Field (Arity verifier role)) :=
  [indexField verifier role, .constant 1, .constant 2]

theorem fields_values {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) (role : Role) :
    BuilderRegisterPack.values (fields problem.verifier role) (view (literalValues problem index remaining role)) =
      payloadValues problem index role := by
  change [(indexField problem.verifier role).eval (view (literalValues problem index remaining role)), 1, 2] = _
  rw [indexField_eval]
  rfl

def literalMachine {language : Language} (verifier : PolynomialTimeVerifier language) (role : Role) : WorkMachine :=
  BuilderLiteralArgumentSource.machine verifier (region role) 0 (plan verifier role) (kind role)
def packMachine {language : Language} (verifier : PolynomialTimeVerifier language) (role : Role) : WorkMachine :=
  BuilderRegisterPack.machine (fields verifier role) 0
def machine {language : Language} (verifier : PolynomialTimeVerifier language) (role : Role) : WorkMachine :=
  WorkMachineChain.machine (literalMachine verifier role) (packMachine verifier role)

def literalSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) (role : Role) : Nat :=
  BuilderLiteralArgumentSource.workSteps problem index remaining (region role) 0 [] (plan problem.verifier role) (kind role)
def packSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) (role : Role) : Nat :=
  BuilderRegisterPack.workSteps (fields problem.verifier role) (view (literalValues problem index remaining role)) []
def workSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) (role : Role) : Nat :=
  literalSteps problem index remaining role + 1 + packSteps problem index remaining role

def writtenValues {language : Language} (problem : VerifierTableauProblem language) (index : Nat) (role : Role) : List Nat :=
  BuilderLiteralArgumentSource.writtenValues problem index (region role) [] (plan problem.verifier role) (kind role) ++
    payloadValues problem index role
def finalValues {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) (role : Role) : List Nat :=
  literalValues problem index remaining role ++ payloadValues problem index role
def finalOutside {language : Language} (problem : VerifierTableauProblem language) (index : Nat) (role : Role)
    (outside : List WorkSymbol) : List WorkSymbol :=
  outside.drop (registerWord (writtenValues problem index role)).length

def initialConfiguration {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) (role : Role)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration (machine problem.verifier role)
    (endTape (BuilderLiteralArgumentSource.inputValues problem index remaining (region role) []) inside outside)
def finalConfiguration {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) (role : Role)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  {state := (machine problem.verifier role).acceptState,
   tape := endTape (finalValues problem index remaining role) inside (finalOutside problem index role outside)}

private theorem chain_run (first second : WorkMachine) (firstSteps secondSteps : Nat)
    (initial middle final : WorkTape)
    (hFirst : workRunExact? first firstSteps (workStartConfiguration first initial) =
      some {state := first.acceptState, tape := middle})
    (hSecond : workRunExact? second secondSteps (workStartConfiguration second middle) =
      some {state := second.acceptState, tape := final}) :
    workRunExact? (WorkMachineChain.machine first second) (firstSteps + 1 + secondSteps)
      (workStartConfiguration (WorkMachineChain.machine first second) initial) =
      some {state := (WorkMachineChain.machine first second).acceptState, tape := final} :=
  WorkMachineChain.workRunExact first second firstSteps secondSteps _ _ _ hFirst rfl hSecond

theorem workRunExact {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) (role : Role)
    (inside outside : List WorkSymbol) :
    workRunExact? (machine problem.verifier role) (workSteps problem index remaining role)
      (initialConfiguration problem index remaining role inside outside) =
      some (finalConfiguration problem index remaining role inside outside) := by
  have hLiteral := BuilderLiteralArgumentSource.workRunExact problem index remaining (region role) 0 []
    (plan problem.verifier role) (kind role) inside outside rfl
  simp only [BuilderLiteralArgumentSource.initialConfiguration, BuilderLiteralArgumentSource.finalConfiguration] at hLiteral
  have hPack := BuilderRegisterPack.workRunExact (fields problem.verifier role) 0 []
    (view (literalValues problem index remaining role)) [] inside
    (outside.drop (registerWord
      (BuilderLiteralArgumentSource.writtenValues problem index (region role) [] (plan problem.verifier role) (kind role))).length) rfl
  simp only [BuilderRegisterPack.initialConfiguration, BuilderRegisterPack.finalConfiguration,
    List.nil_append, List.append_nil, view_ofFn _ (literalValues_length problem index remaining role), fields_values] at hPack
  have h := chain_run (literalMachine problem.verifier role) (packMachine problem.verifier role) _ _ _ _ _ hLiteral hPack
  simpa only [machine, workSteps, literalSteps, packSteps, initialConfiguration, finalConfiguration,
    finalValues, finalOutside, writtenValues, List.drop_drop, registerWord_append, List.length_append] using h

theorem run_compile_exact {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) (role : Role)
    (inside outside : List WorkSymbol) :
    run (compileWorkMachine (machine problem.verifier role)) (6 * workSteps problem index remaining role)
      (encodeWorkConfiguration (initialConfiguration problem index remaining role inside outside)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining role inside outside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact problem index remaining role inside outside)

theorem source_preserved {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) (role : Role) :
    finalValues problem index remaining role =
      BuilderLiteralArgumentSource.inputValues problem index remaining (region role) [] ++ writtenValues problem index role := by
  simp only [finalValues, literalValues, BuilderLiteralArgumentSource.finalValues, writtenValues, List.append_assoc]

theorem final_inside_preserved {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) (role : Role)
    (inside outside : List WorkSymbol) :
    (finalConfiguration problem index remaining role inside outside).tape.right =
      (registerWord (payloadValues problem index role)).reverse ++
        ((registerWord (literalValues problem index remaining role)).reverse ++ inside) := by
  simp only [finalConfiguration, finalValues, endTape, registerWord_append, List.reverse_append, List.append_assoc]

theorem final_exterior {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) (role : Role)
    (inside outside : List WorkSymbol) :
    (finalConfiguration problem index remaining role inside outside).tape.left = finalOutside problem index role outside := rfl

theorem finalOutside_nil {language : Language} (problem : VerifierTableauProblem language) (index : Nat) (role : Role) :
    finalOutside problem index role [] = [] := List.drop_nil

theorem final_canonical {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) (role : Role) :
    finalValues problem index remaining role = literalValues problem index remaining role ++
      BuilderLocalConstraintPayload.values (some (some (constraint problem role))) := by
  rw [finalValues, payload_canonical]

theorem source_canonical_payload {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) (role : Role)
    (output : List CNFToken) (outside : List WorkSymbol) :
    workRunExact? (machine problem.verifier role) (workSteps problem index remaining role)
      (initialConfiguration problem index remaining role (BuilderDividerOperands.inside problem.input output) outside) =
      some
        {state := (machine problem.verifier role).acceptState,
         tape := endTape (literalValues problem index remaining role ++
           BuilderLocalConstraintPayload.values (some (some (constraint problem role))))
           (BuilderDividerOperands.inside problem.input output) (finalOutside problem index role outside)} := by
  simpa only [finalConfiguration, final_canonical] using
    workRunExact problem index remaining role (BuilderDividerOperands.inside problem.input output) outside

theorem accepting_source_execution {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (output : List CNFToken) (outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .accepting) :
    workRunExact? (machine problem.verifier .acceptingState) (workSteps problem index remaining .acceptingState)
      (initialConfiguration problem index remaining .acceptingState (BuilderDividerOperands.inside problem.input output) outside) =
      some
        {state := (machine problem.verifier .acceptingState).acceptState,
         tape := endTape (literalValues problem index remaining .acceptingState ++ BuilderLocalConstraintPayload.values
           (problem.formulaConstraintSlotDirect (BuilderClauseDividerExecution.constraintIndex problem index)))
           (BuilderDividerOperands.inside problem.input output) (finalOutside problem index .acceptingState outside)} := by
  simpa only [finalConfiguration, finalValues, accepting_source_payload problem index hRegion] using
    workRunExact problem index remaining .acceptingState (BuilderDividerOperands.inside problem.input output) outside

theorem rules_pairwise_query_distinct {language : Language} (verifier : PolynomialTimeVerifier language) (role : Role) :
    (machine verifier role).rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineChain.rules_pairwise_query_distinct _ _
    (BuilderLiteralArgumentSource.rules_pairwise_query_distinct verifier (region role) 0 (plan verifier role) (kind role))
    (BuilderRegisterPack.rules_pairwise_query_distinct (fields verifier role) 0)
    (BuilderLiteralArgumentSource.noRuleAtAccept verifier (region role) 0 (plan verifier role) (kind role))
theorem noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language) (role : Role) :
    WorkMachineChain.NoRuleAtAccept (machine verifier role) :=
  WorkMachineChain.noRuleAtAccept _ _ (BuilderRegisterPack.noRuleAtAccept (fields verifier role) 0)
theorem noRuleAtReject {language : Language} (verifier : PolynomialTimeVerifier language) (role : Role) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier role) (machine verifier role).rejectState :=
  WorkMachineChain.noRuleAtAccept (literalMachine verifier role)
    {(packMachine verifier role) with acceptState := (packMachine verifier role).rejectState}
    (BuilderRegisterPack.noRuleAtReject (fields verifier role) 0)
theorem acceptState_ne_rejectState {language : Language} (verifier : PolynomialTimeVerifier language) (role : Role) :
    (machine verifier role).acceptState ≠ (machine verifier role).rejectState :=
  WorkMachineChain.machine_acceptState_ne_rejectState _ _ (BuilderRegisterPack.acceptState_ne_rejectState (fields verifier role) 0)

def literalSpanPolynomial {language : Language} (verifier : PolynomialTimeVerifier language) (role : Role) : NatPolynomial :=
  BuilderLiteralArgumentSource.finalSpanBound verifier (region role) 0 (plan verifier role) (kind role) (.constant 0)
def spanPolynomial {language : Language} (verifier : PolynomialTimeVerifier language) (role : Role) : NatPolynomial :=
  BuilderRegisterPack.spanPolynomial (fields verifier role) (literalSpanPolynomial verifier role)
def rawTimePolynomial {language : Language} (verifier : PolynomialTimeVerifier language) (role : Role) : NatPolynomial :=
  .add (BuilderLiteralArgumentSource.rawTimeBound verifier (region role) 0 (plan verifier role) (kind role) (.constant 0))
    (.add (.constant 6) (BuilderRegisterPack.rawTimePolynomial (fields verifier role) (literalSpanPolynomial verifier role)))

theorem source_polynomial_bounds {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) (role : Role)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some (region role)) :
    (registerWord (finalValues problem index remaining role)).length ≤ (spanPolynomial problem.verifier role).eval problem.input.length ∧
      6 * workSteps problem index remaining role ≤ (rawTimePolynomial problem.verifier role).eval problem.input.length := by
  have hLiteral := BuilderLiteralArgumentSource.source_polynomial_bounds problem index remaining (region role) 0 []
    (plan problem.verifier role) (kind role) (.constant 0) rfl hBody hBalance hRegion (Nat.le_refl 0)
  have hEnvironment :
      (registerWord ([] ++ List.ofFn (view (literalValues problem index remaining role) : Fin (Arity problem.verifier role) → Nat) ++ [])).length ≤
        (literalSpanPolynomial problem.verifier role).eval problem.input.length := by
    rw [List.nil_append, List.append_nil, view_ofFn _ (literalValues_length problem index remaining role)]
    exact hLiteral.1
  have hPack := BuilderRegisterPack.source_polynomial_bounds (fields problem.verifier role)
    (literalSpanPolynomial problem.verifier role) problem.input.length [] (view (literalValues problem index remaining role)) [] hEnvironment
  constructor
  · simpa only [List.nil_append, List.append_nil, view_ofFn _ (literalValues_length problem index remaining role),
      fields_values, finalValues, spanPolynomial] using hPack.1
  · have hLiteralTime := hLiteral.2
    have hPackTime := hPack.2
    simp only [workSteps, literalSteps, packSteps, rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

theorem source_polynomial_boundsWithOutside {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (role : Role) (outside : List WorkSymbol) (outsideBound : NatPolynomial)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some (region role))
    (hOutside : outside.length ≤ outsideBound.eval problem.input.length) :
    (registerWord (finalValues problem index remaining role)).length + (finalOutside problem index role outside).length ≤
        (NatPolynomial.add (spanPolynomial problem.verifier role) outsideBound).eval problem.input.length ∧
      6 * workSteps problem index remaining role ≤ (rawTimePolynomial problem.verifier role).eval problem.input.length := by
  have h := source_polynomial_bounds problem index remaining role hBody hBalance hRegion
  have hDrop : (finalOutside problem index role outside).length ≤ outside.length := by
    rw [finalOutside, List.length_drop]
    exact Nat.sub_le _ _
  constructor
  · rw [NatPolynomial.eval_add]
    omega
  · exact h.2

end PNP.Concrete.CookLevin.BuilderBoundaryPayload
