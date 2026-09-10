/-
Copyright (c) 2026 PNP Labs.
Canonical boundary payload numbering, source binding and physical runtime
contracts. Universal problem parameters cover both verifier input modes.
No branch fixture or added declaration changes milestone/progress credit.
-/
import PNP.Concrete.CookLevinBuilderBoundaryPayload

namespace PNP.Concrete.CookLevin.BuilderBoundaryPayload.Regression
open BuilderBoundaryPayload
open BuilderUnaryPolynomial

example : region .initialState = .initial := rfl
example : region .initialHead = .initial := rfl
example : region .acceptingState = .accepting := rfl
example : kind .initialState = .state := rfl
example : kind .initialHead = .head := rfl
example : kind .acceptingState = .state := rfl

-- T=3,W=25,S=5,C=6: symbol block 225, head block 75, state base 300.
example : BuilderRegisterExpression.eval (BuilderLiteralIndexExpression.expression .state)
    (fun i => ([3,25,5,6,0,0,2,0] : List Nat).getD i.val 0) = 302 := rfl
example : BuilderRegisterExpression.eval (BuilderLiteralIndexExpression.expression .head)
    (fun i => ([3,25,5,6,0,2,0,0] : List Nat).getD i.val 0) = 227 := rfl
example : BuilderRegisterExpression.eval (BuilderLiteralIndexExpression.expression .state)
    (fun i => ([3,25,5,6,2,0,3,0] : List Nat).getD i.val 0) = 313 := rfl
-- C=0 has the same canonical state/head conventions, including fuel zero.
example : BuilderRegisterExpression.eval (BuilderLiteralIndexExpression.expression .state)
    (fun i => ([1,3,2,0,0,0,0,0] : List Nat).getD i.val 0) = 12 := rfl
example : BuilderRegisterExpression.eval (BuilderLiteralIndexExpression.expression .head)
    (fun i => ([1,3,2,0,0,0,0,0] : List Nat).getD i.val 0) = 9 := rfl
example : BuilderRegisterExpression.eval (BuilderLiteralIndexExpression.expression .state)
    (fun i => ([1,3,2,0,0,0,1,0] : List Nat).getD i.val 0) = 13 := rfl
example : BuilderLocalConstraintPayload.decode 14 [13,1,2] =
    some (some (some (.require ⟨true, ⟨13, by decide⟩⟩))) := rfl
example : BuilderLocalConstraintPayload.decode 14 [13,0,2] ≠
    some (some (some (.require ⟨true, ⟨13, by decide⟩⟩))) := by
  intro h
  have hLiteral := LocalConstraint.require.inj (Option.some.inj (Option.some.inj (Option.some.inj h)))
  have hSign : false = true := congrArg BoundedLiteral.positive hLiteral
  cases hSign
example : BuilderLocalConstraintPayload.decode 14 [13,1,3] = none := by decide
example : BuilderLocalConstraintPayload.decode 13 [13,1,2] = none := by decide
example : BuilderLocalConstraintPayload.decode 14 [2,1,13] = none := by decide

section Source
variable {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) (role : Role)
example : (request problem role).kind = kind role := request_kind problem role
example : BuilderLiteralArgumentSource.argumentEnvironment problem index (region role) [] (plan problem.verifier role) =
    (request problem role).environment := argument_environment problem index role
example : indexValue problem index role = (request problem role).index := index_canonical problem index role
example : indexValue problem index role < problem.FormulaWidth := by
  rw [index_canonical]
  exact (request problem role).index_lt
example : (payloadValues problem index role).length = 3 := payload_length problem index role
example : payloadValues problem index role ≠ [] := by
  intro h
  have hLength := payload_length problem index role
  rw [h, List.length_nil] at hLength
  omega
example : payloadValues problem index role = BuilderLocalConstraintPayload.values (some (some (constraint problem role))) :=
  payload_canonical problem index role
example : BuilderLocalConstraintPayload.decode problem.FormulaWidth (payloadValues problem index role) =
    some (some (some (constraint problem role))) := payload_decode problem index role
example : payloadValues problem index .initialState = BuilderInitialConstraintPayload.values problem 0 :=
  initial_state_payload problem index
example : payloadValues problem index .initialHead = BuilderInitialConstraintPayload.values problem 1 :=
  initial_head_payload problem index
example (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .accepting) :
    BuilderConstraintRegionSource.localCoordinate problem index .accepting = 0 := accepting_coordinate problem index hRegion
example (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .accepting) :
    payloadValues problem index .acceptingState = BuilderLocalConstraintPayload.values
      (problem.formulaConstraintSlotDirect (BuilderClauseDividerExecution.constraintIndex problem index)) :=
  accepting_source_payload problem index hRegion
example : (literalValues problem index remaining role).length = Arity problem.verifier role :=
  literalValues_length problem index remaining role
example : (indexField problem.verifier role).eval
    (fun i => (literalValues problem index remaining role).getD i.val 0) = indexValue problem index role :=
  indexField_eval problem index remaining role
example : BuilderRegisterPack.values (fields problem.verifier role)
    (fun i => (literalValues problem index remaining role).getD i.val 0) = payloadValues problem index role :=
  fields_values problem index remaining role
example (inside outside : List WorkSymbol) :
    workRunExact? (machine problem.verifier role) (workSteps problem index remaining role)
      (initialConfiguration problem index remaining role inside outside) =
      some (finalConfiguration problem index remaining role inside outside) :=
  workRunExact problem index remaining role inside outside
example (inside outside : List WorkSymbol) :
    run (compileWorkMachine (machine problem.verifier role)) (6 * workSteps problem index remaining role)
      (encodeWorkConfiguration (initialConfiguration problem index remaining role inside outside)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining role inside outside) :=
  run_compile_exact problem index remaining role inside outside
example : finalValues problem index remaining role =
    BuilderLiteralArgumentSource.inputValues problem index remaining (region role) [] ++ writtenValues problem index role :=
  source_preserved problem index remaining role
example (inside outside : List WorkSymbol) : (finalConfiguration problem index remaining role inside outside).tape.right =
    (registerWord (payloadValues problem index role)).reverse ++
      ((registerWord (literalValues problem index remaining role)).reverse ++ inside) :=
  final_inside_preserved problem index remaining role inside outside
example (inside outside : List WorkSymbol) : (finalConfiguration problem index remaining role inside outside).tape.left =
    finalOutside problem index role outside := final_exterior problem index remaining role inside outside
example : finalOutside problem index role [] = [] := finalOutside_nil problem index role
example : finalValues problem index remaining role = literalValues problem index remaining role ++
    BuilderLocalConstraintPayload.values (some (some (constraint problem role))) := final_canonical problem index remaining role
example (output : List CNFToken) (outside : List WorkSymbol) :
    workRunExact? (machine problem.verifier role) (workSteps problem index remaining role)
      (initialConfiguration problem index remaining role (BuilderDividerOperands.inside problem.input output) outside) =
      some
        {state := (machine problem.verifier role).acceptState,
         tape := BuilderDividerOperands.endTape (literalValues problem index remaining role ++
           BuilderLocalConstraintPayload.values (some (some (constraint problem role))))
           (BuilderDividerOperands.inside problem.input output) (finalOutside problem index role outside)} :=
  source_canonical_payload problem index remaining role output outside
example (output : List CNFToken) (outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .accepting) :
    workRunExact? (machine problem.verifier .acceptingState) (workSteps problem index remaining .acceptingState)
      (initialConfiguration problem index remaining .acceptingState (BuilderDividerOperands.inside problem.input output) outside) =
      some
        {state := (machine problem.verifier .acceptingState).acceptState,
         tape := BuilderDividerOperands.endTape (literalValues problem index remaining .acceptingState ++ BuilderLocalConstraintPayload.values
           (problem.formulaConstraintSlotDirect (BuilderClauseDividerExecution.constraintIndex problem index)))
           (BuilderDividerOperands.inside problem.input output) (finalOutside problem index .acceptingState outside)} :=
  accepting_source_execution problem index remaining output outside hRegion
example : (machine problem.verifier role).rules.Pairwise WorkMachineChain.QueryDistinct :=
  rules_pairwise_query_distinct problem.verifier role
example : WorkMachineChain.NoRuleAtAccept (machine problem.verifier role) := noRuleAtAccept problem.verifier role
example : WorkMachineProgramGraph.NoRuleAt (machine problem.verifier role) (machine problem.verifier role).rejectState :=
  noRuleAtReject problem.verifier role
example : (machine problem.verifier role).acceptState ≠ (machine problem.verifier role).rejectState :=
  acceptState_ne_rejectState problem.verifier role
example
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some (region role)) :
    (registerWord (finalValues problem index remaining role)).length ≤ (spanPolynomial problem.verifier role).eval problem.input.length ∧
      6 * workSteps problem index remaining role ≤ (rawTimePolynomial problem.verifier role).eval problem.input.length :=
  source_polynomial_bounds problem index remaining role hBody hBalance hRegion
example (outside : List WorkSymbol) (outsideBound : NatPolynomial)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some (region role))
    (hOutside : outside.length ≤ outsideBound.eval problem.input.length) :
    (registerWord (finalValues problem index remaining role)).length + (finalOutside problem index role outside).length ≤
        (NatPolynomial.add (spanPolynomial problem.verifier role) outsideBound).eval problem.input.length ∧
      6 * workSteps problem index remaining role ≤ (rawTimePolynomial problem.verifier role).eval problem.input.length :=
  source_polynomial_boundsWithOutside problem index remaining role outside outsideBound hBody hBalance hRegion hOutside
end Source
end PNP.Concrete.CookLevin.BuilderBoundaryPayload.Regression
