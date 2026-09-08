/-
Copyright (c) 2026 PNP Labs.
Source-bound arbitrary-width initial length payload: independent numbering,
range order, tags, zero-width edge, physical execution and polynomial contracts.
These regression fixtures do not award another milestone or supplied-data credit.
-/
import PNP.Concrete.CookLevinBuilderInitialLengthPayload

namespace PNP.Concrete.CookLevin.BuilderInitialLengthPayload.Regression

open BuilderInitialLengthPayload
open BuilderUnaryPolynomial

-- Independent canonical block arithmetic: T*W*3 + T*W + T*S + C.
example : BuilderRegisterExpression.eval kernel
    (fun i => ([3, 25, 5, 6, 0, 0, 0, 0] : List Nat).getD i.val 0) = 321 := rfl
example : BuilderRegisterExpression.eval kernel
    (fun i => ([1, 3, 0, 0, 0, 0, 0, 0] : List Nat).getD i.val 0) = 12 := rfl
example : BuilderRegisterExactlyOnePayload.payloadValues 7 328 =
    [327, 326, 325, 324, 323, 322, 321, 7, 4] := rfl
example : BuilderRegisterExactlyOnePayload.payloadValues 1 13 = [12, 1, 4] := rfl
example : BuilderRegisterExactlyOnePayload.payloadValues 7 328 ≠
    [321, 322, 323, 324, 325, 326, 327, 7, 4] := by decide
example : BuilderRegisterExactlyOnePayload.payloadValues 7 328 ≠
    [327, 326, 325, 324, 323, 322, 321, 6, 4] := by decide
example : BuilderRegisterExactlyOnePayload.payloadValues 7 328 ≠
    [327, 326, 325, 324, 323, 322, 321, 7, 3] := by decide
example : BuilderRegisterExactlyOnePayload.payloadValues 1 13 ≠ [9, 1, 4] := by decide
example : ((List.replicate (328 - 7 + 1) WorkSymbol.blank).drop (7 + 6)).length = 309 := by
  simpa only [List.length_drop, List.length_replicate] using (show (328 - 7 + 1) - (7 + 6) = 309 from by decide)
example : ((List.replicate (13 - 1 + 1) WorkSymbol.blank).drop (1 + 6)).length = 6 := by
  simpa only [List.length_drop, List.length_replicate] using (show (13 - 1 + 1) - (1 + 6) = 6 from by decide)
example (i : Fin 4) : plan i = .constant 0 := rfl

section Source
variable {language : Language} (problem : VerifierTableauProblem language)
variable (index remaining : Nat)

example : (baseValues problem index remaining).length = Arity problem.verifier :=
  baseValues_length problem index remaining
example : (baseField problem.verifier).eval (fun i => (baseValues problem index remaining).getD i.val 0) =
    baseValue problem index := baseField_eval problem index remaining
example : (certificateField problem.verifier).eval (fun i => (baseValues problem index remaining).getD i.val 0) =
    problem.layout.certificateBitWidth := certificateField_eval problem index remaining
example : BuilderRegisterExpression.nodeCount (expression problem.verifier) = 5 := rfl
example : BuilderRegisterExpression.eval (expression problem.verifier)
    (fun i => (baseValues problem index remaining).getD i.val 0) = upperValue problem index :=
  expression_eval problem index remaining
example : BuilderRegisterExpression.values (expression problem.verifier)
    (fun i => (baseValues problem index remaining).getD i.val 0) =
      [baseValue problem index, problem.layout.certificateBitWidth, 1, countValue problem, upperValue problem index] :=
  expression_values problem index remaining
example : countValue problem ≤ upperValue problem index := count_le_upper problem index
example : (payloadValues problem index).length = countValue problem + 2 := payload_length problem index
example : payloadValues problem index ≠ [] := by
  intro h
  have hLength := payload_length problem index
  rw [h, List.length_nil] at hLength
  omega
example (hMode : problem.tableauInputMode = .paired) :
    countValue problem = problem.certificateLimit + 1 := count_canonical problem hMode
example (hMode : problem.tableauInputMode = .paired) (hZero : problem.certificateLimit = 0) :
    countValue problem = 1 := by rw [count_canonical problem hMode, hZero]
example (hMode : problem.tableauInputMode = .paired) (length : Fin (problem.certificateLimit + 1)) :
    (problem.pairedLengthLiteral hMode length).index.val = baseValue problem index + length.val :=
  length_index_offset problem index hMode length
example (hMode : problem.tableauInputMode = .paired) :
    (problem.pairedLengthVariables hMode).map Fin.val =
      (finiteIndices (problem.certificateLimit + 1)).map (fun length => baseValue problem index + length.val) :=
  length_variables problem index hMode
example (hMode : problem.tableauInputMode = .paired) :
    payloadValues problem index = BuilderInitialConstraintPayload.lengthValues problem hMode :=
  payload_canonical problem index hMode
example : (graph problem.verifier).nodes.length = 3 := graph_nodes_length problem.verifier
example : (graph problem.verifier).WellFormed := graph_wellFormed problem.verifier
example : baseValues problem index remaining ++ BuilderRegisterExpression.values (expression problem.verifier)
    (fun i => (baseValues problem index remaining).getD i.val 0) =
      scratchValues problem index remaining ++ [countValue problem, upperValue problem index] :=
  fields_suffix problem index remaining
example (inside : List WorkSymbol) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
      (initialConfiguration problem index remaining inside) = some (finalConfiguration problem index remaining inside) :=
  workRunExact problem index remaining inside
example (inside : List WorkSymbol) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining)
      (encodeWorkConfiguration (initialConfiguration problem index remaining inside)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining inside) :=
  run_compile_exact problem index remaining inside
example : finalValues problem index remaining = (scratchValues problem index remaining ++ [countValue problem]) ++
    payloadValues problem index := final_suffix problem index remaining
example (inside : List WorkSymbol) : (finalConfiguration problem index remaining inside).tape.left =
    exterior problem index := final_exterior problem index remaining inside
example (inside : List WorkSymbol) : (finalConfiguration problem index remaining inside).tape.right =
    (registerWord (payloadValues problem index)).reverse ++
      ((registerWord (scratchValues problem index remaining ++ [countValue problem])).reverse ++ inside) :=
  final_inside_preserved problem index remaining inside
example (hMode : problem.tableauInputMode = .paired) :
    finalValues problem index remaining = (scratchValues problem index remaining ++ [countValue problem]) ++
      BuilderInitialConstraintPayload.lengthValues problem hMode := final_canonical problem index remaining hMode
example (output : List CNFToken) (hMode : problem.tableauInputMode = .paired) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
      (initialConfiguration problem index remaining (BuilderDividerOperands.inside problem.input output)) =
      some
        {state := (machine problem.verifier).acceptState,
         tape := BuilderDividerOperands.endTape
           ((scratchValues problem index remaining ++ [countValue problem]) ++ BuilderInitialConstraintPayload.lengthValues problem hMode)
           (BuilderDividerOperands.inside problem.input output) (exterior problem index)} :=
  source_canonical_payload problem index remaining output hMode
example (hMode : problem.tableauInputMode = .paired) :
    payloadValues problem index = BuilderInitialConstraintPayload.values problem 2 := payload_initial_slot problem index hMode
example (hMode : problem.tableauInputMode = .paired) :
    BuilderLocalConstraintPayload.decode problem.FormulaWidth (payloadValues problem index) =
      some (problem.initialConstraintSlotDirect 2) := payload_decode problem index hMode
example : (machine problem.verifier).rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  rules_pairwise_query_distinct problem.verifier
example : WorkMachineProgramGraph.NoRuleAt (machine problem.verifier) (machine problem.verifier).acceptState :=
  noRuleAtAccept problem.verifier
example : WorkMachineProgramGraph.NoRuleAt (machine problem.verifier) (machine problem.verifier).rejectState :=
  noRuleAtReject problem.verifier
example : (machine problem.verifier).acceptState ≠ (machine problem.verifier).rejectState :=
  acceptState_ne_rejectState problem.verifier
example
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .initial) :
    (registerWord (finalValues problem index remaining)).length + (exterior problem index).length ≤
        (spanPolynomial problem.verifier).eval problem.input.length ∧
      6 * workSteps problem index remaining ≤ (rawTimePolynomial problem.verifier).eval problem.input.length :=
  source_polynomial_bounds problem index remaining hBody hBalance hRegion
end Source
end PNP.Concrete.CookLevin.BuilderInitialLengthPayload.Regression
