import PNP.Concrete.CookLevinBuilderControlPayload

open PNP.Concrete PNP.Concrete.CookLevin
open BuilderControlPayload
open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape)

example : conclusionOfCode ⟨0, by decide⟩ = .state := rfl
example : conclusionOfCode ⟨1, by decide⟩ = .head := rfl
example : conclusionOfCode ⟨2, by decide⟩ = .symbol := rfl
example (code : Fin 3) : BuilderControlImplicationPayload.conclusionCode (conclusionOfCode code) = code :=
  conclusionOfCode_code code
example : dispatchOverhead .state = 9 := rfl
example : dispatchOverhead .head = 16 := rfl
example : dispatchOverhead .symbol = 25 := rfl
example (conclusion : BuilderControlImplicationPayload.Conclusion) : testSteps conclusion ≤ 18 :=
  testSteps_le conclusion
example (conclusion : BuilderControlImplicationPayload.Conclusion) : dispatchOverhead conclusion ≤ 25 :=
  dispatchOverhead_le conclusion
example (tag : Nat) (outside : List WorkSymbol) :
    restoredOutside tag outside = List.replicate (tag + 1) WorkSymbol.blank ++ outside.drop (tag + 1) := rfl
example (tag : Nat) (outside : List WorkSymbol) :
    (restoredOutside tag outside).length ≤ outside.length + tag + 1 :=
  restoredOutside_length_le tag outside

section Universal
variable {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
variable (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control)

example : tagValue problem index = (BuilderControlCoordinates.ofSource problem index hRegion).conclusion.val :=
  tag_canonical problem index hRegion
example : tagValue problem index < 3 := tag_lt problem index hRegion
example : BuilderControlImplicationPayload.conclusionCode (selectedConclusion problem index hRegion) =
    (BuilderControlCoordinates.ofSource problem index hRegion).conclusion :=
  selected_code problem index hRegion
example : tagValue problem index = (BuilderControlImplicationPayload.conclusionCode
    (selectedConclusion problem index hRegion)).val :=
  tag_selected problem index hRegion
example : BuilderRegisterPack.values (fields problem.verifier)
    (BuilderLiteralArgumentSource.environment problem index remaining .control 0 []) = [tagValue problem index] :=
  fields_values problem index remaining

-- No caller-selected conclusion or branch-correctness premise is available here.
example (inside outside : List WorkSymbol) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining hRegion)
      (initialConfiguration problem index remaining inside outside) =
      some (finalConfiguration problem index remaining inside outside hRegion) :=
  workRunExact problem index remaining inside outside hRegion
example (inside outside : List WorkSymbol) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining hRegion)
      (encodeWorkConfiguration (initialConfiguration problem index remaining inside outside)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining inside outside hRegion) :=
  run_compile_exact problem index remaining inside outside hRegion
example : (payloadValues problem index remaining hRegion).length = 10 :=
  payloadValues_length problem index remaining hRegion
example : (payloadValues problem index remaining hRegion).length ≠ 8 := by
  rw [payloadValues_length]
  decide
example : payloadValues problem index remaining hRegion = BuilderLocalConstraintPayload.values
    (problem.controlConstraintSlotDirect (BuilderConstraintRegionSource.localCoordinate problem index .control)) :=
  payload_source_values problem index remaining hRegion
example : BuilderLocalConstraintPayload.decode problem.FormulaWidth (payloadValues problem index remaining hRegion) =
    some (problem.controlConstraintSlotDirect (BuilderConstraintRegionSource.localCoordinate problem index .control)) :=
  payload_source_slot problem index remaining hRegion
example (inside outside : List WorkSymbol) :
    (finalConfiguration problem index remaining inside outside hRegion).tape.right =
      (registerWord (BuilderLocalConstraintPayload.values
        (problem.controlConstraintSlotDirect (BuilderConstraintRegionSource.localCoordinate problem index .control)))).reverse ++
      ((registerWord (BuilderLiteralArgumentSource.inputValues problem index remaining .control
        (BuilderControlImplicationPayload.allValues problem index (selectedConclusion problem index hRegion) hRegion))).reverse ++ inside) :=
  final_canonical_payload problem index remaining inside outside hRegion
example (inside outside : List WorkSymbol) :
    (finalConfiguration problem index remaining inside outside hRegion).tape.left =
      BuilderControlImplicationPayload.finalOutside problem index remaining (selectedConclusion problem index hRegion)
        (List.replicate (tagValue problem index + 1) WorkSymbol.blank ++ outside.drop (tagValue problem index + 1)) hRegion :=
  final_exterior_accounted problem index remaining inside outside hRegion
example : workSteps problem index remaining hRegion = copySteps problem index remaining +
    BuilderControlImplicationPayload.workSteps problem index remaining (selectedConclusion problem index hRegion) hRegion +
    dispatchOverhead (selectedConclusion problem index hRegion) :=
  workSteps_decomposition problem index remaining hRegion

example (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    (registerWord (finalValues problem index remaining hRegion)).length ≤
        (spanBound problem.verifier).eval problem.input.length ∧
      6 * workSteps problem index remaining hRegion ≤ (rawTimeBound problem.verifier).eval problem.input.length :=
  source_polynomial_bounds problem index remaining hBody hBalance hRegion

example : (graph problem.verifier).WellFormed := graph_wellFormed problem.verifier
example : (graph problem.verifier).nodes.length = 10 := rfl
example : (symbolTestNode problem.verifier).onReject = .reject := rfl
example : (machine problem.verifier).rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  rules_pairwise_query_distinct problem.verifier
example : WorkMachineProgramGraph.NoRuleAt (machine problem.verifier) (machine problem.verifier).acceptState :=
  noRuleAtAccept problem.verifier
example : WorkMachineProgramGraph.NoRuleAt (machine problem.verifier) (machine problem.verifier).rejectState :=
  noRuleAtReject problem.verifier
example : (machine problem.verifier).acceptState ≠ (machine problem.verifier).rejectState :=
  acceptState_ne_rejectState problem.verifier
example (code : Nat) (older : List Nat) (inside outside : List WorkSymbol)
    (hInvalid : code ≠ 0 ∧ code ≠ 1 ∧ code ≠ 2) :
    workRunExact? (machine problem.verifier) (invalidSteps code)
      (WorkMachineProgramGraph.endpointConfiguration (.node (stateTestNode problem.verifier).reference)
        (endTape (older ++ [code]) inside outside)) =
      some {state := (machine problem.verifier).rejectState, tape := endTape (older ++ [code]) inside outside} :=
  invalid_tag_workRunExact problem.verifier code older inside outside hInvalid
end Universal
