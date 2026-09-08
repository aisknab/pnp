import PNP.Concrete.CookLevinBuilderControlImplicationPayload

open PNP.Concrete PNP.Concrete.CookLevin
open BuilderControlImplicationPayload
open BuilderUnaryPolynomial (registerWord)

example : (conclusionCode .state).val = 0 := rfl
example : (conclusionCode .head).val = 1 := rfl
example : (conclusionCode .symbol).val = 2 := rfl
example : conclusionCode .state ≠ conclusionCode .head := by decide
example : conclusionRole .state = .nextState := rfl
example : conclusionRole .head = .nextHead := rfl
example : conclusionRole .symbol = .nextWrite := rfl

section Universal
variable {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) (conclusion : Conclusion)
variable (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control)

example : BuilderControlLiteralSources.request (conclusionRole conclusion) (BuilderControlCoordinates.ofSource problem index hRegion) =
    BuilderControlCoordinates.conclusionRequest (targetCoordinates conclusion (BuilderControlCoordinates.ofSource problem index hRegion)) :=
  conclusion_request conclusion _
example : (newValues problem index conclusion hRegion).length = newCount conclusion :=
  newValues_length problem index conclusion hRegion
example : (stateValues problem index conclusion hRegion).length = stateCount conclusion :=
  stateValues_length problem index conclusion hRegion
example : (headValues problem index conclusion hRegion).length = headCount conclusion :=
  headValues_length problem index conclusion hRegion
example : (allValues problem index conclusion hRegion).length = allCount conclusion :=
  allValues_length problem index conclusion hRegion

example : (allValues problem index conclusion hRegion).getD (newCount conclusion - 1) 0 =
      (BuilderControlLiteralSources.request (conclusionRole conclusion) (BuilderControlCoordinates.ofSource problem index hRegion)).index ∧
    (allValues problem index conclusion hRegion).getD (stateCount conclusion - 1) 0 =
      (BuilderControlCoordinates.stateRequest (BuilderControlCoordinates.ofSource problem index hRegion)).index ∧
    (allValues problem index conclusion hRegion).getD (headCount conclusion - 1) 0 =
      (BuilderControlCoordinates.headRequest (BuilderControlCoordinates.ofSource problem index hRegion)).index ∧
    (allValues problem index conclusion hRegion).getD (allCount conclusion - 1) 0 =
      (BuilderControlCoordinates.readRequest (BuilderControlCoordinates.ofSource problem index hRegion)).index :=
  retained_indices problem index conclusion hRegion

example : (payloadValues problem index remaining conclusion hRegion).length = 10 :=
  payloadValues_length problem index remaining conclusion hRegion
example : (payloadValues problem index remaining conclusion hRegion).length ≠ 8 := by
  rw [payloadValues_length]
  decide
example : payloadValues problem index remaining conclusion hRegion =
    BuilderLocalConstraintPayload.values
      (BuilderControlCoordinates.slot (targetCoordinates conclusion (BuilderControlCoordinates.ofSource problem index hRegion))) :=
  payload_values_eq problem index remaining conclusion hRegion
example : BuilderLocalConstraintPayload.decode problem.FormulaWidth (payloadValues problem index remaining conclusion hRegion) =
    some (BuilderControlCoordinates.slot (targetCoordinates conclusion (BuilderControlCoordinates.ofSource problem index hRegion))) :=
  payload_decode problem index remaining conclusion hRegion
example (hSelected : conclusionCode conclusion = (BuilderControlCoordinates.ofSource problem index hRegion).conclusion) :
    BuilderLocalConstraintPayload.decode problem.FormulaWidth (payloadValues problem index remaining conclusion hRegion) =
      some (problem.controlConstraintSlotDirect (BuilderConstraintRegionSource.localCoordinate problem index .control)) :=
  payload_source_slot problem index remaining conclusion hRegion hSelected

example (inside outside : List WorkSymbol) :
    workRunExact? (prefixMachine problem.verifier conclusion) (prefixSteps problem index remaining conclusion hRegion)
      (prefixInitial problem index remaining conclusion inside outside) =
      some (prefixFinal problem index remaining conclusion inside outside hRegion) :=
  prefix_workRunExact problem index remaining conclusion inside outside hRegion
example (inside outside : List WorkSymbol) :
    workRunExact? (machine problem.verifier conclusion) (workSteps problem index remaining conclusion hRegion)
      (initialConfiguration problem index remaining conclusion inside outside) =
      some (finalConfiguration problem index remaining conclusion inside outside hRegion) :=
  workRunExact problem index remaining conclusion inside outside hRegion
example (inside outside : List WorkSymbol) :
    run (compileWorkMachine (machine problem.verifier conclusion)) (6 * workSteps problem index remaining conclusion hRegion)
      (encodeWorkConfiguration (initialConfiguration problem index remaining conclusion inside outside)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining conclusion inside outside hRegion) :=
  run_compile_exact problem index remaining conclusion inside outside hRegion
example (inside outside : List WorkSymbol) :
    (finalConfiguration problem index remaining conclusion inside outside hRegion).tape.right =
      (registerWord (BuilderLocalConstraintPayload.values
        (BuilderControlCoordinates.slot (targetCoordinates conclusion (BuilderControlCoordinates.ofSource problem index hRegion))))).reverse ++
      ((registerWord (BuilderLiteralArgumentSource.inputValues problem index remaining .control
        (allValues problem index conclusion hRegion))).reverse ++ inside) :=
  final_canonical_payload problem index remaining conclusion inside outside hRegion
example (inside outside : List WorkSymbol) :
    (finalConfiguration problem index remaining conclusion inside outside hRegion).tape.left =
      finalOutside problem index remaining conclusion outside hRegion :=
  final_exterior_accounted problem index remaining conclusion inside outside hRegion

example (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    (registerWord (BuilderLiteralArgumentSource.inputValues problem index remaining .control
      (allValues problem index conclusion hRegion))).length ≤
        (prefixSpanBound problem.verifier conclusion).eval problem.input.length ∧
      6 * prefixSteps problem index remaining conclusion hRegion ≤
        (prefixRawTimeBound problem.verifier conclusion).eval problem.input.length :=
  prefix_source_polynomial_bounds problem index remaining conclusion hBody hBalance hRegion
example (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    (registerWord (finalValues problem index remaining conclusion hRegion)).length ≤
        (spanBound problem.verifier conclusion).eval problem.input.length ∧
      6 * workSteps problem index remaining conclusion hRegion ≤
        (rawTimeBound problem.verifier conclusion).eval problem.input.length :=
  source_polynomial_bounds problem index remaining conclusion hBody hBalance hRegion

end Universal

example {language : Language} (verifier : PolynomialTimeVerifier language) (conclusion : Conclusion) :
    (machine verifier conclusion).rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  rules_pairwise_query_distinct verifier conclusion
example {language : Language} (verifier : PolynomialTimeVerifier language) (conclusion : Conclusion) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier conclusion) (machine verifier conclusion).acceptState :=
  noRuleAtAccept verifier conclusion
example {language : Language} (verifier : PolynomialTimeVerifier language) (conclusion : Conclusion) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier conclusion) (machine verifier conclusion).rejectState :=
  noRuleAtReject verifier conclusion
example {language : Language} (verifier : PolynomialTimeVerifier language) (conclusion : Conclusion) :
    (machine verifier conclusion).acceptState ≠ (machine verifier conclusion).rejectState :=
  acceptState_ne_rejectState verifier conclusion
