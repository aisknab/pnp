import PNP.Concrete.CookLevinBuilderControlHeadSource

open PNP.Concrete PNP.Concrete.CookLevin
open BuilderControlHeadSource
open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape)

section Universal
variable {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
variable (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control)

example : (fields problem.verifier).length = 3 := rfl
example : (retainedValues problem index).length = 8 := retainedValues_length problem index hRegion
example : positionValue problem index =
    (BuilderControlCoordinates.ofSource problem index hRegion).position.val :=
  position_canonical problem index hRegion
example : BuilderLiteralArgumentSource.referenceValue problem index .control
    (retainedValues problem index) moveReference =
    BuilderRegisterHeadMove.moveCode (actualMove problem index hRegion) :=
  move_reference_canonical problem index hRegion

example : BuilderRegisterPack.values (fields problem.verifier)
    (BuilderLiteralArgumentSource.environment problem index remaining .control 8 (retainedValues problem index)) =
    packedValues problem index hRegion := fields_values problem index remaining hRegion

example : List.ofFn (BuilderLiteralArgumentSource.environment problem index remaining .control 8
    (retainedValues problem index)) = BuilderControlActionSource.finalValues problem index remaining :=
  environment_frame problem index remaining hRegion

example : (finalRetainedValues problem index hRegion).length = 12 :=
  finalRetainedValues_length problem index hRegion
example : finalValues problem index remaining hRegion =
    BuilderLiteralArgumentSource.inputValues problem index remaining .control (finalRetainedValues problem index hRegion) :=
  finalValues_frame problem index remaining hRegion
example : finalValues problem index remaining hRegion =
    BuilderControlActionSource.finalValues problem index remaining ++ headValues problem index hRegion := rfl

example : BuilderRegisterHeadMove.moved (widthValue problem) (positionValue problem index)
    (actualMove problem index hRegion) =
    (VerifierTableauProblem.movePosition (BuilderControlCoordinates.ofSource problem index hRegion).position
      (BuilderControlCoordinates.action (BuilderControlCoordinates.ofSource problem index hRegion)).move).val :=
  moved_canonical problem index hRegion

example (hMove : actualMove problem index hRegion = .stay) :
    headValues problem index hRegion = [widthValue problem, positionValue problem index, 0, positionValue problem index] := by
  simp only [headValues, hMove, BuilderRegisterHeadMove.finalValues, BuilderRegisterHeadMove.moveCode,
    BuilderControlActionSource.moveCode, BuilderRegisterHeadMove.moved]
example (hMove : actualMove problem index hRegion = .left) (hZero : positionValue problem index = 0) :
    headValues problem index hRegion = [widthValue problem, 0, 1, 0] := by
  simp only [headValues, hMove, hZero, BuilderRegisterHeadMove.finalValues, BuilderRegisterHeadMove.moveCode,
    BuilderControlActionSource.moveCode, BuilderRegisterHeadMove.moved, Nat.zero_sub]
example (hMove : actualMove problem index hRegion = .left) (position : Nat)
    (hPosition : positionValue problem index = position + 1) :
    headValues problem index hRegion = [widthValue problem, position + 1, 1, position] := by
  simp only [headValues, hMove, hPosition, BuilderRegisterHeadMove.finalValues, BuilderRegisterHeadMove.moveCode,
    BuilderControlActionSource.moveCode, BuilderRegisterHeadMove.moved, Nat.add_sub_cancel]
example (hMove : actualMove problem index hRegion = .right)
    (hNext : positionValue problem index + 1 < widthValue problem) :
    headValues problem index hRegion =
      [widthValue problem, positionValue problem index, 2, positionValue problem index + 1] := by
  simp only [headValues, hMove, BuilderRegisterHeadMove.finalValues, BuilderRegisterHeadMove.moveCode,
    BuilderControlActionSource.moveCode, BuilderRegisterHeadMove.moved, if_pos hNext]
example (hMove : actualMove problem index hRegion = .right)
    (hEdge : ¬ positionValue problem index + 1 < widthValue problem) :
    headValues problem index hRegion =
      [widthValue problem, positionValue problem index, 2, positionValue problem index] := by
  simp only [headValues, hMove, BuilderRegisterHeadMove.finalValues, BuilderRegisterHeadMove.moveCode,
    BuilderControlActionSource.moveCode, BuilderRegisterHeadMove.moved, if_neg hEdge]

example (inside outside : List WorkSymbol) :
    workRunExact? (packMachine problem.verifier) (packSteps problem index remaining)
      (workStartConfiguration (packMachine problem.verifier)
        (endTape (BuilderControlActionSource.finalValues problem index remaining) inside outside)) =
      some {
        state := (packMachine problem.verifier).acceptState
        tape := endTape (BuilderControlActionSource.finalValues problem index remaining ++ packedValues problem index hRegion)
          inside (outside.drop (registerWord (packedValues problem index hRegion)).length)} :=
  pack_workRunExact problem index remaining inside outside hRegion

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

example (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    (registerWord (finalValues problem index remaining hRegion)).length ≤
        (spanBound problem.verifier).eval problem.input.length ∧
      6 * workSteps problem index remaining hRegion ≤ (rawTimeBound problem.verifier).eval problem.input.length :=
  source_polynomial_bounds problem index remaining hBody hBalance hRegion

example (inside outside : List WorkSymbol) :
    (finalConfiguration problem index remaining inside outside hRegion).tape.right =
      (registerWord (finalValues problem index remaining hRegion)).reverse ++ inside :=
  final_inside_preserved problem index remaining inside outside hRegion
example (inside outside : List WorkSymbol) :
    (finalConfiguration problem index remaining inside outside hRegion).tape.left =
      finalOutside problem index outside hRegion :=
  final_exterior_accounted problem index remaining inside outside hRegion
example (inside outside : List WorkSymbol) :
    (finalConfiguration problem index remaining inside outside hRegion).tape.left.length ≤
      outside.length + positionValue problem index + widthValue problem + 5 :=
  final_exterior_length_le problem index remaining inside outside hRegion

end Universal

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineProgramGraph.QueryDistinct := rules_pairwise_query_distinct verifier
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier) (machine verifier).acceptState := noRuleAtAccept verifier
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier) (machine verifier).rejectState := noRuleAtReject verifier
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState := acceptState_ne_rejectState verifier
