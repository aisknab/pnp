import PNP.Concrete.CookLevinBuilderShapePayload

namespace PNP.Concrete.CookLevin.BuilderShapePayload.Regression

open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape)
open BuilderShapeCoordinates (Kind Width)
open BuilderShapeBranchPayload (rowValue)
open BuilderArbitrarySlotHeaderRouter
open WorkMachineProgramGraph (Node)

example : rowReference = BuilderLiteralArgumentSource.Reference.digit ⟨0, by decide⟩ := rfl
example : widthReference = BuilderLiteralArgumentSource.Reference.source .tapeWidth := rfl
example {language : Language} (verifier : PolynomialTimeVerifier language) : (pairFields verifier).length = 2 :=
  pairFields_length verifier
example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    BuilderRegisterPack.values (pairFields problem.verifier)
      (BuilderLiteralArgumentSource.environment problem index remaining .shape 0 []) =
      [rowValue problem index, Width problem] := pair_values problem index remaining

example (matched rest : Nat) : resultKind (.less matched rest) = Kind.symbol := rfl
example (matched : Nat) : resultKind (.equal matched) = Kind.head := rfl
example (matched rest : Nat) : resultKind (.greater matched rest) = Kind.state := rfl
example (coordinate boundary : Nat) (h : coordinate < boundary) :
    resultKind (RawRouter.compareResult 0 coordinate boundary) = Kind.symbol := by
  rw [resultKind_compareResult_eq, if_pos h]
example (coordinate boundary : Nat) (h : coordinate = boundary) :
    resultKind (RawRouter.compareResult 0 coordinate boundary) = Kind.head := by
  rw [resultKind_compareResult_eq, if_neg (by omega : ¬ coordinate < boundary), if_pos h]
example (coordinate boundary : Nat) (h : boundary < coordinate) :
    resultKind (RawRouter.compareResult 0 coordinate boundary) = Kind.state := by
  rw [resultKind_compareResult_eq, if_neg (by omega : ¬ coordinate < boundary), if_neg (by omega : coordinate ≠ boundary)]
example : resultKind (RawRouter.compareResult 0 0 0) = Kind.head := rfl
example : resultKind (RawRouter.compareResult 0 0 1) = Kind.symbol := rfl
example : resultKind (RawRouter.compareResult 0 1 0) = Kind.state := rfl
example {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape) :
    selectedKind problem index = BuilderShapeCoordinates.kind (BuilderShapeCoordinates.ofSource problem index hRegion) :=
  selectedKind_canonical problem index hRegion

-- Finite program shape is independent of every input length, row and branch verdict.
example {language : Language} (verifier : PolynomialTimeVerifier language) : (graph verifier).nodes.length = 9 := rfl
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (graph verifier).nodes.map Node.name = [0, 1, 2, 3, 4, 5, 6, 7, 8] := rfl
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (graph verifier).entry = (pairNode verifier).reference := rfl
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (pairNode verifier).onAccept = .node (comparisonNode verifier).reference := rfl
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (comparisonNode verifier).program = BuilderRegionResidualSelection.machine := rfl
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (comparisonNode verifier).onAccept = .node (eraseNode verifier .symbol).reference := rfl
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (comparisonNode verifier).onReject = .node (zeroNode verifier).reference := rfl
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (zeroNode verifier).program = BuilderUnaryTagMatch.machine 0 := rfl
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (zeroNode verifier).onAccept = .node (eraseNode verifier .head).reference := rfl
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (zeroNode verifier).onReject = .node (eraseNode verifier .state).reference := rfl
example {language : Language} (verifier : PolynomialTimeVerifier language) (branch : Kind) :
    (eraseNode verifier branch).program = BuilderRegisterErase.machine 4 := rfl
example {language : Language} (verifier : PolynomialTimeVerifier language) (branch : Kind) :
    (eraseNode verifier branch).onAccept = .node (payloadNode verifier branch).reference := rfl
example {language : Language} (verifier : PolynomialTimeVerifier language) (branch : Kind) :
    (payloadNode verifier branch).program = BuilderShapeBranchPayload.machine verifier 0 branch := rfl
example {language : Language} (verifier : PolynomialTimeVerifier language) (branch : Kind) :
    (payloadNode verifier branch).onAccept = .accept := rfl
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (graph verifier).WellFormed := graph_wellFormed verifier

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    workSteps problem index remaining = pairSteps problem index remaining + 1 +
      (BuilderRegisterEquality.workSteps (rowValue problem index) (Width problem) +
        (BuilderShapeBranchPayload.workSteps problem index remaining 0 [] (selectedKind problem index) + 1)) := rfl

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) :
    workRunExact? (pairMachine problem.verifier) (pairSteps problem index remaining)
      (workStartConfiguration (pairMachine problem.verifier) (endTape (frame problem index remaining) inside [])) =
      some {
        state := (pairMachine problem.verifier).acceptState
        tape := endTape (frame problem index remaining ++ [rowValue problem index, Width problem]) inside [] } :=
  pair_workRunExact problem index remaining inside

-- Neither complete machine execution nor canonical execution is given a Kind premise.
example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
      (initialConfiguration problem index remaining inside) = some (finalConfiguration problem index remaining inside) :=
  workRunExact problem index remaining inside
example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining)
      (encodeWorkConfiguration (initialConfiguration problem index remaining inside)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining inside) :=
  run_compile_exact problem index remaining inside
example {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape) :
    payloadValues problem index = BuilderLocalConstraintPayload.values
      (problem.shapeConstraintSlotDirect (BuilderConstraintRegionSource.localCoordinate problem index .shape)) :=
  payload_canonical problem index hRegion
example {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape) :
    BuilderLocalConstraintPayload.decode problem.FormulaWidth (payloadValues problem index) =
      some (problem.shapeConstraintSlotDirect (BuilderConstraintRegionSource.localCoordinate problem index .shape)) :=
  payload_decode problem index hRegion
example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape) :
    finalValues problem index remaining =
      BuilderShapeBranchPayload.scratchValues problem index remaining 0 [] (selectedKind problem index) ++
        [BuilderShapeBranchPayload.countValue problem (selectedKind problem index)] ++
        BuilderLocalConstraintPayload.values
          (problem.shapeConstraintSlotDirect (BuilderConstraintRegionSource.localCoordinate problem index .shape)) :=
  final_canonical_payload problem index remaining hRegion
example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
      (initialConfiguration problem index remaining inside) =
      some {
        state := (machine problem.verifier).acceptState
        tape := endTape
          (BuilderShapeBranchPayload.scratchValues problem index remaining 0 [] (selectedKind problem index) ++
            [BuilderShapeBranchPayload.countValue problem (selectedKind problem index)] ++
            BuilderLocalConstraintPayload.values
              (problem.shapeConstraintSlotDirect (BuilderConstraintRegionSource.localCoordinate problem index .shape)))
          inside (BuilderShapeBranchPayload.exteriorWithOutside problem index remaining 0 []
            (selectedKind problem index) (comparisonBlanks problem index)) } :=
  canonical_workRunExact problem index remaining inside hRegion
example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) :
    (finalConfiguration problem index remaining inside).tape.right =
      (registerWord (finalValues problem index remaining)).reverse ++ inside :=
  final_inside_preserved problem index remaining inside
example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) :
    (finalConfiguration problem index remaining inside).tape.left =
      BuilderShapeBranchPayload.exteriorWithOutside problem index remaining 0 []
        (selectedKind problem index) (comparisonBlanks problem index) :=
  final_exterior problem index remaining inside

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape) :
    (registerWord (frame problem index remaining ++ [rowValue problem index, Width problem])).length ≤
      (pairSpanBound problem.verifier).eval problem.input.length ∧
    6 * pairSteps problem index remaining ≤ (pairRawTimeBound problem.verifier).eval problem.input.length :=
  pair_source_polynomial_bounds problem index remaining hBody hBalance hRegion
example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape) :
    (comparisonBlanks problem index).length ≤ (comparisonSpanBound problem.verifier).eval problem.input.length ∧
    6 * BuilderRegisterEquality.workSteps (rowValue problem index) (Width problem) ≤
      (BuilderRegisterEquality.rawTimePolynomial (pairSpanBound problem.verifier)).eval problem.input.length :=
  comparison_source_polynomial_bounds problem index remaining hBody hBalance hRegion
example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape) :
    (registerWord (finalValues problem index remaining)).length +
        (finalConfiguration problem index remaining inside).tape.left.length ≤
      (spanBound problem.verifier).eval problem.input.length ∧
    6 * workSteps problem index remaining ≤ (rawTimeBound problem.verifier).eval problem.input.length :=
  source_polynomial_bounds problem index remaining inside hBody hBalance hRegion

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct := rules_pairwise_query_distinct verifier
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (machine verifier) := noRuleAtAccept verifier
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier) (machine verifier).rejectState := noRuleAtReject verifier
example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState := acceptState_ne_rejectState verifier

-- The canonical identity cannot turn the actual head branch into a symbol branch.
example {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape)
    (hHead : BuilderShapeCoordinates.kind (BuilderShapeCoordinates.ofSource problem index hRegion) = Kind.head) :
    selectedKind problem index ≠ Kind.symbol := by
  rw [selectedKind_canonical problem index hRegion, hHead]
  intro h
  cases h

end PNP.Concrete.CookLevin.BuilderShapePayload.Regression
