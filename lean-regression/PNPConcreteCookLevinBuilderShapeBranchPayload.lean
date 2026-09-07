/-
Copyright (c) 2026 PNP Labs.
Source-bound fixed-branch contracts, with the runtime dispatch premise explicit.
No prepared count, upper bound, variable list or arithmetic result is supplied.
-/
import PNP.Concrete.CookLevinBuilderShapeBranchPayload

namespace PNP.Concrete.CookLevin.BuilderShapeBranchPayload.Regression

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderShapeCoordinates (Kind Width)

example {language : Language} (problem : VerifierTableauProblem language) :
    countValue problem .symbol = 3 := rfl
example {language : Language} (problem : VerifierTableauProblem language) :
    countValue problem .head = problem.dimensions.tapeWidth problem.tableauInputMode := rfl
example {language : Language} (problem : VerifierTableauProblem language) :
    countValue problem .state = problem.dimensions.stateBound := rfl

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat) (branch : Kind) :
    (countField problem.verifier afterCount branch).eval
        (BuilderLiteralArgumentSource.environment problem index remaining .shape afterCount after) =
      countValue problem branch := countField_eval problem index remaining afterCount after branch
example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat) (branch : Kind) :
    BuilderRegisterExpression.eval (baseExpression problem.verifier afterCount branch)
        (BuilderLiteralArgumentSource.environment problem index remaining .shape afterCount after) =
      baseValue problem index branch := base_eval problem index remaining afterCount after branch
example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat) (branch : Kind) :
    BuilderRegisterExpression.eval (expression problem.verifier afterCount branch)
        (BuilderLiteralArgumentSource.environment problem index remaining .shape afterCount after) =
      upperValue problem index branch := expression_eval problem index remaining afterCount after branch

-- The physically emitted suffix, not just an abstract expression value, is the next machine's input.
example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat) (branch : Kind) :
    BuilderRegisterExpression.values (expression problem.verifier afterCount branch)
        (BuilderLiteralArgumentSource.environment problem index remaining .shape afterCount after) =
      BuilderRegisterExpression.values (baseExpression problem.verifier afterCount branch)
        (BuilderLiteralArgumentSource.environment problem index remaining .shape afterCount after) ++
      [countValue problem branch, upperValue problem index branch] :=
  expression_values problem index remaining afterCount after branch
example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) (branch : Kind) :
    countValue problem branch ≤ upperValue problem index branch := count_le_upper problem index branch

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat) (branch : Kind)
    (inside outside : List WorkSymbol) (hAfter : after.length = afterCount) :
    workRunExact? (fieldsMachine problem.verifier afterCount branch)
      (fieldsSteps problem index remaining afterCount after branch)
      (workStartConfiguration (fieldsMachine problem.verifier afterCount branch)
        (endTape (BuilderLiteralArgumentSource.inputValues problem index remaining .shape after) inside outside)) =
      some {
        state := (fieldsMachine problem.verifier afterCount branch).acceptState
        tape := endTape (scratchValues problem index remaining afterCount after branch ++
            [countValue problem branch, upperValue problem index branch]) inside
          (outside.drop (registerWord (BuilderRegisterExpression.values
            (expression problem.verifier afterCount branch)
            (BuilderLiteralArgumentSource.environment problem index remaining .shape afterCount after))).length) } :=
  fields_workRunExact problem index remaining afterCount after branch inside outside hAfter

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat) (branch : Kind)
    (inside : List WorkSymbol) (hAfter : after.length = afterCount) :
    workRunExact? (machine problem.verifier afterCount branch)
      (workSteps problem index remaining afterCount after branch)
      (initialConfiguration problem index remaining afterCount after branch inside) =
      some (finalConfiguration problem index remaining afterCount after branch inside) :=
  workRunExact problem index remaining afterCount after branch inside hAfter
example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat) (branch : Kind)
    (inside : List WorkSymbol) (hAfter : after.length = afterCount) :
    run (compileWorkMachine (machine problem.verifier afterCount branch))
      (6 * workSteps problem index remaining afterCount after branch)
      (encodeWorkConfiguration (initialConfiguration problem index remaining afterCount after branch inside)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining afterCount after branch inside) :=
  run_compile_exact problem index remaining afterCount after branch inside hAfter

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape) :
    timeValue problem index = (BuilderShapeCoordinates.ofSource problem index hRegion).time.val ∧
    rowValue problem index = (BuilderShapeCoordinates.ofSource problem index hRegion).row.val :=
  source_coordinates problem index hRegion
example {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape)
    (branch : Kind) (hBranch : BuilderShapeCoordinates.kind (BuilderShapeCoordinates.ofSource problem index hRegion) = branch) :
    countValue problem branch = BuilderShapeCoordinates.count (BuilderShapeCoordinates.ofSource problem index hRegion) :=
  source_count problem index hRegion branch hBranch
example {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape)
    (branch : Kind) (hBranch : BuilderShapeCoordinates.kind (BuilderShapeCoordinates.ofSource problem index hRegion) = branch) :
    baseValue problem index branch = BuilderShapeCoordinates.base (BuilderShapeCoordinates.ofSource problem index hRegion) :=
  source_base problem index hRegion branch hBranch
example {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape)
    (branch : Kind) (hBranch : BuilderShapeCoordinates.kind (BuilderShapeCoordinates.ofSource problem index hRegion) = branch) :
    upperValue problem index branch = BuilderShapeCoordinates.upper (BuilderShapeCoordinates.ofSource problem index hRegion) :=
  source_upper problem index hRegion branch hBranch
example {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape)
    (branch : Kind) (hBranch : BuilderShapeCoordinates.kind (BuilderShapeCoordinates.ofSource problem index hRegion) = branch) :
    BuilderRegisterExactlyOnePayload.payloadValues (countValue problem branch) (upperValue problem index branch) =
      BuilderLocalConstraintPayload.values
        (problem.shapeConstraintSlotDirect (BuilderConstraintRegionSource.localCoordinate problem index .shape)) :=
  source_payload problem index hRegion branch hBranch
example {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape)
    (branch : Kind) (hBranch : BuilderShapeCoordinates.kind (BuilderShapeCoordinates.ofSource problem index hRegion) = branch) :
    BuilderLocalConstraintPayload.decode problem.FormulaWidth
      (BuilderRegisterExactlyOnePayload.payloadValues (countValue problem branch) (upperValue problem index branch)) =
      some (problem.shapeConstraintSlotDirect (BuilderConstraintRegionSource.localCoordinate problem index .shape)) :=
  payload_decode problem index hRegion branch hBranch
example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape)
    (branch : Kind) (hBranch : BuilderShapeCoordinates.kind (BuilderShapeCoordinates.ofSource problem index hRegion) = branch) :
    finalValues problem index remaining afterCount after branch =
      scratchValues problem index remaining afterCount after branch ++ [countValue problem branch] ++
        BuilderLocalConstraintPayload.values
          (problem.shapeConstraintSlotDirect (BuilderConstraintRegionSource.localCoordinate problem index .shape)) :=
  canonical_final_values problem index remaining afterCount after hRegion branch hBranch
example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat) (branch : Kind)
    (inside : List WorkSymbol) (hAfter : after.length = afterCount)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape)
    (hBranch : BuilderShapeCoordinates.kind (BuilderShapeCoordinates.ofSource problem index hRegion) = branch) :
    workRunExact? (machine problem.verifier afterCount branch)
      (workSteps problem index remaining afterCount after branch)
      (initialConfiguration problem index remaining afterCount after branch inside) =
      some {
        state := (machine problem.verifier afterCount branch).acceptState
        tape := endTape (scratchValues problem index remaining afterCount after branch ++
          [countValue problem branch] ++ BuilderLocalConstraintPayload.values
            (problem.shapeConstraintSlotDirect (BuilderConstraintRegionSource.localCoordinate problem index .shape)))
          inside (exterior problem index branch) } :=
  canonical_workRunExact problem index remaining afterCount after branch inside hAfter hRegion hBranch

-- Exact preservation and bridge cost are observable contracts, not narrative claims.
example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat) (branch : Kind) (inside : List WorkSymbol) :
    (finalConfiguration problem index remaining afterCount after branch inside).tape.right =
      (registerWord (finalValues problem index remaining afterCount after branch)).reverse ++ inside := rfl
example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat) (branch : Kind) :
    workSteps problem index remaining afterCount after branch =
      fieldsSteps problem index remaining afterCount after branch + 1 +
        BuilderRegisterExactlyOnePayload.workSteps (countValue problem branch) (upperValue problem index branch) := rfl

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat) (branch : Kind) (retainedBound : NatPolynomial)
    (hAfter : after.length = afterCount)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape)
    (hRetained : (registerWord after).length ≤ retainedBound.eval problem.input.length) :
    (registerWord (scratchValues problem index remaining afterCount after branch ++
        [countValue problem branch, upperValue problem index branch])).length ≤
      (fieldsSpanPolynomial problem.verifier afterCount branch retainedBound).eval problem.input.length ∧
    6 * fieldsSteps problem index remaining afterCount after branch ≤
      (fieldsRawTimePolynomial problem.verifier afterCount branch retainedBound).eval problem.input.length :=
  fields_source_polynomial_bounds problem index remaining afterCount after branch retainedBound hAfter hBody hBalance hRegion hRetained
example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining afterCount : Nat) (after : List Nat) (branch : Kind) (retainedBound : NatPolynomial)
    (hAfter : after.length = afterCount)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape)
    (hRetained : (registerWord after).length ≤ retainedBound.eval problem.input.length) :
    (registerWord (finalValues problem index remaining afterCount after branch)).length +
        (finalConfiguration problem index remaining afterCount after branch []).tape.left.length ≤
      (spanPolynomial problem.verifier afterCount branch retainedBound).eval problem.input.length ∧
    6 * workSteps problem index remaining afterCount after branch ≤
      (rawTimePolynomial problem.verifier afterCount branch retainedBound).eval problem.input.length :=
  source_polynomial_bounds problem index remaining afterCount after branch retainedBound hAfter hBody hBalance hRegion hRetained

example {language : Language} (verifier : PolynomialTimeVerifier language) (afterCount : Nat) (branch : Kind) :
    (machine verifier afterCount branch).rules.Pairwise WorkMachineChain.QueryDistinct :=
  rules_pairwise_query_distinct verifier afterCount branch
example {language : Language} (verifier : PolynomialTimeVerifier language) (afterCount : Nat) (branch : Kind) :
    WorkMachineChain.NoRuleAtAccept (machine verifier afterCount branch) := noRuleAtAccept verifier afterCount branch
example {language : Language} (verifier : PolynomialTimeVerifier language) (afterCount : Nat) (branch : Kind) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier afterCount branch) (machine verifier afterCount branch).rejectState :=
  noRuleAtReject verifier afterCount branch
example {language : Language} (verifier : PolynomialTimeVerifier language) (afterCount : Nat) (branch : Kind) :
    (machine verifier afterCount branch).acceptState ≠ (machine verifier afterCount branch).rejectState :=
  acceptState_ne_rejectState verifier afterCount branch

-- A head coordinate cannot supply the symbol-branch premise.
example {language : Language} (problem : VerifierTableauProblem language)
    (coordinates : BuilderShapeCoordinates.Coordinates problem) (hHead : coordinates.row.val = Width problem) :
    BuilderShapeCoordinates.kind coordinates ≠ .symbol := by
  have hNot : ¬ coordinates.row.val < Width problem := by omega
  have hKind : BuilderShapeCoordinates.kind coordinates = .head := by
    simp only [BuilderShapeCoordinates.kind, if_neg hNot, if_pos hHead]
  intro h
  have hImpossible : Kind.head = Kind.symbol := hKind.symm.trans h
  cases hImpossible

end PNP.Concrete.CookLevin.BuilderShapeBranchPayload.Regression
