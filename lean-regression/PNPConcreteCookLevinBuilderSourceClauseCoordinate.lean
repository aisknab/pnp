/-
Copyright (c) 2026 PNP Labs.
Actual preserved source coordinate, verifier-fixed control, all five families,
paired packet cuts, exact tape allocation and source-encoded polynomial bounds.
-/
import PNP.Concrete.CookLevinBuilderSourceClauseCoordinate

namespace PNP.Concrete.CookLevin.BuilderSourceClauseCoordinate.Regression
open BuilderSourceClauseCoordinate
open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape inside count)
open BuilderClauseDividerOperands (quotient clauseWidth)
open BuilderClauseDividerExecution (clauseIndex constraintIndex)
open BuilderConstraintRegionRegisters (Region)

section Program
variable {language : Language} (verifier : PolynomialTimeVerifier language)
example : copier verifier = BuilderRegisterRootCopy.machine (rootOrdinal verifier) := rfl
example : machine verifier = WorkMachineChain.machine (BuilderSourcePayload.machine verifier) (copier verifier) := rfl
example : rootOrdinal verifier =
    nodeCount (BuilderFullScheduleCursorController.bodySlotCountPolynomial verifier) +
      nodeCount (BuilderDimensionRegisters.widthPolynomial verifier) + 11 := rfl
example : (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct := rules_pairwise_query_distinct verifier
example : WorkMachineChain.NoRuleAtAccept (machine verifier) := noRuleAtAccept verifier
example : WorkMachineProgramGraph.NoRuleAt (machine verifier) (machine verifier).rejectState := noRuleAtReject verifier
example : (machine verifier).acceptState ≠ (machine verifier).rejectState := acceptState_ne_rejectState verifier
end Program

section Source
variable {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) (output : List CNFToken)
example : (before problem index remaining).length = rootOrdinal problem.verifier := before_length problem index remaining
example : (before problem 0 0).length = (before problem index remaining).length := by
  rw [before_length, before_length]
example : BuilderClauseCoordinateRegisters.finalValues problem index remaining =
    before problem index remaining ++ [clauseIndex problem index, clauseWidth problem, constraintIndex problem index] :=
  coordinate_frame_layout problem index remaining
example (region : Region) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some region) :
    ∃ tail, BuilderFamilyPayload.finalValues problem index remaining region hRegion =
      BuilderClauseCoordinateRegisters.finalValues problem index remaining ++ tail :=
  family_preserves_coordinate_frame problem index remaining region hRegion
example (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape) :
    ∃ tail, BuilderShapePayload.finalValues problem index remaining =
      BuilderClauseCoordinateRegisters.finalValues problem index remaining ++ tail :=
  family_preserves_coordinate_frame problem index remaining .shape hRegion
example (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .initial) :
    ∃ tail, BuilderInitialPayload.finalValues problem index remaining =
      BuilderClauseCoordinateRegisters.finalValues problem index remaining ++ tail :=
  family_preserves_coordinate_frame problem index remaining .initial hRegion
example (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    ∃ tail, BuilderControlPayload.finalValues problem index remaining hRegion =
      BuilderClauseCoordinateRegisters.finalValues problem index remaining ++ tail :=
  family_preserves_coordinate_frame problem index remaining .control hRegion
example (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    ∃ tail, BuilderPreservationPayload.finalValues problem index remaining =
      BuilderClauseCoordinateRegisters.finalValues problem index remaining ++ tail :=
  family_preserves_coordinate_frame problem index remaining .preservation hRegion
example (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .accepting) :
    ∃ tail, BuilderBoundaryPayload.finalValues problem index remaining .acceptingState =
      BuilderClauseCoordinateRegisters.finalValues problem index remaining ++ tail :=
  family_preserves_coordinate_frame problem index remaining .accepting hRegion
example : (initialConfiguration problem index remaining output).tape =
    BuilderCursorSource.cursorTape problem index remaining output := rfl

variable (hBody : quotient problem index < count problem)
example : ∃ tail, BuilderSourcePayload.finalValues problem index remaining hBody =
    BuilderClauseCoordinateRegisters.finalValues problem index remaining ++ tail :=
  source_preserves_coordinate_frame problem index remaining hBody
example : BuilderSourcePayload.finalValues problem index remaining hBody =
    before problem index remaining ++ [clauseIndex problem index] ++ after problem index remaining hBody :=
  source_coordinate_layout problem index remaining hBody
example : after problem index remaining hBody =
    (BuilderSourcePayload.finalValues problem index remaining hBody).drop (rootOrdinal problem.verifier + 1) := rfl
example : workRunExact? (copier problem.verifier) (copySteps problem index remaining hBody)
    (workStartConfiguration (copier problem.verifier)
      (BuilderSourcePayload.finalConfiguration problem index remaining output hBody).tape) =
    some {state := (copier problem.verifier).acceptState,
          tape := endTape (finalValues problem index remaining hBody) (inside problem.input output)
            (exterior problem index remaining hBody)} :=
  copy_workRunExact problem index remaining output hBody
example : workRunExact? (machine problem.verifier) (workSteps problem index remaining hBody)
    (initialConfiguration problem index remaining output) = some (finalConfiguration problem index remaining output hBody) :=
  workRunExact problem index remaining output hBody
example : run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining hBody)
    (encodeWorkConfiguration (initialConfiguration problem index remaining output)) =
    encodeWorkConfiguration (finalConfiguration problem index remaining output hBody) :=
  run_compile_exact problem index remaining output hBody
example : finalValues problem index remaining hBody =
    BuilderSourcePayload.finalValues problem index remaining hBody ++ [clauseIndex problem index] := rfl
example : (finalConfiguration problem index remaining output hBody).tape =
    endTape (BuilderSourcePayload.finalValues problem index remaining hBody ++ [clauseIndex problem index])
      (inside problem.input output)
      ((BuilderSourcePayload.exterior problem index remaining hBody).drop (clauseIndex problem index + 1)) :=
  final_tape problem index remaining output hBody
example : (finalConfiguration problem index remaining output hBody).tape =
    endTape (BuilderSourcePayload.history problem index remaining hBody ++
      BuilderLocalConstraintPayload.values (problem.formulaConstraintSlotDirect (constraintIndex problem index)) ++
      [clauseIndex problem index]) (inside problem.input output) (exterior problem index remaining hBody) :=
  final_tape_canonical problem index remaining output hBody
example : (finalConfiguration problem index remaining output hBody).state = (machine problem.verifier).acceptState :=
  final_accept problem index remaining output hBody
example : (finalConfiguration problem index remaining output hBody).tape.left = exterior problem index remaining hBody := rfl
example : (finalConfiguration problem index remaining output hBody).tape.right =
    (registerWord (finalValues problem index remaining hBody)).reverse ++ inside problem.input output := rfl
example (hZero : clauseIndex problem index = 0) : exterior problem index remaining hBody =
    (BuilderSourcePayload.exterior problem index remaining hBody).drop 1 := by rw [exterior, hZero]
example : workSteps problem index remaining hBody =
    BuilderSourcePayload.workSteps problem index remaining hBody + 1 + copySteps problem index remaining hBody := rfl
example (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    (registerWord (finalValues problem index remaining hBody)).length + (exterior problem index remaining hBody).length ≤
        (spanBound problem.verifier).eval problem.input.length ∧
      6 * workSteps problem index remaining hBody ≤ (rawTimeBound problem.verifier).eval problem.input.length :=
  source_polynomial_bounds problem index remaining hBody hBalance
end Source
end PNP.Concrete.CookLevin.BuilderSourceClauseCoordinate.Regression
