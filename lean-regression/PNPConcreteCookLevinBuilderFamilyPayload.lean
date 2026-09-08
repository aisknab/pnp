/-
Copyright (c) 2026 PNP Labs.
All five radix/payload entry contracts, canonical slots and explicit exterior.
These branch checks do not replace the source-selected dispatcher contract.
-/
import PNP.Concrete.CookLevinBuilderFamilyPayload

namespace PNP.Concrete.CookLevin.BuilderFamilyPayload.Regression
open BuilderFamilyPayload
open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape inside)
open BuilderConstraintRegionRegisters (Region)

section Branches
variable {language : Language} (verifier : PolynomialTimeVerifier language)
example : leafMachine verifier .shape = BuilderShapePayload.machine verifier := rfl
example : leafMachine verifier .initial = BuilderInitialPayload.machine verifier := rfl
example : leafMachine verifier .control = BuilderControlPayload.machine verifier := rfl
example : leafMachine verifier .preservation = BuilderPreservationPayload.machine verifier := rfl
example : leafMachine verifier .accepting = BuilderBoundaryPayload.machine verifier .acceptingState := rfl
example (region : Region) : machine verifier region =
    WorkMachineChain.machine (BuilderRegionRadixSource.machine verifier region) (leafMachine verifier region) := rfl
example (region : Region) : (machine verifier region).rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  rules_pairwise_query_distinct verifier region
example (region : Region) : WorkMachineProgramGraph.NoRuleAt (machine verifier region) (machine verifier region).acceptState :=
  noRuleAtAccept verifier region
example (region : Region) : WorkMachineProgramGraph.NoRuleAt (machine verifier region) (machine verifier region).rejectState :=
  noRuleAtReject verifier region
example (region : Region) : (machine verifier region).acceptState ≠ (machine verifier region).rejectState :=
  acceptState_ne_rejectState verifier region
end Branches

section Source
variable {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
variable (output : List CNFToken) (region : Region)
variable (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some region)

example : (initialConfiguration problem index remaining output region).tape =
    endTape (BuilderRegionRadixSource.selectedValues problem index remaining region) (inside problem.input output) [] := rfl
example : finalValues problem index remaining region hRegion =
    history problem index remaining region hRegion ++ payloadValues problem index remaining region hRegion :=
  final_suffix problem index remaining region hRegion
example : payloadValues problem index remaining region hRegion = BuilderLocalConstraintPayload.values
    (problem.formulaConstraintSlotDirect (BuilderClauseDividerExecution.constraintIndex problem index)) :=
  payload_canonical problem index remaining region hRegion
example : BuilderLocalConstraintPayload.decode problem.FormulaWidth (payloadValues problem index remaining region hRegion) =
    some (problem.formulaConstraintSlotDirect (BuilderClauseDividerExecution.constraintIndex problem index)) :=
  payload_decode problem index remaining region hRegion
example : workRunExact? (machine problem.verifier region) (workSteps problem index remaining region hRegion)
    (initialConfiguration problem index remaining output region) =
    some (finalConfiguration problem index remaining output region hRegion) :=
  workRunExact problem index remaining output region hRegion
example : run (compileWorkMachine (machine problem.verifier region)) (6 * workSteps problem index remaining region hRegion)
    (encodeWorkConfiguration (initialConfiguration problem index remaining output region)) =
    encodeWorkConfiguration (finalConfiguration problem index remaining output region hRegion) :=
  run_compile_exact problem index remaining output region hRegion
example : workRunExact? (machine problem.verifier region) (workSteps problem index remaining region hRegion)
    (initialConfiguration problem index remaining output region) =
    some
      {state := (machine problem.verifier region).acceptState,
       tape := endTape (history problem index remaining region hRegion ++ BuilderLocalConstraintPayload.values
         (problem.formulaConstraintSlotDirect (BuilderClauseDividerExecution.constraintIndex problem index)))
         (inside problem.input output) (exterior problem index remaining region hRegion)} :=
  canonical_workRunExact problem index remaining output region hRegion
example : (finalConfiguration problem index remaining output region hRegion).tape =
    endTape (finalValues problem index remaining region hRegion) (inside problem.input output)
      (exterior problem index remaining region hRegion) := final_tape problem index remaining output region hRegion
example : (finalConfiguration problem index remaining output region hRegion).tape.left =
    exterior problem index remaining region hRegion := final_exterior problem index remaining output region hRegion
example : (finalConfiguration problem index remaining output region hRegion).state = (machine problem.verifier region).acceptState := rfl

example (h : BuilderConstraintRegionSource.selectedRegion problem index = some .shape) :
    exterior problem index remaining .shape h =
      BuilderShapeBranchPayload.exteriorWithOutside problem index remaining 0 []
        (BuilderShapePayload.selectedKind problem index) (BuilderShapePayload.comparisonBlanks problem index) := rfl
example (h : BuilderConstraintRegionSource.selectedRegion problem index = some .initial) :
    exterior problem index remaining .initial h = BuilderInitialPayload.exterior problem index := rfl
example (h : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    exterior problem index remaining .control h = BuilderControlPayload.finalOutside problem index remaining [] h := rfl
example (h : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    exterior problem index remaining .preservation h =
      (BuilderPreservationPayload.comparisonBlanks problem index).drop
        (registerWord (BuilderPreservationPayload.retainedValues problem index ++
          BuilderPreservationPayload.payloadValues problem index remaining)).length := rfl
example (h : BuilderConstraintRegionSource.selectedRegion problem index = some .accepting) :
    exterior problem index remaining .accepting h = [] := rfl
example (h : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    (exterior problem index remaining .control h).length ≤
      (controlExteriorBound problem.verifier).eval problem.input.length := control_exterior_le problem index remaining h
example : (controlExteriorBound problem.verifier).eval problem.input.length =
    2 * (formulaTapeWidthPolynomial problem.verifier).eval problem.input.length + 8 := rfl
example (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    (registerWord (finalValues problem index remaining region hRegion)).length +
        (exterior problem index remaining region hRegion).length ≤ (spanBound problem.verifier region).eval problem.input.length ∧
      6 * workSteps problem index remaining region hRegion ≤ (rawTimeBound problem.verifier region).eval problem.input.length :=
  source_polynomial_bounds problem index remaining region hRegion hBody hBalance
end Source
end PNP.Concrete.CookLevin.BuilderFamilyPayload.Regression
