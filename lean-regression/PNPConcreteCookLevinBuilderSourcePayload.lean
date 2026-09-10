/-
Copyright (c) 2026 PNP Labs.
Source-selected all-family execution, unchanged canonical slots, malformed tags
and source-size bounds. The main contracts supply no region or payload premise.
-/
import PNP.Concrete.CookLevinBuilderSourcePayload

namespace PNP.Concrete.CookLevin.BuilderSourcePayload.Regression
open BuilderSourcePayload
open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape inside)
open BuilderConstraintRegionRegisters (Region)
open BuilderConstraintRegionDispatch (regionTag)

example : ([Region.shape, .initial, .control, .preservation, .accepting].map regionTag) = [0,1,2,3,4] := rfl
example : ([Region.shape, .initial, .control, .preservation, .accepting].map testSteps) = [4,10,18,28,40] := by decide
example (region : Region) : testSteps region ≤ 40 := testSteps_le region
example : invalidSteps 5 = 40 := by decide
example : invalidSteps 1000 = 40 := by decide

section Graph
variable {language : Language} (verifier : PolynomialTimeVerifier language)
example : (graph verifier).nodes.map WorkMachineProgramGraph.Node.name = [0,1,2,3,4,5,6,7,8,9,10] := rfl
example : (graph verifier).nodes.length = 11 := graph_nodes_length verifier
example : (sourceNode verifier).onAccept = .node (testNode verifier .shape).reference := rfl
example : (sourceNode verifier).onReject = .reject := rfl
example : (testNode verifier .shape).onReject = .node (testNode verifier .initial).reference := rfl
example : (testNode verifier .initial).onReject = .node (testNode verifier .control).reference := rfl
example : (testNode verifier .control).onReject = .node (testNode verifier .preservation).reference := rfl
example : (testNode verifier .preservation).onReject = .node (testNode verifier .accepting).reference := rfl
example : (testNode verifier .accepting).onReject = .reject := rfl
example (region : Region) : (testNode verifier region).onAccept = .node (familyNode verifier region).reference := rfl
example (region : Region) : (familyNode verifier region).program = BuilderFamilyPayload.machine verifier region := rfl
example (region : Region) : (familyNode verifier region).onAccept = .accept := rfl
example (region : Region) : (familyNode verifier region).onReject = .reject := rfl
example : (graph verifier).WellFormed := graph_wellFormed verifier
example : (machine verifier).rules.Pairwise WorkMachineProgramGraph.QueryDistinct := rules_pairwise_query_distinct verifier
example : WorkMachineProgramGraph.NoRuleAt (machine verifier) (machine verifier).acceptState := noRuleAtAccept verifier
example : WorkMachineProgramGraph.NoRuleAt (machine verifier) (machine verifier).rejectState := noRuleAtReject verifier
example : (machine verifier).acceptState ≠ (machine verifier).rejectState := acceptState_ne_rejectState verifier
example (code : Nat) (older : List Nat) (workspace outside : List WorkSymbol) (hInvalid : 4 < code) :
    workRunExact? (machine verifier) (invalidSteps code)
      (WorkMachineProgramGraph.endpointConfiguration (.node (testNode verifier .shape).reference)
        (endTape (older ++ [code]) workspace outside)) =
      some {state := (machine verifier).rejectState, tape := endTape (older ++ [code]) workspace outside} :=
  invalid_tag_workRunExact verifier code older workspace outside hInvalid
end Graph

section Source
variable {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
variable (output : List CNFToken)
example (region : Region) :
    BuilderRegionRadixSource.selectedValues problem index remaining region = tagPrefix problem index remaining region ++ [regionTag region] :=
  selected_suffix problem index remaining region
example (region : Region) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some region) :
    selected problem index = region := by simp only [selected, hRegion, Option.getD_some]
example : (initialConfiguration problem index remaining output).tape = BuilderCursorSource.cursorTape problem index remaining output := rfl

variable (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
example : BuilderConstraintRegionSource.selectedRegion problem index = some (selected problem index) := selected_valid problem index hBody
example : workRunExact? (machine problem.verifier) (workSteps problem index remaining hBody)
    (initialConfiguration problem index remaining output) = some (finalConfiguration problem index remaining output hBody) :=
  workRunExact problem index remaining output hBody
example : run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining hBody)
    (encodeWorkConfiguration (initialConfiguration problem index remaining output)) =
    encodeWorkConfiguration (finalConfiguration problem index remaining output hBody) := run_compile_exact problem index remaining output hBody
example : finalValues problem index remaining hBody = history problem index remaining hBody ++ payloadValues problem index remaining hBody :=
  final_suffix problem index remaining hBody
example : payloadValues problem index remaining hBody = BuilderLocalConstraintPayload.values
    (problem.formulaConstraintSlotDirect (BuilderClauseDividerExecution.constraintIndex problem index)) :=
  payload_canonical problem index remaining hBody
example : BuilderLocalConstraintPayload.decode problem.FormulaWidth (payloadValues problem index remaining hBody) =
    some (problem.formulaConstraintSlotDirect (BuilderClauseDividerExecution.constraintIndex problem index)) :=
  payload_decode problem index remaining hBody
example : workRunExact? (machine problem.verifier) (workSteps problem index remaining hBody)
    (initialConfiguration problem index remaining output) =
    some
      {state := (machine problem.verifier).acceptState,
       tape := endTape (history problem index remaining hBody ++ BuilderLocalConstraintPayload.values
         (problem.formulaConstraintSlotDirect (BuilderClauseDividerExecution.constraintIndex problem index)))
         (inside problem.input output) (exterior problem index remaining hBody)} :=
  canonical_workRunExact problem index remaining output hBody
example : (finalConfiguration problem index remaining output hBody).tape =
    endTape (finalValues problem index remaining hBody) (inside problem.input output) (exterior problem index remaining hBody) :=
  final_tape problem index remaining output hBody
example : (finalConfiguration problem index remaining output hBody).state = (machine problem.verifier).acceptState :=
  final_accept problem index remaining output hBody
example : (finalConfiguration problem index remaining output hBody).tape.left = exterior problem index remaining hBody :=
  final_exterior problem index remaining output hBody
example : (finalConfiguration problem index remaining output hBody).tape.right =
    (registerWord (finalValues problem index remaining hBody)).reverse ++ inside problem.input output := rfl
example : exterior problem index remaining hBody =
    BuilderFamilyPayload.exterior problem index remaining (selected problem index) (selected_valid problem index hBody) := rfl
example (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    (registerWord (finalValues problem index remaining hBody)).length + (exterior problem index remaining hBody).length ≤
        (spanBound problem.verifier).eval problem.input.length ∧
      6 * workSteps problem index remaining hBody ≤ (rawTimeBound problem.verifier).eval problem.input.length :=
  source_polynomial_bounds problem index remaining hBody hBalance
end Source
end PNP.Concrete.CookLevin.BuilderSourcePayload.Regression
