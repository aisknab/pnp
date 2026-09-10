/-
Copyright (c) 2026 PNP Labs.
The fixed tag graph must dispatch at runtime, preserve its source, reject
invalid tags, and charge all original source work and control handoffs.
-/
import PNP.Concrete.CookLevinBuilderRegionRadixDispatch

namespace PNP.Concrete.CookLevin.BuilderRegionRadixDispatch.Regression

open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape inside count)
open BuilderClauseDividerOperands (quotient)
open BuilderConstraintRegionRegisters (Region)
open BuilderConstraintRegionDispatch (regionTag)

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (graph verifier).WellFormed := graph_wellFormed verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (graph verifier).nodes.length = 10 := graph_nodes_length verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) :
    (checkNode verifier region).reference = checkRef region := checkNode_reference verifier region

example {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) :
    (checkNode verifier region).program = BuilderUnaryTagMatch.machine (regionTag region) := rfl

example {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) :
    (entryNode verifier region).program = BuilderRegionRadixSource.machine verifier region := rfl

example {language : Language} (verifier : PolynomialTimeVerifier language) (region : Region) :
    (checkNode verifier region).onAccept = .node (entryNode verifier region).reference := rfl

example : rejectTarget .shape = .node (checkRef .initial) := rfl
example : rejectTarget .initial = .node (checkRef .control) := rfl
example : rejectTarget .control = .node (checkRef .preservation) := rfl
example : rejectTarget .preservation = .node (checkRef .accepting) := rfl
example : rejectTarget .accepting = .reject := rfl

example : routeSteps .shape = 4 := rfl
example : routeSteps .initial = 10 := rfl
example : routeSteps .control = 18 := rfl
example : routeSteps .preservation = 28 := rfl
example : routeSteps .accepting = 40 := rfl

example (region : Region) : routeSteps region ≤ 40 := routeSteps_le region

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) :
    BuilderRegionRadixSource.selectedValues problem index remaining region =
      beforeTag problem index remaining region ++ [regionTag region] :=
  selectedValues_tag problem index remaining region

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) (workspace : List WorkSymbol) :
    workRunExact? (dispatchMachine problem.verifier) (dispatchSteps problem index remaining region)
      (workStartConfiguration (dispatchMachine problem.verifier)
        (endTape (BuilderRegionRadixSource.selectedValues problem index remaining region) workspace [])) =
      some { state := (dispatchMachine problem.verifier).acceptState,
             tape := endTape (BuilderRegionRadixSource.finalValues problem index remaining region) workspace [] } :=
  dispatch_workRunExact problem index remaining region workspace

example {language : Language} (verifier : PolynomialTimeVerifier language)
    (actual : Nat) (older : List Nat) (workspace tail : List WorkSymbol) (hInvalid : 5 ≤ actual) :
    workRunExact? (dispatchMachine verifier) 40
      (workStartConfiguration (dispatchMachine verifier) (endTape (older ++ [actual]) workspace tail)) =
      some { state := (dispatchMachine verifier).rejectState, tape := endTape (older ++ [actual]) workspace tail } :=
  reject_invalid_tag verifier actual older workspace tail hInvalid

example {language : Language} (verifier : PolynomialTimeVerifier language)
    (older : List Nat) (workspace tail : List WorkSymbol) :
    workRunExact? (dispatchMachine verifier) 40
      (workStartConfiguration (dispatchMachine verifier) (endTape (older ++ [5]) workspace tail)) =
      some { state := (dispatchMachine verifier).rejectState, tape := endTape (older ++ [5]) workspace tail } :=
  reject_invalid_tag verifier 5 older workspace tail (by decide)

example {language : Language} (verifier : PolynomialTimeVerifier language)
    (older : List Nat) (workspace tail : List WorkSymbol) :
    workRunExact? (dispatchMachine verifier) 40
      (workStartConfiguration (dispatchMachine verifier) (endTape (older ++ [1000000]) workspace tail)) =
      some { state := (dispatchMachine verifier).rejectState, tape := endTape (older ++ [1000000]) workspace tail } :=
  reject_invalid_tag verifier 1000000 older workspace tail (by decide)

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hBody : quotient problem index < count problem) :
    BuilderConstraintRegionSource.selectedRegion problem index = some (selectedRegion problem index) :=
  selectedRegion_correct problem index hBody

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    machine verifier =
      WorkMachineChain.machine (BuilderConstraintRegionSource.machine verifier) (dispatchMachine verifier) := rfl

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (hBody : quotient problem index < count problem) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
      (initialConfiguration problem index remaining output) =
      some (finalConfiguration problem index remaining output) :=
  workRunExact problem index remaining output hBody

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (hBody : quotient problem index < count problem) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining)
      (encodeWorkConfiguration (initialConfiguration problem index remaining output)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining output) :=
  run_compile_exact problem index remaining output hBody

example {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    workSteps problem index remaining =
      BuilderConstraintRegionSource.workSteps problem index remaining + 1 +
        dispatchSteps problem index remaining (selectedRegion problem index) := rfl

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (region : Region) :
    dispatchSteps problem index remaining region =
      routeSteps region + BuilderRegionRadixSource.workSteps problem index remaining region + 1 := rfl

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).tape =
      endTape (finalValues problem index remaining) (inside problem.input output) [] :=
  final_tape problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).state = (machine problem.verifier).acceptState :=
  final_accept problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (hBody : quotient problem index < count problem) :
    ∃ suffix, finalValues problem index remaining = BuilderConstraintRegionSource.finalValues problem index remaining ++ suffix :=
  finalValues_preserve_source problem index remaining hBody

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) :
    BuilderRegionRadixDecoder.reconstruct (BuilderRegionRadixSource.radices problem (selectedRegion problem index))
      (BuilderRegionRadixDecoder.packetDigits
        (BuilderRegionRadixDecoder.extraValues (BuilderRegionRadixSource.radices problem (selectedRegion problem index))
          (BuilderConstraintRegionSource.localCoordinate problem index (selectedRegion problem index))))
      ((finalValues problem index remaining).reverse.headD 0) =
        BuilderConstraintRegionSource.localCoordinate problem index (selectedRegion problem index) :=
  written_coordinate_reconstruct problem index remaining

example {language : Language} (verifier : PolynomialTimeVerifier language)
    (region : Region) (inputLength : Nat) :
    (BuilderRegionRadixSource.rawTimeBound verifier region).eval inputLength ≤ (entryTimeBound verifier).eval inputLength :=
  entryTimeBound_le verifier region inputLength

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    rawTimeBound verifier =
      .add (BuilderConstraintRegionSource.rawTimeBound verifier) (.add (.constant 252) (entryTimeBound verifier)) := rfl

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (hBody : quotient problem index < count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    6 * workSteps problem index remaining ≤ (rawTimeBound problem.verifier).eval problem.input.length :=
  rawTimeBound_le problem index remaining hBody hBalance

example {language : Language} (verifier : PolynomialTimeVerifier language)
    (region : Region) (inputLength : Nat) :
    (entrySpanPolynomial verifier region).eval inputLength ≤ (finalRegisterSpanBound verifier).eval inputLength :=
  entrySpanPolynomial_le verifier region inputLength

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (hBody : quotient problem index < count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    (registerWord (finalValues problem index remaining)).length ≤
      (finalRegisterSpanBound problem.verifier).eval problem.input.length :=
  final_register_span_le problem index remaining hBody hBalance

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (dispatchMachine verifier).rules.Pairwise WorkMachineChain.QueryDistinct := dispatch_rules_pairwise verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (dispatchMachine verifier) := dispatch_noRuleAtAccept verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineProgramGraph.NoRuleAt (dispatchMachine verifier) (dispatchMachine verifier).rejectState :=
  dispatch_noRuleAtReject verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (dispatchMachine verifier).acceptState ≠ (dispatchMachine verifier).rejectState := dispatch_accept_ne_reject verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct := rules_pairwise_query_distinct verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (machine verifier) := noRuleAtAccept verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier) (machine verifier).rejectState := noRuleAtReject verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState := acceptState_ne_rejectState verifier

end PNP.Concrete.CookLevin.BuilderRegionRadixDispatch.Regression
