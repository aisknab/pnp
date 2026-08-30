import PNP

namespace PNP.Concrete.CookLevinBuilderPostDividerRawRouteClassifierRegression

open CookLevin
open CookLevin.BuilderArbitrarySlotPostHeaderDecoder
open CookLevin.BuilderPostDividerRawRouteClassifier

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

example (consumed remainder width quotient count : Nat)
    (exteriorPrefix workspace : List WorkSymbol)
    (hPrefix : SafeExteriorPrefix exteriorPrefix) :
    workRunExact? machine
        (workSteps consumed remainder width quotient count exteriorPrefix)
        (inputConfiguration consumed remainder width quotient exteriorPrefix
          count workspace) =
      some (comparatorInputConfiguration quotient count
        (preservedExterior consumed remainder width exteriorPrefix count
          workspace)) :=
  workRunExact consumed remainder width quotient count exteriorPrefix workspace
    hPrefix

example (processed width count : Nat) (workspace : List WorkSymbol) :
    (inputConfiguration 0 0 width 0 (equalExteriorPrefix processed width)
      count workspace).tape =
      (BuilderPostHeaderRawTapeBridge.shieldedDividerFinalConfiguration
        0 width
        (BuilderPostHeaderRawTapeBridge.equalExterior processed width
          (sidecar count workspace))).tape :=
  equal_input_tape_is_exact_m213_final processed width count workspace

example (processed remainingCoordinate width count : Nat)
    (workspace : List WorkSymbol) :
    (inputConfiguration
      (((remainingCoordinate + 1) / width) * width)
      ((remainingCoordinate + 1) % width) width
      ((remainingCoordinate + 1) / width)
      (greaterExteriorPrefix processed remainingCoordinate width)
      count workspace).tape =
      (BuilderPostHeaderRawTapeBridge.shieldedDividerFinalConfiguration
        (remainingCoordinate + 1) width
        (BuilderPostHeaderRawTapeBridge.greaterExterior processed
          remainingCoordinate width (sidecar count workspace))).tape :=
  greater_input_tape_is_exact_m213_final processed remainingCoordinate width
    count workspace

example (quotient count : Nat) (exterior : List WorkSymbol) :
    workRunExact? comparatorMachine
        (BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps quotient count)
        (shieldedComparatorStartConfiguration quotient count exterior) =
      some (shieldedComparatorFinalConfiguration quotient count exterior) :=
  shielded_comparator_workRunExact quotient count exterior

example {language : Language} (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol)
    (result : BuilderArbitrarySlotHeaderRouter.RawRouter.ComparisonResult) :
    BranchPhysicalHolds problem workspace result :=
  branchPhysicalHolds problem workspace result

example {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hInRange : postHeaderRoute problem index ≠ .outOfRange) :
    DecodedRouteHolds problem index :=
  decodedRouteHolds_of_not_outOfRange problem index hInRange

example {language : Language} (problem : VerifierTableauProblem language)
    (coordinate :
      Fin (BuilderFullScheduleCursorController.terminalSlot problem))
    (workspace : List WorkSymbol) :
    InRangeRouteClassifierHolds problem coordinate workspace :=
  inRangeRouteClassifierHolds problem coordinate workspace

example (consumed remainder width quotient count : Nat)
    (exteriorPrefix workspace : List WorkSymbol)
    (hPrefix : SafeExteriorPrefix exteriorPrefix) :
    run (compileWorkMachine machine)
        (6 * workSteps consumed remainder width quotient count exteriorPrefix)
        (encodeWorkConfiguration
          (inputConfiguration consumed remainder width quotient exteriorPrefix
            count workspace)) =
      encodeWorkConfiguration
        (comparatorInputConfiguration quotient count
          (preservedExterior consumed remainder width exteriorPrefix count
            workspace)) :=
  run_compile_exact consumed remainder width quotient count exteriorPrefix
    workspace hPrefix

example (quotient count : Nat) (exterior : List WorkSymbol) :
    run (compileWorkMachine comparatorMachine)
        (6 * BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps quotient count)
        (encodeWorkConfiguration
          (shieldedComparatorStartConfiguration quotient count exterior)) =
      encodeWorkConfiguration
        (shieldedComparatorFinalConfiguration quotient count exterior) :=
  run_compile_shielded_comparator_exact quotient count exterior

example (consumed remainder width quotient count : Nat)
    (exteriorPrefix workspace : List WorkSymbol)
    (hPrefix : SafeExteriorPrefix exteriorPrefix) :
    machine.isHalted
        (workRun machine
          (workSteps consumed remainder width quotient count exteriorPrefix - 1)
          (inputConfiguration consumed remainder width quotient exteriorPrefix
            count workspace)) = false :=
  one_step_short_not_halted consumed remainder width quotient count
    exteriorPrefix workspace hPrefix

example (quotient count : Nat) (exterior : List WorkSymbol) :
    comparatorMachine.isHalted
        (workRun comparatorMachine
          (BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps quotient count -
            1)
          (shieldedComparatorStartConfiguration quotient count exterior)) =
      false :=
  shielded_comparator_one_step_short_not_halted quotient count exterior

example (processed coordinate boundary width count : Nat)
    (hWidth : 0 < width) :
    postDividerWorkStepsForResult width count
        (BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult processed
          coordinate boundary) ≤
      1000 * (processed + coordinate + boundary + width + count + 1) *
        (processed + coordinate + boundary + width + count + 1) :=
  postDividerWorkSteps_compareResult_le processed coordinate boundary width
    count hWidth

example {language : Language} (problem : VerifierTableauProblem language)
    (coordinate : Nat)
    (hCoordinate :
      coordinate < BuilderFullScheduleCursorController.terminalSlot problem) :
    stagedCompiledSteps problem coordinate ≤
      (rawTimeBound problem.verifier).eval problem.input.length :=
  stagedCompiledSteps_le_rawTimeBound problem coordinate hCoordinate

example {language : Language} (problem : VerifierTableauProblem language) :=
  cook_levin_builder_post_divider_raw_route_classifier_checked_complete problem

end PNP.Concrete.CookLevinBuilderPostDividerRawRouteClassifierRegression
