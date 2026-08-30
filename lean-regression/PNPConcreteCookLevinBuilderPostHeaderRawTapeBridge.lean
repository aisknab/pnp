import PNP

namespace PNP.Concrete.CookLevinBuilderPostHeaderRawTapeBridgeRegression

open CookLevin
open CookLevin.BuilderArbitrarySlotHeaderRouter
open CookLevin.BuilderPostHeaderRawTapeBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

example (processed width : Nat) (workspace : List WorkSymbol)
    (hWidth : 0 < width) :
    workRunExact? machine (equalWorkSteps width)
        (equalInputConfiguration processed width workspace) =
      some (equalFinalConfiguration processed width workspace) :=
  equal_workRunExact processed width workspace hWidth

example (processed remainingCoordinate width : Nat)
    (workspace : List WorkSymbol) (hWidth : 0 < width) :
    workRunExact? machine
        (greaterWorkSteps processed remainingCoordinate width)
        (greaterInputConfiguration processed remainingCoordinate width
          workspace) =
      some (greaterFinalConfiguration processed remainingCoordinate width
        workspace) :=
  greater_workRunExact processed remainingCoordinate width workspace hWidth

example (processed : Nat) (workspace : List WorkSymbol) :
    (workRun machine 2
      (equalInputConfiguration processed 0 workspace)).state = 38 :=
  equal_zero_width_dead_state processed workspace

example (processed remainingCoordinate : Nat)
    (workspace : List WorkSymbol) :
    (workRun machine 2
      (greaterInputConfiguration processed remainingCoordinate 0
        workspace)).state = 38 :=
  greater_zero_width_dead_state processed remainingCoordinate workspace

example (dividend width : Nat) (exterior : List WorkSymbol)
    (hWidth : 0 < width) :
    workRunExact? dividerMachine
        (BuilderPostHeaderRawDivider.workSteps dividend width)
        (shieldedDividerStartConfiguration dividend width exterior) =
      some (shieldedDividerFinalConfiguration dividend width exterior) :=
  shielded_divider_workRunExact dividend width exterior hWidth

example (dividend width : Nat) (exterior : List WorkSymbol) :
    (shieldedDividerFinalConfiguration dividend width exterior).tape.left =
      (BuilderPostHeaderRawDivider.finalConfiguration dividend width).tape.left ++
        exterior :=
  shieldedDividerFinal_exterior_preserved dividend width exterior

example (dividend width : Nat) (exterior : List WorkSymbol) :
    shieldedTerminalQuotientRemainder
        (shieldedDividerFinalConfiguration dividend width exterior) exterior =
      (dividend / width, dividend % width) :=
  shielded_final_quotient_remainder dividend width exterior

example (processed width : Nat) (workspace : List WorkSymbol)
    (hWidth : 0 < width) :
    run (compileWorkMachine machine) (6 * equalWorkSteps width)
        (encodeWorkConfiguration
          (equalInputConfiguration processed width workspace)) =
      encodeWorkConfiguration
        (equalFinalConfiguration processed width workspace) :=
  run_compile_equal_exact processed width workspace hWidth

example (dividend width : Nat) (exterior : List WorkSymbol)
    (hWidth : 0 < width) :
    run (compileWorkMachine dividerMachine)
        (6 * BuilderPostHeaderRawDivider.workSteps dividend width)
        (encodeWorkConfiguration
          (shieldedDividerStartConfiguration dividend width exterior)) =
      encodeWorkConfiguration
        (shieldedDividerFinalConfiguration dividend width exterior) :=
  run_compile_shielded_divider_exact dividend width exterior hWidth

example (processed width : Nat) (workspace : List WorkSymbol)
    (hWidth : 0 < width) :
    machine.isHalted
        (workRun machine (equalWorkSteps width - 1)
          (equalInputConfiguration processed width workspace)) = false :=
  equal_one_step_short_not_halted processed width workspace hWidth

example (processed remainingCoordinate width : Nat) :
    greaterWorkSteps processed remainingCoordinate width ≤
      40 * (processed + remainingCoordinate + width + 1) *
        (processed + remainingCoordinate + width + 1) :=
  greaterWorkSteps_le_quadratic processed remainingCoordinate width

example {language : Language} (problem : VerifierTableauProblem language)
    (coordinate :
      Fin (BuilderFullScheduleCursorController.terminalSlot problem))
    (workspace : List WorkSymbol) :
    InRangeRouteBridgeHolds problem coordinate workspace :=
  inRangeRouteBridgeHolds problem coordinate workspace

example {language : Language} (problem : VerifierTableauProblem language)
    (coordinate : Nat)
    (hCoordinate :
      coordinate < BuilderFullScheduleCursorController.terminalSlot problem) :
    stagedCompiledSteps problem coordinate ≤
      (rawTimeBound problem.verifier).eval problem.input.length :=
  stagedCompiledSteps_le_rawTimeBound problem coordinate hCoordinate

example {language : Language} (problem : VerifierTableauProblem language) :=
  cook_levin_builder_post_header_raw_tape_bridge_checked_complete problem

end PNP.Concrete.CookLevinBuilderPostHeaderRawTapeBridgeRegression
