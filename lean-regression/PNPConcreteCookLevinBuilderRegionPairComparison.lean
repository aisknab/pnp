import PNP.Concrete.CookLevinBuilderRegionPairComparison

namespace PNP.Concrete.CookLevinBuilderRegionPairComparisonRegression

open CookLevin BuilderUnaryPolynomial PipelineTape
open BuilderRegionPairComparison
open BuilderDividerOperands (endTape)
open BuilderArbitrarySlotHeaderRouter.RawRouter (coordinateMark boundaryMark)

example : Layout.rules.length = 5 := Layout.rules_length

example : machine.rules.length = 68 := rfl

example : Layout.rules.Pairwise WorkMachineChain.QueryDistinct :=
  Layout.rules_pairwise_query_distinct

example : WorkMachineChain.NoRuleAtAccept Layout.machine := Layout.noRuleAtAccept

example : Layout.machine.acceptState ≠ Layout.machine.rejectState := Layout.acceptState_ne_rejectState

example (coordinate boundary : Nat) (older : List Nat) (workspace : List WorkSymbol) :
    (Layout.initialConfiguration coordinate boundary older workspace).tape =
      {
        left := []
        head := scratchEndSymbol
        right := List.replicate boundary unitSymbol ++ separatorSymbol ::
          (List.replicate coordinate unitSymbol ++ separatorSymbol :: exterior older workspace)
      } := Layout.initial_tape_layout coordinate boundary older workspace

example (coordinate boundary : Nat) (older : List Nat) (workspace : List WorkSymbol) :
    workRunExact? Layout.machine (boundary + coordinate + 3)
      (workStartConfiguration Layout.machine (endTape (older ++ [coordinate, boundary]) workspace [])) =
      some (Layout.finalConfiguration coordinate boundary older workspace) :=
  Layout.workRunExact coordinate boundary older workspace

example :
    workRunExact? Layout.machine 3 (Layout.initialConfiguration 0 0 [2, 0] [.blank, .zeroZero]) =
      some {
        state := Layout.machine.acceptState
        tape := {
          left := [scratchEndSymbol]
          head := separatorSymbol
          right := leftMarker :: exterior [2, 0] [.blank, .zeroZero]
        }
      } := by decide

example :
    workRunExact? Layout.machine 8 (Layout.initialConfiguration 2 3 [0, 1] [.blankOne, .zeroOne]) =
      some {
        state := Layout.machine.acceptState
        tape := {
          left := [unitSymbol, separatorSymbol, unitSymbol, unitSymbol, unitSymbol, scratchEndSymbol]
          head := unitSymbol
          right := leftMarker :: exterior [0, 1] [.blankOne, .zeroOne]
        }
      } := by decide

example :
    workRunExact? Layout.machine 2 (Layout.initialConfiguration 0 0 [] []) ≠
      some (Layout.finalConfiguration 0 0 [] []) := by decide

example :
    workRunExact? Layout.machine 1
      { state := Layout.machine.startState, tape := { left := [], head := .blank, right := [] } } =
      none := by decide

example :
    workRunExact? Layout.machine 4
      { state := Layout.machine.startState,
        tape := { left := [], head := scratchEndSymbol, right := [separatorSymbol, unitSymbol] } } =
      none := by decide

example (coordinate boundary : Nat) (older : List Nat) (workspace : List WorkSymbol) :
    (Layout.finalConfiguration coordinate boundary older workspace).tape =
      BuilderPhysicalClassifierFinishMirroredDispatch.mirrorTape
        (BuilderPostDividerRawRouteClassifier.shieldedComparatorStartConfiguration
          coordinate boundary (exterior older workspace)).tape :=
  layout_tape_eq_mirrored_comparator_input coordinate boundary older workspace

example (coordinate boundary : Nat) (older : List Nat) (workspace : List WorkSymbol) :
    workRunExact? machine (workSteps coordinate boundary)
      (workStartConfiguration machine (endTape (older ++ [coordinate, boundary]) workspace [])) =
      some (finalConfiguration coordinate boundary older workspace) :=
  workRunExact coordinate boundary older workspace

example (coordinate boundary : Nat) (older : List Nat) (workspace : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps coordinate boundary)
      (encodeWorkConfiguration (initialConfiguration coordinate boundary older workspace)) =
      encodeWorkConfiguration (finalConfiguration coordinate boundary older workspace) :=
  run_compile_exact coordinate boundary older workspace

example (coordinate boundary : Nat) (older : List Nat) (workspace : List WorkSymbol) :
    (finalConfiguration coordinate boundary older workspace).state = machine.acceptState ↔
      coordinate < boundary := final_accept_iff coordinate boundary older workspace

example (coordinate boundary : Nat) (older : List Nat) (workspace : List WorkSymbol) :
    (finalConfiguration coordinate boundary older workspace).state = machine.rejectState ↔
      boundary ≤ coordinate := final_reject_iff coordinate boundary older workspace

example :
    workRunExact? machine (workSteps 0 0) (initialConfiguration 0 0 [1] [.oneBlank]) =
      some {
        state := machine.rejectState
        tape := {
          left := []
          head := scratchEndSymbol
          right := separatorSymbol :: leftMarker :: exterior [1] [.oneBlank]
        }
      } := by decide

example :
    workRunExact? machine (workSteps 0 2) (initialConfiguration 0 2 [0] [.blankOne]) =
      some {
        state := machine.acceptState
        tape := {
          left := [unitSymbol, scratchEndSymbol]
          head := unitSymbol
          right := separatorSymbol :: leftMarker :: exterior [0] [.blankOne]
        }
      } := by decide

example :
    workRunExact? machine (workSteps 2 3) (initialConfiguration 2 3 [0, 1] [.blank, .zeroZero, .oneZero]) =
      some {
        state := machine.acceptState
        tape := {
          left := [scratchEndSymbol]
          head := unitSymbol
          right := [boundaryMark, boundaryMark, separatorSymbol, coordinateMark, coordinateMark, leftMarker] ++
            exterior [0, 1] [.blank, .zeroZero, .oneZero]
        }
      } := by decide

example :
    workRunExact? machine (workSteps 2 2) (initialConfiguration 2 2 [3] [.oneBlank]) =
      some {
        state := machine.rejectState
        tape := {
          left := []
          head := scratchEndSymbol
          right := [boundaryMark, boundaryMark, separatorSymbol, coordinateMark, coordinateMark, leftMarker] ++
            exterior [3] [.oneBlank]
        }
      } := by decide

/-- The greater branch has residual minus one unmarked; the marked extra unit must be restored. -/
example :
    workRunExact? machine (workSteps 4 2) (initialConfiguration 4 2 [0] [.zeroBlank]) =
      some {
        state := machine.rejectState
        tape := {
          left := []
          head := scratchEndSymbol
          right := [boundaryMark, boundaryMark, separatorSymbol, unitSymbol,
            coordinateMark, coordinateMark, coordinateMark, leftMarker] ++ exterior [0] [.zeroBlank]
        }
      } := by decide

example :
    workRunExact? machine (workSteps 1 0) (initialConfiguration 1 0 [] [.blankOne, .zeroZero]) =
      some {
        state := machine.rejectState
        tape := {
          left := []
          head := scratchEndSymbol
          right := [separatorSymbol, coordinateMark, leftMarker] ++ exterior [] [.blankOne, .zeroZero]
        }
      } := by decide

example :
    (finalConfiguration 2 2 [] []).state ≠ machine.acceptState := by decide

example :
    workRunExact? machine (workSteps 2 3 - 1) (initialConfiguration 2 3 [] []) ≠
      some (finalConfiguration 2 3 [] []) := by decide

example (coordinate boundary : Nat) (older : List Nat) (workspace : List WorkSymbol) :
    (finalConfiguration coordinate boundary older workspace).tape.right =
      (BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration coordinate boundary).tape.left ++
        ((registerWord older).reverse ++ workspace) :=
  final_exterior_preserved coordinate boundary older workspace

example : machine.rules.Pairwise WorkMachineChain.QueryDistinct := rules_pairwise_query_distinct

example : WorkMachineChain.NoRuleAtAccept machine := noRuleAtAccept

example : machine.acceptState ≠ machine.rejectState := acceptState_ne_rejectState

example (coordinate boundary bound : Nat) (hCoordinate : coordinate ≤ bound) (hBoundary : boundary ≤ bound) :
    workSteps coordinate boundary ≤ 2 * bound + 4 + 6 * (bound + 1) * (bound + 1) :=
  workSteps_le coordinate boundary bound hCoordinate hBoundary

example (coordinate boundary bound : Nat) (hCoordinate : coordinate ≤ bound) (hBoundary : boundary ≤ bound) :
    6 * workSteps coordinate boundary ≤ rawTimeBound bound :=
  rawTimeBound_le coordinate boundary bound hCoordinate hBoundary

end PNP.Concrete.CookLevinBuilderRegionPairComparisonRegression
