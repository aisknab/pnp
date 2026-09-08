import PNP.Concrete.CookLevinBuilderInitialCellDecoder

namespace PNP.Concrete.CookLevin.BuilderInitialCellDecoderRegression

open BuilderInitialCellDecoder
open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)

example (coordinate boundary : Nat) :
    comparisonValues coordinate boundary =
      BuilderRegisterCompareResidual.outputValues (BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult 0 coordinate boundary) :=
  comparisonValues_eq coordinate boundary

example (start length coordinate : Nat) : (beforeOutput start length coordinate).length = 10 :=
  beforeOutput_length start length coordinate
example (start length coordinate : Nat) : (middleOutput start length coordinate).length = 29 :=
  middleOutput_length start length coordinate
example (start length coordinate : Nat) : (afterOutput start length coordinate).length = 23 :=
  afterOutput_length start length coordinate

example : outputValues 3 2 1 = [3, 2, 1, 1, 0, 3, 3, 1, 1, 0] := by decide
example : (outputValues 0 0 0).drop 21 = [0, 0] := by decide
example : (outputValues 0 0 4).drop 21 = [4, 0] := by decide
example : (outputValues 3 0 2).drop 8 = [2, 0] := by decide
example : (outputValues 3 0 3).drop 21 = [3, 0] := by decide
example : (outputValues 3 0 7).drop 21 = [7, 0] := by decide
example : (outputValues 0 2 0).drop 27 = [0, 0] := by decide
example : (outputValues 0 2 1).drop 27 = [0, 1] := by decide
example : (outputValues 0 2 2).drop 27 = [1, 0] := by decide
example : (outputValues 0 2 3).drop 27 = [1, 1] := by decide
example : (outputValues 0 2 4).drop 21 = [2, 0] := by decide
example : (outputValues 3 2 0).drop 8 = [0, 0] := by decide
example : (outputValues 3 2 2).drop 8 = [2, 0] := by decide
example : (outputValues 3 2 3).drop 27 = [3, 0] := by decide
example : (outputValues 3 2 4).drop 27 = [3, 1] := by decide
example : (outputValues 3 2 5).drop 27 = [4, 0] := by decide
example : (outputValues 3 2 6).drop 27 = [4, 1] := by decide
example : (outputValues 3 2 7).drop 21 = [5, 0] := by decide
example : (outputValues 3 2 8).drop 21 = [6, 0] := by decide
example : (outputValues 3 2 11).drop 21 = [9, 0] := by decide

example : (outputValues 3 2 4).drop 27 ≠ [4, 0] := by decide
example : (outputValues 3 2 6).drop 27 ≠ [5, 0] := by decide
example : (outputValues 3 2 7).drop 21 ≠ [4, 1] := by decide
example : (outputValues 0 0 0).drop 21 ≠ [0, 1] := by decide

example (start length coordinate : Nat) :
    outputValues start length coordinate = outputPrefix start length coordinate ++
      [(BuilderInitialCellSelection.cellCoordinate start length coordinate).1,
       (BuilderInitialCellSelection.cellCoordinate start length coordinate).2] :=
  canonical_output start length coordinate

example (start length coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? machine (workSteps start length coordinate)
      (initialConfiguration start length coordinate older inside) =
      some (finalConfiguration start length coordinate older inside) :=
  workRunExact start length coordinate older inside
example (start length coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps start length coordinate)
      (encodeWorkConfiguration (initialConfiguration start length coordinate older inside)) =
      encodeWorkConfiguration (finalConfiguration start length coordinate older inside) :=
  run_compile_exact start length coordinate older inside
example (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? machine (workSteps 3 2 1)
      (initialConfiguration 3 2 1 older inside) =
      some (finalConfiguration 3 2 1 older inside) :=
  workRunExact 3 2 1 older inside
example (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? machine (workSteps 3 2 4)
      (initialConfiguration 3 2 4 older inside) =
      some (finalConfiguration 3 2 4 older inside) :=
  workRunExact 3 2 4 older inside
example (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? machine (workSteps 3 2 7)
      (initialConfiguration 3 2 7 older inside) =
      some (finalConfiguration 3 2 7 older inside) :=
  workRunExact 3 2 7 older inside
example (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? machine (workSteps 0 0 0)
      (initialConfiguration 0 0 0 older inside) =
      some (finalConfiguration 0 0 0 older inside) :=
  workRunExact 0 0 0 older inside
example (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? machine (workSteps 3 0 3)
      (initialConfiguration 3 0 3 older inside) =
      some (finalConfiguration 3 0 3 older inside) :=
  workRunExact 3 0 3 older inside

example (start length coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration start length coordinate older inside).tape.left = [] :=
  final_frontier start length coordinate older inside
example (start length coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration start length coordinate older inside).tape =
      endTape (older ++ outputPrefix start length coordinate ++
        [(BuilderInitialCellSelection.cellCoordinate start length coordinate).1,
         (BuilderInitialCellSelection.cellCoordinate start length coordinate).2]) inside [] :=
  final_tape start length coordinate older inside
example (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration 3 2 4 older inside).tape =
      endTape (older ++ outputPrefix 3 2 4 ++ [3, 1]) inside [] :=
  final_tape 3 2 4 older inside
example (width start length coordinate : Nat)
    (hInterval : start + length ≤ width) (hInside : coordinate < width + length) :
    (BuilderInitialCellSelection.cellCoordinate start length coordinate).1 < width ∧
      (BuilderInitialCellSelection.cellCoordinate start length coordinate).2 <
        BuilderInitialCellCoordinates.intervalWidth start length
          (BuilderInitialCellSelection.cellCoordinate start length coordinate).1 ∧
      coordinate = (BuilderInitialCellSelection.cellCoordinate start length coordinate).1 +
        min length ((BuilderInitialCellSelection.cellCoordinate start length coordinate).1 - start) +
        (BuilderInitialCellSelection.cellCoordinate start length coordinate).2 :=
  decoded_bounds width start length coordinate hInterval hInside

example (start length coordinate : Nat) (older : List Nat) (bound : NatPolynomial) (inputLength : Nat)
    (hSpan : (registerWord (older ++ inputValues start length coordinate)).length ≤ bound.eval inputLength) :
    (registerWord (older ++ outputValues start length coordinate)).length ≤ (spanPolynomial bound).eval inputLength ∧
      6 * workSteps start length coordinate ≤ (rawTimePolynomial bound).eval inputLength :=
  source_polynomial_bounds start length coordinate older bound inputLength hSpan

example : graph.nodes.length = 11 := graph_nodes_length
example : graph.WellFormed := graph_wellFormed
example : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct := rules_pairwise_query_distinct
example : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState := noRuleAtAccept
example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := noRuleAtReject
example : machine.acceptState ≠ machine.rejectState := acceptState_ne_rejectState

end PNP.Concrete.CookLevin.BuilderInitialCellDecoderRegression
