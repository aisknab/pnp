import PNP.Concrete.CookLevinBuilderInitialRowCarry

namespace PNP.Concrete.CookLevin.BuilderInitialRowCarryRegression

open BuilderInitialRowCarry
open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)

example (inputLength fuel length width coordinate remaining : Nat) :
    (frame inputLength fuel length width coordinate remaining).length = 6 :=
  frame_length inputLength fuel length width coordinate remaining
example (inputLength fuel length width coordinate remaining : Nat) :
    (foundStage inputLength fuel length width coordinate remaining).length = 15 :=
  foundStage_length inputLength fuel length width coordinate remaining
example (inputLength fuel length width coordinate remaining : Nat) :
    (advanceStage inputLength fuel length width coordinate remaining).length = 19 :=
  advanceStage_length inputLength fuel length width coordinate remaining

example : finishValues 0 7 11 0 2 9 = [7, 11, 0, 2, 9, 0] := by decide
example : (finishValues 1 7 11 0 2 0).drop 15 = [7, 11, 0, 2, 0, 0] := by decide
example : (finishValues 1 7 11 0 2 1).drop 15 = [7, 11, 0, 2, 1, 0] := by decide
example : (finishValues 1 7 11 0 2 2).drop 19 = [7, 11, 1, 3, 0, 0] := by decide
example : (finishValues 2 7 11 0 2 2).drop 34 = [7, 11, 1, 3, 0, 0] := by decide
example : (finishValues 2 7 11 0 2 4).drop 34 = [7, 11, 1, 3, 2, 0] := by decide
example : (finishValues 2 7 11 0 2 5).drop 38 = [7, 11, 2, 4, 0, 0] := by decide
example : (finishValues 3 7 11 0 2 0).drop 15 = [7, 11, 0, 2, 0, 2] := by decide
example : (finishValues 3 7 11 0 2 2).drop 34 = [7, 11, 1, 3, 0, 1] := by decide
example : (finishValues 3 7 11 0 2 4).drop 34 = [7, 11, 1, 3, 2, 1] := by decide
example : (finishValues 3 7 11 0 2 5).drop 53 = [7, 11, 2, 4, 0, 0] := by decide
example : (finishValues 3 7 11 0 2 8).drop 53 = [7, 11, 2, 4, 3, 0] := by decide
example : (finishValues 3 7 11 0 2 9).drop 57 = [7, 11, 3, 5, 0, 0] := by decide
example : (finishValues 3 7 11 0 2 10).drop 57 = [7, 11, 3, 5, 1, 0] := by decide
example : (finishValues 1 7 11 0 0 0).drop 19 = [7, 11, 1, 1, 0, 0] := by decide
example : (finishValues 2 7 11 0 0 0).drop 34 = [7, 11, 1, 1, 0, 0] := by decide
example : (finishValues 3 7 11 0 0 1).drop 53 = [7, 11, 2, 2, 0, 0] := by decide
example : (finishValues 2 7 11 4 3 3).drop 34 = [7, 11, 5, 4, 0, 0] := by decide

example : (finishValues 3 7 11 0 2 5).drop 53 ≠ [6, 11, 2, 4, 0, 0] := by decide
example : (finishValues 3 7 11 0 2 5).drop 53 ≠ [7, 10, 2, 4, 0, 0] := by decide
example : (finishValues 3 7 11 0 2 5).drop 53 ≠ [7, 11, 1, 4, 0, 0] := by decide
example : (finishValues 3 7 11 0 2 5).drop 53 ≠ [7, 11, 2, 4, 1, 0] := by decide
example : (finishValues 3 7 11 0 2 5).drop 53 ≠ [7, 11, 2, 4, 0, 1] := by decide

example (remaining inputLength fuel length width coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? machine (workSteps remaining inputLength fuel length width coordinate)
      (initialConfiguration remaining inputLength fuel length width coordinate older inside) =
      some (finalConfiguration remaining inputLength fuel length width coordinate older inside) :=
  workRunExact remaining inputLength fuel length width coordinate older inside
example (remaining inputLength fuel length width coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps remaining inputLength fuel length width coordinate)
      (encodeWorkConfiguration (initialConfiguration remaining inputLength fuel length width coordinate older inside)) =
      encodeWorkConfiguration (finalConfiguration remaining inputLength fuel length width coordinate older inside) :=
  run_compile_exact remaining inputLength fuel length width coordinate older inside
example (inputLength fuel : Nat) (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? machine (workSteps 0 inputLength fuel 0 2 9)
      (initialConfiguration 0 inputLength fuel 0 2 9 older inside) =
      some (finalConfiguration 0 inputLength fuel 0 2 9 older inside) :=
  workRunExact 0 inputLength fuel 0 2 9 older inside
example (inputLength fuel : Nat) (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? machine (workSteps 3 inputLength fuel 0 2 0)
      (initialConfiguration 3 inputLength fuel 0 2 0 older inside) =
      some (finalConfiguration 3 inputLength fuel 0 2 0 older inside) :=
  workRunExact 3 inputLength fuel 0 2 0 older inside
example (inputLength fuel : Nat) (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? machine (workSteps 3 inputLength fuel 0 2 5)
      (initialConfiguration 3 inputLength fuel 0 2 5 older inside) =
      some (finalConfiguration 3 inputLength fuel 0 2 5 older inside) :=
  workRunExact 3 inputLength fuel 0 2 5 older inside
example (inputLength fuel : Nat) (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? machine (workSteps 3 inputLength fuel 0 2 9)
      (initialConfiguration 3 inputLength fuel 0 2 9 older inside) =
      some (finalConfiguration 3 inputLength fuel 0 2 9 older inside) :=
  workRunExact 3 inputLength fuel 0 2 9 older inside
example (inputLength fuel : Nat) (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? machine (workSteps 2 inputLength fuel 0 0 0)
      (initialConfiguration 2 inputLength fuel 0 0 0 older inside) =
      some (finalConfiguration 2 inputLength fuel 0 0 0 older inside) :=
  workRunExact 2 inputLength fuel 0 0 0 older inside

example (remaining inputLength fuel length width coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration remaining inputLength fuel length width coordinate older inside).tape =
      endTape (older ++ finishValues remaining inputLength fuel length width coordinate) inside [] :=
  final_tape remaining inputLength fuel length width coordinate older inside
example (remaining inputLength fuel length width coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration remaining inputLength fuel length width coordinate older inside).tape.left = [] :=
  final_frontier remaining inputLength fuel length width coordinate older inside
example (remaining inputLength fuel length width coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration remaining inputLength fuel length width coordinate older inside).state = machine.acceptState ↔
      (BuilderInitialLengthSelection.locate remaining width coordinate).isSome = true :=
  final_accept_iff remaining inputLength fuel length width coordinate older inside
example (remaining inputLength fuel length width coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration remaining inputLength fuel length width coordinate older inside).state = machine.rejectState ↔
      BuilderInitialLengthSelection.locate remaining width coordinate = none :=
  final_reject_iff remaining inputLength fuel length width coordinate older inside

example (remaining inputLength fuel length width coordinate : Nat) (position : Fin remaining) (offset : Nat)
    (hFound : BuilderInitialLengthSelection.locate remaining width coordinate = some (position, offset)) :
    ∃ history : List Nat, finishValues remaining inputLength fuel length width coordinate =
      history ++ frame inputLength fuel (length + position.val) (width + position.val) offset
        (remaining - (position.val + 1)) :=
  found_suffix remaining inputLength fuel length width coordinate position offset hFound

example (remaining inputLength fuel length width coordinate bound : Nat)
    (hInput : inputLength ≤ bound) (hFuel : fuel ≤ bound) (hLength : length + remaining ≤ bound)
    (hWidth : width + remaining ≤ bound) (hCoordinate : coordinate ≤ bound) :
    (registerWord (finishValues remaining inputLength fuel length width coordinate)).length ≤
      (remaining + 1) * (30 * bound + 38) :=
  finish_span_le remaining inputLength fuel length width coordinate bound hInput hFuel hLength hWidth hCoordinate
example (remaining inputLength fuel length width coordinate : Nat) (older : List Nat)
    (bound : NatPolynomial) (inputSize : Nat)
    (hSpan : (registerWord (older ++ frame inputLength fuel length width coordinate remaining)).length ≤ bound.eval inputSize) :
    (registerWord (older ++ finishValues remaining inputLength fuel length width coordinate)).length ≤
      (spanPolynomial bound).eval inputSize ∧
      6 * workSteps remaining inputLength fuel length width coordinate ≤ (rawTimePolynomial bound).eval inputSize :=
  source_polynomial_bounds remaining inputLength fuel length width coordinate older bound inputSize hSpan

example : graph.nodes.length = 6 := graph_nodes_length
example : graph.WellFormed := graph_wellFormed
example : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct := rules_pairwise_query_distinct
example : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState := noRuleAtAccept
example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := noRuleAtReject
example : machine.acceptState ≠ machine.rejectState := acceptState_ne_rejectState

end PNP.Concrete.CookLevin.BuilderInitialRowCarryRegression
