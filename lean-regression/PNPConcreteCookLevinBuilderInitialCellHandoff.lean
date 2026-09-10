/-
Copyright (c) 2026 PNP Labs.
All-coordinate physical cell metadata handoff. Independent field-order and
branch-boundary expectations precede universal work/raw and polynomial contracts.
-/
import PNP.Concrete.CookLevinBuilderInitialCellHandoff

namespace PNP.Concrete.CookLevin.BuilderInitialCellHandoff.Regression
open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)

private def metadata : Metadata := ⟨7, 11, 2, 40, 3⟩
private def data (values : List Nat) {arity : Nat} (index : Fin arity) : Nat := values.getD index.val 0

example : frame metadata 29 30 = [7, 11, 2, 40, 3, 29, 30] := rfl
example : frame metadata 29 30 ≠ [11, 7, 2, 40, 3, 29, 30] := by decide
example : selectedBranch metadata 29 28 = .before := by decide
example : selectedBranch metadata 29 29 = .middle := by decide
example : selectedBranch metadata 29 32 = .middle := by decide
example : selectedBranch metadata 29 33 = .after := by decide
example : selectedBranch metadata 29 33 ≠ .middle := by decide
example : selectedBranch {metadata with length := 0} 29 29 = .after := by decide
example : selectedBranch {metadata with length := 0} 29 28 = .before := by decide
example : selectedBranch {metadata with length := 0} 29 29 ≠ .middle := by decide
example : upper metadata 29 = 33 := rfl
example : BuilderRegisterPack.values firstFields (data (frame metadata 29 30)) = [30, 29] := by decide
example : BuilderRegisterPack.values firstFields (data (frame metadata 29 30)) ≠ [29, 30] := by decide
example : BuilderRegisterExpression.eval upperExpression (data (firstValues metadata 29 30)) = 33 := by decide
example : BuilderRegisterExpression.eval upperExpression (data (firstValues metadata 29 30)) ≠ 31 := by decide
example : BuilderRegisterPack.values secondFields
    (data (firstValues metadata 29 30 ++ upperValues metadata 29)) = [30, 33] := by decide
example : BuilderRegisterPack.values (decoderFields .before) (data (baseValues .before metadata 29 28)) =
    [29, 2, 28] := by decide
example : BuilderRegisterPack.values (decoderFields .middle) (data (baseValues .middle metadata 29 30)) =
    [29, 2, 30] := by decide
example : BuilderRegisterPack.values (decoderFields .after) (data (baseValues .after metadata 29 35)) =
    [29, 2, 35] := by decide
example : BuilderRegisterPack.values (decoderFields .middle) (data (baseValues .middle metadata 29 30)) ≠
    [30, 2, 29] := by decide
example : carriedValues metadata 29 28 = [7, 11, 2, 40, 3, 28, 0] := by decide
example : carriedValues metadata 29 29 = [7, 11, 2, 40, 3, 29, 0] := by decide
example : carriedValues metadata 29 30 = [7, 11, 2, 40, 3, 29, 1] := by decide
example : carriedValues metadata 29 32 = [7, 11, 2, 40, 3, 30, 1] := by decide
example : carriedValues metadata 29 33 = [7, 11, 2, 40, 3, 31, 0] := by decide
example : carriedValues metadata 29 35 = [7, 11, 2, 40, 3, 33, 0] := by decide
example : carriedValues {metadata with length := 0} 29 29 = [7, 11, 0, 40, 3, 29, 0] := by decide
example : carriedValues metadata 29 30 ≠ [7, 11, 2, 40, 3, 30, 0] := by decide
example : BuilderRegisterPack.values (carryFields .before) (data (resultFrame .before metadata 29 28)) =
    [7, 11, 2, 40, 3, 28, 0] := by decide
example : BuilderRegisterPack.values (carryFields .middle) (data (resultFrame .middle metadata 29 30)) =
    [7, 11, 2, 40, 3, 29, 1] := by decide
example : BuilderRegisterPack.values (carryFields .after) (data (resultFrame .after metadata 29 35)) =
    [7, 11, 2, 40, 3, 33, 0] := by decide
example : (resultFrame .before metadata 29 28).length = 22 := rfl
example : (resultFrame .middle metadata 29 30).length = 51 := rfl
example : (resultFrame .after metadata 29 35).length = 45 := rfl
example : graph.nodes.length = 14 := graph_nodes_length
example : graph.WellFormed := graph_wellFormed

section Universal
variable (context : Metadata) (start coordinate : Nat) (older : List Nat) (inside : List WorkSymbol)

example : (frame context start coordinate).length = 7 := frame_length context start coordinate
example : (carriedValues context start coordinate).length = 7 := carriedValues_length context start coordinate
example (branch : Branch) : (baseValues branch context start coordinate).length = baseCount branch :=
  baseValues_length branch context start coordinate
example (branch : Branch) : (resultFrame branch context start coordinate).length = resultCount branch :=
  resultFrame_length branch context start coordinate
example : decodedValues (selectedBranch context start coordinate) context start coordinate =
    BuilderInitialCellDecoder.outputValues start context.length coordinate := selected_decoder_values context start coordinate
example : branchResult (selectedBranch context start coordinate) context start coordinate =
    carriedValues context start coordinate := selected_carried_values context start coordinate
example : workRunExact? machine (workSteps context start coordinate)
    (initialConfiguration context start coordinate older inside) =
      some (finalConfiguration context start coordinate older inside) := workRunExact context start coordinate older inside
example : run (compileWorkMachine machine) (6 * workSteps context start coordinate)
    (encodeWorkConfiguration (initialConfiguration context start coordinate older inside)) =
      encodeWorkConfiguration (finalConfiguration context start coordinate older inside) :=
  run_compile_exact context start coordinate older inside
example : (finalConfiguration context start coordinate older inside).tape =
    endTape (older ++ resultFrame (selectedBranch context start coordinate) context start coordinate ++
      context.values ++ [(BuilderInitialCellSelection.cellCoordinate start context.length coordinate).1,
        (BuilderInitialCellSelection.cellCoordinate start context.length coordinate).2]) inside [] :=
  final_tape context start coordinate older inside
example : (finalConfiguration context start coordinate older inside).tape.left = [] :=
  final_frontier context start coordinate older inside
example : (finalConfiguration context start coordinate older inside).state = machine.acceptState :=
  final_accept context start coordinate older inside
example : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct := rules_pairwise_query_distinct
example : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState := noRuleAtAccept
example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := noRuleAtReject
example : machine.acceptState ≠ machine.rejectState := acceptState_ne_rejectState
example (bound : NatPolynomial) (inputLength : Nat)
    (hSpan : (registerWord (older ++ frame context start coordinate)).length ≤ bound.eval inputLength) :
    (registerWord (older ++ outputValues context start coordinate)).length ≤ (spanPolynomial bound).eval inputLength ∧
      6 * workSteps context start coordinate ≤ (rawTimePolynomial bound).eval inputLength :=
  source_polynomial_bounds context start coordinate older bound inputLength hSpan
example (width : Nat) (hInterval : start + context.length ≤ width) (hInside : coordinate < width + context.length) :
    (BuilderInitialCellSelection.cellCoordinate start context.length coordinate).1 < width ∧
      (BuilderInitialCellSelection.cellCoordinate start context.length coordinate).2 <
        BuilderInitialCellCoordinates.intervalWidth start context.length
          (BuilderInitialCellSelection.cellCoordinate start context.length coordinate).1 ∧
      coordinate = (BuilderInitialCellSelection.cellCoordinate start context.length coordinate).1 +
        min context.length ((BuilderInitialCellSelection.cellCoordinate start context.length coordinate).1 - start) +
        (BuilderInitialCellSelection.cellCoordinate start context.length coordinate).2 :=
  decoded_bounds context width start coordinate hInterval hInside
end Universal
end PNP.Concrete.CookLevin.BuilderInitialCellHandoff.Regression
