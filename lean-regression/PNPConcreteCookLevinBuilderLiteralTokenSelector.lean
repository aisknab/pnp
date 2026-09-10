/-
Copyright (c) 2026 PNP Labs.
Uniform literal-token selection: physical sign and position, unary boundaries,
preserved source frame, exact work/raw execution and polynomial resource bounds.
-/
import PNP.Concrete.CookLevinBuilderLiteralTokenSelector

namespace PNP.Concrete.CookLevin.BuilderLiteralTokenSelector.Regression
open BuilderLiteralTokenSelector
open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape)

example : graph.nodes.length = 10 := graph_nodes_length
example : graph.WellFormed := graph_wellFormed
example : copySignNode.program = BuilderUnaryPolynomial.RegisterCopy.machine 2 := rfl
example : copyPositionNode.program = BuilderUnaryPolynomial.RegisterCopy.machine 0 := rfl
example : copyValueNode.program = BuilderUnaryPolynomial.RegisterCopy.machine 2 := rfl
example : residualNode.onAccept = .reject := rfl
example : residualNode.onReject = .dead := rfl
example : observe (finalConfiguration false 0 0 [] [] []) = some .f := rfl
example : observe (finalConfiguration true 0 0 [] [] []) = some .t := rfl
example : observe (finalConfiguration false 0 1 [] [] []) = some .f := rfl
example : observe (finalConfiguration true 0 1 [] [] []) = some .f := rfl
example : observe (finalConfiguration false 0 2 [] [] []) = none := rfl
example : observe (finalConfiguration true 0 2 [] [] []) = none := rfl
example : observe (finalConfiguration false 3 1 [] [] []) = some .t := rfl
example : observe (finalConfiguration false 3 3 [] [] []) = some .t := rfl
example : observe (finalConfiguration false 3 4 [] [] []) = some .f := rfl
example : observe (finalConfiguration false 3 5 [] [] []) = none := rfl
example : literal true 19 = {positive := true, variableIndex := 19} := rfl
example : literal false 19 = {positive := false, variableIndex := 19} := rfl

variable (positive : Bool) (value position : Nat) (older : List Nat) (inside outside : List WorkSymbol)
example : (initialConfiguration positive value position older inside outside).tape =
    endTape (older ++ [BuilderLocalConstraintPayload.signValue positive, value, position]) inside outside := rfl
example : workRunExact? machine (workSteps positive value position)
    (initialConfiguration positive value position older inside outside) =
    some (finalConfiguration positive value position older inside outside) :=
  workRunExact positive value position older inside outside
example : run (compileWorkMachine machine) (6 * workSteps positive value position)
    (encodeWorkConfiguration (initialConfiguration positive value position older inside outside)) =
    encodeWorkConfiguration (finalConfiguration positive value position older inside outside) :=
  run_compile_exact positive value position older inside outside
example : observe (workRun machine (workSteps positive value position)
    (initialConfiguration positive value position older inside outside)) =
    DirectToken.literalSlot {positive := positive, variableIndex := value} position :=
  workRun_observes_literal positive value position older inside outside
example : observe (finalConfiguration positive value position older inside outside) =
    DirectToken.literalSlot (literal positive value) position := canonical_result positive value position older inside outside
example : DirectToken.unarySlot value position =
    if position < value then some .t else if position = value then some .f else none := unarySlot_cases value position
example : (finalConfiguration positive value position older inside outside).tape =
    endTape (finalValues positive value position older) inside (finalOutside positive value position outside) :=
  final_tape positive value position older inside outside
example : (finalConfiguration positive value position older inside outside).tape.right =
    (registerWord (finalValues positive value position older)).reverse ++ inside := rfl
example : ∃ history, finalValues positive value position older = older ++ frame positive value position ++ history :=
  original_frame_preserved positive value position older
example : (BuilderRegisterCompareResidual.outputValues (comparisonResult value position)).length = 5 :=
  comparison_history_length value position
example : finalValues positive value 0 older = older ++ frame positive value 0 := by
  simp only [finalValues, ite_true, List.append_nil]
example : (finalOutside positive value position outside).length ≤ outside.length + 2 :=
  final_outside_length_le positive value position outside
example : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct := rules_pairwise_query_distinct
example : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState := noRuleAtAccept
example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := noRuleAtReject
example : machine.acceptState ≠ machine.rejectState := acceptState_ne_rejectState
example (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (older ++ frame positive value position)).length + outside.length ≤ bound.eval input) :
    (registerWord (finalValues positive value position older)).length + (finalOutside positive value position outside).length ≤
        (spanPolynomial bound).eval input ∧
      6 * workSteps positive value position ≤ (rawTimePolynomial bound).eval input :=
  source_polynomial_bounds positive value position older outside bound input hSpan

end PNP.Concrete.CookLevin.BuilderLiteralTokenSelector.Regression
