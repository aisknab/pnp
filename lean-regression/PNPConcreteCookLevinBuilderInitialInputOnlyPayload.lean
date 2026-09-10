/-
Copyright (c) 2026 PNP Labs.
Independent input-only boundary, source-bit and payload fixtures, with uniform
physical execution and encoded-span bounds. These fixtures earn no milestone.
-/
import PNP.Concrete.CookLevinBuilderInitialInputOnlyPayload

namespace PNP.Concrete.CookLevin.BuilderInitialInputOnlyPayload.Regression
open BuilderInitialInputOnlyPayload
open BuilderUnaryPolynomial

example : endpoint ⟨2, 3, 11, 0⟩ = .reject := rfl
example : endpoint ⟨2, 3, 11, 1⟩ = .reject := rfl
example : endpoint ⟨2, 3, 11, 2⟩ = .accept := rfl
example : position ⟨2, 3, 11, 2⟩ = 0 := rfl
example : position ⟨2, 3, 11, 5⟩ = 3 := rfl
example : request ⟨2, 3, 11, 4⟩ = .blank := rfl
example : request ⟨2, 3, 11, 5⟩ = .sourceBit 0 := rfl
example : request ⟨2, 3, 11, 6⟩ = .sourceBit 1 := rfl
example : request ⟨2, 3, 11, 7⟩ = .sourceBit 2 := rfl
example : request ⟨0, 0, 1, 2⟩ = .sourceBit 0 := rfl
example : code ⟨2, 3, 11, 4⟩ [true, false] = 0 := rfl
example : code ⟨2, 3, 11, 5⟩ [true, false] = 2 := rfl
example : code ⟨2, 3, 11, 6⟩ [true, false] = 1 := rfl
example : code ⟨2, 3, 11, 7⟩ [true, false] = 0 := rfl
example : code ⟨0, 0, 1, 2⟩ [] = 0 := rfl
example : payloadValues ⟨2, 3, 11, 4⟩ [true, false] = [6,1,2] := rfl
example : payloadValues ⟨2, 3, 11, 5⟩ [true, false] = [11,1,2] := rfl
example : payloadValues ⟨2, 3, 11, 6⟩ [true, false] = [13,1,2] := rfl
example : payloadValues ⟨2, 3, 11, 7⟩ [true, false] = [15,1,2] := rfl
example : payloadValues ⟨0, 0, 1, 2⟩ [] = [0,1,2] := rfl
example : payloadValues ⟨2, 3, 11, 12⟩ [true, false] = [30,1,2] := rfl
example : outputValues ⟨2, 3, 11, 13⟩ [true, false] = widthStage ⟨2,3,11,13⟩ ++ [1] := rfl
example : outputValues ⟨0, 0, 0, 2⟩ [] = widthStage ⟨0,0,0,2⟩ ++ [1] := rfl
example : (outputValues ⟨2,3,11,0⟩ [true,false]).length = 9 := rfl
example : (outputValues ⟨2,3,11,13⟩ [true,false]).length = 15 := rfl
example : (outputValues ⟨2,3,11,5⟩ [true,false]).length = 47 := rfl
example : BuilderLocalConstraintPayload.decode 33 [11,1,2] =
    some (some (some (.require ⟨true, ⟨11, by decide⟩⟩))) := rfl
example : BuilderLocalConstraintPayload.decode 33 [1] = some (some none) := rfl
example : BuilderLocalConstraintPayload.decode 33 [0] = some none := rfl
example : BuilderLocalConstraintPayload.decode 33 [11,0,2] ≠
    some (some (some (.require ⟨true, ⟨11, by decide⟩⟩))) := by
  intro h
  have hLiteral := LocalConstraint.require.inj (Option.some.inj (Option.some.inj (Option.some.inj h)))
  have hSign : false = true := congrArg BoundedLiteral.positive hLiteral
  cases hSign
example : BuilderLocalConstraintPayload.decode 11 [11,1,2] = none := by decide
example : BuilderLocalConstraintPayload.decode 33 [11,1,3] = none := by decide
example : BuilderLocalConstraintPayload.decode 33 [2,1,11] = none := by decide

section Uniform
variable (data : Data) (older : List Nat) (input : BitString) (output : List CNFToken)
example : request data = BuilderInitialCellCoordinates.inputOnlyRequest data.fuel (position data) :=
  request_canonical data
example : code data input = VariableLayout.tapeSymbolCode
    (BuilderInitialConstraintPayload.inputOnlySymbol input data.fuel (position data)) := code_canonical data input
example : code data input ≤ 2 := code_le data input
example : (cellValues data input).length = 47 := cellValues_length data input
example : workRunExact? machine (workSteps data older input) (initialConfiguration data older input output) =
    some (finalConfiguration data older input output) := workRunExact data older input output
example : run (compileWorkMachine machine) (6 * workSteps data older input)
    (encodeWorkConfiguration (initialConfiguration data older input output)) =
    encodeWorkConfiguration (finalConfiguration data older input output) := run_compile_exact data older input output
example : (finalConfiguration data older input output).state = machine.acceptState ↔ 2 ≤ data.coordinate :=
  final_accept_iff data older input output
example : (finalConfiguration data older input output).state = machine.rejectState ↔ data.coordinate < 2 :=
  final_reject_iff data older input output
example : (finalConfiguration data older input output).tape =
    BuilderDividerOperands.endTape (older ++ outputValues data input) (BuilderDividerOperands.inside input output) [] :=
  final_tape data older input output
example : (finalConfiguration data older input output).tape.left = [] := final_frontier data older input output
example (hPrefix : ¬ data.coordinate < 2) (hWidth : ¬ position data < data.tapeWidth) :
    outputValues data input = widthStage data ++ [1] := padding_output data input hPrefix hWidth
example (bound : NatPolynomial) (inputSize : Nat)
    (hSpan : (registerWord (older ++ dataValues data)).length ≤ bound.eval inputSize) :
    (registerWord (older ++ outputValues data input)).length ≤ (spanPolynomial bound).eval inputSize ∧
      6 * workSteps data older input ≤ (rawTimePolynomial bound).eval inputSize :=
  packet_polynomial_bounds data older input bound inputSize hSpan
end Uniform

example : graph.nodes.length = 12 := graph_nodes_length
example : graph.WellFormed := graph_wellFormed
example : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct := rules_pairwise_query_distinct
example : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState := noRuleAtAccept
example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := noRuleAtReject
example : machine.acceptState ≠ machine.rejectState := acceptState_ne_rejectState

end PNP.Concrete.CookLevin.BuilderInitialInputOnlyPayload.Regression
