/-
Copyright (c) 2026 PNP Labs.
The fixed resolver must use the encoded request tag, retain all request fields,
read actual input only for source requests, preserve prior output, and charge
complete physical work. Pure result examples complement universal execution
and bounds; they are not substitutes for source-to-resolver integration.
-/
import PNP.Concrete.CookLevinBuilderInitialRequestResolution

namespace PNP.Concrete.CookLevin.BuilderInitialRequestResolution.Regression
open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape inside)
open BuilderInitialCellCoordinates (Request)

private def metadata : Metadata :=
  {inputLength := 3, fuel := 2, length := 2, rowWidth := 17, remaining := 4}
private def bits : BitString := [true, false, true]
private def data (values : List Nat) {arity : Nat} (index : Fin arity) : Nat := values.getD index.val 0

example : graph.nodes.length = 13 := graph_nodes_length
example : graph.WellFormed := graph_wellFormed
example : BuilderRegisterPack.values tagFields (data [3,2,2,17,4,7,1,2,1]) = [2] := by decide
example : BuilderRegisterPack.values tagFields (data [3,2,2,17,4,7,1,2,1]) ≠ [1] := by decide
example : BuilderRegisterPack.values sourceFields (data [3,2,2,17,4,7,1,2,1,2]) =
    [3,2,2,17,4,7,1,2,1] := by decide
example : BuilderRegisterPack.values offsetFields (data [3,2,2,17,4,7,1,3,0,3]) = [1] := by decide
example : BuilderRegisterPack.values offsetFields (data [3,2,2,17,4,7,1,3,0,3]) ≠ [0] := by decide
example : BuilderRegisterExpression.eval fixedExpression (data [3,2,2,17,4,7,1,1,0,1]) = 1 := by decide
example : BuilderRegisterExpression.eval fixedExpression (data [3,2,2,17,4,7,1,1,1,1]) = 2 := by decide
example : symbolCode bits (.blank : Request 6) 0 = 0 := rfl
example : symbolCode bits (.fixed false : Request 6) 0 = 1 := rfl
example : symbolCode bits (.fixed true : Request 6) 0 = 2 := rfl
example : symbolCode bits (.sourceBit 0 : Request 6) 0 = 2 := rfl
example : symbolCode bits (.sourceBit 1 : Request 6) 0 = 1 := rfl
example : symbolCode bits (.sourceBit 2 : Request 6) 0 = 2 := rfl
example : symbolCode bits (.sourceBit 3 : Request 6) 0 = 0 := rfl
example : symbolCode bits (.sourceBit 99 : Request 6) 0 = 0 := rfl
example : symbolCode [] (.sourceBit 0 : Request 0) 0 = 0 := rfl
example : symbolCode bits (.certificate ⟨0, by decide⟩ : Request 6) 0 = 2 := rfl
example : symbolCode bits (.certificate ⟨0, by decide⟩ : Request 6) 1 = 1 := rfl
example : symbolCode bits (.fixed true : Request 6) 1 ≠ symbolCode bits (.sourceBit 1 : Request 6) 1 := by decide
example : symbolCode bits (.certificate ⟨1, by decide⟩ : Request 6) 0 ≠
    symbolCode bits (.certificate ⟨1, by decide⟩ : Request 6) 1 := by decide
example : resultValues metadata 7 1 (.sourceBit 1 : Request 6) bits = [3,2,2,17,4,7,1,2,1,1] := rfl
example : resultValues metadata 7 1 (.fixed true : Request 6) bits = [3,2,2,17,4,7,1,1,1,2] := rfl
example : resultValues metadata 7 0 (.certificate ⟨1, by decide⟩ : Request 6) bits =
    [3,2,2,17,4,7,0,3,1,2] := rfl
example : resultValues metadata 7 1 (.certificate ⟨1, by decide⟩ : Request 6) bits =
    [3,2,2,17,4,7,1,3,1,1] := rfl
example : sourceTestNode.onAccept = .node sourcePrepareNode.reference := rfl
example : sourcePrepareNode.onAccept = .node readerNode.reference := rfl
example : readerNode.program = BuilderIndexedInputRead.machine := rfl
example : fixedTestNode.onAccept = .node fixedExpressionNode.reference := rfl
example : zeroNode.onAccept = .node blankNode.reference := rfl

section Universal
variable (m : Metadata) (position offset : Nat) (request : Request width)
variable (older : List Nat) (input : BitString) (output : List CNFToken)

example : (inputValues m position offset request).length = 9 := inputValues_length m position offset request
example : (resultValues m position offset request input).length = 10 := resultValues_length m position offset request input
example : workRunExact? machine (workSteps m position offset request older input)
    (initialConfiguration m position offset request older input output) =
      some (finalConfiguration m position offset request older input output) :=
  workRunExact m position offset request older input output
example : run (compileWorkMachine machine) (6 * workSteps m position offset request older input)
    (encodeWorkConfiguration (initialConfiguration m position offset request older input output)) =
      encodeWorkConfiguration (finalConfiguration m position offset request older input output) :=
  run_compile_exact m position offset request older input output
example : (finalConfiguration m position offset request older input output).tape =
    endTape (older ++ outputValues m position offset request input) (inside input output) [] :=
  final_tape m position offset request older input output
example : (finalConfiguration m position offset request older input output).tape.left = [] :=
  final_frontier m position offset request older input output
example : (finalConfiguration m position offset request older input output).state = machine.acceptState :=
  final_accept m position offset request older input output
example : ∃ history : List Nat, outputValues m position offset request input =
    history ++ resultValues m position offset request input := output_suffix m position offset request input
example : symbolCode input request offset ≤ 2 := symbolCode_le input request offset
example (bound : NatPolynomial) (inputSize : Nat)
    (hSpan : (registerWord (older ++ inputValues m position offset request)).length ≤ bound.eval inputSize) :
    (registerWord (older ++ outputValues m position offset request input)).length ≤ (spanPolynomial bound).eval inputSize ∧
      6 * workSteps m position offset request older input ≤ (rawTimePolynomial bound).eval inputSize :=
  source_polynomial_bounds m position offset request older input bound inputSize hSpan
example : (registerWord (resultValues m position offset request input)).length ≤
    (registerWord (outputValues m position offset request input)).length :=
  result_span_le_output m position offset request input

end Universal
example : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct := rules_pairwise_query_distinct
example : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState := noRuleAtAccept
example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := noRuleAtReject
example : machine.acceptState ≠ machine.rejectState := acceptState_ne_rejectState

end PNP.Concrete.CookLevin.BuilderInitialRequestResolution.Regression
