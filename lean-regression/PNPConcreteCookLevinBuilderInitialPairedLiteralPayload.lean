/-
Copyright (c) 2026 PNP Labs.
The complete literal writer uses the global tape width rather than a selected
row's slot count. Fixed examples check signs, fields and index arithmetic;
universal contracts check exact physical execution and encoded-size bounds.
Canonical requests are tied to the existing literal and initial-payload APIs.
-/
import PNP.Concrete.CookLevinBuilderInitialPairedLiteralPayload

namespace PNP.Concrete.CookLevin.BuilderInitialPairedLiteralPayload.Regression
open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderInitialCellCoordinates (Request)

private def sample : Data :=
  {inputLength := 3, fuel := 2, length := 2, rowSlots := 27, remaining := 4,
   position := 7, offset := 1, kind := 2, argument := 1, code := 1}
private def positive : Data := {sample with kind := 3, offset := 0, code := 2}
private def negative : Data := {sample with kind := 3}
private def empty : Data :=
  {inputLength := 0, fuel := 0, length := 0, rowSlots := 3, remaining := 0,
   position := 0, offset := 0, kind := 0, argument := 0, code := 0}
private def bits : BitString := [true, false, true]

example : dataValues sample = [3,2,2,27,4,7,1,2,1,1] := rfl
example : certificateBound sample = 6 := rfl
example : timeCount sample = 3 := rfl
example : tapeWidth sample = 25 := rfl
example : tapeWidth sample ≠ sample.rowSlots := by decide
example : indexValue 5 .length sample = 323 := by decide
example : indexValue 5 .symbol sample = 22 := by decide
example : indexValue 5 .bit sample = 316 := by decide
example : payloadValues 5 sample = [323,1,22,1,1,3] := by decide
example : payloadValues 5 positive = [316,1,323,1,23,1,2,3] := by decide
example : payloadValues 5 negative = [316,0,323,1,22,1,2,3] := by decide
example : payloadValues 5 positive ≠ payloadValues 5 negative := by decide
example : (payloadValues 5 sample).length = 6 := by decide
example : (payloadValues 5 positive).length = 8 := by decide
example : (payloadValues 5 negative).length = 8 := by decide
example : tapeWidth empty = 3 := rfl
-- T=1, W=3, S=C=0: certificate offset = 1*3*3 + 1*3 + 1*0 = 12.
example : payloadValues 0 empty = [12,1,0,1,1,3] := by decide
example : resolvedSymbol bits (.blank : Request 6) 0 = .blank := rfl
example : resolvedSymbol bits (.fixed false : Request 6) 0 = .zero := rfl
example : resolvedSymbol bits (.fixed true : Request 6) 0 = .one := rfl
example : resolvedSymbol bits (.sourceBit 0 : Request 6) 0 = .one := rfl
example : resolvedSymbol bits (.sourceBit 1 : Request 6) 0 = .zero := rfl
example : resolvedSymbol bits (.sourceBit 3 : Request 6) 0 = .blank := rfl
example : resolvedSymbol [] (.sourceBit 0 : Request 0) 0 = .blank := rfl
example : resolvedSymbol bits (.certificate ⟨1, by decide⟩ : Request 6) 0 = .one := rfl
example : resolvedSymbol bits (.certificate ⟨1, by decide⟩ : Request 6) 1 = .zero := rfl

section Numeric
variable (states : Nat) (data : Data) (older : List Nat) (inside : List WorkSymbol)

example : (dataValues data).length = 10 := dataValues_length data
example : (preparedValues states data).length = preparedCount states := preparedValues_length states data
example : (graph states).nodes.length = 10 := graph_nodes_length states
example : (graph states).WellFormed := graph_wellFormed states
example : (kindNode states).onAccept = .node (offsetPrepareNode states).reference := rfl
example : (kindNode states).onReject = .node (ordinaryNode states).reference := rfl
example : (offsetTestNode states).onAccept = .node (positiveNode states).reference := rfl
example : (offsetTestNode states).onReject = .node (negativeNode states).reference := rfl
example : workRunExact? (machine states) (workSteps states data) (initialConfiguration states data older inside) =
    some (finalConfiguration states data older inside) := workRunExact states data older inside
example : run (compileWorkMachine (machine states)) (6 * workSteps states data)
    (encodeWorkConfiguration (initialConfiguration states data older inside)) =
      encodeWorkConfiguration (finalConfiguration states data older inside) := run_compile_exact states data older inside
example : (finalConfiguration states data older inside).tape = endTape (older ++ outputValues states data) inside [] :=
  final_tape states data older inside
example : (finalConfiguration states data older inside).tape.left = [] := final_frontier states data older inside
example : (finalConfiguration states data older inside).state = (machine states).acceptState := final_accept states data older inside
example : ∃ history : List Nat, outputValues states data = history ++ payloadValues states data := output_suffix states data
example : (machine states).rules.Pairwise WorkMachineProgramGraph.QueryDistinct := rules_pairwise_query_distinct states
example : WorkMachineProgramGraph.NoRuleAt (machine states) (machine states).acceptState := noRuleAtAccept states
example : WorkMachineProgramGraph.NoRuleAt (machine states) (machine states).rejectState := noRuleAtReject states
example : (machine states).acceptState ≠ (machine states).rejectState := acceptState_ne_rejectState states
example (bound : NatPolynomial) (inputSize : Nat)
    (hSpan : (registerWord (older ++ dataValues data)).length ≤ bound.eval inputSize) :
    (registerWord (older ++ outputValues states data)).length ≤ (spanPolynomial states bound).eval inputSize ∧
      6 * workSteps states data ≤ (rawTimePolynomial states bound).eval inputSize :=
  source_polynomial_bounds states data older bound inputSize hSpan
example : (registerWord (payloadValues states data)).length ≤ (registerWord (outputValues states data)).length :=
  payload_span_le_output states data
end Numeric

section Canonical
variable {language : Language} (problem : VerifierTableauProblem language)
variable (hMode : problem.tableauInputMode = .paired)
variable (length : Fin (problem.certificateLimit + 1))
variable (position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode))
variable (request : Request problem.certificateLimit) (offset : Nat)

example : stateCount problem.verifier = problem.dimensions.stateBound := stateCount_canonical problem
example : VariableLayout.tapeSymbolCode (resolvedSymbol problem.input request offset) =
    BuilderInitialRequestResolution.symbolCode problem.input request offset :=
  resolvedSymbol_code problem.input request offset
example : dataValues (canonicalData problem length position request offset) =
    BuilderInitialRequestResolution.resultValues (BuilderInitialPairedCellSource.metadata problem length.val)
      position.val offset request problem.input :=
  ofResolved_values _ _ _ _ _
example : timeCount (canonicalData problem length position request offset) = problem.dimensions.timeCount ∧
    tapeWidth (canonicalData problem length position request offset) =
      problem.dimensions.tapeWidth problem.tableauInputMode ∧
    stateCount problem.verifier = problem.dimensions.stateBound ∧
    certificateBound (canonicalData problem length position request offset) = problem.layout.certificateBitWidth :=
  canonical_dimensions problem hMode length position request offset
example : indexValue (stateCount problem.verifier) .length (canonicalData problem length position request offset) =
    (problem.pairedLengthLiteral hMode length).index.val :=
  length_index_canonical problem hMode length position request offset
example : indexValue (stateCount problem.verifier) .symbol (canonicalData problem length position request offset) =
    (problem.symbolLiteral problem.initialTime position (resolvedSymbol problem.input request offset)).index.val :=
  symbol_index_canonical problem hMode length position request offset
example (index : Fin problem.certificateLimit) :
    indexValue (stateCount problem.verifier) .bit (canonicalData problem length position (.certificate index) offset) =
      (problem.pairedBitLiteral hMode index).index.val :=
  bit_index_canonical problem hMode length position index offset
example (hOffset : offset < BuilderInitialCellCoordinates.requestWidth request) :
    BuilderInitialConstraintPayload.requestValues problem hMode length position request offset =
      some (payloadValues (stateCount problem.verifier) (canonicalData problem length position request offset)) :=
  canonical_payload problem hMode length position request offset hOffset
end Canonical

end PNP.Concrete.CookLevin.BuilderInitialPairedLiteralPayload.Regression
