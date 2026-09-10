/-
Copyright (c) 2026 PNP Labs.

Physical resolution of every encoded initial-cell request. One fixed program
preserves source and prior output, reads the actual indexed input only for a
source request, and appends the canonical symbol code to the nine carried
request fields. Certificate signs use the actual within-cell offset.
This component is not the literal/payload writer or complete formula builder.
-/

import PNP.Concrete.CookLevinBuilderInitialPairedRequest
import PNP.Concrete.CookLevinBuilderInitialConstraintPayload
import PNP.Concrete.CookLevinBuilderUnaryTagMatch

namespace PNP.Concrete.CookLevin.BuilderInitialRequestResolution

open BuilderUnaryPolynomial
open VerifierTableauProblem
open BuilderDividerOperands (endTape inside)
open BuilderInitialCellCoordinates (Request)
open WorkMachineProgramGraph (Node Endpoint Graph)
open WorkMachineProgramPath (AcceptPath)

abbrev Metadata := BuilderInitialPairedRequest.Metadata

private def view {arity : Nat} (data : List Nat) (index : Fin arity) : Nat :=
  data[index.val]?.getD 0

private theorem view_ofFn {arity : Nat} (data : List Nat) (hLength : data.length = arity) :
    List.ofFn (view data : Fin arity → Nat) = data := by
  subst arity
  have h : (view data : Fin data.length → Nat) = fun index => data[index.val] := by
    funext index
    simp only [view, List.getElem?_eq_getElem index.isLt, Option.getD_some]
  rw [h]
  exact List.ofFn_getElem

def inputValues (metadata : Metadata) (position offset : Nat) (request : Request width) : List Nat :=
  BuilderInitialPairedRequest.requestValues metadata position offset
    (BuilderInitialPairedRequest.encodeRequest request)
def inputPrefix (metadata : Metadata) (position offset : Nat) (request : Request width) : List Nat :=
  BuilderInitialPairedRequest.inputValues metadata position offset ++
    [(BuilderInitialPairedRequest.encodeRequest request).1]
def tagFrame (metadata : Metadata) (position offset : Nat) (request : Request width) : List Nat :=
  inputValues metadata position offset request ++ [(BuilderInitialPairedRequest.encodeRequest request).1]

def symbolCode (input : BitString) : Request width → Nat → Nat
  | .blank, _ => 0
  | .fixed value, _ => if value then 2 else 1
  | .sourceBit index, _ => BuilderIndexedInputRead.resultCode input[index]?
  | .certificate _, offset => if offset = 0 then 2 else 1

def resultValues (metadata : Metadata) (position offset : Nat) (request : Request width)
    (input : BitString) : List Nat :=
  inputValues metadata position offset request ++ [symbolCode input request offset]

def fixedValues (value : Bool) : List Nat :=
  [if value then 1 else 0, 1, if value then 2 else 1]

def outputValues (metadata : Metadata) (position offset : Nat) (request : Request width)
    (input : BitString) : List Nat :=
  tagFrame metadata position offset request ++
    match request with
    | .blank => resultValues metadata position offset request input
    | .fixed value => fixedValues value ++ resultValues metadata position offset request input
    | .sourceBit _ => resultValues metadata position offset request input
    | .certificate _ => [offset] ++ resultValues metadata position offset request input

def originalFields (arity : Nat) (h : 9 ≤ arity) : List (BuilderRegisterPack.Field arity) :=
  [.argument ⟨0, by omega⟩, .argument ⟨1, by omega⟩, .argument ⟨2, by omega⟩,
   .argument ⟨3, by omega⟩, .argument ⟨4, by omega⟩, .argument ⟨5, by omega⟩,
   .argument ⟨6, by omega⟩, .argument ⟨7, by omega⟩, .argument ⟨8, by omega⟩]

def tagFields : List (BuilderRegisterPack.Field 9) := [.argument ⟨7, by decide⟩]
def blankFields : List (BuilderRegisterPack.Field 10) :=
  originalFields 10 (by decide) ++ [.constant 0]
def fixedExpression : BuilderRegisterExpression.Expr 10 :=
  .binary .add (.argument ⟨8, by decide⟩) (.constant 1)
def fixedFields : List (BuilderRegisterPack.Field 13) :=
  originalFields 13 (by decide) ++ [.argument ⟨12, by decide⟩]
def sourceFields : List (BuilderRegisterPack.Field 10) := originalFields 10 (by decide)
def offsetFields : List (BuilderRegisterPack.Field 10) := [.argument ⟨6, by decide⟩]
def certificateFields (positive : Bool) : List (BuilderRegisterPack.Field 11) :=
  originalFields 11 (by decide) ++ [.constant (if positive then 2 else 1)]

theorem inputValues_length (metadata : Metadata) (position offset : Nat) (request : Request width) :
    (inputValues metadata position offset request).length = 9 := rfl
theorem inputPrefix_length (metadata : Metadata) (position offset : Nat) (request : Request width) :
    (inputPrefix metadata position offset request).length = 8 := rfl
theorem tagFrame_length (metadata : Metadata) (position offset : Nat) (request : Request width) :
    (tagFrame metadata position offset request).length = 10 := rfl
theorem resultValues_length (metadata : Metadata) (position offset : Nat) (request : Request width)
    (input : BitString) : (resultValues metadata position offset request input).length = 10 := rfl
theorem input_prefix (metadata : Metadata) (position offset : Nat) (request : Request width) :
    inputValues metadata position offset request =
      inputPrefix metadata position offset request ++ [(BuilderInitialPairedRequest.encodeRequest request).2] := rfl
theorem tag_values (metadata : Metadata) (position offset : Nat) (request : Request width) :
    BuilderRegisterPack.values tagFields (view (inputValues metadata position offset request)) =
      [(BuilderInitialPairedRequest.encodeRequest request).1] := rfl
theorem blank_values (metadata : Metadata) (position offset : Nat) (input : BitString) :
    BuilderRegisterPack.values blankFields (view (tagFrame metadata position offset (.blank : Request width))) =
      resultValues metadata position offset (.blank : Request width) input := rfl
theorem fixed_values (metadata : Metadata) (position offset : Nat) (value : Bool) :
    BuilderRegisterExpression.values fixedExpression
      (view (tagFrame metadata position offset (.fixed value : Request width))) = fixedValues value := by
  cases value <;> rfl
theorem fixed_report_values (metadata : Metadata) (position offset : Nat) (value : Bool) (input : BitString) :
    BuilderRegisterPack.values fixedFields
      (view (tagFrame metadata position offset (.fixed value : Request width) ++ fixedValues value)) =
      resultValues metadata position offset (.fixed value : Request width) input := by
  cases value <;> rfl
theorem source_values (metadata : Metadata) (position offset : Nat) (index : Nat) :
    BuilderRegisterPack.values sourceFields (view (tagFrame metadata position offset (.sourceBit index : Request width))) =
      inputValues metadata position offset (.sourceBit index : Request width) := rfl
theorem offset_values (metadata : Metadata) (position offset : Nat) (index : Fin width) :
    BuilderRegisterPack.values offsetFields (view (tagFrame metadata position offset (.certificate index))) =
      [offset] := rfl
theorem certificate_values (metadata : Metadata) (position offset : Nat) (index : Fin width) (input : BitString) :
    BuilderRegisterPack.values (certificateFields (decide (offset = 0)))
      (view (tagFrame metadata position offset (.certificate index) ++ [offset])) =
      resultValues metadata position offset (.certificate index) input := by
  cases offset <;> rfl

def blankNode : Node :=
  {name := 4, program := BuilderRegisterPack.machine blankFields 0, onAccept := .accept, onReject := .dead}

def fixedReportNode : Node :=
  {name := 6, program := BuilderRegisterPack.machine fixedFields 0, onAccept := .accept, onReject := .dead}

def fixedExpressionNode : Node :=
  {name := 5, program := BuilderRegisterExpression.machine fixedExpression 0, onAccept := .node fixedReportNode.reference, onReject := .dead}

def readerNode : Node :=
  {name := 8, program := BuilderIndexedInputRead.machine, onAccept := .accept, onReject := .dead}

def sourcePrepareNode : Node :=
  {name := 7, program := BuilderRegisterPack.machine sourceFields 0, onAccept := .node readerNode.reference, onReject := .dead}

def positiveNode : Node :=
  {name := 11, program := BuilderRegisterPack.machine (certificateFields true) 0, onAccept := .accept, onReject := .dead}

def negativeNode : Node :=
  {name := 12, program := BuilderRegisterPack.machine (certificateFields false) 0, onAccept := .accept, onReject := .dead}

def offsetTestNode : Node :=
  {name := 10, program := BuilderUnaryTagMatch.machine 0, onAccept := .node positiveNode.reference, onReject := .node negativeNode.reference}

def offsetPrepareNode : Node :=
  {name := 9, program := BuilderRegisterPack.machine offsetFields 0, onAccept := .node offsetTestNode.reference, onReject := .dead}

def sourceTestNode : Node :=
  {name := 3, program := BuilderUnaryTagMatch.machine 2, onAccept := .node sourcePrepareNode.reference, onReject := .node offsetPrepareNode.reference}

def fixedTestNode : Node :=
  {name := 2, program := BuilderUnaryTagMatch.machine 1, onAccept := .node fixedExpressionNode.reference, onReject := .node sourceTestNode.reference}

def zeroNode : Node :=
  {name := 1, program := BuilderUnaryTagMatch.machine 0, onAccept := .node blankNode.reference, onReject := .node fixedTestNode.reference}

def tagPrepareNode : Node :=
  {name := 0, program := BuilderRegisterPack.machine tagFields 0, onAccept := .node zeroNode.reference, onReject := .dead}

def graph : Graph :=
  {nodes := [tagPrepareNode, zeroNode, fixedTestNode, sourceTestNode, blankNode, fixedExpressionNode, fixedReportNode, sourcePrepareNode, readerNode, offsetPrepareNode, offsetTestNode, positiveNode, negativeNode], entry := tagPrepareNode.reference}
def machine : WorkMachine := WorkMachineProgramGraph.machine graph

theorem graph_nodes_length : graph.nodes.length = 13 := rfl

private theorem tagPrepare_mem : tagPrepareNode ∈ graph.nodes := List.Mem.head _

private theorem zero_mem : zeroNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.head _)

private theorem fixedTest_mem : fixedTestNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

private theorem sourceTest_mem : sourceTestNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

private theorem blank_mem : blankNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

private theorem fixedExpression_mem : fixedExpressionNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

private theorem fixedReport_mem : fixedReportNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))

private theorem sourcePrepare_mem : sourcePrepareNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))

private theorem reader_mem : readerNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))

private theorem offsetPrepare_mem : offsetPrepareNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

private theorem offsetTest_mem : offsetTestNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))

private theorem positive_mem : positiveNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))

private theorem negative_mem : negativeNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineProgramGraph.QueryDistinct ∧
    WorkMachineProgramGraph.NoRuleAt program program.acceptState ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧
    program.acceptState ≠ program.rejectState

private theorem pack_good {arity : Nat} (fields : List (BuilderRegisterPack.Field arity)) :
    Good (BuilderRegisterPack.machine fields 0) :=
  ⟨BuilderRegisterPack.rules_pairwise_query_distinct fields 0,
    BuilderRegisterPack.noRuleAtAccept fields 0, BuilderRegisterPack.noRuleAtReject fields 0,
    BuilderRegisterPack.acceptState_ne_rejectState fields 0⟩

private theorem expression_good {arity : Nat} (expression : BuilderRegisterExpression.Expr arity) :
    Good (BuilderRegisterExpression.machine expression 0) :=
  ⟨BuilderRegisterExpression.rules_pairwise_query_distinct expression 0,
    BuilderRegisterExpression.noRuleAtAccept expression 0, BuilderRegisterExpression.noRuleAtReject expression 0,
    BuilderRegisterExpression.acceptState_ne_rejectState expression 0⟩

private theorem tag_good (expected : Nat) : Good (BuilderUnaryTagMatch.machine expected) :=
  ⟨BuilderUnaryTagMatch.rules_pairwise_query_distinct expected, BuilderUnaryTagMatch.noRuleAtAccept expected,
    BuilderUnaryTagMatch.noRuleAtReject expected, BuilderUnaryTagMatch.acceptState_ne_rejectState expected⟩
private theorem reader_good : Good BuilderIndexedInputRead.machine :=
  ⟨BuilderIndexedInputRead.rules_pairwise_query_distinct, BuilderIndexedInputRead.noRuleAtAccept,
    BuilderIndexedInputRead.noRuleAtReject, BuilderIndexedInputRead.acceptState_ne_rejectState⟩

theorem graph_wellFormed : graph.WellFormed := by
  have hNames : (graph.nodes.map Node.name).Pairwise (fun a b : Nat => a ≠ b) := by
    change ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] : List Nat).Pairwise _
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.pairwise_map] using hNames
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact pack_good tagFields
    · exact tag_good 0
    · exact tag_good 1
    · exact tag_good 2
    · exact pack_good blankFields
    · exact expression_good fixedExpression
    · exact pack_good fixedFields
    · exact pack_good sourceFields
    · exact reader_good
    · exact pack_good offsetFields
    · exact tag_good 0
    · exact pack_good (certificateFields true)
    · exact pack_good (certificateFields false)
  · exact ⟨tagPrepareNode, tagPrepare_mem, rfl, rfl⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨zeroNode, zero_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨blankNode, blank_mem, rfl, rfl⟩, ⟨fixedTestNode, fixedTest_mem, rfl, rfl⟩⟩
    · exact ⟨⟨fixedExpressionNode, fixedExpression_mem, rfl, rfl⟩, ⟨sourceTestNode, sourceTest_mem, rfl, rfl⟩⟩
    · exact ⟨⟨sourcePrepareNode, sourcePrepare_mem, rfl, rfl⟩, ⟨offsetPrepareNode, offsetPrepare_mem, rfl, rfl⟩⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨⟨fixedReportNode, fixedReport_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨⟨readerNode, reader_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨⟨offsetTestNode, offsetTest_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨positiveNode, positive_mem, rfl, rfl⟩, ⟨negativeNode, negative_mem, rfl, rfl⟩⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨True.intro, True.intro⟩

private theorem pack_run {arity : Nat} (fields : List (BuilderRegisterPack.Field arity))
    (data older : List Nat) (inside : List WorkSymbol) (hLength : data.length = arity) :
    workRunExact? (BuilderRegisterPack.machine fields 0)
      (BuilderRegisterPack.workSteps fields (view data) [])
      (workStartConfiguration (BuilderRegisterPack.machine fields 0) (endTape (older ++ data) inside [])) =
      some {
        state := (BuilderRegisterPack.machine fields 0).acceptState
        tape := endTape (older ++ data ++ BuilderRegisterPack.values fields (view data)) inside [] } := by
  have h := BuilderRegisterPack.workRunExact fields 0 older (view data) [] inside [] rfl
  simpa only [BuilderRegisterPack.initialConfiguration, BuilderRegisterPack.finalConfiguration,
    view_ofFn data hLength, List.append_nil, List.drop_nil] using h

private theorem expression_run {arity : Nat} (expression : BuilderRegisterExpression.Expr arity)
    (data older : List Nat) (inside : List WorkSymbol) (hLength : data.length = arity) :
    workRunExact? (BuilderRegisterExpression.machine expression 0)
      (BuilderRegisterExpression.workSteps expression (view data) [])
      (workStartConfiguration (BuilderRegisterExpression.machine expression 0) (endTape (older ++ data) inside [])) =
      some {
        state := (BuilderRegisterExpression.machine expression 0).acceptState
        tape := endTape (older ++ data ++ BuilderRegisterExpression.values expression (view data)) inside [] } := by
  have h := BuilderRegisterExpression.workRunExact expression 0 older (view data) [] inside [] rfl
  simpa only [BuilderRegisterExpression.initialConfiguration, BuilderRegisterExpression.finalConfiguration,
    view_ofFn data hLength, List.append_nil, List.drop_nil] using h

private theorem pack_bounds {arity : Nat} (fields : List (BuilderRegisterPack.Field arity))
    (data older : List Nat) (bound : NatPolynomial) (inputLength : Nat)
    (hLength : data.length = arity)
    (hSpan : (registerWord (older ++ data)).length ≤ bound.eval inputLength) :
    (registerWord (older ++ data ++ BuilderRegisterPack.values fields (view data))).length ≤
        (BuilderRegisterPack.spanPolynomial fields bound).eval inputLength ∧
      6 * BuilderRegisterPack.workSteps fields (view data) [] ≤
        (BuilderRegisterPack.rawTimePolynomial fields bound).eval inputLength := by
  have h := BuilderRegisterPack.source_polynomial_bounds fields bound inputLength older (view data) [] (by
    simpa only [view_ofFn data hLength, List.append_nil] using hSpan)
  simpa only [view_ofFn data hLength, List.append_nil] using h

private theorem expression_bounds {arity : Nat} (expression : BuilderRegisterExpression.Expr arity)
    (data older : List Nat) (bound : NatPolynomial) (inputLength : Nat)
    (hLength : data.length = arity)
    (hSpan : (registerWord (older ++ data)).length ≤ bound.eval inputLength) :
    (registerWord (older ++ data ++ BuilderRegisterExpression.values expression (view data))).length ≤
        (BuilderRegisterExpression.spanPolynomial expression bound).eval inputLength ∧
      6 * BuilderRegisterExpression.workSteps expression (view data) [] ≤
        (BuilderRegisterExpression.rawTimePolynomial expression bound).eval inputLength := by
  have h := BuilderRegisterExpression.source_polynomial_bounds expression bound inputLength older (view data) [] (by
    simpa only [view_ofFn data hLength, List.append_nil] using hSpan)
  simpa only [view_ofFn data hLength, List.append_nil] using h

def tagSteps (metadata : Metadata) (position offset : Nat) (request : Request width) : Nat :=
  BuilderRegisterPack.workSteps tagFields (view (inputValues metadata position offset request)) []
def blankSteps {width : Nat} (metadata : Metadata) (position offset : Nat) : Nat :=
  BuilderRegisterPack.workSteps blankFields (view (tagFrame metadata position offset (.blank : Request width))) []
def fixedExpressionSteps {width : Nat} (metadata : Metadata) (position offset : Nat) (value : Bool) : Nat :=
  BuilderRegisterExpression.workSteps fixedExpression
    (view (tagFrame metadata position offset (.fixed value : Request width))) []
def fixedReportSteps {width : Nat} (metadata : Metadata) (position offset : Nat) (value : Bool) : Nat :=
  BuilderRegisterPack.workSteps fixedFields
    (view (tagFrame metadata position offset (.fixed value : Request width) ++ fixedValues value)) []
def sourcePrepareSteps {width : Nat} (metadata : Metadata) (position offset index : Nat) : Nat :=
  BuilderRegisterPack.workSteps sourceFields
    (view (tagFrame metadata position offset (.sourceBit index : Request width))) []
def readerSteps {width : Nat} (metadata : Metadata) (position offset index : Nat) (older : List Nat) (input : BitString) : Nat :=
  BuilderIndexedInputRead.workSteps
    (older ++ tagFrame metadata position offset (.sourceBit index : Request width) ++
      inputPrefix metadata position offset (.sourceBit index : Request width)) index input
def offsetPrepareSteps (metadata : Metadata) (position offset : Nat) (index : Fin width) : Nat :=
  BuilderRegisterPack.workSteps offsetFields (view (tagFrame metadata position offset (.certificate index))) []
def certificateReportSteps (metadata : Metadata) (position offset : Nat) (index : Fin width) : Nat :=
  BuilderRegisterPack.workSteps (certificateFields (decide (offset = 0)))
    (view (tagFrame metadata position offset (.certificate index) ++ [offset])) []

def branchSteps (metadata : Metadata) (position offset : Nat) (request : Request width)
    (older : List Nat) (input : BitString) : Nat :=
  match request with
  | .blank => blankSteps (width := width) metadata position offset + 1
  | .fixed value => 5 + 1 + (fixedExpressionSteps (width := width) metadata position offset value + 1 +
      (fixedReportSteps (width := width) metadata position offset value + 1))
  | .sourceBit index => 5 + 1 + (7 + 1 + (sourcePrepareSteps (width := width) metadata position offset index + 1 +
      (readerSteps (width := width) metadata position offset index older input + 1)))
  | .certificate index => 5 + 1 + (7 + 1 + (offsetPrepareSteps metadata position offset index + 1 +
      (3 + 1 + (certificateReportSteps metadata position offset index + 1))))

def workSteps (metadata : Metadata) (position offset : Nat) (request : Request width)
    (older : List Nat) (input : BitString) : Nat :=
  tagSteps metadata position offset request + 1 + (3 + 1 + branchSteps metadata position offset request older input)

def initialConfiguration (metadata : Metadata) (position offset : Nat) (request : Request width)
    (older : List Nat) (input : BitString) (output : List CNFToken) : WorkConfiguration :=
  workStartConfiguration machine (endTape (older ++ inputValues metadata position offset request) (inside input output) [])
def finalConfiguration (metadata : Metadata) (position offset : Nat) (request : Request width)
    (older : List Nat) (input : BitString) (output : List CNFToken) : WorkConfiguration :=
  {state := machine.acceptState, tape := endTape (older ++ outputValues metadata position offset request input)
    (inside input output) []}

private theorem source_run (metadata : Metadata) (position offset index : Nat)
    (older : List Nat) (input : BitString) (output : List CNFToken) :
    workRunExact? BuilderIndexedInputRead.machine
      (readerSteps (width := width) metadata position offset index older input)
      (workStartConfiguration BuilderIndexedInputRead.machine
        (endTape (older ++ tagFrame metadata position offset (.sourceBit index : Request width) ++
          inputValues metadata position offset (.sourceBit index : Request width)) (inside input output) [])) =
      some {
        state := BuilderIndexedInputRead.machine.acceptState
        tape := endTape (older ++ tagFrame metadata position offset (.sourceBit index : Request width) ++
          resultValues metadata position offset (.sourceBit index : Request width) input) (inside input output) [] } := by
  have h := BuilderIndexedInputRead.workRunExact
    (older ++ tagFrame metadata position offset (.sourceBit index : Request width) ++
      inputPrefix metadata position offset (.sourceBit index : Request width)) index input output []
  simpa only [BuilderIndexedInputRead.initialConfiguration, BuilderIndexedInputRead.finalConfiguration,
    readerSteps, resultValues, input_prefix, BuilderInitialPairedRequest.encodeRequest, symbolCode,
    List.drop_nil, List.append_assoc, List.cons_append, List.nil_append] using h

private theorem tag_zero (actual : Nat) : BuilderUnaryTagMatch.workSteps 0 actual = 3 := by
  simp only [BuilderUnaryTagMatch.workSteps, Nat.min_zero, Nat.mul_zero, Nat.zero_add]
private theorem tag_one_one : BuilderUnaryTagMatch.workSteps 1 1 = 5 := by decide
private theorem tag_one_two : BuilderUnaryTagMatch.workSteps 1 2 = 5 := by decide
private theorem tag_one_three : BuilderUnaryTagMatch.workSteps 1 3 = 5 := by decide
private theorem tag_two_two : BuilderUnaryTagMatch.workSteps 2 2 = 7 := by decide
private theorem tag_two_three : BuilderUnaryTagMatch.workSteps 2 3 = 7 := by decide

private theorem tail_path (metadata : Metadata) (position offset : Nat) (request : Request width)
    (older : List Nat) (input : BitString) (output : List CNFToken) :
    AcceptPath graph (.node zeroNode.reference) .accept
      (3 + 1 + branchSteps metadata position offset request older input)
      (endTape (older ++ tagFrame metadata position offset request) (inside input output) [])
      (endTape (older ++ outputValues metadata position offset request input) (inside input output) []) := by
  cases request with
  | blank =>
      have hPack := pack_run blankFields (tagFrame metadata position offset (.blank : Request width))
        older (inside input output) rfl
      rw [blank_values metadata position offset input] at hPack
      have hP := AcceptPath.step blankNode .accept _ 0 _ _ _ blank_mem hPack (.terminal .accept _)
      have hTest := BuilderUnaryTagMatch.accept_workRunExact 0
        (older ++ inputValues metadata position offset (.blank : Request width)) (inside input output) []
      simp only [List.append_assoc] at hTest
      have hT := AcceptPath.step zeroNode .accept _ _ _ _ _ zero_mem hTest hP
      simpa only [branchSteps, blankSteps, outputValues, tagFrame, tag_zero, tag_one_one, tag_one_two, tag_one_three, tag_two_two, tag_two_three,
        BuilderInitialPairedRequest.encodeRequest,
        List.append_assoc, Nat.add_zero] using hT
  | fixed value =>
      have hPack := pack_run fixedFields
        (tagFrame metadata position offset (.fixed value : Request width) ++ fixedValues value)
        older (inside input output) rfl
      rw [fixed_report_values metadata position offset value input] at hPack
      simp only [List.append_assoc] at hPack
      have hP := AcceptPath.step fixedReportNode .accept _ 0 _ _ _ fixedReport_mem hPack (.terminal .accept _)
      have hExpr := expression_run fixedExpression (tagFrame metadata position offset (.fixed value : Request width))
        older (inside input output) rfl
      rw [fixed_values] at hExpr
      simp only [List.append_assoc] at hExpr
      have hE := AcceptPath.step fixedExpressionNode .accept _ _ _ _ _ fixedExpression_mem hExpr hP
      have hOne := BuilderUnaryTagMatch.accept_workRunExact 1
        (older ++ inputValues metadata position offset (.fixed value : Request width)) (inside input output) []
      simp only [List.append_assoc] at hOne
      have hO := AcceptPath.step fixedTestNode .accept _ _ _ _ _ fixedTest_mem hOne hE
      have hZero := BuilderUnaryTagMatch.reject_workRunExact 0 1
        (older ++ inputValues metadata position offset (.fixed value : Request width)) (inside input output) [] (by decide)
      simp only [List.append_assoc] at hZero
      have hZ := AcceptPath.stepReject zeroNode .accept _ _ _ _ _ zero_mem hZero hO
      simpa only [branchSteps, fixedExpressionSteps, fixedReportSteps, outputValues, tagFrame,
        tag_zero, tag_one_one, tag_one_two, tag_one_three, tag_two_two, tag_two_three,
        BuilderInitialPairedRequest.encodeRequest, List.append_assoc, Nat.add_zero] using hZ
  | sourceBit index =>
      have hRead := source_run (width := width) metadata position offset index older input output
      simp only [List.append_assoc] at hRead
      have hR := AcceptPath.step readerNode .accept _ 0 _ _ _ reader_mem hRead (.terminal .accept _)
      have hPack := pack_run sourceFields (tagFrame metadata position offset (.sourceBit index : Request width))
        older (inside input output) rfl
      rw [source_values] at hPack
      simp only [List.append_assoc] at hPack
      have hP := AcceptPath.step sourcePrepareNode .accept _ _ _ _ _ sourcePrepare_mem hPack hR
      have hTwo := BuilderUnaryTagMatch.accept_workRunExact 2
        (older ++ inputValues metadata position offset (.sourceBit index : Request width)) (inside input output) []
      simp only [List.append_assoc] at hTwo
      have hT := AcceptPath.step sourceTestNode .accept _ _ _ _ _ sourceTest_mem hTwo hP
      have hOne := BuilderUnaryTagMatch.reject_workRunExact 1 2
        (older ++ inputValues metadata position offset (.sourceBit index : Request width)) (inside input output) [] (by decide)
      simp only [List.append_assoc] at hOne
      have hO := AcceptPath.stepReject fixedTestNode .accept _ _ _ _ _ fixedTest_mem hOne hT
      have hZero := BuilderUnaryTagMatch.reject_workRunExact 0 2
        (older ++ inputValues metadata position offset (.sourceBit index : Request width)) (inside input output) [] (by decide)
      simp only [List.append_assoc] at hZero
      have hZ := AcceptPath.stepReject zeroNode .accept _ _ _ _ _ zero_mem hZero hO
      simpa only [branchSteps, sourcePrepareSteps, outputValues, tagFrame, tag_zero, tag_one_one, tag_one_two, tag_one_three, tag_two_two, tag_two_three,
        BuilderInitialPairedRequest.encodeRequest,
        List.append_assoc, Nat.add_zero] using hZ
  | certificate index =>
      have hEnd : AcceptPath graph (.node offsetTestNode.reference) .accept
          (3 + 1 + (certificateReportSteps metadata position offset index + 1))
          (endTape (older ++ tagFrame metadata position offset (.certificate index) ++ [offset]) (inside input output) [])
          (endTape (older ++ outputValues metadata position offset (.certificate index) input) (inside input output) []) := by
        have hPack := pack_run (certificateFields (decide (offset = 0)))
          (tagFrame metadata position offset (.certificate index) ++ [offset]) older (inside input output) rfl
        rw [certificate_values metadata position offset index input] at hPack
        simp only [List.append_assoc] at hPack
        cases offset with
        | zero =>
            have hP := AcceptPath.step positiveNode .accept _ 0 _ _ _ positive_mem hPack (.terminal .accept _)
            have hZero := BuilderUnaryTagMatch.accept_workRunExact 0
              (older ++ tagFrame metadata position 0 (.certificate index)) (inside input output) []
            simp only [List.append_assoc] at hZero
            have hZ := AcceptPath.step offsetTestNode .accept _ _ _ _ _ offsetTest_mem hZero hP
            simpa only [certificateReportSteps, outputValues, tag_zero, tag_one_one, tag_one_two, tag_one_three, tag_two_two, tag_two_three,
        BuilderInitialPairedRequest.encodeRequest,
              List.append_assoc, Nat.add_zero] using hZ
        | succ offset =>
            have hP := AcceptPath.step negativeNode .accept _ 0 _ _ _ negative_mem hPack (.terminal .accept _)
            have hZero := BuilderUnaryTagMatch.reject_workRunExact 0 (offset + 1)
              (older ++ tagFrame metadata position (offset + 1) (.certificate index)) (inside input output) [] (by omega)
            simp only [List.append_assoc] at hZero
            have hZ := AcceptPath.stepReject offsetTestNode .accept _ _ _ _ _ offsetTest_mem hZero hP
            simpa only [certificateReportSteps, outputValues, tag_zero, tag_one_one, tag_one_two, tag_one_three, tag_two_two, tag_two_three,
        BuilderInitialPairedRequest.encodeRequest,
              Nat.min_zero, Nat.mul_zero, Nat.zero_add, List.append_assoc, Nat.add_zero] using hZ
      have hPack := pack_run offsetFields (tagFrame metadata position offset (.certificate index))
        older (inside input output) rfl
      rw [offset_values] at hPack
      simp only [List.append_assoc] at hPack hEnd
      have hP := AcceptPath.step offsetPrepareNode .accept _ _ _ _ _ offsetPrepare_mem hPack hEnd
      have hTwo := BuilderUnaryTagMatch.reject_workRunExact 2 3
        (older ++ inputValues metadata position offset (.certificate index)) (inside input output) [] (by decide)
      simp only [List.append_assoc] at hTwo
      have hT := AcceptPath.stepReject sourceTestNode .accept _ _ _ _ _ sourceTest_mem hTwo hP
      have hOne := BuilderUnaryTagMatch.reject_workRunExact 1 3
        (older ++ inputValues metadata position offset (.certificate index)) (inside input output) [] (by decide)
      simp only [List.append_assoc] at hOne
      have hO := AcceptPath.stepReject fixedTestNode .accept _ _ _ _ _ fixedTest_mem hOne hT
      have hZero := BuilderUnaryTagMatch.reject_workRunExact 0 3
        (older ++ inputValues metadata position offset (.certificate index)) (inside input output) [] (by decide)
      simp only [List.append_assoc] at hZero
      have hZ := AcceptPath.stepReject zeroNode .accept _ _ _ _ _ zero_mem hZero hO
      simpa only [branchSteps, offsetPrepareSteps, outputValues, tagFrame, tag_zero, tag_one_one, tag_one_two, tag_one_three, tag_two_two, tag_two_three,
        BuilderInitialPairedRequest.encodeRequest,
        List.append_assoc] using hZ

/-- All runtime requests are resolved by the fixed program; input bits are read from tape. -/
theorem workRunExact (metadata : Metadata) (position offset : Nat) (request : Request width)
    (older : List Nat) (input : BitString) (output : List CNFToken) :
    workRunExact? machine (workSteps metadata position offset request older input)
      (initialConfiguration metadata position offset request older input output) =
      some (finalConfiguration metadata position offset request older input output) := by
  have hTail := tail_path metadata position offset request older input output
  have hPack := pack_run tagFields (inputValues metadata position offset request) older (inside input output) rfl
  rw [tag_values] at hPack
  simp only [tagFrame, List.append_assoc] at hTail hPack
  have hP := AcceptPath.step tagPrepareNode .accept _ _ _ _ _ tagPrepare_mem hPack hTail
  have h := WorkMachineProgramPath.runExact graph _ _ _ _ _ graph_wellFormed hP
  have hStart (tape : WorkTape) :
      WorkMachineProgramGraph.endpointConfiguration (.node tagPrepareNode.reference) tape =
        workStartConfiguration machine tape := rfl
  have hMachine : WorkMachineProgramGraph.machine graph = machine := rfl
  have hAccept (tape : WorkTape) :
      WorkMachineProgramGraph.endpointConfiguration .accept tape = {state := machine.acceptState, tape := tape} := rfl
  rw [hStart, hMachine, hAccept] at h
  simpa only [workSteps, tagSteps, initialConfiguration, finalConfiguration, List.append_assoc] using h

theorem run_compile_exact (metadata : Metadata) (position offset : Nat) (request : Request width)
    (older : List Nat) (input : BitString) (output : List CNFToken) :
    run (compileWorkMachine machine) (6 * workSteps metadata position offset request older input)
      (encodeWorkConfiguration (initialConfiguration metadata position offset request older input output)) =
      encodeWorkConfiguration (finalConfiguration metadata position offset request older input output) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact metadata position offset request older input output)
theorem final_tape (metadata : Metadata) (position offset : Nat) (request : Request width)
    (older : List Nat) (input : BitString) (output : List CNFToken) :
    (finalConfiguration metadata position offset request older input output).tape =
      endTape (older ++ outputValues metadata position offset request input) (inside input output) [] := rfl
theorem final_frontier (metadata : Metadata) (position offset : Nat) (request : Request width)
    (older : List Nat) (input : BitString) (output : List CNFToken) :
    (finalConfiguration metadata position offset request older input output).tape.left = [] := rfl
theorem final_accept (metadata : Metadata) (position offset : Nat) (request : Request width)
    (older : List Nat) (input : BitString) (output : List CNFToken) :
    (finalConfiguration metadata position offset request older input output).state = machine.acceptState := rfl

theorem output_suffix (metadata : Metadata) (position offset : Nat) (request : Request width) (input : BitString) :
    ∃ history : List Nat, outputValues metadata position offset request input =
      history ++ resultValues metadata position offset request input := by
  cases request with
  | blank => exact ⟨_, rfl⟩
  | fixed value => exact ⟨tagFrame metadata position offset (.fixed value : Request width) ++ fixedValues value,
      (List.append_assoc _ _ _).symm⟩
  | sourceBit index => exact ⟨_, rfl⟩
  | certificate index => exact ⟨tagFrame metadata position offset (.certificate index) ++ [offset],
      (List.append_assoc _ _ _).symm⟩

theorem symbolCode_le (input : BitString) (request : Request width) (offset : Nat) :
    symbolCode input request offset ≤ 2 := by
  cases request with
  | blank => exact Nat.zero_le 2
  | fixed value =>
      cases value with
      | false => exact (by decide : (1 : Nat) ≤ 2)
      | true => exact Nat.le_refl 2
  | sourceBit index => exact BuilderIndexedInputRead.resultCode_le _
  | certificate index =>
      cases offset with
      | zero => exact Nat.le_refl 2
      | succ offset => exact (by decide : (1 : Nat) ≤ 2)

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise graph graph_wellFormed
theorem noRuleAtAccept : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState :=
  WorkMachineProgramGraph.noRuleAt_globalAccept graph
theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  WorkMachineProgramGraph.noRuleAt_globalReject graph
theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := by
  change (0 : Nat) ≠ 1
  decide

def tagSpan (bound : NatPolynomial) : NatPolynomial := BuilderRegisterPack.spanPolynomial tagFields bound
def blankSpan (bound : NatPolynomial) : NatPolynomial := BuilderRegisterPack.spanPolynomial blankFields (tagSpan bound)
def fixedSpan (bound : NatPolynomial) : NatPolynomial := BuilderRegisterExpression.spanPolynomial fixedExpression (tagSpan bound)
def fixedResultSpan (bound : NatPolynomial) : NatPolynomial := BuilderRegisterPack.spanPolynomial fixedFields (fixedSpan bound)
def sourcePackedSpan (bound : NatPolynomial) : NatPolynomial := BuilderRegisterPack.spanPolynomial sourceFields (tagSpan bound)
def sourceSpan (bound : NatPolynomial) : NatPolynomial := .add (sourcePackedSpan bound) (.constant 3)
def offsetSpan (bound : NatPolynomial) : NatPolynomial := BuilderRegisterPack.spanPolynomial offsetFields (tagSpan bound)
def certificateSpan (positive : Bool) (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterPack.spanPolynomial (certificateFields positive) (offsetSpan bound)
def spanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (blankSpan bound) (.add (fixedResultSpan bound)
    (.add (sourceSpan bound) (.add (certificateSpan true bound) (certificateSpan false bound))))
def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (BuilderRegisterPack.rawTimePolynomial tagFields bound)
    (.add (BuilderRegisterPack.rawTimePolynomial blankFields (tagSpan bound))
    (.add (BuilderRegisterExpression.rawTimePolynomial fixedExpression (tagSpan bound))
    (.add (BuilderRegisterPack.rawTimePolynomial fixedFields (fixedSpan bound))
    (.add (BuilderRegisterPack.rawTimePolynomial sourceFields (tagSpan bound))
    (.add (BuilderIndexedInputRead.rawTimePolynomial (sourcePackedSpan bound))
    (.add (BuilderRegisterPack.rawTimePolynomial offsetFields (tagSpan bound))
    (.add (BuilderRegisterPack.rawTimePolynomial (certificateFields true) (offsetSpan bound))
    (.add (BuilderRegisterPack.rawTimePolynomial (certificateFields false) (offsetSpan bound))
      (.constant 150)))))))))

private theorem reader_bounds (older : List Nat) (index : Nat) (input : BitString)
    (bound : NatPolynomial) (inputSize : Nat)
    (hSpan : (registerWord (older ++ [index])).length ≤ bound.eval inputSize) :
    (registerWord (older ++ [index, BuilderIndexedInputRead.resultCode input[index]?])).length ≤
        (.add bound (.constant 3) : NatPolynomial).eval inputSize ∧
      6 * BuilderIndexedInputRead.workSteps older index input ≤
        (BuilderIndexedInputRead.rawTimePolynomial bound).eval inputSize := by
  have hLength : (registerWord (older ++ [index])).length = (registerWord older).length + index + 1 := by
    simp only [registerWord_append, List.length_append, registerWord_length,
      List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
    omega
  have hIncrease := BuilderIndexedInputRead.register_span_increase_le older index input
  constructor
  · simp only [NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega
  · rw [BuilderIndexedInputRead.rawTimePolynomial_eval]
    apply Nat.mul_le_mul_left 6
    apply Nat.le_trans (BuilderIndexedInputRead.workSteps_le older index input)
    apply Nat.mul_le_mul <;> omega

/-- Every actual tag test, copy, indexed scan, retained register and graph bridge is charged. -/
theorem source_polynomial_bounds (metadata : Metadata) (position offset : Nat) (request : Request width)
    (older : List Nat) (input : BitString) (bound : NatPolynomial) (inputSize : Nat)
    (hSpan : (registerWord (older ++ inputValues metadata position offset request)).length ≤ bound.eval inputSize) :
    (registerWord (older ++ outputValues metadata position offset request input)).length ≤
        (spanPolynomial bound).eval inputSize ∧
      6 * workSteps metadata position offset request older input ≤
        (rawTimePolynomial bound).eval inputSize := by
  have hPack := pack_bounds tagFields (inputValues metadata position offset request) older bound inputSize rfl hSpan
  rw [tag_values] at hPack
  have hTag : (registerWord (older ++ tagFrame metadata position offset request)).length ≤
      (tagSpan bound).eval inputSize := by
    simpa only [tagFrame, tagSpan, List.append_assoc] using hPack.1
  cases request with
  | blank =>
      have hBlank := pack_bounds blankFields (tagFrame metadata position offset (.blank : Request width))
        older (tagSpan bound) inputSize rfl hTag
      rw [blank_values metadata position offset input] at hBlank
      constructor
      · have hFinal : (registerWord (older ++ outputValues metadata position offset (.blank : Request width) input)).length ≤
            (blankSpan bound).eval inputSize := by
          simpa only [outputValues, blankSpan, List.append_assoc] using hBlank.1
        simp only [spanPolynomial, NatPolynomial.eval_add]
        omega
      · simp only [workSteps, branchSteps, tagSteps, blankSteps, rawTimePolynomial,
          NatPolynomial.eval_add, NatPolynomial.eval_constant]
        omega
  | fixed value =>
      have hExpr := expression_bounds fixedExpression
        (tagFrame metadata position offset (.fixed value : Request width)) older (tagSpan bound) inputSize rfl hTag
      rw [fixed_values] at hExpr
      have hReport := pack_bounds fixedFields
        (tagFrame metadata position offset (.fixed value : Request width) ++ fixedValues value)
        older (fixedSpan bound) inputSize rfl (by simpa only [fixedSpan, List.append_assoc] using hExpr.1)
      rw [fixed_report_values metadata position offset value input] at hReport
      constructor
      · have hFinal : (registerWord (older ++ outputValues metadata position offset (.fixed value : Request width) input)).length ≤
            (fixedResultSpan bound).eval inputSize := by
          simpa only [outputValues, fixedResultSpan, List.append_assoc] using hReport.1
        simp only [spanPolynomial, NatPolynomial.eval_add]
        omega
      · simp only [workSteps, branchSteps, tagSteps, fixedExpressionSteps, fixedReportSteps,
          rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
        omega
  | sourceBit index =>
      have hSource := pack_bounds sourceFields (tagFrame metadata position offset (.sourceBit index : Request width))
        older (tagSpan bound) inputSize rfl hTag
      rw [source_values] at hSource
      have hRead := reader_bounds
        (older ++ tagFrame metadata position offset (.sourceBit index : Request width) ++
          inputPrefix metadata position offset (.sourceBit index : Request width)) index input
        (sourcePackedSpan bound) inputSize (by
          simpa only [sourcePackedSpan, input_prefix, BuilderInitialPairedRequest.encodeRequest, List.append_assoc] using hSource.1)
      constructor
      · have hFinal : (registerWord (older ++ outputValues metadata position offset (.sourceBit index : Request width) input)).length ≤
            (sourceSpan bound).eval inputSize := by
          simpa only [outputValues, resultValues, input_prefix, symbolCode,
            BuilderInitialPairedRequest.encodeRequest, sourceSpan, List.append_assoc,
            List.cons_append, List.nil_append] using hRead.1
        simp only [spanPolynomial, NatPolynomial.eval_add]
        omega
      · simp only [workSteps, branchSteps, tagSteps, sourcePrepareSteps, readerSteps,
          rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
        omega
  | certificate index =>
      have hOffset := pack_bounds offsetFields (tagFrame metadata position offset (.certificate index))
        older (tagSpan bound) inputSize rfl hTag
      rw [offset_values] at hOffset
      have hReport := pack_bounds (certificateFields (decide (offset = 0)))
        (tagFrame metadata position offset (.certificate index) ++ [offset])
        older (offsetSpan bound) inputSize rfl (by simpa only [offsetSpan, List.append_assoc] using hOffset.1)
      rw [certificate_values metadata position offset index input] at hReport
      cases offset with
      | zero =>
          have hFlag : decide ((0 : Nat) = 0) = true := rfl
          have hTrue : decide True = true := rfl
          rw [hFlag] at hReport
          constructor
          · have hFinal : (registerWord (older ++ outputValues metadata position 0 (.certificate index) input)).length ≤
                (certificateSpan true bound).eval inputSize := by
              simpa only [outputValues, certificateSpan, List.append_assoc] using hReport.1
            simp only [spanPolynomial, NatPolynomial.eval_add]
            omega
          · simp only [workSteps, branchSteps, tagSteps, offsetPrepareSteps, certificateReportSteps,
              rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant, hTrue]
            omega
      | succ offset =>
          have hFlag : decide (offset + 1 = 0) = false := rfl
          rw [hFlag] at hReport
          constructor
          · have hFinal : (registerWord (older ++ outputValues metadata position (offset + 1) (.certificate index) input)).length ≤
                (certificateSpan false bound).eval inputSize := by
              simpa only [outputValues, certificateSpan, List.append_assoc] using hReport.1
            simp only [spanPolynomial, NatPolynomial.eval_add]
            omega
          · simp only [workSteps, branchSteps, tagSteps, offsetPrepareSteps, certificateReportSteps,
              rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant, hFlag]
            omega

theorem result_span_le_output (metadata : Metadata) (position offset : Nat) (request : Request width) (input : BitString) :
    (registerWord (resultValues metadata position offset request input)).length ≤
      (registerWord (outputValues metadata position offset request input)).length := by
  obtain ⟨history, h⟩ := output_suffix metadata position offset request input
  rw [h, registerWord_append, List.length_append]
  omega

theorem blank_code (input : BitString) (offset : Nat) : symbolCode input (.blank : Request width) offset = 0 := rfl
theorem fixed_code (input : BitString) (value : Bool) (offset : Nat) :
    symbolCode input (.fixed value : Request width) offset =
      VariableLayout.tapeSymbolCode (symbolOfFixedBit value) := by
  cases value <;> rfl
theorem source_code (input : BitString) (index offset : Nat) :
    symbolCode input (.sourceBit index : Request width) offset =
      VariableLayout.tapeSymbolCode (BuilderInitialConstraintPayload.sourceSymbol input[index]?) :=
  (BuilderInitialConstraintPayload.sourceSymbol_code _).symm
theorem certificate_positive_code (input : BitString) (index : Fin width) :
    symbolCode input (.certificate index) 0 = VariableLayout.tapeSymbolCode .one := rfl
theorem certificate_negative_code (input : BitString) (index : Fin width) (offset : Nat) :
    symbolCode input (.certificate index) (offset + 1) = VariableLayout.tapeSymbolCode .zero := rfl

end PNP.Concrete.CookLevin.BuilderInitialRequestResolution
