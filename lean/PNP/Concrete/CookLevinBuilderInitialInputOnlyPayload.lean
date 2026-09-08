/-
Copyright (c) 2026 PNP Labs.

Uniform physical input-only initial-cell payload construction. Runtime
comparisons remove the two prefix entries, detect padding and derive source
offsets; the existing resolver reads the actual input. Literal arithmetic and
packing preserve the canonical blank/bit/padding distinction. This is a
family component, not the complete formula builder or reduction.
-/

import PNP.Concrete.CookLevinBuilderInitialRequestResolution
import PNP.Concrete.CookLevinBuilderInitialCellDecoder

namespace PNP.Concrete.CookLevin.BuilderInitialInputOnlyPayload

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape inside)
open BuilderInitialCellCoordinates (Request)
open BuilderInitialCellDecoder (comparisonValues residual)
open BuilderArbitrarySlotHeaderRouter
open WorkMachineProgramGraph (Node Endpoint Graph)
open WorkMachineProgramPath (AcceptPath)

structure Data where
  inputLength : Nat
  fuel : Nat
  tapeWidth : Nat
  coordinate : Nat
  deriving DecidableEq

def dataValues (data : Data) : List Nat :=
  [data.inputLength, data.fuel, data.tapeWidth, data.coordinate]
def position (data : Data) : Nat := data.coordinate - 2
def metadata (data : Data) : BuilderInitialRequestResolution.Metadata :=
  {inputLength := data.inputLength, fuel := data.fuel, length := 0,
   rowWidth := data.tapeWidth, remaining := 0}
def request (data : Data) : Request 0 :=
  if position data < data.fuel then .blank else .sourceBit (position data - data.fuel)
def code (data : Data) (input : BitString) : Nat :=
  BuilderInitialRequestResolution.symbolCode input (request data) 0
def indexValue (data : Data) (input : BitString) : Nat := position data * 3 + code data input
def payloadValues (data : Data) (input : BitString) : List Nat := [indexValue data input, 1, 2]

def prefixStage (data : Data) : List Nat :=
  dataValues data ++ comparisonValues data.coordinate 2
def widthStage (data : Data) : List Nat :=
  prefixStage data ++ comparisonValues (position data) data.tapeWidth
def centerStage (data : Data) : List Nat :=
  widthStage data ++ comparisonValues (position data) data.fuel
def requestValues (data : Data) : List Nat :=
  BuilderInitialRequestResolution.inputValues (metadata data) (position data) 0 (request data)
def resultValues (data : Data) (input : BitString) : List Nat :=
  BuilderInitialRequestResolution.resultValues (metadata data) (position data) 0 (request data) input
def tagFrame (data : Data) : List Nat :=
  BuilderInitialRequestResolution.tagFrame (metadata data) (position data) 0 (request data)
def resolvedValues (data : Data) (input : BitString) : List Nat :=
  BuilderInitialRequestResolution.outputValues (metadata data) (position data) 0 (request data) input
def indexValues (data : Data) (input : BitString) : List Nat :=
  [position data, 3, position data * 3, code data input, indexValue data input]
def cellValues (data : Data) (input : BitString) : List Nat :=
  centerStage data ++ resolvedValues data input ++ indexValues data input ++ payloadValues data input
def outputValues (data : Data) (input : BitString) : List Nat :=
  if data.coordinate < 2 then prefixStage data
  else if position data < data.tapeWidth then cellValues data input
  else widthStage data ++ [1]
def endpoint (data : Data) : Endpoint := if data.coordinate < 2 then .reject else .accept

theorem dataValues_length (data : Data) : (dataValues data).length = 4 := rfl
theorem prefixStage_length (data : Data) : (prefixStage data).length = 9 := rfl
theorem widthStage_length (data : Data) : (widthStage data).length = 14 := rfl
theorem centerStage_length (data : Data) : (centerStage data).length = 19 := rfl
theorem payloadValues_length (data : Data) (input : BitString) : (payloadValues data input).length = 3 := rfl

theorem request_canonical (data : Data) :
    request data = BuilderInitialCellCoordinates.inputOnlyRequest data.fuel (position data) := by
  by_cases h : position data < data.fuel
  · simp only [request, if_pos h, BuilderInitialCellCoordinates.inputOnlyRequest,
      if_neg (by omega : ¬ data.fuel ≤ position data)]
  · simp only [request, if_neg h, BuilderInitialCellCoordinates.inputOnlyRequest,
      if_pos (by omega : data.fuel ≤ position data)]

theorem code_canonical (data : Data) (input : BitString) :
    code data input = VariableLayout.tapeSymbolCode
      (BuilderInitialConstraintPayload.inputOnlySymbol input data.fuel (position data)) := by
  by_cases h : position data < data.fuel
  · simp only [code, request, if_pos h, BuilderInitialRequestResolution.symbolCode,
      BuilderInitialConstraintPayload.inputOnlySymbol, if_neg (by omega : ¬ data.fuel ≤ position data)]
    rfl
  · simp only [code, request, if_neg h, BuilderInitialRequestResolution.symbolCode,
      BuilderInitialConstraintPayload.inputOnlySymbol, if_pos (by omega : data.fuel ≤ position data)]
    exact (BuilderInitialConstraintPayload.sourceSymbol_code _).symm

theorem code_le (data : Data) (input : BitString) : code data input ≤ 2 :=
  BuilderInitialRequestResolution.symbolCode_le input (request data) 0

theorem resolvedValues_eq (data : Data) (input : BitString) :
    resolvedValues data input = tagFrame data ++ resultValues data input := by
  by_cases h : position data < data.fuel <;>
    simp only [resolvedValues, tagFrame, resultValues, request, h, ite_true, ite_false,
      BuilderInitialRequestResolution.outputValues]

private theorem resolved_output (data : Data) (input : BitString) :
    BuilderInitialRequestResolution.outputValues (metadata data) (position data) 0 (request data) input =
      tagFrame data ++ resultValues data input := resolvedValues_eq data input

theorem resultValues_length (data : Data) (input : BitString) : (resultValues data input).length = 10 := rfl
theorem cellValues_length (data : Data) (input : BitString) : (cellValues data input).length = 47 := by
  rw [cellValues, resolvedValues_eq]
  rfl

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


def prefixFields : List (BuilderRegisterPack.Field 4) :=
  [.argument ⟨3, by decide⟩, .constant 2]
def widthFields : List (BuilderRegisterPack.Field 9) :=
  [.argument ⟨8, by decide⟩, .argument ⟨2, by decide⟩]
def centerFields : List (BuilderRegisterPack.Field 14) :=
  [.argument ⟨8, by decide⟩, .argument ⟨1, by decide⟩]
def requestFields (source : Bool) : List (BuilderRegisterPack.Field 19) :=
  [.argument ⟨0, by decide⟩, .argument ⟨1, by decide⟩, .constant 0,
   .argument ⟨2, by decide⟩, .constant 0, .argument ⟨8, by decide⟩, .constant 0,
   .constant (if source then 2 else 0),
   if source then .argument ⟨18, by decide⟩ else .constant 0]
def indexExpression : BuilderRegisterExpression.Expr 10 :=
  .binary .add (.binary .mul (.argument ⟨5, by decide⟩) (.constant 3)) (.argument ⟨9, by decide⟩)
def payloadFields : List (BuilderRegisterPack.Field 15) :=
  [.argument ⟨14, by decide⟩, .constant 1, .constant 2]
def paddingFields : List (BuilderRegisterPack.Field 14) := [.constant 1]

theorem prefix_values (data : Data) :
    BuilderRegisterPack.values prefixFields (view (dataValues data)) = [data.coordinate, 2] := rfl

theorem width_values (data : Data) (hPrefix : ¬ data.coordinate < 2) :
    BuilderRegisterPack.values widthFields (view (prefixStage data)) = [position data, data.tapeWidth] := by
  change [residual data.coordinate 2, data.tapeWidth] = _
  simp only [residual, if_neg hPrefix, position]

theorem center_values (data : Data) (hPrefix : ¬ data.coordinate < 2) :
    BuilderRegisterPack.values centerFields (view (widthStage data)) = [position data, data.fuel] := by
  change [residual data.coordinate 2, data.fuel] = _
  simp only [residual, if_neg hPrefix, position]

theorem blank_values (data : Data) (hPrefix : ¬ data.coordinate < 2) (hBefore : position data < data.fuel) :
    BuilderRegisterPack.values (requestFields false) (view (centerStage data)) = requestValues data := by
  change [data.inputLength, data.fuel, 0, data.tapeWidth, 0, residual data.coordinate 2, 0, 0, 0] = _
  simp only [residual, if_neg hPrefix, requestValues, request, if_pos hBefore]
  rfl

theorem source_values (data : Data) (hPrefix : ¬ data.coordinate < 2) (hBefore : ¬ position data < data.fuel) :
    BuilderRegisterPack.values (requestFields true) (view (centerStage data)) = requestValues data := by
  change [data.inputLength, data.fuel, 0, data.tapeWidth, 0, residual data.coordinate 2, 0, 2,
    residual (position data) data.fuel] = _
  simp only [residual, if_neg hPrefix, if_neg hBefore, requestValues, request]
  rfl

theorem index_values (data : Data) (input : BitString) :
    BuilderRegisterExpression.values indexExpression (view (resultValues data input)) = indexValues data input := rfl
theorem payload_values (data : Data) (input : BitString) :
    BuilderRegisterPack.values payloadFields (view (resultValues data input ++ indexValues data input)) =
      payloadValues data input := rfl
theorem padding_values (data : Data) :
    BuilderRegisterPack.values paddingFields (view (widthStage data)) = [1] := rfl

def paddingNode : Node :=
  {name := 11, program := BuilderRegisterPack.machine paddingFields 0, onAccept := .accept, onReject := .dead}

def payloadNode : Node :=
  {name := 10, program := BuilderRegisterPack.machine payloadFields 0, onAccept := .accept, onReject := .dead}

def indexNode : Node :=
  {name := 9, program := BuilderRegisterExpression.machine indexExpression 0, onAccept := .node payloadNode.reference, onReject := .dead}

def resolveNode : Node :=
  {name := 8, program := BuilderInitialRequestResolution.machine, onAccept := .node indexNode.reference, onReject := .dead}

def sourceNode : Node :=
  {name := 7, program := BuilderRegisterPack.machine (requestFields true) 0, onAccept := .node resolveNode.reference, onReject := .dead}

def blankNode : Node :=
  {name := 6, program := BuilderRegisterPack.machine (requestFields false) 0, onAccept := .node resolveNode.reference, onReject := .dead}

def centerCompareNode : Node :=
  {name := 5, program := BuilderRegisterCompareResidual.machine, onAccept := .node blankNode.reference, onReject := .node sourceNode.reference}

def centerNode : Node :=
  {name := 4, program := BuilderRegisterPack.machine centerFields 0, onAccept := .node centerCompareNode.reference, onReject := .dead}

def widthCompareNode : Node :=
  {name := 3, program := BuilderRegisterCompareResidual.machine, onAccept := .node centerNode.reference, onReject := .node paddingNode.reference}

def widthNode : Node :=
  {name := 2, program := BuilderRegisterPack.machine widthFields 0, onAccept := .node widthCompareNode.reference, onReject := .dead}

def prefixCompareNode : Node :=
  {name := 1, program := BuilderRegisterCompareResidual.machine, onAccept := .reject, onReject := .node widthNode.reference}

def prefixNode : Node :=
  {name := 0, program := BuilderRegisterPack.machine prefixFields 0, onAccept := .node prefixCompareNode.reference, onReject := .dead}

def graph : Graph :=
  {nodes := [prefixNode, prefixCompareNode, widthNode, widthCompareNode, centerNode, centerCompareNode, blankNode, sourceNode, resolveNode, indexNode, payloadNode, paddingNode], entry := prefixNode.reference}
def machine : WorkMachine := WorkMachineProgramGraph.machine graph

theorem graph_nodes_length : graph.nodes.length = 12 := rfl

private theorem prefix_mem : prefixNode ∈ graph.nodes := List.Mem.head _

private theorem prefixCompare_mem : prefixCompareNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.head _)

private theorem width_mem : widthNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

private theorem widthCompare_mem : widthCompareNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

private theorem center_mem : centerNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

private theorem centerCompare_mem : centerCompareNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

private theorem blank_mem : blankNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))

private theorem source_mem : sourceNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))

private theorem resolve_mem : resolveNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))

private theorem index_mem : indexNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

private theorem payload_mem : payloadNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))

private theorem padding_mem : paddingNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))

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

private theorem compare_good : Good BuilderRegisterCompareResidual.machine :=
  ⟨BuilderRegisterCompareResidual.rules_pairwise_query_distinct, BuilderRegisterCompareResidual.noRuleAtAccept,
    BuilderRegisterCompareResidual.noRuleAtReject, BuilderRegisterCompareResidual.acceptState_ne_rejectState⟩
private theorem resolve_good : Good BuilderInitialRequestResolution.machine :=
  ⟨BuilderInitialRequestResolution.rules_pairwise_query_distinct, BuilderInitialRequestResolution.noRuleAtAccept,
    BuilderInitialRequestResolution.noRuleAtReject, BuilderInitialRequestResolution.acceptState_ne_rejectState⟩

theorem graph_wellFormed : graph.WellFormed := by
  have hNames : (graph.nodes.map Node.name).Pairwise (fun a b : Nat => a ≠ b) := by
    change ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat).Pairwise _
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.pairwise_map] using hNames
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact pack_good prefixFields
    · exact compare_good
    · exact pack_good widthFields
    · exact compare_good
    · exact pack_good centerFields
    · exact compare_good
    · exact pack_good (requestFields false)
    · exact pack_good (requestFields true)
    · exact resolve_good
    · exact expression_good indexExpression
    · exact pack_good payloadFields
    · exact pack_good paddingFields
  · exact ⟨prefixNode, prefix_mem, rfl, rfl⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨prefixCompareNode, prefixCompare_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, ⟨widthNode, width_mem, rfl, rfl⟩⟩
    · exact ⟨⟨widthCompareNode, widthCompare_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨centerNode, center_mem, rfl, rfl⟩, ⟨paddingNode, padding_mem, rfl, rfl⟩⟩
    · exact ⟨⟨centerCompareNode, centerCompare_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨blankNode, blank_mem, rfl, rfl⟩, ⟨sourceNode, source_mem, rfl, rfl⟩⟩
    · exact ⟨⟨resolveNode, resolve_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨resolveNode, resolve_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨indexNode, index_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨payloadNode, payload_mem, rfl, rfl⟩, True.intro⟩
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

private theorem configuration_eq_of_fields (config : WorkConfiguration) (state : Nat) (tape : WorkTape)
    (hState : config.state = state) (hTape : config.tape = tape) :
    config = {state := state, tape := tape} := by
  cases config with
  | mk currentState currentTape =>
      change currentState = state at hState
      change currentTape = tape at hTape
      subst currentState
      subst currentTape
      rfl

private theorem comparison_run (coordinate boundary : Nat) (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? BuilderRegisterCompareResidual.machine
      (BuilderRegisterCompareResidual.workSteps coordinate boundary)
      (workStartConfiguration BuilderRegisterCompareResidual.machine (endTape (older ++ [coordinate, boundary]) inside [])) =
      some {
        state := if coordinate < boundary then BuilderRegisterCompareResidual.machine.acceptState
          else BuilderRegisterCompareResidual.machine.rejectState
        tape := endTape (older ++ BuilderInitialCellDecoder.comparisonValues coordinate boundary) inside [] } := by
  have hState : (BuilderRegisterCompareResidual.finalConfiguration coordinate boundary older inside []).state =
      if coordinate < boundary then BuilderRegisterCompareResidual.machine.acceptState
      else BuilderRegisterCompareResidual.machine.rejectState := by
    by_cases hLess : coordinate < boundary
    · rw [if_pos hLess]
      exact (BuilderRegisterCompareResidual.final_accept_iff coordinate boundary older inside []).mpr hLess
    · rw [if_neg hLess]
      exact (BuilderRegisterCompareResidual.final_reject_iff coordinate boundary older inside []).mpr (by omega)
  have hTape : (BuilderRegisterCompareResidual.finalConfiguration coordinate boundary older inside []).tape =
      endTape (older ++ BuilderInitialCellDecoder.comparisonValues coordinate boundary) inside [] := by
    rw [BuilderRegisterCompareResidual.final_tape, BuilderInitialCellDecoder.comparisonValues_eq]
    simp only [BuilderRegisterCompareResidual.outputValues, BuilderRegisterCompareResidual.resultBoundary_eq,
      BuilderRegisterCompareResidual.resultCoordinate_eq, List.drop_nil, List.append_assoc]
  have h := BuilderRegisterCompareResidual.workRunExact coordinate boundary older inside []
  rw [configuration_eq_of_fields _ _ _ hState hTape] at h
  exact h


def prefixSteps (data : Data) : Nat := BuilderRegisterPack.workSteps prefixFields (view (dataValues data)) []
def widthSteps (data : Data) : Nat := BuilderRegisterPack.workSteps widthFields (view (prefixStage data)) []
def centerSteps (data : Data) : Nat := BuilderRegisterPack.workSteps centerFields (view (widthStage data)) []
def requestSteps (data : Data) : Nat :=
  BuilderRegisterPack.workSteps (requestFields (decide (¬ position data < data.fuel))) (view (centerStage data)) []
def resolveSteps (data : Data) (older : List Nat) (input : BitString) : Nat :=
  BuilderInitialRequestResolution.workSteps (metadata data) (position data) 0 (request data)
    (older ++ centerStage data) input
def indexSteps (data : Data) (input : BitString) : Nat :=
  BuilderRegisterExpression.workSteps indexExpression (view (resultValues data input)) []
def payloadSteps (data : Data) (input : BitString) : Nat :=
  BuilderRegisterPack.workSteps payloadFields (view (resultValues data input ++ indexValues data input)) []
def paddingSteps (data : Data) : Nat := BuilderRegisterPack.workSteps paddingFields (view (widthStage data)) []
def resolvedSteps (data : Data) (older : List Nat) (input : BitString) : Nat :=
  resolveSteps data older input + 1 + (indexSteps data input + 1 + (payloadSteps data input + 1))
def cellSteps (data : Data) (older : List Nat) (input : BitString) : Nat :=
  BuilderRegisterCompareResidual.workSteps (position data) data.fuel + 1 +
    (requestSteps data + 1 + resolvedSteps data older input)
def widthTailSteps (data : Data) (older : List Nat) (input : BitString) : Nat :=
  if position data < data.tapeWidth then centerSteps data + 1 + cellSteps data older input
  else paddingSteps data + 1
def afterPrefixSteps (data : Data) (older : List Nat) (input : BitString) : Nat :=
  if data.coordinate < 2 then 0
  else widthSteps data + 1 + (BuilderRegisterCompareResidual.workSteps (position data) data.tapeWidth + 1 +
    widthTailSteps data older input)
def workSteps (data : Data) (older : List Nat) (input : BitString) : Nat :=
  prefixSteps data + 1 + (BuilderRegisterCompareResidual.workSteps data.coordinate 2 + 1 +
    afterPrefixSteps data older input)

def initialConfiguration (data : Data) (older : List Nat) (input : BitString) (output : List CNFToken) : WorkConfiguration :=
  workStartConfiguration machine (endTape (older ++ dataValues data) (inside input output) [])
def finalConfiguration (data : Data) (older : List Nat) (input : BitString) (output : List CNFToken) : WorkConfiguration :=
  WorkMachineProgramGraph.endpointConfiguration (endpoint data)
    (endTape (older ++ outputValues data input) (inside input output) [])

private theorem resolved_path (data : Data) (older : List Nat) (input : BitString) (output : List CNFToken) :
    AcceptPath graph (.node resolveNode.reference) .accept (resolvedSteps data older input)
      (endTape (older ++ centerStage data ++ requestValues data) (inside input output) [])
      (endTape (older ++ cellValues data input) (inside input output) []) := by
  have hPack := pack_run payloadFields (resultValues data input ++ indexValues data input)
    (older ++ centerStage data ++ tagFrame data) (inside input output) rfl
  rw [payload_values] at hPack
  simp only [List.append_assoc] at hPack
  have hP := AcceptPath.step payloadNode .accept _ 0 _ _ _ payload_mem hPack (.terminal .accept _)
  have hIndex := expression_run indexExpression (resultValues data input)
    (older ++ centerStage data ++ tagFrame data) (inside input output) rfl
  rw [index_values] at hIndex
  simp only [List.append_assoc] at hIndex
  have hI := AcceptPath.step indexNode .accept _ _ _ _ _ index_mem hIndex hP
  have hResolve := BuilderInitialRequestResolution.workRunExact (metadata data) (position data) 0 (request data)
    (older ++ centerStage data) input output
  simp only [BuilderInitialRequestResolution.initialConfiguration, BuilderInitialRequestResolution.finalConfiguration,
    resolved_output, List.append_assoc] at hResolve
  have hR := AcceptPath.step resolveNode .accept _ _ _ _ _ resolve_mem hResolve hI
  simpa only [resolvedSteps, resolveSteps, indexSteps, payloadSteps, requestValues, cellValues, resolvedValues_eq,
    List.append_assoc, Nat.add_zero] using hR

private theorem center_path (data : Data) (older : List Nat) (input : BitString) (output : List CNFToken)
    (hPrefix : ¬ data.coordinate < 2) :
    AcceptPath graph (.node centerCompareNode.reference) .accept (cellSteps data older input)
      (endTape (older ++ widthStage data ++ [position data, data.fuel]) (inside input output) [])
      (endTape (older ++ cellValues data input) (inside input output) []) := by
  have hTail := resolved_path data older input output
  have hCompare := comparison_run (position data) data.fuel (older ++ widthStage data) (inside input output)
  simp only [List.append_assoc] at hCompare
  by_cases hBefore : position data < data.fuel
  · have hPack := pack_run (requestFields false) (centerStage data) older (inside input output) rfl
    rw [blank_values data hPrefix hBefore] at hPack
    simp only [List.append_assoc] at hPack hTail
    have hP := AcceptPath.step blankNode .accept _ _ _ _ _ blank_mem hPack hTail
    simp only [if_pos hBefore] at hCompare
    have hC := AcceptPath.step centerCompareNode .accept _ _ _ _ _ centerCompare_mem hCompare hP
    simpa only [cellSteps, requestSteps, hBefore, not_true_eq_false, decide_false, List.append_assoc] using hC
  · have hPack := pack_run (requestFields true) (centerStage data) older (inside input output) rfl
    rw [source_values data hPrefix hBefore] at hPack
    simp only [List.append_assoc] at hPack hTail
    have hP := AcceptPath.step sourceNode .accept _ _ _ _ _ source_mem hPack hTail
    simp only [if_neg hBefore] at hCompare
    have hC := AcceptPath.stepReject centerCompareNode .accept _ _ _ _ _ centerCompare_mem hCompare hP
    simpa only [cellSteps, requestSteps, hBefore, not_false_eq_true, decide_true, List.append_assoc] using hC

private theorem width_path (data : Data) (older : List Nat) (input : BitString) (output : List CNFToken)
    (hPrefix : ¬ data.coordinate < 2) :
    AcceptPath graph (.node widthCompareNode.reference) .accept
      (BuilderRegisterCompareResidual.workSteps (position data) data.tapeWidth + 1 + widthTailSteps data older input)
      (endTape (older ++ prefixStage data ++ [position data, data.tapeWidth]) (inside input output) [])
      (endTape (older ++ outputValues data input) (inside input output) []) := by
  have hCompare := comparison_run (position data) data.tapeWidth (older ++ prefixStage data) (inside input output)
  simp only [List.append_assoc] at hCompare
  by_cases hWidth : position data < data.tapeWidth
  · have hTail := center_path data older input output hPrefix
    have hPack := pack_run centerFields (widthStage data) older (inside input output) rfl
    rw [center_values data hPrefix] at hPack
    simp only [List.append_assoc] at hPack hTail
    have hP := AcceptPath.step centerNode .accept _ _ _ _ _ center_mem hPack hTail
    simp only [if_pos hWidth, widthStage, List.append_assoc] at hCompare hP
    have hC := AcceptPath.step widthCompareNode .accept _ _ _ _ _ widthCompare_mem hCompare hP
    simpa only [outputValues, if_neg hPrefix, if_pos hWidth, widthTailSteps, centerSteps,
      widthStage, List.append_assoc] using hC
  · have hPack := pack_run paddingFields (widthStage data) older (inside input output) rfl
    rw [padding_values] at hPack
    simp only [List.append_assoc] at hPack
    have hP := AcceptPath.step paddingNode .accept _ 0 _ _ _ padding_mem hPack (.terminal .accept _)
    simp only [if_neg hWidth, widthStage, List.append_assoc] at hCompare hP
    have hC := AcceptPath.stepReject widthCompareNode .accept _ _ _ _ _ widthCompare_mem hCompare hP
    simpa only [outputValues, if_neg hPrefix, if_neg hWidth, widthTailSteps, paddingSteps,
      widthStage, List.append_assoc, Nat.add_zero] using hC

private theorem prefix_path (data : Data) (older : List Nat) (input : BitString) (output : List CNFToken) :
    AcceptPath graph (.node prefixCompareNode.reference) (endpoint data)
      (BuilderRegisterCompareResidual.workSteps data.coordinate 2 + 1 + afterPrefixSteps data older input)
      (endTape (older ++ dataValues data ++ [data.coordinate, 2]) (inside input output) [])
      (endTape (older ++ outputValues data input) (inside input output) []) := by
  have hCompare := comparison_run data.coordinate 2 (older ++ dataValues data) (inside input output)
  simp only [List.append_assoc] at hCompare
  by_cases hPrefix : data.coordinate < 2
  · simp only [if_pos hPrefix] at hCompare
    have h := AcceptPath.step prefixCompareNode .reject _ 0 _ _ _ prefixCompare_mem hCompare (.terminal .reject _)
    simpa only [endpoint, outputValues, if_pos hPrefix, afterPrefixSteps, prefixStage, List.append_assoc] using h
  · have hTail := width_path data older input output hPrefix
    have hPack := pack_run widthFields (prefixStage data) older (inside input output) rfl
    rw [width_values data hPrefix] at hPack
    simp only [List.append_assoc] at hPack hTail
    have hP := AcceptPath.step widthNode .accept _ _ _ _ _ width_mem hPack hTail
    simp only [if_neg hPrefix, prefixStage, List.append_assoc] at hCompare hP
    have hC := AcceptPath.stepReject prefixCompareNode .accept _ _ _ _ _ prefixCompare_mem hCompare hP
    simpa only [endpoint, if_neg hPrefix, afterPrefixSteps, widthSteps, prefixStage, List.append_assoc] using hC

theorem workRunExact (data : Data) (older : List Nat) (input : BitString) (output : List CNFToken) :
    workRunExact? machine (workSteps data older input) (initialConfiguration data older input output) =
      some (finalConfiguration data older input output) := by
  have hTail := prefix_path data older input output
  have hPack := pack_run prefixFields (dataValues data) older (inside input output) rfl
  rw [prefix_values] at hPack
  simp only [List.append_assoc] at hPack hTail
  have hP := AcceptPath.step prefixNode _ _ _ _ _ _ prefix_mem hPack hTail
  have h := WorkMachineProgramPath.runExact graph _ _ _ _ _ graph_wellFormed hP
  have hStart (tape : WorkTape) :
      WorkMachineProgramGraph.endpointConfiguration (.node prefixNode.reference) tape =
        workStartConfiguration machine tape := rfl
  have hMachine : WorkMachineProgramGraph.machine graph = machine := rfl
  rw [hStart, hMachine] at h
  simpa only [workSteps, prefixSteps, initialConfiguration, finalConfiguration, List.append_assoc] using h

theorem run_compile_exact (data : Data) (older : List Nat) (input : BitString) (output : List CNFToken) :
    run (compileWorkMachine machine) (6 * workSteps data older input)
      (encodeWorkConfiguration (initialConfiguration data older input output)) =
      encodeWorkConfiguration (finalConfiguration data older input output) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact data older input output)

theorem final_accept_iff (data : Data) (older : List Nat) (input : BitString) (output : List CNFToken) :
    (finalConfiguration data older input output).state = machine.acceptState ↔ 2 ≤ data.coordinate := by
  change WorkMachineProgramGraph.endpointState (endpoint data) = 0 ↔ _
  by_cases h : data.coordinate < 2
  · rw [endpoint, if_pos h]
    constructor
    · intro hState
      cases hState
    · intro hLe
      omega
  · rw [endpoint, if_neg h]
    exact ⟨fun _ => by omega, fun _ => rfl⟩
theorem final_reject_iff (data : Data) (older : List Nat) (input : BitString) (output : List CNFToken) :
    (finalConfiguration data older input output).state = machine.rejectState ↔ data.coordinate < 2 := by
  change WorkMachineProgramGraph.endpointState (endpoint data) = 1 ↔ _
  by_cases h : data.coordinate < 2
  · rw [endpoint, if_pos h]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [endpoint, if_neg h]
    constructor
    · intro hState
      cases hState
    · intro hPrefix
      exact (h hPrefix).elim
theorem prefix_output (data : Data) (input : BitString) (hPrefix : data.coordinate < 2) :
    outputValues data input = prefixStage data := by simp only [outputValues, if_pos hPrefix]
theorem cell_output (data : Data) (input : BitString) (hPrefix : ¬ data.coordinate < 2)
    (hWidth : position data < data.tapeWidth) : outputValues data input = cellValues data input := by
  simp only [outputValues, if_neg hPrefix, if_pos hWidth]
theorem padding_output (data : Data) (input : BitString) (hPrefix : ¬ data.coordinate < 2)
    (hWidth : ¬ position data < data.tapeWidth) : outputValues data input = widthStage data ++ [1] := by
  simp only [outputValues, if_neg hPrefix, if_neg hWidth]
theorem final_tape (data : Data) (older : List Nat) (input : BitString) (output : List CNFToken) :
    (finalConfiguration data older input output).tape =
      endTape (older ++ outputValues data input) (inside input output) [] := rfl
theorem final_frontier (data : Data) (older : List Nat) (input : BitString) (output : List CNFToken) :
    (finalConfiguration data older input output).tape.left = [] := rfl

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise graph graph_wellFormed
theorem noRuleAtAccept : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState :=
  WorkMachineProgramGraph.noRuleAt_globalAccept graph
theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  WorkMachineProgramGraph.noRuleAt_globalReject graph
theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := by
  change (0 : Nat) ≠ 1
  decide


private theorem comparison_bounds (coordinate boundary : Nat) (older : List Nat)
    (bound : NatPolynomial) (inputSize : Nat)
    (hSpan : (registerWord (older ++ [coordinate, boundary])).length ≤ bound.eval inputSize) :
    (registerWord (older ++ comparisonValues coordinate boundary)).length ≤
        (BuilderRegisterCompareResidual.spanPolynomial bound).eval inputSize ∧
      6 * BuilderRegisterCompareResidual.workSteps coordinate boundary ≤
        (BuilderRegisterCompareResidual.rawTimePolynomial bound).eval inputSize := by
  rw [BuilderInitialCellDecoder.comparisonValues_eq]
  exact BuilderRegisterCompareResidual.source_polynomial_bounds coordinate boundary older bound inputSize hSpan

def prefixPackedSpan (bound : NatPolynomial) : NatPolynomial := BuilderRegisterPack.spanPolynomial prefixFields bound
def prefixSpan (bound : NatPolynomial) : NatPolynomial := BuilderRegisterCompareResidual.spanPolynomial (prefixPackedSpan bound)
def widthPackedSpan (bound : NatPolynomial) : NatPolynomial := BuilderRegisterPack.spanPolynomial widthFields (prefixSpan bound)
def widthSpan (bound : NatPolynomial) : NatPolynomial := BuilderRegisterCompareResidual.spanPolynomial (widthPackedSpan bound)
def centerPackedSpan (bound : NatPolynomial) : NatPolynomial := BuilderRegisterPack.spanPolynomial centerFields (widthSpan bound)
def centerSpan (bound : NatPolynomial) : NatPolynomial := BuilderRegisterCompareResidual.spanPolynomial (centerPackedSpan bound)
def requestSpan (bound : NatPolynomial) : NatPolynomial :=
  .add (BuilderRegisterPack.spanPolynomial (requestFields false) (centerSpan bound))
    (BuilderRegisterPack.spanPolynomial (requestFields true) (centerSpan bound))
def requestRawTime (bound : NatPolynomial) : NatPolynomial :=
  .add (BuilderRegisterPack.rawTimePolynomial (requestFields false) (centerSpan bound))
    (BuilderRegisterPack.rawTimePolynomial (requestFields true) (centerSpan bound))
def resolvedSpan (bound : NatPolynomial) : NatPolynomial :=
  BuilderInitialRequestResolution.spanPolynomial (requestSpan bound)
def indexSpan (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterExpression.spanPolynomial indexExpression (resolvedSpan bound)
def cellSpan (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterPack.spanPolynomial payloadFields (indexSpan bound)
def paddingSpan (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterPack.spanPolynomial paddingFields (widthSpan bound)
def spanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (prefixSpan bound) (.add (paddingSpan bound) (cellSpan bound))
def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (BuilderRegisterPack.rawTimePolynomial prefixFields bound)
  (.add (BuilderRegisterCompareResidual.rawTimePolynomial (prefixPackedSpan bound))
  (.add (BuilderRegisterPack.rawTimePolynomial widthFields (prefixSpan bound))
  (.add (BuilderRegisterCompareResidual.rawTimePolynomial (widthPackedSpan bound))
  (.add (BuilderRegisterPack.rawTimePolynomial centerFields (widthSpan bound))
  (.add (BuilderRegisterCompareResidual.rawTimePolynomial (centerPackedSpan bound))
  (.add (requestRawTime bound)
  (.add (BuilderInitialRequestResolution.rawTimePolynomial (requestSpan bound))
  (.add (BuilderRegisterExpression.rawTimePolynomial indexExpression (resolvedSpan bound))
  (.add (BuilderRegisterPack.rawTimePolynomial payloadFields (indexSpan bound))
  (.add (BuilderRegisterPack.rawTimePolynomial paddingFields (widthSpan bound)) (.constant 72)))))))))))

private theorem request_bounds (data : Data) (older : List Nat) (bound : NatPolynomial) (inputSize : Nat)
    (hPrefix : ¬ data.coordinate < 2)
    (hSpan : (registerWord (older ++ centerStage data)).length ≤ (centerSpan bound).eval inputSize) :
    (registerWord (older ++ centerStage data ++ requestValues data)).length ≤ (requestSpan bound).eval inputSize ∧
      6 * requestSteps data ≤ (requestRawTime bound).eval inputSize := by
  by_cases hBefore : position data < data.fuel
  · have h := pack_bounds (requestFields false) (centerStage data) older (centerSpan bound) inputSize rfl hSpan
    rw [blank_values data hPrefix hBefore] at h
    simp only [requestSpan, requestRawTime, NatPolynomial.eval_add, requestSteps,
      hBefore, not_true_eq_false, decide_false]
    exact ⟨by omega, by omega⟩
  · have h := pack_bounds (requestFields true) (centerStage data) older (centerSpan bound) inputSize rfl hSpan
    rw [source_values data hPrefix hBefore] at h
    simp only [requestSpan, requestRawTime, NatPolynomial.eval_add, requestSteps,
      hBefore, not_false_eq_true, decide_true]
    exact ⟨by omega, by omega⟩

/-- Complete branch work and retained registers have a fixed encoded-span polynomial. -/
theorem packet_polynomial_bounds (data : Data) (older : List Nat) (input : BitString)
    (bound : NatPolynomial) (inputSize : Nat)
    (hSpan : (registerWord (older ++ dataValues data)).length ≤ bound.eval inputSize) :
    (registerWord (older ++ outputValues data input)).length ≤ (spanPolynomial bound).eval inputSize ∧
      6 * workSteps data older input ≤ (rawTimePolynomial bound).eval inputSize := by
  have hPrefixPack := pack_bounds prefixFields (dataValues data) older bound inputSize rfl hSpan
  rw [prefix_values] at hPrefixPack
  have hPrefix := comparison_bounds data.coordinate 2 (older ++ dataValues data) (prefixPackedSpan bound) inputSize hPrefixPack.1
  have hPrefixSpan : (registerWord (older ++ prefixStage data)).length ≤ (prefixSpan bound).eval inputSize := by
    simpa only [prefixStage, prefixSpan, List.append_assoc] using hPrefix.1
  by_cases hEarly : data.coordinate < 2
  · constructor
    · simp only [outputValues, if_pos hEarly, spanPolynomial, NatPolynomial.eval_add]
      omega
    · simp only [workSteps, afterPrefixSteps, if_pos hEarly, prefixSteps, rawTimePolynomial,
        NatPolynomial.eval_add, NatPolynomial.eval_constant]
      omega
  · have hWidthPack := pack_bounds widthFields (prefixStage data) older (prefixSpan bound) inputSize rfl hPrefixSpan
    rw [width_values data hEarly] at hWidthPack
    have hWidth := comparison_bounds (position data) data.tapeWidth (older ++ prefixStage data)
      (widthPackedSpan bound) inputSize hWidthPack.1
    have hWidthSpan : (registerWord (older ++ widthStage data)).length ≤ (widthSpan bound).eval inputSize := by
      simpa only [widthStage, widthSpan, List.append_assoc] using hWidth.1
    by_cases hCell : position data < data.tapeWidth
    · have hCenterPack := pack_bounds centerFields (widthStage data) older (widthSpan bound) inputSize rfl hWidthSpan
      rw [center_values data hEarly] at hCenterPack
      have hCenter := comparison_bounds (position data) data.fuel (older ++ widthStage data)
        (centerPackedSpan bound) inputSize hCenterPack.1
      have hCenterSpan : (registerWord (older ++ centerStage data)).length ≤ (centerSpan bound).eval inputSize := by
        simpa only [centerStage, centerSpan, List.append_assoc] using hCenter.1
      have hRequest := request_bounds data older bound inputSize hEarly hCenterSpan
      have hResolve := BuilderInitialRequestResolution.source_polynomial_bounds (metadata data) (position data) 0 (request data)
        (older ++ centerStage data) input (requestSpan bound) inputSize hRequest.1
      have hResolved : (registerWord ((older ++ centerStage data ++ tagFrame data) ++ resultValues data input)).length ≤
          (resolvedSpan bound).eval inputSize := by
        simpa only [resolved_output, resolvedSpan, List.append_assoc] using hResolve.1
      have hIndex := expression_bounds indexExpression (resultValues data input)
        (older ++ centerStage data ++ tagFrame data) (resolvedSpan bound) inputSize rfl hResolved
      rw [index_values] at hIndex
      have hPack := pack_bounds payloadFields (resultValues data input ++ indexValues data input)
        (older ++ centerStage data ++ tagFrame data) (indexSpan bound) inputSize rfl
        (by simpa only [indexSpan, List.append_assoc] using hIndex.1)
      rw [payload_values] at hPack
      have hFinal : (registerWord (older ++ cellValues data input)).length ≤ (cellSpan bound).eval inputSize := by
        simpa only [cellValues, resolvedValues_eq, cellSpan, List.append_assoc] using hPack.1
      constructor
      · simp only [outputValues, if_neg hEarly, if_pos hCell, spanPolynomial, NatPolynomial.eval_add]
        omega
      · have hResolveTime := hResolve.2
        have hIndexTime := hIndex.2
        have hPackTime := hPack.2
        have hRequestTime := hRequest.2
        simp only [workSteps, afterPrefixSteps, widthTailSteps, cellSteps, resolvedSteps,
          if_neg hEarly, if_pos hCell, prefixSteps, widthSteps, centerSteps, resolveSteps, indexSteps, payloadSteps,
          rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
        omega
    · have hPadding := pack_bounds paddingFields (widthStage data) older (widthSpan bound) inputSize rfl hWidthSpan
      rw [padding_values] at hPadding
      have hFinal : (registerWord (older ++ (widthStage data ++ [1]))).length ≤ (paddingSpan bound).eval inputSize := by
        simpa only [paddingSpan, List.append_assoc] using hPadding.1
      constructor
      · simp only [outputValues, if_neg hEarly, if_neg hCell, spanPolynomial, NatPolynomial.eval_add]
        omega
      · simp only [workSteps, afterPrefixSteps, widthTailSteps, if_neg hEarly, if_neg hCell,
          prefixSteps, widthSteps, paddingSteps, rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
        omega

end PNP.Concrete.CookLevin.BuilderInitialInputOnlyPayload
