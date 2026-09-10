/-
Copyright (c) 2026 PNP Labs.

Physical canonical initial-cell literal and payload construction from the ten
source-resolution registers. The row slot count is not used as the global tape
width. Existing literal-expression syntax is specialized to source fields,
then the existing expression compiler and fixed tag tests write the complete
guarded or signed bit-guarded payload. Source composition remains explicit.
-/

import PNP.Concrete.CookLevinBuilderInitialRequestResolution
import PNP.Concrete.CookLevinBuilderInitialPairedCellSource
import PNP.Concrete.CookLevinBuilderLiteralIndexExpression

namespace PNP.Concrete.CookLevin.BuilderInitialPairedLiteralPayload

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderRegisterExpression (Expr)
open BuilderInitialCellCoordinates (Request)
open WorkMachineProgramGraph (Node Endpoint Graph)
open WorkMachineProgramPath (AcceptPath)

/-- A view of the ten actually written registers, not an execution premise about their answer. -/
structure Data where
  inputLength : Nat
  fuel : Nat
  length : Nat
  rowSlots : Nat
  remaining : Nat
  position : Nat
  offset : Nat
  kind : Nat
  argument : Nat
  code : Nat
  deriving DecidableEq, Repr

def dataValues (data : Data) : List Nat :=
  [data.inputLength, data.fuel, data.length, data.rowSlots, data.remaining,
    data.position, data.offset, data.kind, data.argument, data.code]

theorem dataValues_length (data : Data) : (dataValues data).length = 10 := rfl

def ofResolved (metadata : BuilderInitialRequestResolution.Metadata)
    (position offset : Nat) (request : Request width) (input : BitString) : Data :=
  {inputLength := metadata.inputLength, fuel := metadata.fuel, length := metadata.length,
   rowSlots := metadata.rowWidth, remaining := metadata.remaining, position, offset,
   kind := (BuilderInitialPairedRequest.encodeRequest request).1,
   argument := (BuilderInitialPairedRequest.encodeRequest request).2,
   code := BuilderInitialRequestResolution.symbolCode input request offset}

theorem ofResolved_values (metadata : BuilderInitialRequestResolution.Metadata)
    (position offset : Nat) (request : Request width) (input : BitString) :
    dataValues (ofResolved metadata position offset request input) =
      BuilderInitialRequestResolution.resultValues metadata position offset request input := rfl

def stateCount {language : Language} (verifier : PolynomialTimeVerifier language) : Nat :=
  (formulaStateCountPolynomial verifier).eval 0

theorem stateCount_canonical {language : Language} (problem : VerifierTableauProblem language) :
    stateCount problem.verifier = problem.dimensions.stateBound := rfl

inductive Role where
  | length | symbol | bit
  deriving DecidableEq, Repr

def kind : Role → BuilderLiteralIndexExpression.Kind
  | .length => .certificateLength
  | .symbol => .symbol
  | .bit => .certificateBit

def certificateBound (data : Data) : Nat := data.length + data.remaining
def timeCount (data : Data) : Nat := data.fuel + 1
def tapeWidth (data : Data) : Nat :=
  (2 * data.inputLength + 2 * certificateBound data + 2) + 2 * data.fuel + 1

private def argument (index : Fin 10) : Expr 10 := .argument index
private def plus (left right : Expr 10) : Expr 10 := .binary .add left right
private def times (left right : Expr 10) : Expr 10 := .binary .mul left right
private def certificateExpression : Expr 10 := plus (argument ⟨2, by decide⟩) (argument ⟨4, by decide⟩)
private def timeExpression : Expr 10 := plus (argument ⟨1, by decide⟩) (.constant 1)
private def widthExpression : Expr 10 :=
  plus (plus (plus (plus (times (.constant 2) (argument ⟨0, by decide⟩))
    (times (.constant 2) certificateExpression)) (.constant 2))
      (times (.constant 2) (argument ⟨1, by decide⟩))) (.constant 1)

private def environmentExpressions (states : Nat) (role : Role) : Fin 8 → Expr 10 :=
  fun index => match index.val with
  | 0 => timeExpression
  | 1 => widthExpression
  | 2 => .constant states
  | 3 => certificateExpression
  | 4 => .constant 0
  | 5 => match role with
    | .length => argument ⟨2, by decide⟩
    | .symbol => argument ⟨5, by decide⟩
    | .bit => argument ⟨8, by decide⟩
  | 6 => .constant 0
  | 7 => match role with
    | .symbol => argument ⟨9, by decide⟩
    | _ => .constant 0
  | _ => .constant 0

private def substitute {sourceArity targetArity : Nat}
    (arguments : Fin sourceArity → Expr targetArity) : Expr sourceArity → Expr targetArity
  | .constant value => .constant value
  | .argument index => arguments index
  | .binary operator left right => .binary operator (substitute arguments left) (substitute arguments right)

private theorem substitute_eval {sourceArity targetArity : Nat}
    (arguments : Fin sourceArity → Expr targetArity) (expression : Expr sourceArity)
    (environment : Fin targetArity → Nat) :
    BuilderRegisterExpression.eval (substitute arguments expression) environment =
      BuilderRegisterExpression.eval expression (fun index => BuilderRegisterExpression.eval (arguments index) environment) := by
  induction expression with
  | constant value => rfl
  | argument index => rfl
  | binary operator left right ihLeft ihRight =>
      simp only [substitute, BuilderRegisterExpression.eval, ihLeft, ihRight]

def expression (states : Nat) (role : Role) : Expr 10 :=
  substitute (environmentExpressions states role) (BuilderLiteralIndexExpression.expression (kind role))

private def view {arity : Nat} (values : List Nat) (index : Fin arity) : Nat := values.getD index.val 0

private theorem view_ofFn {arity : Nat} (values : List Nat) (hLength : values.length = arity) :
    List.ofFn (view values : Fin arity → Nat) = values := by
  subst arity
  have h : (view values : Fin values.length → Nat) = fun index => values[index.val] := by
    funext index
    simp only [view, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem index.isLt, Option.getD_some]
  rw [h]
  exact List.ofFn_getElem

def literalEnvironment (states : Nat) (role : Role) (data : Data) : Fin 8 → Nat :=
  fun index => match index.val with
  | 0 => timeCount data
  | 1 => tapeWidth data
  | 2 => states
  | 3 => certificateBound data
  | 4 => 0
  | 5 => match role with | .length => data.length | .symbol => data.position | .bit => data.argument
  | 6 => 0
  | 7 => match role with | .symbol => data.code | _ => 0
  | _ => 0

theorem expression_eval (states : Nat) (role : Role) (data : Data) :
    BuilderRegisterExpression.eval (expression states role) (view (dataValues data)) =
      BuilderRegisterExpression.eval (BuilderLiteralIndexExpression.expression (kind role))
        (literalEnvironment states role data) := by
  rw [expression, substitute_eval]
  apply congrArg (BuilderRegisterExpression.eval _)
  funext index
  rcases index with ⟨index, hIndex⟩
  have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by omega
  cases role <;> rcases hCases with h | h | h | h | h | h | h | h <;> subst index <;> rfl

def indexValue (states : Nat) (role : Role) (data : Data) : Nat :=
  BuilderRegisterExpression.eval (expression states role) (view (dataValues data))
def expressionValues (states : Nat) (role : Role) (data : Data) : List Nat :=
  BuilderRegisterExpression.values (expression states role) (view (dataValues data))
def count (states : Nat) (role : Role) : Nat := BuilderRegisterExpression.nodeCount (expression states role)

theorem expressionValues_length (states : Nat) (role : Role) (data : Data) :
    (expressionValues states role data).length = count states role :=
  BuilderRegisterExpression.values_length _ _
theorem expressionValues_root (states : Nat) (role : Role) (data : Data) :
    expressionValues states role data =
      BuilderRegisterExpression.prefixValues (expression states role) (view (dataValues data)) ++
        [indexValue states role data] :=
  BuilderRegisterExpression.values_root _ _

def literalValues (states : Nat) (data : Data) : List Nat :=
  expressionValues states .length data ++ expressionValues states .symbol data ++ expressionValues states .bit data
def preparedValues (states : Nat) (data : Data) : List Nat := dataValues data ++ literalValues states data
def preparedCount (states : Nat) : Nat := 10 + count states .length + count states .symbol + count states .bit

theorem preparedValues_length (states : Nat) (data : Data) :
    (preparedValues states data).length = preparedCount states := by
  simp only [preparedValues, literalValues, List.length_append, dataValues_length, expressionValues_length, preparedCount]
  omega

def payloadValues (states : Nat) (data : Data) : List Nat :=
  if data.kind = 3 then BuilderInitialConstraintPayload.bitGuardedValues
    (indexValue states .length data) (indexValue states .bit data) (indexValue states .symbol data)
    (decide (data.offset = 0))
  else BuilderInitialConstraintPayload.guardedValues (indexValue states .length data) (indexValue states .symbol data)

def outputValues (states : Nat) (data : Data) : List Nat :=
  preparedValues states data ++ [data.kind] ++
    if data.kind = 3 then [data.offset] ++ payloadValues states data else payloadValues states data

theorem output_suffix (states : Nat) (data : Data) :
    ∃ history : List Nat, outputValues states data = history ++ payloadValues states data := by
  by_cases hKind : data.kind = 3
  · refine ⟨preparedValues states data ++ [data.kind] ++ [data.offset], ?_⟩
    simp only [outputValues, if_pos hKind, List.append_assoc]
  · exact ⟨preparedValues states data ++ [data.kind], by simp only [outputValues, if_neg hKind]⟩


private def beforeValues (states : Nat) (role : Role) (data : Data) : List Nat :=
  match role with
  | .length => []
  | .symbol => expressionValues states .length data
  | .bit => expressionValues states .length data ++ expressionValues states .symbol data
private def beforeCount (states : Nat) : Role → Nat
  | .length => 0
  | .symbol => count states .length
  | .bit => count states .length + count states .symbol
private def afterValues (states : Nat) (role : Role) (data : Data) : List Nat :=
  match role with
  | .length => expressionValues states .symbol data ++ expressionValues states .bit data
  | .symbol => expressionValues states .bit data
  | .bit => []

private theorem beforeValues_length (states : Nat) (role : Role) (data : Data) :
    (beforeValues states role data).length = beforeCount states role := by
  cases role <;> simp only [beforeValues, beforeCount, List.length_nil, List.length_append, expressionValues_length]

def rootPosition (states : Nat) (role : Role) : Nat :=
  10 + beforeCount states role + count states role - 1

private theorem prepared_split (states : Nat) (role : Role) (data : Data) :
    preparedValues states data =
      (dataValues data ++ beforeValues states role data ++
        BuilderRegisterExpression.prefixValues (expression states role) (view (dataValues data))) ++
        [indexValue states role data] ++ afterValues states role data := by
  cases role <;>
    simp only [preparedValues, literalValues, beforeValues, afterValues, expressionValues_root,
      List.append_assoc, List.nil_append, List.append_nil]

private theorem getD_at_append (leading trailing : List Nat) (value : Nat) :
    (leading ++ [value] ++ trailing).getD leading.length 0 = value := by
  rw [List.append_assoc]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

private theorem prepared_root (states : Nat) (role : Role) (data : Data) (extra : List Nat) :
    (preparedValues states data ++ extra).getD (rootPosition states role) 0 = indexValue states role data := by
  have hCount := BuilderRegisterExpression.nodeCount_positive (expression states role)
  have hPosition : rootPosition states role =
      (dataValues data ++ beforeValues states role data ++
        BuilderRegisterExpression.prefixValues (expression states role) (view (dataValues data))).length := by
    simp only [rootPosition, List.length_append, dataValues_length, beforeValues_length,
      BuilderRegisterExpression.prefixValues_length, count] at hCount ⊢
    omega
  rw [prepared_split states role data, hPosition]
  simpa only [List.append_assoc] using getD_at_append
    (dataValues data ++ beforeValues states role data ++
      BuilderRegisterExpression.prefixValues (expression states role) (view (dataValues data)))
    (afterValues states role data ++ extra) (indexValue states role data)

def rootField (states : Nat) (role : Role) (extraCount : Nat) :
    BuilderRegisterPack.Field (preparedCount states + extraCount) :=
  .argument ⟨rootPosition states role, by
    have h := BuilderRegisterExpression.nodeCount_positive (expression states role)
    cases role <;> simp only [rootPosition, beforeCount, preparedCount] <;> omega⟩

private theorem rootField_eval (states : Nat) (role : Role) (extraCount : Nat)
    (data : Data) (extra : List Nat) :
    (rootField states role extraCount).eval (view (preparedValues states data ++ extra)) =
      indexValue states role data := by
  exact prepared_root states role data extra

def tagFields (states : Nat) : List (BuilderRegisterPack.Field (preparedCount states)) :=
  [.argument ⟨7, by simp only [preparedCount]; omega⟩]
def ordinaryFields (states : Nat) : List (BuilderRegisterPack.Field (preparedCount states + 1)) :=
  [rootField states .length 1, .constant 1, rootField states .symbol 1, .constant 1, .constant 1, .constant 3]
def offsetFields (states : Nat) : List (BuilderRegisterPack.Field (preparedCount states + 1)) :=
  [.argument ⟨6, by simp only [preparedCount]; omega⟩]
def certificateFields (states : Nat) (positive : Bool) : List (BuilderRegisterPack.Field (preparedCount states + 2)) :=
  [rootField states .bit 2, .constant (BuilderLocalConstraintPayload.signValue positive),
   rootField states .length 2, .constant 1, rootField states .symbol 2, .constant 1, .constant 2, .constant 3]

theorem tag_values (states : Nat) (data : Data) :
    BuilderRegisterPack.values (tagFields states) (view (preparedValues states data)) = [data.kind] := rfl
theorem offset_values (states : Nat) (data : Data) :
    BuilderRegisterPack.values (offsetFields states) (view (preparedValues states data ++ [data.kind])) = [data.offset] := rfl
theorem ordinary_values (states : Nat) (data : Data) :
    BuilderRegisterPack.values (ordinaryFields states) (view (preparedValues states data ++ [data.kind])) =
      BuilderInitialConstraintPayload.guardedValues (indexValue states .length data) (indexValue states .symbol data) := by
  change [(rootField states .length 1).eval (view (preparedValues states data ++ [data.kind])), 1,
    (rootField states .symbol 1).eval (view (preparedValues states data ++ [data.kind])), 1, 1, 3] =
      [indexValue states .length data, 1, indexValue states .symbol data, 1, 1, 3]
  rw [rootField_eval, rootField_eval]
theorem certificate_values (states : Nat) (data : Data) (positive : Bool) :
    BuilderRegisterPack.values (certificateFields states positive)
      (view (preparedValues states data ++ [data.kind, data.offset])) =
      BuilderInitialConstraintPayload.bitGuardedValues (indexValue states .length data)
        (indexValue states .bit data) (indexValue states .symbol data) positive := by
  change [(rootField states .bit 2).eval (view (preparedValues states data ++ [data.kind, data.offset])),
    BuilderLocalConstraintPayload.signValue positive,
    (rootField states .length 2).eval (view (preparedValues states data ++ [data.kind, data.offset])), 1,
    (rootField states .symbol 2).eval (view (preparedValues states data ++ [data.kind, data.offset])), 1, 2, 3] =
      [indexValue states .bit data, BuilderLocalConstraintPayload.signValue positive,
        indexValue states .length data, 1, indexValue states .symbol data, 1, 2, 3]
  rw [rootField_eval, rootField_eval, rootField_eval]


def ordinaryNode (states : Nat) : Node :=
  {name := 5, program := BuilderRegisterPack.machine (ordinaryFields states) 0,
   onAccept := .accept, onReject := .dead}
def positiveNode (states : Nat) : Node :=
  {name := 8, program := BuilderRegisterPack.machine (certificateFields states true) 0,
   onAccept := .accept, onReject := .dead}
def negativeNode (states : Nat) : Node :=
  {name := 9, program := BuilderRegisterPack.machine (certificateFields states false) 0,
   onAccept := .accept, onReject := .dead}
def offsetTestNode (states : Nat) : Node :=
  {name := 7, program := BuilderUnaryTagMatch.machine 0,
   onAccept := .node (positiveNode states).reference, onReject := .node (negativeNode states).reference}
def offsetPrepareNode (states : Nat) : Node :=
  {name := 6, program := BuilderRegisterPack.machine (offsetFields states) 0,
   onAccept := .node (offsetTestNode states).reference, onReject := .dead}
def kindNode (states : Nat) : Node :=
  {name := 4, program := BuilderUnaryTagMatch.machine 3,
   onAccept := .node (offsetPrepareNode states).reference, onReject := .node (ordinaryNode states).reference}
def tagPrepareNode (states : Nat) : Node :=
  {name := 3, program := BuilderRegisterPack.machine (tagFields states) 0,
   onAccept := .node (kindNode states).reference, onReject := .dead}
def bitNode (states : Nat) : Node :=
  {name := 2, program := BuilderRegisterExpression.machine (expression states .bit)
    (count states .length + count states .symbol),
   onAccept := .node (tagPrepareNode states).reference, onReject := .dead}
def symbolNode (states : Nat) : Node :=
  {name := 1, program := BuilderRegisterExpression.machine (expression states .symbol) (count states .length),
   onAccept := .node (bitNode states).reference, onReject := .dead}
def lengthNode (states : Nat) : Node :=
  {name := 0, program := BuilderRegisterExpression.machine (expression states .length) 0,
   onAccept := .node (symbolNode states).reference, onReject := .dead}

def graph (states : Nat) : Graph :=
  {nodes := [lengthNode states, symbolNode states, bitNode states, tagPrepareNode states, kindNode states,
    ordinaryNode states, offsetPrepareNode states, offsetTestNode states, positiveNode states, negativeNode states],
   entry := (lengthNode states).reference}
def machine (states : Nat) : WorkMachine := WorkMachineProgramGraph.machine (graph states)

theorem graph_nodes_length (states : Nat) : (graph states).nodes.length = 10 := rfl

private theorem length_mem (states : Nat) : lengthNode states ∈ (graph states).nodes := List.Mem.head _
private theorem symbol_mem (states : Nat) : symbolNode states ∈ (graph states).nodes :=
  List.Mem.tail _ (List.Mem.head _)
private theorem bit_mem (states : Nat) : bitNode states ∈ (graph states).nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
private theorem tagPrepare_mem (states : Nat) : tagPrepareNode states ∈ (graph states).nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
private theorem kind_mem (states : Nat) : kindNode states ∈ (graph states).nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
private theorem ordinary_mem (states : Nat) : ordinaryNode states ∈ (graph states).nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
private theorem offsetPrepare_mem (states : Nat) : offsetPrepareNode states ∈ (graph states).nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
private theorem offsetTest_mem (states : Nat) : offsetTestNode states ∈ (graph states).nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
private theorem positive_mem (states : Nat) : positiveNode states ∈ (graph states).nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
private theorem negative_mem (states : Nat) : negativeNode states ∈ (graph states).nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineProgramGraph.QueryDistinct ∧
    WorkMachineProgramGraph.NoRuleAt program program.acceptState ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧ program.acceptState ≠ program.rejectState
private theorem expression_good {arity : Nat} (expression : Expr arity) (afterCount : Nat) :
    Good (BuilderRegisterExpression.machine expression afterCount) :=
  ⟨BuilderRegisterExpression.rules_pairwise_query_distinct expression afterCount,
    BuilderRegisterExpression.noRuleAtAccept expression afterCount,
    BuilderRegisterExpression.noRuleAtReject expression afterCount,
    BuilderRegisterExpression.acceptState_ne_rejectState expression afterCount⟩
private theorem pack_good {arity : Nat} (fields : List (BuilderRegisterPack.Field arity)) :
    Good (BuilderRegisterPack.machine fields 0) :=
  ⟨BuilderRegisterPack.rules_pairwise_query_distinct fields 0,
    BuilderRegisterPack.noRuleAtAccept fields 0, BuilderRegisterPack.noRuleAtReject fields 0,
    BuilderRegisterPack.acceptState_ne_rejectState fields 0⟩
private theorem tag_good (expected : Nat) : Good (BuilderUnaryTagMatch.machine expected) :=
  ⟨BuilderUnaryTagMatch.rules_pairwise_query_distinct expected, BuilderUnaryTagMatch.noRuleAtAccept expected,
    BuilderUnaryTagMatch.noRuleAtReject expected, BuilderUnaryTagMatch.acceptState_ne_rejectState expected⟩

theorem graph_wellFormed (states : Nat) : (graph states).WellFormed := by
  have hNames : ((graph states).nodes.map Node.name).Pairwise (fun a b : Nat => a ≠ b) := by
    change ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : List Nat).Pairwise _
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.pairwise_map] using hNames
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact expression_good _ _
    · exact expression_good _ _
    · exact expression_good _ _
    · exact pack_good _
    · exact tag_good 3
    · exact pack_good _
    · exact pack_good _
    · exact tag_good 0
    · exact pack_good _
    · exact pack_good _
  · exact ⟨lengthNode states, length_mem states, rfl, rfl⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨symbolNode states, symbol_mem states, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨bitNode states, bit_mem states, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨tagPrepareNode states, tagPrepare_mem states, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨kindNode states, kind_mem states, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨offsetPrepareNode states, offsetPrepare_mem states, rfl, rfl⟩,
        ⟨ordinaryNode states, ordinary_mem states, rfl, rfl⟩⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨⟨offsetTestNode states, offsetTest_mem states, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨positiveNode states, positive_mem states, rfl, rfl⟩,
        ⟨negativeNode states, negative_mem states, rfl, rfl⟩⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨True.intro, True.intro⟩


private theorem pack_run {arity : Nat} (fields : List (BuilderRegisterPack.Field arity))
    (values older : List Nat) (inside : List WorkSymbol) (hLength : values.length = arity) :
    workRunExact? (BuilderRegisterPack.machine fields 0)
      (BuilderRegisterPack.workSteps fields (view values) [])
      (workStartConfiguration (BuilderRegisterPack.machine fields 0) (endTape (older ++ values) inside [])) =
      some
        {state := (BuilderRegisterPack.machine fields 0).acceptState,
         tape := endTape (older ++ values ++ BuilderRegisterPack.values fields (view values)) inside []} := by
  have h := BuilderRegisterPack.workRunExact fields 0 older (view values) [] inside [] rfl
  simpa only [BuilderRegisterPack.initialConfiguration, BuilderRegisterPack.finalConfiguration,
    view_ofFn values hLength, List.append_nil, List.drop_nil] using h

private theorem expression_run (states : Nat) (role : Role) (data : Data)
    (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? (BuilderRegisterExpression.machine (expression states role) (beforeCount states role))
      (BuilderRegisterExpression.workSteps (expression states role) (view (dataValues data)) (beforeValues states role data))
      (workStartConfiguration (BuilderRegisterExpression.machine (expression states role) (beforeCount states role))
        (endTape (older ++ dataValues data ++ beforeValues states role data) inside [])) =
      some
        {state := (BuilderRegisterExpression.machine (expression states role) (beforeCount states role)).acceptState,
         tape := endTape (older ++ dataValues data ++ beforeValues states role data ++ expressionValues states role data) inside []} := by
  have h := BuilderRegisterExpression.workRunExact (expression states role) (beforeCount states role)
    older (view (dataValues data)) (beforeValues states role data) inside [] (beforeValues_length states role data)
  simpa only [BuilderRegisterExpression.initialConfiguration, BuilderRegisterExpression.finalConfiguration,
    view_ofFn (dataValues data) (dataValues_length data), expressionValues, List.drop_nil] using h

def expressionSteps (states : Nat) (role : Role) (data : Data) : Nat :=
  BuilderRegisterExpression.workSteps (expression states role) (view (dataValues data)) (beforeValues states role data)
def tagSteps (states : Nat) (data : Data) : Nat :=
  BuilderRegisterPack.workSteps (tagFields states) (view (preparedValues states data)) []
def ordinarySteps (states : Nat) (data : Data) : Nat :=
  BuilderRegisterPack.workSteps (ordinaryFields states) (view (preparedValues states data ++ [data.kind])) []
def offsetSteps (states : Nat) (data : Data) : Nat :=
  BuilderRegisterPack.workSteps (offsetFields states) (view (preparedValues states data ++ [data.kind])) []
def certificateSteps (states : Nat) (data : Data) : Nat :=
  BuilderRegisterPack.workSteps (certificateFields states (decide (data.offset = 0)))
    (view (preparedValues states data ++ [data.kind, data.offset])) []
def branchSteps (states : Nat) (data : Data) : Nat :=
  if data.kind = 3 then offsetSteps states data + 1 + (3 + 1 + (certificateSteps states data + 1))
  else ordinarySteps states data + 1
def tailSteps (states : Nat) (data : Data) : Nat :=
  tagSteps states data + 1 + (BuilderUnaryTagMatch.workSteps 3 data.kind + 1 + branchSteps states data)
def workSteps (states : Nat) (data : Data) : Nat :=
  expressionSteps states .length data + 1 + (expressionSteps states .symbol data + 1 +
    (expressionSteps states .bit data + 1 + tailSteps states data))

private theorem tag_zero (actual : Nat) : BuilderUnaryTagMatch.workSteps 0 actual = 3 := by
  simp only [BuilderUnaryTagMatch.workSteps, Nat.min_zero, Nat.mul_zero, Nat.zero_add]

private theorem tag_accept (expected actual : Nat) (older : List Nat) (inside : List WorkSymbol)
    (hEqual : actual = expected) :
    workRunExact? (BuilderUnaryTagMatch.machine expected) (BuilderUnaryTagMatch.workSteps expected actual)
      (workStartConfiguration (BuilderUnaryTagMatch.machine expected) (endTape (older ++ [actual]) inside [])) =
      some {state := (BuilderUnaryTagMatch.machine expected).acceptState, tape := endTape (older ++ [actual]) inside []} := by
  subst actual
  exact BuilderUnaryTagMatch.accept_workRunExact expected older inside []

private theorem tail_path (states : Nat) (data : Data) (older : List Nat) (inside : List WorkSymbol) :
    AcceptPath (graph states) (.node (tagPrepareNode states).reference) .accept (tailSteps states data)
      (endTape (older ++ preparedValues states data) inside [])
      (endTape (older ++ outputValues states data) inside []) := by
  have hKind : AcceptPath (graph states) (.node (kindNode states).reference) .accept
      (BuilderUnaryTagMatch.workSteps 3 data.kind + 1 + branchSteps states data)
      (endTape (older ++ preparedValues states data ++ [data.kind]) inside [])
      (endTape (older ++ outputValues states data) inside []) := by
    by_cases hCertificate : data.kind = 3
    · have hOffsetPath : AcceptPath (graph states) (.node (offsetTestNode states).reference) .accept
          (3 + 1 + (certificateSteps states data + 1))
          (endTape (older ++ preparedValues states data ++ [data.kind, data.offset]) inside [])
          (endTape (older ++ outputValues states data) inside []) := by
        have hReport := pack_run (certificateFields states (decide (data.offset = 0)))
          (preparedValues states data ++ [data.kind, data.offset]) older inside (by
            simp only [List.length_append, preparedValues_length, List.length_cons, List.length_nil])
        rw [certificate_values] at hReport
        simp only [List.append_assoc] at hReport
        by_cases hZero : data.offset = 0
        · have hFlag : decide (data.offset = 0) = true := by simp only [hZero, decide_true]
          rw [hFlag] at hReport
          have hP := AcceptPath.step (positiveNode states) .accept _ 0 _ _ _
            (positive_mem states) hReport (.terminal .accept _)
          have hTest := tag_accept 0 data.offset (older ++ preparedValues states data ++ [data.kind]) inside hZero
          simp only [List.append_assoc, List.cons_append, List.nil_append] at hTest
          have h := AcceptPath.step (offsetTestNode states) .accept _ _ _ _ _
            (offsetTest_mem states) hTest hP
          simpa only [certificateSteps, hFlag, outputValues, payloadValues, if_pos hCertificate,
            tag_zero, Nat.add_zero, List.append_assoc, List.cons_append, List.nil_append] using h
        · have hFlag : decide (data.offset = 0) = false := by simp only [hZero, decide_false]
          rw [hFlag] at hReport
          have hP := AcceptPath.step (negativeNode states) .accept _ 0 _ _ _
            (negative_mem states) hReport (.terminal .accept _)
          have hTest := BuilderUnaryTagMatch.reject_workRunExact 0 data.offset
            (older ++ preparedValues states data ++ [data.kind]) inside [] hZero
          simp only [List.append_assoc, List.cons_append, List.nil_append] at hTest
          have h := AcceptPath.stepReject (offsetTestNode states) .accept _ _ _ _ _
            (offsetTest_mem states) hTest hP
          simpa only [certificateSteps, hFlag, outputValues, payloadValues, if_pos hCertificate,
            tag_zero, Nat.add_zero, List.append_assoc, List.cons_append, List.nil_append] using h
      have hOffset := pack_run (offsetFields states) (preparedValues states data ++ [data.kind]) older inside (by
        simp only [List.length_append, preparedValues_length, List.length_cons, List.length_nil])
      rw [offset_values] at hOffset
      simp only [List.append_assoc, List.cons_append, List.nil_append] at hOffset hOffsetPath
      have hP := AcceptPath.step (offsetPrepareNode states) .accept _ _ _ _ _
        (offsetPrepare_mem states) hOffset hOffsetPath
      have hTest := tag_accept 3 data.kind (older ++ preparedValues states data) inside hCertificate
      simp only [List.append_assoc] at hTest
      have h := AcceptPath.step (kindNode states) .accept _ _ _ _ _ (kind_mem states) hTest hP
      simpa only [branchSteps, if_pos hCertificate, offsetSteps, List.append_assoc] using h
    · have hReport := pack_run (ordinaryFields states) (preparedValues states data ++ [data.kind]) older inside (by
        simp only [List.length_append, preparedValues_length, List.length_cons, List.length_nil])
      rw [ordinary_values] at hReport
      simp only [List.append_assoc] at hReport
      have hP := AcceptPath.step (ordinaryNode states) .accept _ 0 _ _ _
        (ordinary_mem states) hReport (.terminal .accept _)
      have hTest := BuilderUnaryTagMatch.reject_workRunExact 3 data.kind
        (older ++ preparedValues states data) inside [] hCertificate
      simp only [List.append_assoc] at hTest
      have h := AcceptPath.stepReject (kindNode states) .accept _ _ _ _ _ (kind_mem states) hTest hP
      simpa only [branchSteps, if_neg hCertificate, ordinarySteps, outputValues, payloadValues,
        List.append_assoc, Nat.add_zero] using h
  have hPack := pack_run (tagFields states) (preparedValues states data) older inside (preparedValues_length states data)
  rw [tag_values] at hPack
  simp only [List.append_assoc] at hPack hKind
  have h := AcceptPath.step (tagPrepareNode states) .accept _ _ _ _ _ (tagPrepare_mem states) hPack hKind
  simpa only [tailSteps, tagSteps] using h

def initialConfiguration (states : Nat) (data : Data) (older : List Nat) (inside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration (machine states) (endTape (older ++ dataValues data) inside [])
def finalConfiguration (states : Nat) (data : Data) (older : List Nat) (inside : List WorkSymbol) : WorkConfiguration :=
  {state := (machine states).acceptState, tape := endTape (older ++ outputValues states data) inside []}

theorem workRunExact (states : Nat) (data : Data) (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? (machine states) (workSteps states data) (initialConfiguration states data older inside) =
      some (finalConfiguration states data older inside) := by
  have hTail := tail_path states data older inside
  have hBit := expression_run states .bit data older inside
  simp only [beforeCount, beforeValues, List.append_assoc] at hBit
  simp only [preparedValues, literalValues, List.append_assoc] at hTail
  have hB := AcceptPath.step (bitNode states) .accept _ _ _ _ _ (bit_mem states) hBit hTail
  have hSymbol := expression_run states .symbol data older inside
  simp only [beforeCount, beforeValues, List.append_assoc] at hSymbol
  have hS := AcceptPath.step (symbolNode states) .accept _ _ _ _ _ (symbol_mem states) hSymbol hB
  have hLength := expression_run states .length data older inside
  simp only [beforeCount, beforeValues, List.append_nil, List.append_assoc] at hLength
  have hL := AcceptPath.step (lengthNode states) .accept _ _ _ _ _ (length_mem states) hLength hS
  have h := WorkMachineProgramPath.runExact (graph states) _ _ _ _ _ (graph_wellFormed states) hL
  have hStart (tape : WorkTape) : WorkMachineProgramGraph.endpointConfiguration (.node (lengthNode states).reference) tape =
      workStartConfiguration (machine states) tape := rfl
  have hMachine : WorkMachineProgramGraph.machine (graph states) = machine states := rfl
  have hAccept (tape : WorkTape) : WorkMachineProgramGraph.endpointConfiguration .accept tape =
      {state := (machine states).acceptState, tape := tape} := rfl
  rw [hStart, hMachine, hAccept] at h
  simpa only [initialConfiguration, finalConfiguration, workSteps, expressionSteps, beforeValues, List.append_assoc] using h

theorem run_compile_exact (states : Nat) (data : Data) (older : List Nat) (inside : List WorkSymbol) :
    run (compileWorkMachine (machine states)) (6 * workSteps states data)
      (encodeWorkConfiguration (initialConfiguration states data older inside)) =
      encodeWorkConfiguration (finalConfiguration states data older inside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact states data older inside)
theorem final_tape (states : Nat) (data : Data) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration states data older inside).tape = endTape (older ++ outputValues states data) inside [] := rfl
theorem final_frontier (states : Nat) (data : Data) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration states data older inside).tape.left = [] := rfl
theorem final_accept (states : Nat) (data : Data) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration states data older inside).state = (machine states).acceptState := rfl
theorem rules_pairwise_query_distinct (states : Nat) :
    (machine states).rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise (graph states) (graph_wellFormed states)
theorem noRuleAtAccept (states : Nat) :
    WorkMachineProgramGraph.NoRuleAt (machine states) (machine states).acceptState :=
  WorkMachineProgramGraph.noRuleAt_globalAccept (graph states)
theorem noRuleAtReject (states : Nat) :
    WorkMachineProgramGraph.NoRuleAt (machine states) (machine states).rejectState :=
  WorkMachineProgramGraph.noRuleAt_globalReject (graph states)
theorem acceptState_ne_rejectState (states : Nat) : (machine states).acceptState ≠ (machine states).rejectState := by
  change (0 : Nat) ≠ 1
  decide


def lengthSpan (states : Nat) (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterExpression.spanPolynomial (expression states .length) bound
def symbolSpan (states : Nat) (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterExpression.spanPolynomial (expression states .symbol) (lengthSpan states bound)
def literalSpan (states : Nat) (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterExpression.spanPolynomial (expression states .bit) (symbolSpan states bound)
def tagSpan (states : Nat) (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterPack.spanPolynomial (tagFields states) (literalSpan states bound)
def ordinarySpan (states : Nat) (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterPack.spanPolynomial (ordinaryFields states) (tagSpan states bound)
def offsetSpan (states : Nat) (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterPack.spanPolynomial (offsetFields states) (tagSpan states bound)
def certificateSpan (states : Nat) (positive : Bool) (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterPack.spanPolynomial (certificateFields states positive) (offsetSpan states bound)
def spanPolynomial (states : Nat) (bound : NatPolynomial) : NatPolynomial :=
  .add (ordinarySpan states bound) (.add (certificateSpan states true bound) (certificateSpan states false bound))
def rawTimePolynomial (states : Nat) (bound : NatPolynomial) : NatPolynomial :=
  .add (BuilderRegisterExpression.rawTimePolynomial (expression states .length) bound)
    (.add (BuilderRegisterExpression.rawTimePolynomial (expression states .symbol) (lengthSpan states bound))
    (.add (BuilderRegisterExpression.rawTimePolynomial (expression states .bit) (symbolSpan states bound))
    (.add (BuilderRegisterPack.rawTimePolynomial (tagFields states) (literalSpan states bound))
    (.add (BuilderRegisterPack.rawTimePolynomial (ordinaryFields states) (tagSpan states bound))
    (.add (BuilderRegisterPack.rawTimePolynomial (offsetFields states) (tagSpan states bound))
    (.add (BuilderRegisterPack.rawTimePolynomial (certificateFields states true) (offsetSpan states bound))
    (.add (BuilderRegisterPack.rawTimePolynomial (certificateFields states false) (offsetSpan states bound))
      (.constant 120))))))))

private theorem expression_bounds (states : Nat) (role : Role) (data : Data)
    (older : List Nat) (bound : NatPolynomial) (inputSize : Nat)
    (hSpan : (registerWord (older ++ dataValues data ++ beforeValues states role data)).length ≤ bound.eval inputSize) :
    (registerWord (older ++ dataValues data ++ beforeValues states role data ++ expressionValues states role data)).length ≤
        (BuilderRegisterExpression.spanPolynomial (expression states role) bound).eval inputSize ∧
      6 * expressionSteps states role data ≤
        (BuilderRegisterExpression.rawTimePolynomial (expression states role) bound).eval inputSize := by
  have h := BuilderRegisterExpression.source_polynomial_bounds (expression states role) bound inputSize
    older (view (dataValues data)) (beforeValues states role data) (by
      simpa only [view_ofFn (dataValues data) (dataValues_length data)] using hSpan)
  simpa only [view_ofFn (dataValues data) (dataValues_length data), expressionValues, expressionSteps] using h

private theorem pack_bounds {arity : Nat} (fields : List (BuilderRegisterPack.Field arity))
    (values older : List Nat) (bound : NatPolynomial) (inputSize : Nat)
    (hLength : values.length = arity)
    (hSpan : (registerWord (older ++ values)).length ≤ bound.eval inputSize) :
    (registerWord (older ++ values ++ BuilderRegisterPack.values fields (view values))).length ≤
        (BuilderRegisterPack.spanPolynomial fields bound).eval inputSize ∧
      6 * BuilderRegisterPack.workSteps fields (view values) [] ≤
        (BuilderRegisterPack.rawTimePolynomial fields bound).eval inputSize := by
  have h := BuilderRegisterPack.source_polynomial_bounds fields bound inputSize older (view values) [] (by
    simpa only [view_ofFn values hLength, List.append_nil] using hSpan)
  simpa only [view_ofFn values hLength, List.append_nil] using h

/-- All index computations, field copies, retained scratch, tag scans and eight possible outer joins are charged. -/
theorem source_polynomial_bounds (states : Nat) (data : Data) (older : List Nat)
    (bound : NatPolynomial) (inputSize : Nat)
    (hSpan : (registerWord (older ++ dataValues data)).length ≤ bound.eval inputSize) :
    (registerWord (older ++ outputValues states data)).length ≤ (spanPolynomial states bound).eval inputSize ∧
      6 * workSteps states data ≤ (rawTimePolynomial states bound).eval inputSize := by
  have hLength := expression_bounds states .length data older bound inputSize (by
    simpa only [beforeValues, List.append_nil] using hSpan)
  have hSymbol := expression_bounds states .symbol data older (lengthSpan states bound) inputSize (by
    simpa only [beforeValues, lengthSpan, List.append_nil] using hLength.1)
  have hBit := expression_bounds states .bit data older (symbolSpan states bound) inputSize (by
    simpa only [beforeValues, symbolSpan, List.append_assoc] using hSymbol.1)
  have hPrepared : (registerWord (older ++ preparedValues states data)).length ≤
      (literalSpan states bound).eval inputSize := by
    simpa only [preparedValues, literalValues, beforeValues, literalSpan, List.append_assoc] using hBit.1
  have hPack := pack_bounds (tagFields states) (preparedValues states data) older (literalSpan states bound) inputSize
    (preparedValues_length states data) hPrepared
  rw [tag_values] at hPack
  have hTag : (registerWord (older ++ (preparedValues states data ++ [data.kind]))).length ≤
      (tagSpan states bound).eval inputSize := by
    simpa only [tagSpan, List.append_assoc] using hPack.1
  have hTagSteps : BuilderUnaryTagMatch.workSteps 3 data.kind ≤ 9 :=
    BuilderUnaryTagMatch.workSteps_le 3 data.kind
  by_cases hKind : data.kind = 3
  · have hOffset := pack_bounds (offsetFields states) (preparedValues states data ++ [data.kind])
      older (tagSpan states bound) inputSize (by
        simp only [List.length_append, preparedValues_length, List.length_cons, List.length_nil]) hTag
    rw [offset_values] at hOffset
    have hReport := pack_bounds (certificateFields states (decide (data.offset = 0)))
      (preparedValues states data ++ [data.kind, data.offset]) older (offsetSpan states bound) inputSize (by
        simp only [List.length_append, preparedValues_length, List.length_cons, List.length_nil]) (by
        simpa only [offsetSpan, List.append_assoc, List.cons_append, List.nil_append] using hOffset.1)
    rw [certificate_values] at hReport
    by_cases hZero : data.offset = 0
    · have hFlag : decide (data.offset = 0) = true := by simp only [hZero, decide_true]
      rw [hFlag] at hReport
      constructor
      · have hFinal : (registerWord (older ++ outputValues states data)).length ≤
            (certificateSpan states true bound).eval inputSize := by
          simpa only [outputValues, payloadValues, if_pos hKind, hFlag, certificateSpan,
            List.append_assoc, List.cons_append, List.nil_append] using hReport.1
        simp only [spanPolynomial, NatPolynomial.eval_add]
        omega
      · simp only [workSteps, tailSteps, branchSteps, if_pos hKind, tagSteps, offsetSteps, certificateSteps,
          hFlag, rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant, Nat.mul_add, Nat.mul_one]
        omega
    · have hFlag : decide (data.offset = 0) = false := by simp only [hZero, decide_false]
      rw [hFlag] at hReport
      constructor
      · have hFinal : (registerWord (older ++ outputValues states data)).length ≤
            (certificateSpan states false bound).eval inputSize := by
          simpa only [outputValues, payloadValues, if_pos hKind, hFlag, certificateSpan,
            List.append_assoc, List.cons_append, List.nil_append] using hReport.1
        simp only [spanPolynomial, NatPolynomial.eval_add]
        omega
      · simp only [workSteps, tailSteps, branchSteps, if_pos hKind, tagSteps, offsetSteps, certificateSteps,
          hFlag, rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant, Nat.mul_add, Nat.mul_one]
        omega
  · have hReport := pack_bounds (ordinaryFields states) (preparedValues states data ++ [data.kind])
      older (tagSpan states bound) inputSize (by
        simp only [List.length_append, preparedValues_length, List.length_cons, List.length_nil]) hTag
    rw [ordinary_values] at hReport
    constructor
    · have hFinal : (registerWord (older ++ outputValues states data)).length ≤
          (ordinarySpan states bound).eval inputSize := by
        simpa only [outputValues, payloadValues, if_neg hKind, ordinarySpan, List.append_assoc] using hReport.1
      simp only [spanPolynomial, NatPolynomial.eval_add]
      omega
    · simp only [workSteps, tailSteps, branchSteps, if_neg hKind, tagSteps, ordinarySteps,
        rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant, Nat.mul_add, Nat.mul_one]
      omega

theorem payload_span_le_output (states : Nat) (data : Data) :
    (registerWord (payloadValues states data)).length ≤ (registerWord (outputValues states data)).length := by
  obtain ⟨history, h⟩ := output_suffix states data
  rw [h, registerWord_append, List.length_append]
  omega


def resolvedSymbol (input : BitString) : Request width → Nat → TapeSymbol
  | .blank, _ => .blank
  | .fixed value, _ => VerifierTableauProblem.symbolOfFixedBit value
  | .sourceBit index, _ => BuilderInitialConstraintPayload.sourceSymbol input[index]?
  | .certificate _, offset => if offset = 0 then .one else .zero

theorem resolvedSymbol_code (input : BitString) (request : Request width) (offset : Nat) :
    VariableLayout.tapeSymbolCode (resolvedSymbol input request offset) =
      BuilderInitialRequestResolution.symbolCode input request offset := by
  cases request with
  | blank => rfl
  | fixed value => cases value <;> rfl
  | sourceBit index => exact BuilderInitialConstraintPayload.sourceSymbol_code _
  | certificate index => cases offset <;> rfl

def canonicalData {language : Language} (problem : VerifierTableauProblem language)
    (length : Fin (problem.certificateLimit + 1))
    (position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode))
    (request : Request problem.certificateLimit) (offset : Nat) : Data :=
  ofResolved (BuilderInitialPairedCellSource.metadata problem length.val) position.val offset request problem.input

theorem canonical_dimensions {language : Language} (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (length : Fin (problem.certificateLimit + 1))
    (position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode))
    (request : Request problem.certificateLimit) (offset : Nat) :
    timeCount (canonicalData problem length position request offset) = problem.dimensions.timeCount ∧
      tapeWidth (canonicalData problem length position request offset) =
        problem.dimensions.tapeWidth problem.tableauInputMode ∧
      stateCount problem.verifier = problem.dimensions.stateBound ∧
      certificateBound (canonicalData problem length position request offset) = problem.layout.certificateBitWidth := by
  have hLength := length.isLt
  have hCertificate : certificateBound (canonicalData problem length position request offset) = problem.certificateLimit := by
    simp only [certificateBound, canonicalData, ofResolved, BuilderInitialPairedCellSource.metadata,
      BuilderInitialPairedCellSource.rowCount]
    omega
  refine ⟨rfl, ?_, stateCount_canonical problem, hCertificate.trans (problem.certificateBitWidth_eq_of_paired hMode).symm⟩
  rw [tapeWidth, hCertificate]
  simp only [Dimensions.tapeWidth, hMode, Dimensions.encodedInputLength,
    VerifierTableauProblem.dimensions_inputLength, VerifierTableauProblem.dimensions_certificateBound,
    VerifierTableauProblem.dimensions_timeBound, BitString.size]
  rfl

private theorem length_environment {language : Language} (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (length : Fin (problem.certificateLimit + 1))
    (position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode))
    (request : Request problem.certificateLimit) (offset : Nat) :
    literalEnvironment (stateCount problem.verifier) .length (canonicalData problem length position request offset) =
      ((.certificateLength (problem.pairedCertificateLengthIndex hMode length) :
        BuilderLiteralIndexExpression.Request problem.layout)).environment := by
  have h := canonical_dimensions problem hMode length position request offset
  funext index
  rcases index with ⟨index, hIndex⟩
  have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by omega
  rcases hCases with hi | hi | hi | hi | hi | hi | hi | hi <;> subst index <;>
    first | exact h.1 | exact h.2.1 | exact h.2.2.1 | exact h.2.2.2 | rfl

private theorem symbol_environment {language : Language} (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (length : Fin (problem.certificateLimit + 1))
    (position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode))
    (request : Request problem.certificateLimit) (offset : Nat) :
    literalEnvironment (stateCount problem.verifier) .symbol (canonicalData problem length position request offset) =
      ((.symbol problem.initialTime position (resolvedSymbol problem.input request offset) :
        BuilderLiteralIndexExpression.Request problem.layout)).environment := by
  have h := canonical_dimensions problem hMode length position request offset
  funext index
  rcases index with ⟨index, hIndex⟩
  have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by omega
  rcases hCases with hi | hi | hi | hi | hi | hi | hi | hi <;> subst index <;>
    first | exact h.1 | exact h.2.1 | exact h.2.2.1 | exact h.2.2.2 |
      exact (resolvedSymbol_code problem.input request offset).symm | rfl

private theorem bit_environment {language : Language} (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (length : Fin (problem.certificateLimit + 1))
    (position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode))
    (index : Fin problem.certificateLimit) (offset : Nat) :
    literalEnvironment (stateCount problem.verifier) .bit (canonicalData problem length position (.certificate index) offset) =
      ((.certificateBit (problem.pairedCertificateBitIndex hMode index) :
        BuilderLiteralIndexExpression.Request problem.layout)).environment := by
  have h := canonical_dimensions problem hMode length position (.certificate index) offset
  funext fieldIndex
  rcases fieldIndex with ⟨fieldIndex, hIndex⟩
  have hCases : fieldIndex = 0 ∨ fieldIndex = 1 ∨ fieldIndex = 2 ∨ fieldIndex = 3 ∨
      fieldIndex = 4 ∨ fieldIndex = 5 ∨ fieldIndex = 6 ∨ fieldIndex = 7 := by omega
  rcases hCases with hi | hi | hi | hi | hi | hi | hi | hi <;> subst fieldIndex <;>
    first | exact h.1 | exact h.2.1 | exact h.2.2.1 | exact h.2.2.2 | rfl

theorem length_index_canonical {language : Language} (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (length : Fin (problem.certificateLimit + 1))
    (position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode))
    (request : Request problem.certificateLimit) (offset : Nat) :
    indexValue (stateCount problem.verifier) .length (canonicalData problem length position request offset) =
      (problem.pairedLengthLiteral hMode length).index.val := by
  rw [indexValue, expression_eval, length_environment problem hMode length position request offset]
  exact BuilderLiteralIndexExpression.eval_eq_index
    (.certificateLength (problem.pairedCertificateLengthIndex hMode length))

theorem symbol_index_canonical {language : Language} (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (length : Fin (problem.certificateLimit + 1))
    (position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode))
    (request : Request problem.certificateLimit) (offset : Nat) :
    indexValue (stateCount problem.verifier) .symbol (canonicalData problem length position request offset) =
      (problem.symbolLiteral problem.initialTime position (resolvedSymbol problem.input request offset)).index.val := by
  rw [indexValue, expression_eval, symbol_environment problem hMode length position request offset]
  exact BuilderLiteralIndexExpression.eval_eq_index
    (.symbol problem.initialTime position (resolvedSymbol problem.input request offset) :
      BuilderLiteralIndexExpression.Request problem.layout)

theorem bit_index_canonical {language : Language} (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (length : Fin (problem.certificateLimit + 1))
    (position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode))
    (index : Fin problem.certificateLimit) (offset : Nat) :
    indexValue (stateCount problem.verifier) .bit (canonicalData problem length position (.certificate index) offset) =
      (problem.pairedBitLiteral hMode index).index.val := by
  rw [indexValue, expression_eval, bit_environment problem hMode length position index offset]
  exact BuilderLiteralIndexExpression.eval_eq_index
    (.certificateBit (problem.pairedCertificateBitIndex hMode index))

/-- Valid one/two-slot offsets yield the unchanged canonical initial-cell payload. -/
theorem canonical_payload {language : Language} (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (length : Fin (problem.certificateLimit + 1))
    (position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode))
    (request : Request problem.certificateLimit) (offset : Nat)
    (hOffset : offset < BuilderInitialCellCoordinates.requestWidth request) :
    BuilderInitialConstraintPayload.requestValues problem hMode length position request offset =
      some (payloadValues (stateCount problem.verifier) (canonicalData problem length position request offset)) := by
  cases request with
  | blank =>
      have hZero : offset = 0 := by change offset < 1 at hOffset; omega
      subst offset
      change some (BuilderInitialConstraintPayload.guardedValues _ _) =
        some (BuilderInitialConstraintPayload.guardedValues
          (indexValue _ .length (canonicalData problem length position .blank 0))
          (indexValue _ .symbol (canonicalData problem length position .blank 0)))
      rw [length_index_canonical problem hMode, symbol_index_canonical problem hMode]
      rfl
  | fixed value =>
      have hZero : offset = 0 := by change offset < 1 at hOffset; omega
      subst offset
      change some (BuilderInitialConstraintPayload.guardedValues _ _) =
        some (BuilderInitialConstraintPayload.guardedValues
          (indexValue _ .length (canonicalData problem length position (.fixed value) 0))
          (indexValue _ .symbol (canonicalData problem length position (.fixed value) 0)))
      rw [length_index_canonical problem hMode, symbol_index_canonical problem hMode]
      rfl
  | sourceBit index =>
      have hZero : offset = 0 := by change offset < 1 at hOffset; omega
      subst offset
      change some (BuilderInitialConstraintPayload.guardedValues _ _) =
        some (BuilderInitialConstraintPayload.guardedValues
          (indexValue _ .length (canonicalData problem length position (.sourceBit index) 0))
          (indexValue _ .symbol (canonicalData problem length position (.sourceBit index) 0)))
      rw [length_index_canonical problem hMode, symbol_index_canonical problem hMode]
      rfl
  | certificate index =>
      have hCases : offset = 0 ∨ offset = 1 := by change offset < 2 at hOffset; omega
      rcases hCases with hZero | hOne
      · subst offset
        change some (BuilderInitialConstraintPayload.bitGuardedValues _ _ _ true) =
          some (BuilderInitialConstraintPayload.bitGuardedValues
            (indexValue _ .length (canonicalData problem length position (.certificate index) 0))
            (indexValue _ .bit (canonicalData problem length position (.certificate index) 0))
            (indexValue _ .symbol (canonicalData problem length position (.certificate index) 0)) true)
        rw [length_index_canonical problem hMode, bit_index_canonical problem hMode, symbol_index_canonical problem hMode]
        rfl
      · subst offset
        change some (BuilderInitialConstraintPayload.bitGuardedValues _ _ _ false) =
          some (BuilderInitialConstraintPayload.bitGuardedValues
            (indexValue _ .length (canonicalData problem length position (.certificate index) 1))
            (indexValue _ .bit (canonicalData problem length position (.certificate index) 1))
            (indexValue _ .symbol (canonicalData problem length position (.certificate index) 1)) false)
        rw [length_index_canonical problem hMode, bit_index_canonical problem hMode, symbol_index_canonical problem hMode]
        rfl

end PNP.Concrete.CookLevin.BuilderInitialPairedLiteralPayload
