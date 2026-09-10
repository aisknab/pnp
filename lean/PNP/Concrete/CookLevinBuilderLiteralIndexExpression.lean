/-
Copyright (c) 2026 PNP Labs.

Fixed register-expression kernels for every canonical tableau literal family.
The kind selects one of five fixed branch programs; coordinate values are read
from the materialized eight-register environment, not compiled into control.
Typed requests specify the canonical result and establish its size bounds.
They do not construct the physical environment or choose a runtime route.
-/

import PNP.Concrete.CookLevinBuilderRegisterExpression
import PNP.Concrete.CookLevinFormulaSize

namespace PNP.Concrete.CookLevin.BuilderLiteralIndexExpression

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderRegisterExpression (Expr)

inductive Kind where
  | symbol | head | state | certificateBit | certificateLength
  deriving DecidableEq, Repr

inductive Request (layout : VariableLayout) where
  | symbol (time : Fin layout.dimensions.timeCount)
      (position : Fin (layout.dimensions.tapeWidth layout.mode)) (symbol : TapeSymbol)
  | head (time : Fin layout.dimensions.timeCount)
      (position : Fin (layout.dimensions.tapeWidth layout.mode))
  | state (time : Fin layout.dimensions.timeCount) (state : Fin layout.dimensions.stateBound)
  | certificateBit (index : Fin layout.certificateBitWidth)
  | certificateLength (length : Fin layout.certificateLengthWidth)

private structure Coordinates where
  time : Nat
  position : Nat
  state : Nat
  code : Nat

private theorem timeCount_le_variableCount (layout : VariableLayout) :
    layout.dimensions.timeCount ≤ layout.variableCount := by
  have hWidth := layout.dimensions.tapeWidth_positive layout.mode
  have h := Nat.mul_le_mul_left layout.dimensions.timeCount (Nat.succ_le_of_lt hWidth)
  simp only [Nat.mul_one] at h
  exact Nat.le_trans h (VariableLayout.headWidth_le_variableCount layout)

namespace Request

def kind {layout : VariableLayout} : Request layout → Kind
  | .symbol _ _ _ => .symbol
  | .head _ _ => .head
  | .state _ _ => .state
  | .certificateBit _ => .certificateBit
  | .certificateLength _ => .certificateLength

def index {layout : VariableLayout} : Request layout → Nat
  | .symbol time position tapeSymbol => layout.symbolVariable time position tapeSymbol
  | .head time position => layout.headVariable time position
  | .state time stateValue => layout.stateVariable time stateValue
  | .certificateBit index => layout.certificateBitVariable index
  | .certificateLength length => layout.certificateLengthVariable length

theorem index_lt {layout : VariableLayout} (request : Request layout) :
    request.index < layout.variableCount := by
  cases request with
  | symbol time position symbol => exact layout.symbolVariable_lt_variableCount time position symbol
  | head time position => exact layout.headVariable_lt_variableCount time position
  | state time state => exact layout.stateVariable_lt_variableCount time state
  | certificateBit index => exact layout.certificateBitVariable_lt_variableCount index
  | certificateLength length => exact layout.certificateLengthVariable_lt_variableCount length

private def coordinates {layout : VariableLayout} : Request layout → Coordinates
  | .symbol time position tapeSymbol => ⟨time.val, position.val, 0, VariableLayout.tapeSymbolCode tapeSymbol⟩
  | .head time position => ⟨time.val, position.val, 0, 0⟩
  | .state time stateValue => ⟨time.val, 0, stateValue.val, 0⟩
  | .certificateBit index => ⟨0, index.val, 0, 0⟩
  | .certificateLength length => ⟨0, length.val, 0, 0⟩

/-- T, W, S, C, time, position, state, symbol-code in this fixed order. -/
def environment {layout : VariableLayout} (request : Request layout) : Fin 8 → Nat :=
  fun field => match field.val with
  | 0 => layout.dimensions.timeCount
  | 1 => layout.dimensions.tapeWidth layout.mode
  | 2 => layout.dimensions.stateBound
  | 3 => layout.certificateBitWidth
  | 4 => request.coordinates.time
  | 5 => request.coordinates.position
  | 6 => request.coordinates.state
  | 7 => request.coordinates.code
  | _ => 0

private theorem environment_values {layout : VariableLayout} (request : Request layout) :
    List.ofFn request.environment =
      [layout.dimensions.timeCount, layout.dimensions.tapeWidth layout.mode,
        layout.dimensions.stateBound, layout.certificateBitWidth,
        request.coordinates.time, request.coordinates.position,
        request.coordinates.state, request.coordinates.code] := rfl

private theorem coordinate_bounds {layout : VariableLayout} (request : Request layout) :
    request.coordinates.time ≤ layout.variableCount ∧
      request.coordinates.position ≤ layout.variableCount ∧
        request.coordinates.state ≤ layout.variableCount ∧
          request.coordinates.code ≤ layout.variableCount := by
  cases request with
  | symbol time position symbol =>
      exact ⟨Nat.le_trans (Nat.le_of_lt time.isLt) (timeCount_le_variableCount layout),
        Nat.le_trans (Nat.le_of_lt position.isLt) (layout.tapeWidth_le_variableCount),
        Nat.zero_le _,
        Nat.le_trans (Nat.le_of_lt (VariableLayout.tapeSymbolCode_lt_three symbol))
          layout.three_le_variableCount⟩
  | head time position =>
      exact ⟨Nat.le_trans (Nat.le_of_lt time.isLt) (timeCount_le_variableCount layout),
        Nat.le_trans (Nat.le_of_lt position.isLt) layout.tapeWidth_le_variableCount,
        Nat.zero_le _, Nat.zero_le _⟩
  | state time state =>
      exact ⟨Nat.le_trans (Nat.le_of_lt time.isLt) (timeCount_le_variableCount layout),
        Nat.zero_le _, Nat.le_trans (Nat.le_of_lt state.isLt) layout.stateBound_le_variableCount,
        Nat.zero_le _⟩
  | certificateBit index =>
      exact ⟨Nat.zero_le _, Nat.le_trans (Nat.le_of_lt index.isLt) layout.certificateBitWidth_le_variableCount,
        Nat.zero_le _, Nat.zero_le _⟩
  | certificateLength length =>
      exact ⟨Nat.zero_le _, Nat.le_trans (Nat.le_of_lt length.isLt) layout.certificateLengthWidth_le_variableCount,
        Nat.zero_le _, Nat.zero_le _⟩

/-- Unary cells, including all eight separators; not just a field count. -/
theorem environment_span_le {layout : VariableLayout} (request : Request layout) :
    (registerWord (List.ofFn request.environment)).length ≤ 8 + 8 * layout.variableCount := by
  have hCoordinates := coordinate_bounds request
  have hTime := timeCount_le_variableCount layout
  have hTape := layout.tapeWidth_le_variableCount
  have hState := layout.stateBound_le_variableCount
  have hCertificate := layout.certificateBitWidth_le_variableCount
  rw [environment_values, registerWord_length]
  simp only [List.length_cons, List.length_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  omega

end Request

private def argument (index : Fin 8) : Expr 8 := .argument index
private def plus (left right : Expr 8) : Expr 8 := .binary .add left right
private def times (left right : Expr 8) : Expr 8 := .binary .mul left right
private def cells : Expr 8 := times (argument ⟨0, by decide⟩) (argument ⟨1, by decide⟩)
private def symbolWidth : Expr 8 := times cells (.constant 3)
private def stateWidth : Expr 8 := times (argument ⟨0, by decide⟩) (argument ⟨2, by decide⟩)
private def cellIndex : Expr 8 :=
  plus (times (argument ⟨4, by decide⟩) (argument ⟨1, by decide⟩)) (argument ⟨5, by decide⟩)
private def certificateOffset : Expr 8 := plus (plus symbolWidth cells) stateWidth

/-- Five fixed syntax trees, independent of source length and coordinate values. -/
def expression : Kind → Expr 8
  | .symbol => plus (times cellIndex (.constant 3)) (argument ⟨7, by decide⟩)
  | .head => plus symbolWidth cellIndex
  | .state => plus (plus symbolWidth cells)
      (plus (times (argument ⟨4, by decide⟩) (argument ⟨2, by decide⟩)) (argument ⟨6, by decide⟩))
  | .certificateBit => plus certificateOffset (argument ⟨5, by decide⟩)
  | .certificateLength => plus (plus certificateOffset (argument ⟨3, by decide⟩)) (argument ⟨5, by decide⟩)

theorem eval_eq_index {layout : VariableLayout} (request : Request layout) :
    BuilderRegisterExpression.eval (expression request.kind) request.environment = request.index := by
  cases request <;>
    simp only [Request.kind, Request.environment, Request.coordinates, Request.index, expression,
      plus, times, argument, cells, cellIndex, symbolWidth, stateWidth, certificateOffset,
      BuilderRegisterExpression.eval, RegisterBinary.value, VariableLayout.symbolVariable,
      VariableLayout.headVariable, VariableLayout.stateVariable, VariableLayout.certificateBitVariable,
      VariableLayout.certificateLengthVariable, VariableBlock.index, VariableBlock.endOffset,
      VariableLayout.symbolBlock, VariableLayout.headBlock, VariableLayout.stateBlock,
      VariableLayout.certificateBitBlock, VariableLayout.certificateLengthBlock,
      VariableLayout.symbolLocalIndex, VariableLayout.headLocalIndex, VariableLayout.stateLocalIndex,
      VariableLayout.symbolWidth, VariableLayout.headWidth, VariableLayout.stateWidth,
      VariableLayout.flattenTwo, Nat.zero_add]

def machine (kind : Kind) (afterCount : Nat) : WorkMachine :=
  BuilderRegisterExpression.machine (expression kind) afterCount

def resultValues {layout : VariableLayout} (request : Request layout) (older after : List Nat) : List Nat :=
  (older ++ List.ofFn request.environment ++ after ++
    BuilderRegisterExpression.prefixValues (expression request.kind) request.environment) ++ [request.index]

theorem resultValues_eq {layout : VariableLayout} (request : Request layout) (older after : List Nat) :
    resultValues request older after = older ++ List.ofFn request.environment ++ after ++
      BuilderRegisterExpression.values (expression request.kind) request.environment := by
  simp only [resultValues, BuilderRegisterExpression.values_root, eval_eq_index, List.append_assoc]

def workSteps {layout : VariableLayout} (request : Request layout) (after : List Nat) : Nat :=
  BuilderRegisterExpression.workSteps (expression request.kind) request.environment after

def initialConfiguration {layout : VariableLayout} (request : Request layout) (afterCount : Nat)
    (older after : List Nat) (inside outsideTail : List WorkSymbol) : WorkConfiguration :=
  BuilderRegisterExpression.initialConfiguration (expression request.kind) afterCount
    older request.environment after inside outsideTail

def finalConfiguration {layout : VariableLayout} (request : Request layout) (afterCount : Nat)
    (older after : List Nat) (inside outsideTail : List WorkSymbol) : WorkConfiguration :=
  { state := (machine request.kind afterCount).acceptState
    tape := endTape (resultValues request older after) inside
      (outsideTail.drop (registerWord (BuilderRegisterExpression.values
        (expression request.kind) request.environment)).length) }

/-- The final written register is the exact layout index for every request family. -/
theorem workRunExact {layout : VariableLayout} (request : Request layout) (afterCount : Nat)
    (older after : List Nat) (inside outsideTail : List WorkSymbol) (hAfter : after.length = afterCount) :
    workRunExact? (machine request.kind afterCount) (workSteps request after)
      (initialConfiguration request afterCount older after inside outsideTail) =
      some (finalConfiguration request afterCount older after inside outsideTail) := by
  simpa only [machine, workSteps, initialConfiguration, finalConfiguration, resultValues_eq,
    BuilderRegisterExpression.finalConfiguration] using BuilderRegisterExpression.workRunExact
      (expression request.kind) afterCount older request.environment after inside outsideTail hAfter

theorem run_compile_exact {layout : VariableLayout} (request : Request layout) (afterCount : Nat)
    (older after : List Nat) (inside outsideTail : List WorkSymbol) (hAfter : after.length = afterCount) :
    run (compileWorkMachine (machine request.kind afterCount)) (6 * workSteps request after)
      (encodeWorkConfiguration (initialConfiguration request afterCount older after inside outsideTail)) =
      encodeWorkConfiguration (finalConfiguration request afterCount older after inside outsideTail) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact request afterCount older after inside outsideTail hAfter)

def environmentSpanPolynomial {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (.constant 8) (.mul (.constant 8) (formulaVariableCountPolynomial verifier))

theorem source_environment_span_le {language : Language} (problem : VerifierTableauProblem language)
    (request : Request problem.layout) :
    (registerWord (List.ofFn request.environment)).length ≤
      (environmentSpanPolynomial problem.verifier).eval problem.input.length := by
  have h := problem.formulaWidth_le_formulaVariableCountPolynomial
  simp only [BitString.size] at h
  exact Nat.le_trans request.environment_span_le (Nat.add_le_add_left (Nat.mul_le_mul_left 8 h) 8)

def inputSpanPolynomial {language : Language} (verifier : PolynomialTimeVerifier language)
    (contextBound : NatPolynomial) : NatPolynomial :=
  .add contextBound (environmentSpanPolynomial verifier)

private def allKindsPolynomial (field : Kind → NatPolynomial) : NatPolynomial :=
  .add (.add (.add (.add (field .symbol) (field .head)) (field .state))
    (field .certificateBit)) (field .certificateLength)

private theorem allKindsPolynomial_le (field : Kind → NatPolynomial) (kind : Kind) (input : Nat) :
    (field kind).eval input ≤ (allKindsPolynomial field).eval input := by
  cases kind <;> simp only [allKindsPolynomial, NatPolynomial.eval_add] <;> omega

/-- The bound is fixed by the verifier/context, not by the runtime kind or request. -/
def uniformSpanPolynomial {language : Language} (verifier : PolynomialTimeVerifier language)
    (contextBound : NatPolynomial) : NatPolynomial :=
  allKindsPolynomial (fun kind => BuilderRegisterExpression.spanPolynomial (expression kind)
    (inputSpanPolynomial verifier contextBound))

def uniformRawTimePolynomial {language : Language} (verifier : PolynomialTimeVerifier language)
    (contextBound : NatPolynomial) : NatPolynomial :=
  allKindsPolynomial (fun kind => BuilderRegisterExpression.rawTimePolynomial (expression kind)
    (inputSpanPolynomial verifier contextBound))

theorem source_polynomial_bounds {language : Language} (problem : VerifierTableauProblem language)
    (request : Request problem.layout) (older after : List Nat) (contextBound : NatPolynomial)
    (hContext : (registerWord (older ++ after)).length ≤ contextBound.eval problem.input.length) :
    (registerWord (resultValues request older after)).length ≤
        (uniformSpanPolynomial problem.verifier contextBound).eval problem.input.length ∧
      6 * workSteps request after ≤
        (uniformRawTimePolynomial problem.verifier contextBound).eval problem.input.length := by
  have hEnvironment := source_environment_span_le problem request
  have hSpan : (registerWord (older ++ List.ofFn request.environment ++ after)).length ≤
      (inputSpanPolynomial problem.verifier contextBound).eval problem.input.length := by
    have hEqual :
        (registerWord (older ++ List.ofFn request.environment ++ after)).length =
        (registerWord (older ++ after)).length + (registerWord (List.ofFn request.environment)).length := by
      simp only [registerWord_append, List.length_append]
      omega
    rw [hEqual]
    exact Nat.add_le_add hContext hEnvironment
  have h := BuilderRegisterExpression.source_polynomial_bounds (expression request.kind)
    (inputSpanPolynomial problem.verifier contextBound) problem.input.length older request.environment after hSpan
  constructor
  · rw [resultValues_eq]
    exact Nat.le_trans h.1 (allKindsPolynomial_le
      (fun kind => BuilderRegisterExpression.spanPolynomial (expression kind)
        (inputSpanPolynomial problem.verifier contextBound)) request.kind problem.input.length)
  · exact Nat.le_trans h.2 (allKindsPolynomial_le
      (fun kind => BuilderRegisterExpression.rawTimePolynomial (expression kind)
        (inputSpanPolynomial problem.verifier contextBound)) request.kind problem.input.length)

theorem rules_pairwise_query_distinct (kind : Kind) (afterCount : Nat) :
    (machine kind afterCount).rules.Pairwise WorkMachineChain.QueryDistinct :=
  BuilderRegisterExpression.rules_pairwise_query_distinct (expression kind) afterCount

theorem noRuleAtAccept (kind : Kind) (afterCount : Nat) :
    WorkMachineChain.NoRuleAtAccept (machine kind afterCount) :=
  BuilderRegisterExpression.noRuleAtAccept (expression kind) afterCount

theorem noRuleAtReject (kind : Kind) (afterCount : Nat) :
    WorkMachineProgramGraph.NoRuleAt (machine kind afterCount) (machine kind afterCount).rejectState :=
  BuilderRegisterExpression.noRuleAtReject (expression kind) afterCount

theorem acceptState_ne_rejectState (kind : Kind) (afterCount : Nat) :
    (machine kind afterCount).acceptState ≠ (machine kind afterCount).rejectState :=
  BuilderRegisterExpression.acceptState_ne_rejectState (expression kind) afterCount

end PNP.Concrete.CookLevin.BuilderLiteralIndexExpression
