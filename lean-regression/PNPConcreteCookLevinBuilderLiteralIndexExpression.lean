/-
Copyright (c) 2026 PNP Labs.
All five literal families must use the unchanged canonical layout, derive
their environment bounds and execute with one fixed program per family.
-/
import PNP.Concrete.CookLevinBuilderLiteralIndexExpression

namespace PNP.Concrete.CookLevin.BuilderLiteralIndexExpression.Regression

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)

private def inputLayout : VariableLayout :=
  { dimensions := { inputLength := 1, certificateBound := 0, timeBound := 1, stateBound := 2 }
    mode := .inputOnly }

private def pairedLayout : VariableLayout :=
  { dimensions := { inputLength := 1, certificateBound := 1, timeBound := 0, stateBound := 2 }
    mode := .paired }

private def symbolRequest : Request inputLayout :=
  .symbol ⟨1, by decide⟩ ⟨2, by decide⟩ .one
private def headRequest : Request inputLayout := .head ⟨1, by decide⟩ ⟨2, by decide⟩
private def stateRequest : Request inputLayout := .state ⟨1, by decide⟩ ⟨1, by decide⟩
private def bitRequest : Request pairedLayout := .certificateBit ⟨0, by decide⟩
private def lengthRequest : Request pairedLayout := .certificateLength ⟨1, by decide⟩

example : inputLayout.variableCount = 36 := rfl
example : pairedLayout.variableCount = 33 := rfl
example : inputLayout.certificateBitWidth = 0 := rfl
example : inputLayout.certificateLengthWidth = 0 := rfl
example : symbolRequest.index = 20 := rfl
example : headRequest.index = 30 := rfl
example : stateRequest.index = 35 := rfl
example : bitRequest.index = 30 := rfl
example : lengthRequest.index = 32 := rfl
example : symbolRequest.kind = .symbol := rfl
example : headRequest.kind = .head := rfl
example : stateRequest.kind = .state := rfl
example : bitRequest.kind = .certificateBit := rfl
example : lengthRequest.kind = .certificateLength := rfl

example : List.ofFn symbolRequest.environment = [2, 4, 2, 0, 1, 2, 0, 2] := rfl
example : List.ofFn bitRequest.environment = [1, 7, 2, 1, 0, 0, 0, 0] := rfl
example : List.ofFn lengthRequest.environment = [1, 7, 2, 1, 0, 1, 0, 0] := rfl
example : BuilderRegisterExpression.eval (expression .symbol) symbolRequest.environment = 20 := rfl
example : BuilderRegisterExpression.eval (expression .head) headRequest.environment = 30 := rfl
example : BuilderRegisterExpression.eval (expression .state) stateRequest.environment = 35 := rfl
example : BuilderRegisterExpression.eval (expression .certificateBit) bitRequest.environment = 30 := rfl
example : BuilderRegisterExpression.eval (expression .certificateLength) lengthRequest.environment = 32 := rfl
example : BuilderRegisterExpression.eval (expression .symbol) symbolRequest.environment ≠
    BuilderRegisterExpression.eval (expression .head) symbolRequest.environment := by decide
example : BuilderRegisterExpression.eval (expression .certificateBit) lengthRequest.environment ≠
    BuilderRegisterExpression.eval (expression .certificateLength) lengthRequest.environment := by decide

example (layout : VariableLayout) (time : Fin layout.dimensions.timeCount)
    (position : Fin (layout.dimensions.tapeWidth layout.mode)) (symbol : TapeSymbol) :
    BuilderRegisterExpression.eval (expression .symbol)
      (Request.symbol time position symbol).environment = layout.symbolVariable time position symbol :=
  eval_eq_index (.symbol time position symbol)
example (layout : VariableLayout) (time : Fin layout.dimensions.timeCount)
    (position : Fin (layout.dimensions.tapeWidth layout.mode)) :
    BuilderRegisterExpression.eval (expression .head)
      (Request.head time position).environment = layout.headVariable time position :=
  eval_eq_index (.head time position)
example (layout : VariableLayout) (time : Fin layout.dimensions.timeCount)
    (state : Fin layout.dimensions.stateBound) :
    BuilderRegisterExpression.eval (expression .state)
      (Request.state time state).environment = layout.stateVariable time state :=
  eval_eq_index (.state time state)
example (layout : VariableLayout) (index : Fin layout.certificateBitWidth) :
    BuilderRegisterExpression.eval (expression .certificateBit)
      (Request.certificateBit index).environment = layout.certificateBitVariable index :=
  eval_eq_index (.certificateBit index)
example (layout : VariableLayout) (length : Fin layout.certificateLengthWidth) :
    BuilderRegisterExpression.eval (expression .certificateLength)
      (Request.certificateLength length).environment = layout.certificateLengthVariable length :=
  eval_eq_index (.certificateLength length)

example {layout : VariableLayout} (request : Request layout) :
    request.index < layout.variableCount := request.index_lt
example {layout : VariableLayout} (request : Request layout) :
    (registerWord (List.ofFn request.environment)).length ≤ 8 + 8 * layout.variableCount :=
  request.environment_span_le
example {layout : VariableLayout} (request : Request layout) :
    (List.ofFn request.environment).length = 8 := List.length_ofFn
example {layout : VariableLayout} (request : Request layout) (older after : List Nat) :
    resultValues request older after = older ++ List.ofFn request.environment ++ after ++
      BuilderRegisterExpression.values (expression request.kind) request.environment :=
  resultValues_eq request older after
example {layout : VariableLayout} (request : Request layout) (afterCount : Nat)
    (older after : List Nat) (inside outside : List WorkSymbol) (hAfter : after.length = afterCount) :
    workRunExact? (BuilderLiteralIndexExpression.machine request.kind afterCount) (workSteps request after)
      (initialConfiguration request afterCount older after inside outside) =
      some (finalConfiguration request afterCount older after inside outside) :=
  workRunExact request afterCount older after inside outside hAfter
example {layout : VariableLayout} (request : Request layout) (afterCount : Nat)
    (older after : List Nat) (inside outside : List WorkSymbol) (hAfter : after.length = afterCount) :
    run (compileWorkMachine (BuilderLiteralIndexExpression.machine request.kind afterCount))
      (6 * workSteps request after)
      (encodeWorkConfiguration (initialConfiguration request afterCount older after inside outside)) =
      encodeWorkConfiguration (finalConfiguration request afterCount older after inside outside) :=
  run_compile_exact request afterCount older after inside outside hAfter
example {layout : VariableLayout} (request : Request layout) (older after : List Nat) :
    workRunExact? (BuilderLiteralIndexExpression.machine request.kind after.length) (workSteps request after)
      (initialConfiguration request after.length older after [.blankZero, .oneZero, .blankOne] [.zeroBlank, .oneOne]) =
      some (finalConfiguration request after.length older after [.blankZero, .oneZero, .blankOne] [.zeroBlank, .oneOne]) :=
  workRunExact request after.length older after [.blankZero, .oneZero, .blankOne] [.zeroBlank, .oneOne] rfl

example {language : Language} (problem : VerifierTableauProblem language) (request : Request problem.layout) :
    (registerWord (List.ofFn request.environment)).length ≤
      (environmentSpanPolynomial problem.verifier).eval problem.input.length :=
  source_environment_span_le problem request
example {language : Language} (problem : VerifierTableauProblem language) (request : Request problem.layout)
    (older after : List Nat) (contextBound : NatPolynomial)
    (hContext : (registerWord (older ++ after)).length ≤ contextBound.eval problem.input.length) :
    (registerWord (resultValues request older after)).length ≤
        (uniformSpanPolynomial problem.verifier contextBound).eval problem.input.length ∧
      6 * workSteps request after ≤ (uniformRawTimePolynomial problem.verifier contextBound).eval problem.input.length :=
  source_polynomial_bounds problem request older after contextBound hContext

example (kind : Kind) (afterCount : Nat) :
    (BuilderLiteralIndexExpression.machine kind afterCount).rules.Pairwise WorkMachineChain.QueryDistinct :=
  rules_pairwise_query_distinct kind afterCount
example (kind : Kind) (afterCount : Nat) :
    WorkMachineChain.NoRuleAtAccept (BuilderLiteralIndexExpression.machine kind afterCount) := noRuleAtAccept kind afterCount
example (kind : Kind) (afterCount : Nat) :
    WorkMachineProgramGraph.NoRuleAt (BuilderLiteralIndexExpression.machine kind afterCount)
      (BuilderLiteralIndexExpression.machine kind afterCount).rejectState := noRuleAtReject kind afterCount
example (kind : Kind) (afterCount : Nat) :
    (BuilderLiteralIndexExpression.machine kind afterCount).acceptState ≠
      (BuilderLiteralIndexExpression.machine kind afterCount).rejectState := acceptState_ne_rejectState kind afterCount

end PNP.Concrete.CookLevin.BuilderLiteralIndexExpression.Regression
