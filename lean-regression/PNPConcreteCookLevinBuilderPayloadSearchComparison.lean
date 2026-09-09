/-
Copyright (c) 2026 PNP Labs.

Universal execution and polynomial contracts, plus independent field-layout and
strict-boundary regressions for actual source-payload width comparisons.
-/
import PNP.Concrete.CookLevinBuilderPayloadSearchComparison
import PNP.Concrete.CookLevinBuilderPayloadSearchAdvance

namespace PNP.Concrete.CookLevin.BuilderPayloadSearchComparisonRegression

open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderPayloadLiteralTokenSelector (Kind Source Context stride valueSlot reader valueHistory)
open BuilderLiteralSearchFrame (widthExpression widthHistory comparisonResult comparisonHistory residual)
open BuilderPayloadSearchComparison

example (kind : Kind) (ordinal count position value : Nat) :
    List.ofFn (valueEnvironment kind ordinal count position value) =
      [ordinal,count,position] ++ valueHistory kind ordinal value :=
  BuilderPayloadSearchComparison.valueEnvironment_values kind ordinal count position value

example (kind : Kind) (ordinal count position value : Nat) :
    BuilderRegisterExpression.values widthExpression (valueEnvironment kind ordinal count position value) =
      widthHistory value :=
  BuilderPayloadSearchComparison.widthExpression_values kind ordinal count position value

example (kind : Kind) (ordinal count position value : Nat) :
    List.ofFn (packedEnvironment kind ordinal count position value) =
      preparationHistory kind ordinal count position value :=
  BuilderPayloadSearchComparison.environment_values kind ordinal count position value

example (kind : Kind) (ordinal count position value : Nat) :
    BuilderRegisterPack.values argumentFields (packedEnvironment kind ordinal count position value) =
      [position,value + 2] :=
  BuilderPayloadSearchComparison.packed_values kind ordinal count position value

example (kind : Kind) (ordinal count position value : Nat) :
    (preparationHistory kind ordinal count position value).length = 12 :=
  BuilderPayloadSearchComparison.preparationHistory_length kind ordinal count position value

example (kind : Kind) (ordinal count position value : Nat) :
    (chunk kind ordinal count position value).length = 17 :=
  BuilderPayloadSearchComparison.chunk_length kind ordinal count position value

example (kind : Kind) (ordinal position value : Nat) :
    (comparisonScratch kind ordinal position value).length = 14 :=
  BuilderPayloadSearchComparison.comparisonScratch_length kind ordinal position value

example (kind : Kind) (ordinal position value : Nat) :
    (cursorMiddle kind ordinal position value).length = 14 :=
  BuilderPayloadSearchComparison.cursorMiddle_length kind ordinal position value

example (kind : Kind) (ordinal count position value : Nat) :
    chunk kind ordinal count position value =
      [ordinal,count] ++ cursorMiddle kind ordinal position value ++ [residual position value] :=
  BuilderPayloadSearchComparison.chunk_cursor_layout kind ordinal count position value

example (kind : Kind) (ordinal count position value : Nat) :
    chunk kind ordinal count position value = [ordinal,count,position] ++ comparisonScratch kind ordinal position value :=
  BuilderPayloadSearchComparison.chunk_scratch_layout kind ordinal count position value

example (kind : Kind) (prior : List Nat) (ordinal count position value : Nat)
    (hPrior : prior.length = 17 * ordinal) :
    (prior ++ chunk kind ordinal count position value).length = 17 * (ordinal + 1) :=
  BuilderPayloadSearchComparison.history_step kind prior ordinal count position value hPrior

example {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (prepareMachine source.kind) (prepareSteps source context)
      (workStartConfiguration (prepareMachine source.kind) (endTape (initialValues source context older) inside outside)) =
      some {state := (prepareMachine source.kind).acceptState, tape := prepareTape source context older inside outside} :=
  BuilderPayloadSearchComparison.prepare_workRunExact source context older inside outside

example {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (BuilderPayloadSearchComparison.machine source.kind) (workSteps source context) (initialConfiguration source context older inside outside) =
      some (finalConfiguration source context older inside outside) :=
  BuilderPayloadSearchComparison.workRunExact source context older inside outside

example {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine (BuilderPayloadSearchComparison.machine source.kind)) (6 * workSteps source context)
      (encodeWorkConfiguration (initialConfiguration source context older inside outside)) =
      encodeWorkConfiguration (finalConfiguration source context older inside outside) :=
  BuilderPayloadSearchComparison.run_compile_exact source context older inside outside

example {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration source context older inside outside).state = (BuilderPayloadSearchComparison.machine source.kind).acceptState ↔
      context.position < source.originalLiteral.index.val + 2 :=
  BuilderPayloadSearchComparison.final_accept_iff source context older inside outside

example {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration source context older inside outside).state = (BuilderPayloadSearchComparison.machine source.kind).rejectState ↔
      source.originalLiteral.index.val + 2 ≤ context.position :=
  BuilderPayloadSearchComparison.final_reject_iff source context older inside outside

example {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration source context older inside outside).tape =
      endTape (finalValues source context older) inside (finalOutside source context outside) :=
  BuilderPayloadSearchComparison.final_tape source context older inside outside

example {width : Nat} (source : Source width) (context : Context source.ordinal) (outside : List WorkSymbol) :
    (finalOutside source context outside).length ≤ outside.length :=
  BuilderPayloadSearchComparison.finalOutside_length_le source context outside

example {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (outside : List WorkSymbol) :
    (registerWord (finalValues source context older)).length + (finalOutside source context outside).length ≤
      (registerWord (initialValues source context older)).length + outside.length +
        (registerWord (chunk source.kind source.ordinal context.remaining context.position source.originalLiteral.index.val)).length :=
  BuilderPayloadSearchComparison.final_span_le_initial_add_chunk source context older outside

example (kind : Kind) (ordinal count position value : Nat) :
    (registerWord (chunk kind ordinal count position value)).length ≤
      (registerWord (BuilderLiteralSearchFrame.chunk ordinal count position value)).length + 30 :=
  BuilderPayloadSearchComparison.chunk_word_le_old_add_thirty kind ordinal count position value

example (kind : Kind) : (BuilderPayloadSearchComparison.machine kind).rules.Pairwise WorkMachineChain.QueryDistinct :=
  BuilderPayloadSearchComparison.rules_pairwise_query_distinct kind

example (kind : Kind) : WorkMachineChain.NoRuleAtAccept (BuilderPayloadSearchComparison.machine kind) :=
  BuilderPayloadSearchComparison.noRuleAtAccept kind

example (kind : Kind) : WorkMachineProgramGraph.NoRuleAt (BuilderPayloadSearchComparison.machine kind) (BuilderPayloadSearchComparison.machine kind).rejectState :=
  BuilderPayloadSearchComparison.noRuleAtReject kind

example (kind : Kind) : (BuilderPayloadSearchComparison.machine kind).acceptState ≠ (BuilderPayloadSearchComparison.machine kind).rejectState :=
  BuilderPayloadSearchComparison.acceptState_ne_rejectState kind

example {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues source context older)).length + outside.length ≤ bound.eval input) :
    (registerWord (prepareOlder source context older ++ [context.position,source.originalLiteral.index.val + 2])).length +
      (prepareOutside source context outside).length ≤ (prepareSpanPolynomial source.kind bound).eval input ∧
    6 * prepareSteps source context ≤ (prepareRawTimePolynomial source.kind bound).eval input :=
  BuilderPayloadSearchComparison.prepare_source_polynomial_bounds source context older outside bound input hSpan

example {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues source context older)).length + outside.length ≤ bound.eval input) :
    (registerWord (finalValues source context older)).length + (finalOutside source context outside).length ≤
      (spanPolynomial source.kind bound).eval input ∧
    6 * workSteps source context ≤ (rawTimePolynomial source.kind bound).eval input :=
  BuilderPayloadSearchComparison.source_polynomial_bounds source context older outside bound input hSpan

-- The four payload address schemas are independent fixed layout expectations.
example : preparationHistory .required 0 1 0 0 =
    [0,1,0,17,0,0,20,20,0,0,2,2] := rfl
example : preparationHistory .premise 2 3 4 5 =
    [2,3,4,19,2,38,23,61,5,5,2,7] := rfl
example : preparationHistory .conclusion 2 1 4 5 =
    [2,1,4,17,2,34,21,55,5,5,2,7] := rfl
example : preparationHistory .positive 2 3 4 5 =
    [2,3,4,18,2,36,20,56,5,5,2,7] := rfl

-- Both operands come from their distinct physical registers.
example (kind : Kind) (ordinal count position value : Nat) :
    packedEnvironment kind ordinal count position value ⟨2, by decide⟩ = position ∧
    packedEnvironment kind ordinal count position value ⟨11, by decide⟩ = value + 2 := ⟨rfl,rfl⟩

-- A hit preserves position; equality is a miss with zero residual.
example : residual 4 3 = 4 := by decide
example : residual 5 3 = 0 := by decide
example : residual 7 3 = 2 := by decide
example : residual 0 0 = 0 := by decide
example : residual 1 0 = 1 := by decide
example : residual 2 0 = 0 := by decide

example {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol)
    (h : context.position = source.originalLiteral.index.val + 1) :
    (finalConfiguration source context older inside outside).state =
      (BuilderPayloadSearchComparison.machine source.kind).acceptState := by
  apply (BuilderPayloadSearchComparison.final_accept_iff source context older inside outside).2
  omega

example {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol)
    (h : context.position = source.originalLiteral.index.val + 2) :
    (finalConfiguration source context older inside outside).state =
      (BuilderPayloadSearchComparison.machine source.kind).rejectState := by
  apply (BuilderPayloadSearchComparison.final_reject_iff source context older inside outside).2
  omega

-- A comparison miss fits the independently verified fixed cursor contract.
example (kind : Kind) (ordinal remaining position value : Nat)
    (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? BuilderPayloadSearchAdvance.machine
      (BuilderPayloadSearchAdvance.workSteps (cursorMiddle kind ordinal position value)
        ordinal remaining (residual position value))
      (BuilderPayloadSearchAdvance.initialConfiguration older (cursorMiddle kind ordinal position value)
        ordinal remaining (residual position value) inside outside) =
      some (BuilderPayloadSearchAdvance.finalConfiguration older (cursorMiddle kind ordinal position value)
        ordinal remaining (residual position value) inside outside) :=
  BuilderPayloadSearchAdvance.workRunExact older (cursorMiddle kind ordinal position value)
    ordinal remaining (residual position value) inside outside (cursorMiddle_length kind ordinal position value)

end PNP.Concrete.CookLevin.BuilderPayloadSearchComparisonRegression
