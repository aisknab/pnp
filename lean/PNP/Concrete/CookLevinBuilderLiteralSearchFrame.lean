/-
Copyright (c) 2026 PNP Labs.

Register/address invariants for the complete variable-width literal-list search.
An unsuccessful iteration retains a 17-register comparison chunk. Its history
therefore shifts a two-field literal address by 17 times the runtime ordinal.
One fixed stride-19 field reader handles every iteration.

These are physical field-access and loop-frame bounds, not a completed search
execution theorem. The guard, comparison, advancement and cyclic graph must
still establish the complete runtime locator and token result.
-/

import PNP.Concrete.CookLevinBuilderPayloadFieldCopy
import PNP.Concrete.CookLevinBuilderRegisterCompareResidual

namespace PNP.Concrete.CookLevin.BuilderLiteralSearchFrame

open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderLocalConstraintPayload (literalListValues)
open BuilderArbitrarySlotHeaderRouter

def historyStride : Nat := 17
def fieldStride : Nat := historyStride + 2

def valueHistory (ordinal value : Nat) : List Nat :=
  BuilderPayloadFieldCopy.scratch fieldStride 1 2 ordinal ++ [value]

def widthExpression : BuilderRegisterExpression.Expr 9 :=
  .binary .add (.argument ⟨8, by decide⟩) (.constant 2)
def widthHistory (value : Nat) : List Nat := [value, 2, value + 2]
def comparisonResult (position value : Nat) : RawRouter.ComparisonResult :=
  RawRouter.compareResult 0 position (value + 2)
def comparisonHistory (position value : Nat) : List Nat :=
  BuilderRegisterCompareResidual.outputValues (comparisonResult position value)
def chunk (ordinal count position value : Nat) : List Nat :=
  [ordinal, count, position] ++ valueHistory ordinal value ++ widthHistory value ++ comparisonHistory position value

def valueEnvironment (ordinal count position value : Nat) (index : Fin 9) : Nat :=
  match index.val with
  | 0 => ordinal
  | 1 => count
  | 2 => position
  | 3 => fieldStride
  | 4 => ordinal
  | 5 => fieldStride * ordinal
  | 6 => 8
  | 7 => fieldStride * ordinal + 8
  | _ => value

theorem valueHistory_length (ordinal value : Nat) : (valueHistory ordinal value).length = 6 := rfl
theorem valueEnvironment_values (ordinal count position value : Nat) :
    List.ofFn (valueEnvironment ordinal count position value) =
      [ordinal, count, position] ++ valueHistory ordinal value := rfl
theorem widthExpression_values (ordinal count position value : Nat) :
    BuilderRegisterExpression.values widthExpression (valueEnvironment ordinal count position value) =
      widthHistory value := rfl
theorem widthExpression_eval (ordinal count position value : Nat) :
    BuilderRegisterExpression.eval widthExpression (valueEnvironment ordinal count position value) = value + 2 := rfl

theorem chunk_length (ordinal count position value : Nat) :
    (chunk ordinal count position value).length = historyStride := by
  simp only [chunk, List.length_append, valueHistory_length, widthHistory, comparisonHistory,
    BuilderRegisterCompareResidual.outputValues_length, List.length_cons, List.length_nil] <;> rfl

theorem history_step (prior : List Nat) (ordinal count position value : Nat)
    (hPrior : prior.length = historyStride * ordinal) :
    (prior ++ chunk ordinal count position value).length = historyStride * (ordinal + 1) := by
  rw [List.length_append, chunk_length, hPrior, Nat.mul_add, Nat.mul_one]

def payloadReader {width : Nat} (literals : List (BoundedLiteral width)) (prior : List Nat) : List Nat :=
  prior.reverse ++ literalListValues literals

theorem payloadReader_layout {width : Nat} (literals : List (BoundedLiteral width)) (prior older : List Nat) :
    older ++ (payloadReader literals prior).reverse =
      older ++ (literalListValues literals).reverse ++ prior := by
  simp only [payloadReader, List.reverse_append, List.reverse_reverse, List.append_assoc]

theorem field_index_lt {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (prior : List Nat) (hPrior : prior.length = historyStride * index.val) (field : Fin 2) :
    fieldStride * index.val + field.val < (payloadReader literals prior).length := by
  have hIndex := index.isLt
  have hField := field.isLt
  simp only [payloadReader, List.length_append, List.length_reverse,
    BuilderLocalConstraintPayload.literalListValues_length, hPrior, fieldStride, historyStride]
  omega

theorem field_index_value {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (prior : List Nat) (hPrior : prior.length = historyStride * index.val) (field : Fin 2) :
    (payloadReader literals prior)[fieldStride * index.val + field.val]'(field_index_lt literals index prior hPrior field) =
      BuilderPayloadFieldCopy.literalField literals[index.val] field := by
  have hSkip : (prior.reverse).length ≤ fieldStride * index.val + field.val := by
    simp only [List.length_reverse, hPrior, historyStride, fieldStride]
    omega
  have hAddress : fieldStride * index.val + field.val - prior.reverse.length = 2 * index.val + field.val := by
    simp only [List.length_reverse, hPrior, historyStride, fieldStride]
    omega
  have hSuffix : fieldStride * index.val + field.val - prior.reverse.length < (literalListValues literals).length := by
    rw [hAddress]
    exact BuilderPayloadFieldCopy.literal_field_lt literals index.val index.isLt field
  calc
    _ = (literalListValues literals)[fieldStride * index.val + field.val - prior.reverse.length]'hSuffix :=
      List.getElem_append_right hSkip
    _ = _ := by
      simpa only [hAddress] using
        BuilderPayloadFieldCopy.literal_field_value literals index.val index.isLt field

/-- The history length is derived by the loop invariant, not an executable input or verdict. -/
theorem field_workRunExact {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (prior : List Nat) (hPrior : prior.length = historyStride * index.val) (field : Fin 2)
    (afterCount : Nat) (older after : List Nat) (hAfter : after.length = afterCount)
    (inside outside : List WorkSymbol) :
    workRunExact? (BuilderPayloadFieldCopy.machine fieldStride field.val afterCount)
      (BuilderPayloadFieldCopy.workSteps fieldStride field.val afterCount index.val after (payloadReader literals prior)
        (BuilderPayloadFieldCopy.literalField literals[index.val] field))
      (workStartConfiguration (BuilderPayloadFieldCopy.machine fieldStride field.val afterCount)
        (endTape (older ++ (literalListValues literals).reverse ++ prior ++ [index.val] ++ after) inside outside)) =
      some {state := (BuilderPayloadFieldCopy.machine fieldStride field.val afterCount).acceptState,
            tape := endTape
              (older ++ (literalListValues literals).reverse ++ prior ++ [index.val] ++ after ++
                BuilderPayloadFieldCopy.scratch fieldStride field.val afterCount index.val ++
                [BuilderPayloadFieldCopy.literalField literals[index.val] field])
              inside (outside.drop (BuilderPayloadFieldCopy.allocation fieldStride field.val afterCount index.val
                (BuilderPayloadFieldCopy.literalField literals[index.val] field)))} := by
  have h := BuilderPayloadFieldCopy.workRunExact fieldStride field.val afterCount index.val
    (payloadReader literals prior) older after inside outside hAfter (field_index_lt literals index prior hPrior field)
  simpa only [field_index_value literals index prior hPrior field, BuilderPayloadFieldCopy.initialConfiguration,
    BuilderPayloadFieldCopy.finalConfiguration, BuilderPayloadFieldCopy.initialValues, BuilderPayloadFieldCopy.finalValues,
    payloadReader_layout] using h

theorem field_run_compile_exact {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (prior : List Nat) (hPrior : prior.length = historyStride * index.val) (field : Fin 2)
    (afterCount : Nat) (older after : List Nat) (hAfter : after.length = afterCount)
    (inside outside : List WorkSymbol) :
    run (compileWorkMachine (BuilderPayloadFieldCopy.machine fieldStride field.val afterCount))
      (6 * BuilderPayloadFieldCopy.workSteps fieldStride field.val afterCount index.val after (payloadReader literals prior)
        (BuilderPayloadFieldCopy.literalField literals[index.val] field))
      (encodeWorkConfiguration (workStartConfiguration (BuilderPayloadFieldCopy.machine fieldStride field.val afterCount)
        (endTape (older ++ (literalListValues literals).reverse ++ prior ++ [index.val] ++ after) inside outside))) =
      encodeWorkConfiguration
        {state := (BuilderPayloadFieldCopy.machine fieldStride field.val afterCount).acceptState,
         tape := endTape
          (older ++ (literalListValues literals).reverse ++ prior ++ [index.val] ++ after ++
            BuilderPayloadFieldCopy.scratch fieldStride field.val afterCount index.val ++
            [BuilderPayloadFieldCopy.literalField literals[index.val] field])
          inside (outside.drop (BuilderPayloadFieldCopy.allocation fieldStride field.val afterCount index.val
            (BuilderPayloadFieldCopy.literalField literals[index.val] field)))} :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (field_workRunExact literals index prior hPrior field afterCount older after hAfter inside outside)

theorem field_source_polynomial_bounds {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (prior : List Nat) (hPrior : prior.length = historyStride * index.val) (field : Fin 2)
    (afterCount : Nat) (older after : List Nat) (hAfter : after.length = afterCount)
    (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (older ++ (literalListValues literals).reverse ++ prior ++ [index.val] ++ after)).length +
      outside.length ≤ bound.eval input) :
    (registerWord (older ++ (literalListValues literals).reverse ++ prior ++ [index.val] ++ after ++
      BuilderPayloadFieldCopy.scratch fieldStride field.val afterCount index.val ++
      [BuilderPayloadFieldCopy.literalField literals[index.val] field])).length +
      (outside.drop (BuilderPayloadFieldCopy.allocation fieldStride field.val afterCount index.val
        (BuilderPayloadFieldCopy.literalField literals[index.val] field))).length ≤
      (BuilderPayloadFieldCopy.spanPolynomial fieldStride field.val afterCount bound).eval input ∧
    6 * BuilderPayloadFieldCopy.workSteps fieldStride field.val afterCount index.val after (payloadReader literals prior)
      (BuilderPayloadFieldCopy.literalField literals[index.val] field) ≤
      (BuilderPayloadFieldCopy.rawTimePolynomial fieldStride field.val afterCount bound).eval input := by
  have hInput : (registerWord (BuilderPayloadFieldCopy.initialValues (payloadReader literals prior) older index.val after)).length +
      outside.length ≤ bound.eval input := by
    simpa only [BuilderPayloadFieldCopy.initialValues, payloadReader_layout] using hSpan
  simpa only [field_index_value literals index prior hPrior field, BuilderPayloadFieldCopy.finalValues,
    BuilderPayloadFieldCopy.initialValues, payloadReader_layout] using
    BuilderPayloadFieldCopy.source_polynomial_bounds fieldStride field.val afterCount index.val (payloadReader literals prior)
      older after outside bound input hAfter (field_index_lt literals index prior hPrior field) hInput

def residual (position value : Nat) : Nat :=
  if position < value + 2 then position else position - (value + 2)

theorem residual_le (position value : Nat) : residual position value ≤ position := by
  unfold residual
  split <;> omega

theorem comparisonHistory_word_length (position value : Nat) :
    (registerWord (comparisonHistory position value)).length = position + 2 * (value + 2) + residual position value + 5 := by
  have hRestored : (registerWord (BuilderRegisterLessThan.resultValues (RawRouter.compareResult 0 position (value + 2)))).length =
      position + (value + 2) + 3 := BuilderRegisterLessThan.clearedSpan_eq position (value + 2)
  simp only [comparisonHistory, BuilderRegisterCompareResidual.outputValues, comparisonResult,
    registerWord_append, List.length_append, hRestored,
    BuilderRegisterCompareResidual.resultBoundary_eq, BuilderRegisterCompareResidual.resultCoordinate_eq,
    registerWord_length, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil, residual]
  omega

theorem chunk_word_length (ordinal count position value : Nat) :
    (registerWord (chunk ordinal count position value)).length =
      40 * ordinal + count + 2 * position + 5 * value + residual position value + 60 := by
  simp only [chunk, registerWord_append, List.length_append]
  rw [comparisonHistory_word_length]
  simp only [valueHistory, widthHistory, BuilderPayloadFieldCopy.scratch, BuilderPayloadFieldCopy.scratchPrefix,
    BuilderPayloadFieldCopy.address, BuilderPayloadFieldCopy.offset, fieldStride, historyStride,
    registerWord_length, List.sum_append, List.sum_cons, List.sum_nil, List.length_append,
    List.length_cons, List.length_nil]
  omega

theorem chunk_word_le (ordinal count position value bound : Nat)
    (hOrdinal : ordinal ≤ bound) (hCount : count ≤ bound)
    (hPosition : position ≤ bound) (hValue : value ≤ bound) :
    (registerWord (chunk ordinal count position value)).length ≤ 50 * bound + 60 := by
  rw [chunk_word_length]
  have hResidual := residual_le position value
  omega

def historyWordBound (bound iterations : Nat) : Nat := iterations * (50 * bound + 60)

theorem history_word_step (prior : List Nat) (ordinal count position value bound : Nat)
    (hHistory : (registerWord prior).length ≤ historyWordBound bound ordinal)
    (hOrdinal : ordinal ≤ bound) (hCount : count ≤ bound)
    (hPosition : position ≤ bound) (hValue : value ≤ bound) :
    (registerWord (prior ++ chunk ordinal count position value)).length ≤ historyWordBound bound (ordinal + 1) := by
  rw [registerWord_append, List.length_append]
  have hChunk := chunk_word_le ordinal count position value bound hOrdinal hCount hPosition hValue
  unfold historyWordBound at hHistory ⊢
  rw [Nat.add_mul]
  omega

def globalSpanBound (bound : Nat) : Nat := bound + (bound + 1) * (100 * bound + 100)
def globalSpanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add bound (.mul (.add bound (.constant 1)) (.add (.mul (.constant 100) bound) (.constant 100)))

theorem globalSpanPolynomial_eval (bound : NatPolynomial) (input : Nat) :
    (globalSpanPolynomial bound).eval input = globalSpanBound (bound.eval input) := rfl

/-- A single quadratic envelope is used for every loop iteration. -/
theorem global_history_envelope (baseSpan exteriorGrowth bound iterations : Nat)
    (hBase : baseSpan ≤ bound) (hIterations : iterations ≤ bound)
    (hExterior : exteriorGrowth ≤ iterations * (bound + 3)) :
    baseSpan + historyWordBound bound iterations + exteriorGrowth ≤ globalSpanBound bound := by
  have hHistory := Nat.mul_le_mul_right (50 * bound + 60) hIterations
  have hExt := Nat.mul_le_mul_right (bound + 3) hIterations
  unfold historyWordBound globalSpanBound
  have hBudget : bound * (50 * bound + 60) + bound * (bound + 3) ≤ (bound + 1) * (100 * bound + 100) := by
    have hSmall : 50 * bound + 60 + (bound + 3) ≤ 100 * bound + 100 := by omega
    have hMul := Nat.mul_le_mul_left bound hSmall
    have hMore := Nat.mul_le_mul_right (100 * bound + 100) (show bound ≤ bound + 1 by omega)
    rw [Nat.mul_add] at hMul
    omega
  omega

end PNP.Concrete.CookLevin.BuilderLiteralSearchFrame
