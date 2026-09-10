import PNP.Concrete.CookLevinBuilderLiteralSearchFrame

open PNP.Concrete PNP.Concrete.CookLevin
open BuilderLiteralSearchFrame
open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape)
open BuilderLocalConstraintPayload (literalListValues)
open PipelineTape

-- Independent layout fixtures for the complete planned miss branch.
example : historyStride = 17 := rfl
example : fieldStride = 19 := rfl
example : valueHistory 1 3 = [19, 1, 19, 8, 27, 3] := rfl
example : widthHistory 3 = [3, 2, 5] := rfl
example : residual 4 3 = 4 := rfl
example : residual 5 3 = 0 := rfl
example : residual 8 3 = 3 := rfl
example : (chunk 0 1 0 0).length = 17 := chunk_length 0 1 0 0
example : (registerWord (chunk 0 1 0 0)).length = 61 := chunk_word_length 0 1 0 0
example : (registerWord (chunk 1 2 5 3)).length = 127 := chunk_word_length 1 2 5 3
example : globalSpanBound 0 = 100 := rfl
example : globalSpanBound 1 = 401 := rfl
example (ordinal count position value : Nat) :
    BuilderRegisterExpression.values widthExpression (valueEnvironment ordinal count position value) = [value,2,value+2] :=
  widthExpression_values ordinal count position value
example (ordinal count position value : Nat) : (chunk ordinal count position value).length = 17 :=
  chunk_length ordinal count position value
example (position value : Nat) : residual position value ≤ position := residual_le position value

example (prior : List Nat) (ordinal count position value : Nat)
    (hPrior : prior.length = historyStride * ordinal) :
    (prior ++ chunk ordinal count position value).length = historyStride * (ordinal + 1) :=
  history_step prior ordinal count position value hPrior

example {width : Nat} (literals : List (BoundedLiteral width)) (prior older : List Nat) :
    older ++ (payloadReader literals prior).reverse =
      older ++ (literalListValues literals).reverse ++ prior :=
  payloadReader_layout literals prior older

example {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (prior : List Nat) (hPrior : prior.length = historyStride * index.val) (field : Fin 2) :
    fieldStride * index.val + field.val < (payloadReader literals prior).length :=
  field_index_lt literals index prior hPrior field

example {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (prior : List Nat) (hPrior : prior.length = historyStride * index.val) (field : Fin 2) :
    (payloadReader literals prior)[fieldStride * index.val + field.val]'(field_index_lt literals index prior hPrior field) =
      BuilderPayloadFieldCopy.literalField literals[index.val] field :=
  field_index_value literals index prior hPrior field

example {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
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
                (BuilderPayloadFieldCopy.literalField literals[index.val] field)))} :=
  field_workRunExact literals index prior hPrior field afterCount older after hAfter inside outside

example {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
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
  field_run_compile_exact literals index prior hPrior field afterCount older after hAfter inside outside

example {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
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
      (BuilderPayloadFieldCopy.rawTimePolynomial fieldStride field.val afterCount bound).eval input :=
  field_source_polynomial_bounds literals index prior hPrior field afterCount older after hAfter outside bound input hSpan

example (position value : Nat) :
    (registerWord (comparisonHistory position value)).length = position + 2 * (value + 2) + residual position value + 5 :=
  comparisonHistory_word_length position value

example (ordinal count position value : Nat) :
    (registerWord (chunk ordinal count position value)).length =
      40 * ordinal + count + 2 * position + 5 * value + residual position value + 60 :=
  chunk_word_length ordinal count position value

example (ordinal count position value bound : Nat)
    (hOrdinal : ordinal ≤ bound) (hCount : count ≤ bound)
    (hPosition : position ≤ bound) (hValue : value ≤ bound) :
    (registerWord (chunk ordinal count position value)).length ≤ 50 * bound + 60 :=
  chunk_word_le ordinal count position value bound hOrdinal hCount hPosition hValue

example (prior : List Nat) (ordinal count position value bound : Nat)
    (hHistory : (registerWord prior).length ≤ historyWordBound bound ordinal)
    (hOrdinal : ordinal ≤ bound) (hCount : count ≤ bound)
    (hPosition : position ≤ bound) (hValue : value ≤ bound) :
    (registerWord (prior ++ chunk ordinal count position value)).length ≤ historyWordBound bound (ordinal + 1) :=
  history_word_step prior ordinal count position value bound hHistory hOrdinal hCount hPosition hValue

example (bound : NatPolynomial) (input : Nat) :
    (globalSpanPolynomial bound).eval input = globalSpanBound (bound.eval input) :=
  globalSpanPolynomial_eval bound input

example (baseSpan exteriorGrowth bound iterations : Nat)
    (hBase : baseSpan ≤ bound) (hIterations : iterations ≤ bound)
    (hExterior : exteriorGrowth ≤ iterations * (bound + 3)) :
    baseSpan + historyWordBound bound iterations + exteriorGrowth ≤ globalSpanBound bound :=
  global_history_envelope baseSpan exteriorGrowth bound iterations hBase hIterations hExterior
