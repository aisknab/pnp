import PNP.Concrete.CookLevinBuilderPayloadFieldCopy

open PNP.Concrete PNP.Concrete.CookLevin
open BuilderPayloadFieldCopy
open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape)

-- Independent layout fixtures include all five address-expression registers.
example : offset 0 0 = 5 := rfl
example : offset 1 6 = 12 := rfl
example : address 2 1 6 3 = 18 := rfl
example : scratch 2 0 0 3 = [2, 3, 6, 5, 11] := rfl
example : reader 2 0 0 1 [] [1, 4, 0, 7] = [5, 2, 1, 2, 1, 1, 4, 0, 7] := rfl
example : initialValues [1, 4, 0, 7] [9] 1 [8] = [9, 7, 0, 4, 1, 1, 8] := rfl
example : finalValues 2 1 0 1 [1, 4, 0, 7] [] [] 7 =
    [7, 0, 4, 1, 1, 2, 1, 2, 6, 8, 7] := rfl
example : allocation 2 1 0 1 7 = 32 := rfl
example (stride slot count ordinal : Nat) : (scratch stride slot count ordinal).length = 5 :=
  scratch_length stride slot count ordinal
example (stride slot count : Nat) : BuilderRegisterExpression.nodeCount (expression stride slot count) = 5 :=
  expression_nodeCount stride slot count
example (stride slot count ordinal : Nat) :
    BuilderRegisterExpression.eval (expression stride slot count) (environment ordinal) =
      stride * ordinal + (count + 5 + slot) := expression_eval stride slot count ordinal

-- The valid field domain is explicit, and addresses account for arbitrary newer values.
example (stride slot count ordinal : Nat) (after payload : List Nat)
    (hAfter : after.length = count) (hField : stride * ordinal + slot < payload.length) :
    (reader stride slot count ordinal after payload)[address stride slot count ordinal]'
      (reader_address_lt stride slot count ordinal after payload hAfter hField) =
      payload[stride * ordinal + slot] :=
  reader_address_value stride slot count ordinal after payload hAfter hField
example (stride slot count ordinal : Nat) (after payload older : List Nat) :
    older ++ (reader stride slot count ordinal after payload).reverse ++ [address stride slot count ordinal] =
      initialValues payload older ordinal after ++ scratch stride slot count ordinal :=
  reader_layout stride slot count ordinal after payload older
example (stride slot count ordinal : Nat) (payload older after : List Nat)
    (inside outside : List WorkSymbol) (hAfter : after.length = count)
    (hField : stride * ordinal + slot < payload.length) :
    workRunExact? (machine stride slot count)
      (workSteps stride slot count ordinal after payload payload[stride * ordinal + slot])
      (initialConfiguration stride slot count ordinal payload older after inside outside) =
      some (finalConfiguration stride slot count ordinal payload older after
        payload[stride * ordinal + slot] inside outside) :=
  workRunExact stride slot count ordinal payload older after inside outside hAfter hField
example (stride slot count ordinal : Nat) (payload older after : List Nat)
    (inside outside : List WorkSymbol) (hAfter : after.length = count)
    (hField : stride * ordinal + slot < payload.length) :
    run (compileWorkMachine (machine stride slot count))
      (6 * workSteps stride slot count ordinal after payload payload[stride * ordinal + slot])
      (encodeWorkConfiguration (initialConfiguration stride slot count ordinal payload older after inside outside)) =
      encodeWorkConfiguration (finalConfiguration stride slot count ordinal payload older after
        payload[stride * ordinal + slot] inside outside) :=
  run_compile_exact stride slot count ordinal payload older after inside outside hAfter hField
example (stride slot count ordinal : Nat) (payload older after : List Nat) (value : Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration stride slot count ordinal payload older after value inside outside).tape =
      endTape (initialValues payload older ordinal after ++ scratch stride slot count ordinal ++ [value])
        inside (outside.drop (allocation stride slot count ordinal value)) :=
  final_tape stride slot count ordinal payload older after value inside outside
example (stride slot count ordinal : Nat) (payload older after : List Nat) (value : Nat) (inside : List WorkSymbol) :
    (finalConfiguration stride slot count ordinal payload older after value inside []).tape.left = [] := rfl

-- Zero-valued fields are still copied; no small fixture determines the machine.
example (inside outside : List WorkSymbol) :
    workRunExact? (machine 2 0 0) (workSteps 2 0 0 1 [] [1, 4, 0, 7] 0)
      (initialConfiguration 2 0 0 1 [1, 4, 0, 7] [] [] inside outside) =
      some (finalConfiguration 2 0 0 1 [1, 4, 0, 7] [] [] 0 inside outside) :=
  workRunExact 2 0 0 1 [1, 4, 0, 7] [] [] inside outside rfl (by decide)
example (inside outside : List WorkSymbol) :
    workRunExact? (machine 2 1 1) (workSteps 2 1 1 1 [8] [1, 4, 0, 7] 7)
      (initialConfiguration 2 1 1 1 [1, 4, 0, 7] [9] [8] inside outside) =
      some (finalConfiguration 2 1 1 1 [1, 4, 0, 7] [9] [8] 7 inside outside) :=
  workRunExact 2 1 1 1 [1, 4, 0, 7] [9] [8] inside outside rfl (by decide)

example (stride slot count : Nat) :
    (machine stride slot count).rules.Pairwise WorkMachineChain.QueryDistinct :=
  rules_pairwise_query_distinct stride slot count
example (stride slot count : Nat) : WorkMachineChain.NoRuleAtAccept (machine stride slot count) :=
  noRuleAtAccept stride slot count
example (stride slot count : Nat) :
    WorkMachineProgramGraph.NoRuleAt (machine stride slot count) (machine stride slot count).rejectState :=
  noRuleAtReject stride slot count
example (stride slot count : Nat) : (machine stride slot count).acceptState ≠ (machine stride slot count).rejectState :=
  acceptState_ne_rejectState stride slot count

example {width : Nat} (index : Fin width) : literalField ⟨true, index⟩ ⟨0, by decide⟩ = 1 := rfl
example {width : Nat} (index : Fin width) : literalField ⟨false, index⟩ ⟨0, by decide⟩ = 0 := rfl
example {width : Nat} (positive : Bool) (index : Fin width) :
    literalField ⟨positive, index⟩ ⟨1, by decide⟩ = index.val := rfl
example {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length) (field : Fin 2) :
    (BuilderLocalConstraintPayload.literalListValues literals)[2 * index.val + field.val]'
      (literal_field_lt literals index.val index.isLt field) = literalField literals[index.val] field :=
  literal_field_value literals index.val index.isLt field

example {width : Nat} (literals : List (BoundedLiteral width))
    (index : Fin literals.length) (field : Fin 2) (count : Nat) (older after : List Nat)
    (inside outside : List WorkSymbol) (hAfter : after.length = count) :
    workRunExact? (machine 2 field.val count)
      (workSteps 2 field.val count index.val after (BuilderLocalConstraintPayload.literalListValues literals)
        (literalField literals[index.val] field))
      (initialConfiguration 2 field.val count index.val
        (BuilderLocalConstraintPayload.literalListValues literals) older after inside outside) =
      some (finalConfiguration 2 field.val count index.val
        (BuilderLocalConstraintPayload.literalListValues literals) older after
        (literalField literals[index.val] field) inside outside) :=
  workRun_literal_field literals index field count older after inside outside hAfter
example {width : Nat} (literals : List (BoundedLiteral width))
    (index : Fin literals.length) (field : Fin 2) (count : Nat) (older after : List Nat)
    (inside outside : List WorkSymbol) (hAfter : after.length = count) :
    run (compileWorkMachine (machine 2 field.val count))
      (6 * workSteps 2 field.val count index.val after (BuilderLocalConstraintPayload.literalListValues literals)
        (literalField literals[index.val] field))
      (encodeWorkConfiguration (initialConfiguration 2 field.val count index.val
        (BuilderLocalConstraintPayload.literalListValues literals) older after inside outside)) =
      encodeWorkConfiguration (finalConfiguration 2 field.val count index.val
        (BuilderLocalConstraintPayload.literalListValues literals) older after
        (literalField literals[index.val] field) inside outside) :=
  run_compile_literal_field literals index field count older after inside outside hAfter
example {width : Nat} (variables : List (Fin width)) (index : Fin variables.length)
    (count : Nat) (older after : List Nat) (inside outside : List WorkSymbol) (hAfter : after.length = count) :
    workRunExact? (machine 1 0 count)
      (workSteps 1 0 count index.val after (BuilderLocalConstraintPayload.variableValues variables) variables[index.val].val)
      (initialConfiguration 1 0 count index.val
        (BuilderLocalConstraintPayload.variableValues variables) older after inside outside) =
      some (finalConfiguration 1 0 count index.val
        (BuilderLocalConstraintPayload.variableValues variables) older after variables[index.val].val inside outside) :=
  workRun_variable_field variables index count older after inside outside hAfter
example {width : Nat} (variables : List (Fin width)) (index : Fin variables.length)
    (count : Nat) (older after : List Nat) (inside outside : List WorkSymbol) (hAfter : after.length = count) :
    run (compileWorkMachine (machine 1 0 count))
      (6 * workSteps 1 0 count index.val after (BuilderLocalConstraintPayload.variableValues variables) variables[index.val].val)
      (encodeWorkConfiguration (initialConfiguration 1 0 count index.val
        (BuilderLocalConstraintPayload.variableValues variables) older after inside outside)) =
      encodeWorkConfiguration (finalConfiguration 1 0 count index.val
        (BuilderLocalConstraintPayload.variableValues variables) older after variables[index.val].val inside outside) :=
  run_compile_variable_field variables index count older after inside outside hAfter

example (stride slot afterCount ordinal : Nat) (payload older after : List Nat)
    (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hAfter : after.length = afterCount) (hField : stride * ordinal + slot < payload.length)
    (hSpan : (registerWord (initialValues payload older ordinal after)).length + outside.length ≤ bound.eval input) :
    (registerWord (finalValues stride slot afterCount ordinal payload older after payload[stride * ordinal + slot])).length +
        (outside.drop (allocation stride slot afterCount ordinal payload[stride * ordinal + slot])).length ≤
        (spanPolynomial stride slot afterCount bound).eval input ∧
      6 * workSteps stride slot afterCount ordinal after payload payload[stride * ordinal + slot] ≤
        (rawTimePolynomial stride slot afterCount bound).eval input :=
  source_polynomial_bounds stride slot afterCount ordinal payload older after outside bound input hAfter hField hSpan

example {width : Nat} (literals : List (BoundedLiteral width))
    (index : Fin literals.length) (field : Fin 2) (afterCount : Nat) (older after : List Nat)
    (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat) (hAfter : after.length = afterCount)
    (hSpan : (registerWord (initialValues (BuilderLocalConstraintPayload.literalListValues literals)
      older index.val after)).length + outside.length ≤ bound.eval input) :
    (registerWord (finalValues 2 field.val afterCount index.val
      (BuilderLocalConstraintPayload.literalListValues literals) older after (literalField literals[index.val] field))).length +
      (outside.drop (allocation 2 field.val afterCount index.val (literalField literals[index.val] field))).length ≤
      (spanPolynomial 2 field.val afterCount bound).eval input ∧
    6 * workSteps 2 field.val afterCount index.val after (BuilderLocalConstraintPayload.literalListValues literals)
      (literalField literals[index.val] field) ≤ (rawTimePolynomial 2 field.val afterCount bound).eval input :=
  literal_source_polynomial_bounds literals index field afterCount older after outside bound input hAfter hSpan

example {width : Nat} (variables : List (Fin width))
    (index : Fin variables.length) (afterCount : Nat) (older after : List Nat)
    (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat) (hAfter : after.length = afterCount)
    (hSpan : (registerWord (initialValues (BuilderLocalConstraintPayload.variableValues variables)
      older index.val after)).length + outside.length ≤ bound.eval input) :
    (registerWord (finalValues 1 0 afterCount index.val
      (BuilderLocalConstraintPayload.variableValues variables) older after variables[index.val].val)).length +
      (outside.drop (allocation 1 0 afterCount index.val variables[index.val].val)).length ≤
      (spanPolynomial 1 0 afterCount bound).eval input ∧
    6 * workSteps 1 0 afterCount index.val after (BuilderLocalConstraintPayload.variableValues variables)
      variables[index.val].val ≤ (rawTimePolynomial 1 0 afterCount bound).eval input :=
  variable_source_polynomial_bounds variables index afterCount older after outside bound input hAfter hSpan
