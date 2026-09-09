/-
Copyright (c) 2026 PNP Labs.

A fixed-schema field reader computes its address from the ordinal on the tape.
It accounts for its own five expression registers, then runs the general
runtime indexer. Payload values, ordinals and list lengths do not generate
control. Literal and variable-list contracts derive their own field bounds.

This is canonical payload access, not a complete literal-token search,
ordered-pair selector, source-bound request generator or formula builder.
-/

import PNP.Concrete.CookLevinBuilderRegisterExpression
import PNP.Concrete.CookLevinBuilderRegisterIndexedCopy
import PNP.Concrete.CookLevinBuilderLocalConstraintPayload

namespace PNP.Concrete.CookLevin.BuilderPayloadFieldCopy

open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)

def offset (slot afterCount : Nat) : Nat := afterCount + 5 + slot
def address (stride slot afterCount ordinal : Nat) : Nat :=
  stride * ordinal + offset slot afterCount

def expression (stride slot afterCount : Nat) : BuilderRegisterExpression.Expr 1 :=
  .binary .add (.binary .mul (.constant stride) (.argument ⟨0, by decide⟩))
    (.constant (offset slot afterCount))

def environment (ordinal : Nat) : Fin 1 → Nat := fun _ => ordinal

def scratchPrefix (stride slot afterCount ordinal : Nat) : List Nat :=
  [stride, ordinal, stride * ordinal, offset slot afterCount]
def scratch (stride slot afterCount ordinal : Nat) : List Nat :=
  scratchPrefix stride slot afterCount ordinal ++ [address stride slot afterCount ordinal]

theorem expression_eval (stride slot afterCount ordinal : Nat) :
    BuilderRegisterExpression.eval (expression stride slot afterCount) (environment ordinal) =
      address stride slot afterCount ordinal := rfl

theorem expression_values (stride slot afterCount ordinal : Nat) :
    BuilderRegisterExpression.values (expression stride slot afterCount) (environment ordinal) =
      scratch stride slot afterCount ordinal := rfl

theorem expression_nodeCount (stride slot afterCount : Nat) :
    BuilderRegisterExpression.nodeCount (expression stride slot afterCount) = 5 := rfl

theorem scratch_length (stride slot afterCount ordinal : Nat) :
    (scratch stride slot afterCount ordinal).length = 5 := rfl

theorem environment_values (ordinal : Nat) :
    List.ofFn (environment ordinal) = [ordinal] := rfl

def reader (stride slot afterCount ordinal : Nat) (after payload : List Nat) : List Nat :=
  (scratchPrefix stride slot afterCount ordinal).reverse ++ after.reverse ++ [ordinal] ++ payload

def initialValues (payload older : List Nat) (ordinal : Nat) (after : List Nat) : List Nat :=
  older ++ payload.reverse ++ [ordinal] ++ after

def finalValues (stride slot afterCount ordinal : Nat) (payload older after : List Nat) (value : Nat) : List Nat :=
  initialValues payload older ordinal after ++ scratch stride slot afterCount ordinal ++ [value]

def allocation (stride slot afterCount ordinal value : Nat) : Nat :=
  (registerWord (scratch stride slot afterCount ordinal)).length + (value + 1)

def machine (stride slot afterCount : Nat) : WorkMachine :=
  WorkMachineChain.machine
    (BuilderRegisterExpression.machine (expression stride slot afterCount) afterCount)
    BuilderRegisterIndexedCopy.machine

def workSteps (stride slot afterCount ordinal : Nat) (after payload : List Nat) (value : Nat) : Nat :=
  BuilderRegisterExpression.workSteps (expression stride slot afterCount) (environment ordinal) after + 1 +
    BuilderRegisterIndexedCopy.workSteps
      ((reader stride slot afterCount ordinal after payload).take (address stride slot afterCount ordinal)) value

def initialConfiguration (stride slot afterCount ordinal : Nat) (payload older after : List Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration (machine stride slot afterCount)
    (endTape (initialValues payload older ordinal after) inside outside)

def finalConfiguration (stride slot afterCount ordinal : Nat) (payload older after : List Nat) (value : Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  {state := (machine stride slot afterCount).acceptState,
   tape := endTape (finalValues stride slot afterCount ordinal payload older after value)
    inside (outside.drop (allocation stride slot afterCount ordinal value))}

theorem reader_address_lt (stride slot afterCount ordinal : Nat) (after payload : List Nat)
    (hAfter : after.length = afterCount) (hField : stride * ordinal + slot < payload.length) :
    address stride slot afterCount ordinal < (reader stride slot afterCount ordinal after payload).length := by
  simp only [address, offset, reader, scratchPrefix, List.length_append, List.length_reverse,
    List.length_cons, List.length_nil, hAfter]
  omega

theorem reader_address_value (stride slot afterCount ordinal : Nat) (after payload : List Nat)
    (hAfter : after.length = afterCount) (hField : stride * ordinal + slot < payload.length) :
    (reader stride slot afterCount ordinal after payload)[address stride slot afterCount ordinal]'
      (reader_address_lt stride slot afterCount ordinal after payload hAfter hField) =
      payload[stride * ordinal + slot] := by
  have hNear : ((scratchPrefix stride slot afterCount ordinal).reverse ++ after.reverse ++ [ordinal]).length =
      afterCount + 5 := by
    simp only [scratchPrefix, List.length_append, List.length_reverse, List.length_cons,
      List.length_nil, hAfter]
    omega
  unfold reader
  rw [List.getElem_append_right (by simp only [hNear, address, offset]; omega)]
  congr 1
  simp only [hNear, address, offset]
  omega

theorem reader_layout (stride slot afterCount ordinal : Nat) (after payload older : List Nat) :
    older ++ (reader stride slot afterCount ordinal after payload).reverse ++ [address stride slot afterCount ordinal] =
      initialValues payload older ordinal after ++ scratch stride slot afterCount ordinal := by
  simp only [reader, initialValues, scratch, List.reverse_append, List.reverse_reverse,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.append_assoc]

private theorem chain_run (first second : WorkMachine) (n m : Nat) (initial middle final : WorkTape)
    (hFirst : workRunExact? first n (workStartConfiguration first initial) =
      some {state := first.acceptState, tape := middle})
    (hSecond : workRunExact? second m (workStartConfiguration second middle) =
      some {state := second.acceptState, tape := final}) :
    workRunExact? (WorkMachineChain.machine first second) (n + 1 + m)
      (workStartConfiguration (WorkMachineChain.machine first second) initial) =
      some {state := (WorkMachineChain.machine first second).acceptState, tape := final} :=
  WorkMachineChain.workRunExact first second n m _ _ _ hFirst rfl hSecond

/-- The schema is fixed. The ordinal is read from its preserved input register. -/
theorem workRunExact (stride slot afterCount ordinal : Nat) (payload older after : List Nat)
    (inside outside : List WorkSymbol) (hAfter : after.length = afterCount)
    (hField : stride * ordinal + slot < payload.length) :
    workRunExact? (machine stride slot afterCount)
      (workSteps stride slot afterCount ordinal after payload payload[stride * ordinal + slot])
      (initialConfiguration stride slot afterCount ordinal payload older after inside outside) =
      some (finalConfiguration stride slot afterCount ordinal payload older after
        payload[stride * ordinal + slot] inside outside) := by
  let value := payload[stride * ordinal + slot]
  let middle := endTape (initialValues payload older ordinal after ++ scratch stride slot afterCount ordinal)
    inside (outside.drop (registerWord (scratch stride slot afterCount ordinal)).length)
  have hExpression := BuilderRegisterExpression.workRunExact (expression stride slot afterCount)
    afterCount (older ++ payload.reverse) (environment ordinal) after inside outside hAfter
  have hFirst : workRunExact? (BuilderRegisterExpression.machine (expression stride slot afterCount) afterCount)
      (BuilderRegisterExpression.workSteps (expression stride slot afterCount) (environment ordinal) after)
      (workStartConfiguration (BuilderRegisterExpression.machine (expression stride slot afterCount) afterCount)
        (endTape (initialValues payload older ordinal after) inside outside)) =
      some {state := (BuilderRegisterExpression.machine (expression stride slot afterCount) afterCount).acceptState,
            tape := middle} := by
    simpa only [BuilderRegisterExpression.initialConfiguration, BuilderRegisterExpression.finalConfiguration,
      expression_values, environment_values, initialValues, middle] using hExpression
  have hCopy := BuilderRegisterIndexedCopy.workRun_select_getElem
    (reader stride slot afterCount ordinal after payload) older
    ⟨address stride slot afterCount ordinal, reader_address_lt stride slot afterCount ordinal after payload hAfter hField⟩
    inside (outside.drop (registerWord (scratch stride slot afterCount ordinal)).length)
  simp only [reader_address_value stride slot afterCount ordinal after payload hAfter hField] at hCopy
  have hSecond : workRunExact? BuilderRegisterIndexedCopy.machine
      (BuilderRegisterIndexedCopy.workSteps
        ((reader stride slot afterCount ordinal after payload).take (address stride slot afterCount ordinal)) value)
      (workStartConfiguration BuilderRegisterIndexedCopy.machine middle) =
      some {state := BuilderRegisterIndexedCopy.machine.acceptState,
            tape := (finalConfiguration stride slot afterCount ordinal payload older after value inside outside).tape} := by
    have hEnd : older ++ (reader stride slot afterCount ordinal after payload).reverse ++
        [address stride slot afterCount ordinal, value] =
        finalValues stride slot afterCount ordinal payload older after value := by
      rw [show [address stride slot afterCount ordinal, value] =
        [address stride slot afterCount ordinal] ++ [value] from rfl, ← List.append_assoc, reader_layout]
      rfl
    simpa only [reader_layout, hEnd, List.drop_drop, middle, finalConfiguration, allocation, value] using hCopy
  have h := chain_run _ _ _ _ _ _ _ hFirst hSecond
  simpa only [machine, workSteps, initialConfiguration, finalConfiguration, value] using h

theorem run_compile_exact (stride slot afterCount ordinal : Nat) (payload older after : List Nat)
    (inside outside : List WorkSymbol) (hAfter : after.length = afterCount)
    (hField : stride * ordinal + slot < payload.length) :
    run (compileWorkMachine (machine stride slot afterCount))
      (6 * workSteps stride slot afterCount ordinal after payload payload[stride * ordinal + slot])
      (encodeWorkConfiguration (initialConfiguration stride slot afterCount ordinal payload older after inside outside)) =
      encodeWorkConfiguration (finalConfiguration stride slot afterCount ordinal payload older after
        payload[stride * ordinal + slot] inside outside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _
    (workRunExact stride slot afterCount ordinal payload older after inside outside hAfter hField)

theorem final_tape (stride slot afterCount ordinal : Nat) (payload older after : List Nat) (value : Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration stride slot afterCount ordinal payload older after value inside outside).tape =
      endTape (initialValues payload older ordinal after ++ scratch stride slot afterCount ordinal ++ [value])
        inside (outside.drop (allocation stride slot afterCount ordinal value)) := rfl

theorem rules_pairwise_query_distinct (stride slot afterCount : Nat) :
    (machine stride slot afterCount).rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineChain.rules_pairwise_query_distinct _ _
    (BuilderRegisterExpression.rules_pairwise_query_distinct _ _)
    BuilderRegisterIndexedCopy.rules_pairwise_query_distinct
    (BuilderRegisterExpression.noRuleAtAccept _ _)

theorem noRuleAtAccept (stride slot afterCount : Nat) :
    WorkMachineChain.NoRuleAtAccept (machine stride slot afterCount) :=
  WorkMachineChain.noRuleAtAccept _ _ BuilderRegisterIndexedCopy.noRuleAtAccept

theorem noRuleAtReject (stride slot afterCount : Nat) :
    WorkMachineProgramGraph.NoRuleAt (machine stride slot afterCount) (machine stride slot afterCount).rejectState :=
  WorkMachineChain.noRuleAtAccept _
    {BuilderRegisterIndexedCopy.machine with acceptState := BuilderRegisterIndexedCopy.machine.rejectState}
    BuilderRegisterIndexedCopy.noRuleAtReject

theorem acceptState_ne_rejectState (stride slot afterCount : Nat) :
    (machine stride slot afterCount).acceptState ≠ (machine stride slot afterCount).rejectState :=
  WorkMachineChain.machine_acceptState_ne_rejectState _ _ BuilderRegisterIndexedCopy.acceptState_ne_rejectState

/-- Retain the original exterior in the intermediate bound as well as expression scratch. -/
def middleSpanPolynomial (stride slot afterCount : Nat) (bound : NatPolynomial) : NatPolynomial :=
  .add (BuilderRegisterExpression.spanPolynomial (expression stride slot afterCount) bound) bound

def spanPolynomial (stride slot afterCount : Nat) (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterIndexedCopy.spanPolynomial (middleSpanPolynomial stride slot afterCount bound)

def rawTimePolynomial (stride slot afterCount : Nat) (bound : NatPolynomial) : NatPolynomial :=
  .add (.add (BuilderRegisterExpression.rawTimePolynomial (expression stride slot afterCount) bound) (.constant 6))
    (BuilderRegisterIndexedCopy.rawTimePolynomial (middleSpanPolynomial stride slot afterCount bound))

theorem source_polynomial_bounds (stride slot afterCount ordinal : Nat) (payload older after : List Nat)
    (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hAfter : after.length = afterCount) (hField : stride * ordinal + slot < payload.length)
    (hSpan : (registerWord (initialValues payload older ordinal after)).length + outside.length ≤ bound.eval input) :
    (registerWord (finalValues stride slot afterCount ordinal payload older after payload[stride * ordinal + slot])).length +
        (outside.drop (allocation stride slot afterCount ordinal payload[stride * ordinal + slot])).length ≤
        (spanPolynomial stride slot afterCount bound).eval input ∧
      6 * workSteps stride slot afterCount ordinal after payload payload[stride * ordinal + slot] ≤
        (rawTimePolynomial stride slot afterCount bound).eval input := by
  have hWord : (registerWord ((older ++ payload.reverse) ++ List.ofFn (environment ordinal) ++ after)).length ≤
      bound.eval input := by
    simpa only [environment_values, initialValues] using (show
      (registerWord (initialValues payload older ordinal after)).length ≤ bound.eval input by omega)
  have hExpression := BuilderRegisterExpression.source_polynomial_bounds (expression stride slot afterCount)
    bound input (older ++ payload.reverse) (environment ordinal) after hWord
  simp only [environment_values, expression_values] at hExpression
  have hMiddle : (registerWord (older ++ (reader stride slot afterCount ordinal after payload).reverse ++
      [address stride slot afterCount ordinal])).length +
      (outside.drop (registerWord (scratch stride slot afterCount ordinal)).length).length ≤
      (middleSpanPolynomial stride slot afterCount bound).eval input := by
    rw [reader_layout]
    simp only [middleSpanPolynomial, NatPolynomial.eval_add, List.length_drop]
    unfold initialValues at hSpan ⊢
    omega
  have hCopy := BuilderRegisterIndexedCopy.selected_source_polynomial_bounds
    (reader stride slot afterCount ordinal after payload) older
    ⟨address stride slot afterCount ordinal, reader_address_lt stride slot afterCount ordinal after payload hAfter hField⟩
    (outside.drop (registerWord (scratch stride slot afterCount ordinal)).length)
    (middleSpanPolynomial stride slot afterCount bound) input hMiddle
  simp only [reader_address_value stride slot afterCount ordinal after payload hAfter hField] at hCopy
  constructor
  · have hEnd : older ++ (reader stride slot afterCount ordinal after payload).reverse ++
        [address stride slot afterCount ordinal, payload[stride * ordinal + slot]] =
        finalValues stride slot afterCount ordinal payload older after payload[stride * ordinal + slot] := by
      rw [show [address stride slot afterCount ordinal, payload[stride * ordinal + slot]] =
        [address stride slot afterCount ordinal] ++ [payload[stride * ordinal + slot]] from rfl,
        ← List.append_assoc, reader_layout]
      rfl
    simpa only [hEnd, List.drop_drop, allocation, spanPolynomial] using hCopy.1
  · simp only [workSteps, rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

def literalField {width : Nat} (literal : BoundedLiteral width) (field : Fin 2) : Nat :=
  if field.val = 0 then BuilderLocalConstraintPayload.signValue literal.positive else literal.index.val

theorem literal_field_lt {width : Nat} (literals : List (BoundedLiteral width)) (ordinal : Nat)
    (hOrdinal : ordinal < literals.length) (field : Fin 2) :
    2 * ordinal + field.val < (BuilderLocalConstraintPayload.literalListValues literals).length := by
  rw [BuilderLocalConstraintPayload.literalListValues_length]
  have hField := field.isLt
  omega

theorem literal_field_value {width : Nat} (literals : List (BoundedLiteral width)) (ordinal : Nat)
    (hOrdinal : ordinal < literals.length) (field : Fin 2) :
    (BuilderLocalConstraintPayload.literalListValues literals)[2 * ordinal + field.val]'
      (literal_field_lt literals ordinal hOrdinal field) = literalField literals[ordinal] field := by
  induction literals generalizing ordinal with
  | nil => simp only [List.length_nil] at hOrdinal; omega
  | cons literal rest ih =>
      cases ordinal with
      | zero =>
          rcases field with ⟨field, hField⟩
          have hCases : field = 0 ∨ field = 1 := by omega
          rcases hCases with hZero | hOne
          · subst field; rfl
          · subst field; rfl
      | succ ordinal =>
          have hRest : ordinal < rest.length := by simp only [List.length_cons] at hOrdinal; omega
          have hIndex : 2 * (ordinal + 1) + field.val = (2 * ordinal + field.val) + 1 + 1 := by omega
          simpa only [BuilderLocalConstraintPayload.literalListValues, BuilderLocalConstraintPayload.literalValues,
            List.cons_append, List.nil_append, hIndex, List.getElem_cons_succ] using ih ordinal hRest

/-- Both fields of every literal are read from the canonical list, not supplied. -/
theorem workRun_literal_field {width : Nat} (literals : List (BoundedLiteral width))
    (index : Fin literals.length) (field : Fin 2) (afterCount : Nat) (older after : List Nat)
    (inside outside : List WorkSymbol) (hAfter : after.length = afterCount) :
    workRunExact? (machine 2 field.val afterCount)
      (workSteps 2 field.val afterCount index.val after (BuilderLocalConstraintPayload.literalListValues literals)
        (literalField literals[index.val] field))
      (initialConfiguration 2 field.val afterCount index.val
        (BuilderLocalConstraintPayload.literalListValues literals) older after inside outside) =
      some (finalConfiguration 2 field.val afterCount index.val
        (BuilderLocalConstraintPayload.literalListValues literals) older after
        (literalField literals[index.val] field) inside outside) := by
  have h := workRunExact 2 field.val afterCount index.val (BuilderLocalConstraintPayload.literalListValues literals)
    older after inside outside hAfter (literal_field_lt literals index.val index.isLt field)
  simpa only [literal_field_value literals index.val index.isLt field] using h

theorem run_compile_literal_field {width : Nat} (literals : List (BoundedLiteral width))
    (index : Fin literals.length) (field : Fin 2) (afterCount : Nat) (older after : List Nat)
    (inside outside : List WorkSymbol) (hAfter : after.length = afterCount) :
    run (compileWorkMachine (machine 2 field.val afterCount))
      (6 * workSteps 2 field.val afterCount index.val after (BuilderLocalConstraintPayload.literalListValues literals)
        (literalField literals[index.val] field))
      (encodeWorkConfiguration (initialConfiguration 2 field.val afterCount index.val
        (BuilderLocalConstraintPayload.literalListValues literals) older after inside outside)) =
      encodeWorkConfiguration (finalConfiguration 2 field.val afterCount index.val
        (BuilderLocalConstraintPayload.literalListValues literals) older after
        (literalField literals[index.val] field) inside outside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _
    (workRun_literal_field literals index field afterCount older after inside outside hAfter)

theorem literal_source_polynomial_bounds {width : Nat} (literals : List (BoundedLiteral width))
    (index : Fin literals.length) (field : Fin 2) (afterCount : Nat) (older after : List Nat)
    (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat) (hAfter : after.length = afterCount)
    (hSpan : (registerWord (initialValues (BuilderLocalConstraintPayload.literalListValues literals)
      older index.val after)).length + outside.length ≤ bound.eval input) :
    (registerWord (finalValues 2 field.val afterCount index.val
      (BuilderLocalConstraintPayload.literalListValues literals) older after (literalField literals[index.val] field))).length +
      (outside.drop (allocation 2 field.val afterCount index.val (literalField literals[index.val] field))).length ≤
      (spanPolynomial 2 field.val afterCount bound).eval input ∧
    6 * workSteps 2 field.val afterCount index.val after (BuilderLocalConstraintPayload.literalListValues literals)
      (literalField literals[index.val] field) ≤ (rawTimePolynomial 2 field.val afterCount bound).eval input := by
  simpa only [literal_field_value literals index.val index.isLt field] using source_polynomial_bounds 2 field.val afterCount index.val
    (BuilderLocalConstraintPayload.literalListValues literals) older after outside bound input hAfter
    (literal_field_lt literals index.val index.isLt field) hSpan

theorem workRun_variable_field {width : Nat} (variables : List (Fin width))
    (index : Fin variables.length) (afterCount : Nat) (older after : List Nat)
    (inside outside : List WorkSymbol) (hAfter : after.length = afterCount) :
    workRunExact? (machine 1 0 afterCount)
      (workSteps 1 0 afterCount index.val after (BuilderLocalConstraintPayload.variableValues variables)
        variables[index.val].val)
      (initialConfiguration 1 0 afterCount index.val
        (BuilderLocalConstraintPayload.variableValues variables) older after inside outside) =
      some (finalConfiguration 1 0 afterCount index.val
        (BuilderLocalConstraintPayload.variableValues variables) older after variables[index.val].val inside outside) := by
  have hField : 1 * index.val + 0 < (BuilderLocalConstraintPayload.variableValues variables).length := by
    simpa only [Nat.one_mul, Nat.add_zero, BuilderLocalConstraintPayload.variableValues, List.length_map] using index.isLt
  simpa only [Nat.one_mul, Nat.add_zero, BuilderLocalConstraintPayload.variableValues, List.getElem_map] using
    workRunExact 1 0 afterCount index.val (BuilderLocalConstraintPayload.variableValues variables)
      older after inside outside hAfter hField

theorem run_compile_variable_field {width : Nat} (variables : List (Fin width))
    (index : Fin variables.length) (afterCount : Nat) (older after : List Nat)
    (inside outside : List WorkSymbol) (hAfter : after.length = afterCount) :
    run (compileWorkMachine (machine 1 0 afterCount))
      (6 * workSteps 1 0 afterCount index.val after (BuilderLocalConstraintPayload.variableValues variables)
        variables[index.val].val)
      (encodeWorkConfiguration (initialConfiguration 1 0 afterCount index.val
        (BuilderLocalConstraintPayload.variableValues variables) older after inside outside)) =
      encodeWorkConfiguration (finalConfiguration 1 0 afterCount index.val
        (BuilderLocalConstraintPayload.variableValues variables) older after variables[index.val].val inside outside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _
    (workRun_variable_field variables index afterCount older after inside outside hAfter)

theorem variable_source_polynomial_bounds {width : Nat} (variables : List (Fin width))
    (index : Fin variables.length) (afterCount : Nat) (older after : List Nat)
    (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat) (hAfter : after.length = afterCount)
    (hSpan : (registerWord (initialValues (BuilderLocalConstraintPayload.variableValues variables)
      older index.val after)).length + outside.length ≤ bound.eval input) :
    (registerWord (finalValues 1 0 afterCount index.val
      (BuilderLocalConstraintPayload.variableValues variables) older after variables[index.val].val)).length +
      (outside.drop (allocation 1 0 afterCount index.val variables[index.val].val)).length ≤
      (spanPolynomial 1 0 afterCount bound).eval input ∧
    6 * workSteps 1 0 afterCount index.val after (BuilderLocalConstraintPayload.variableValues variables)
      variables[index.val].val ≤ (rawTimePolynomial 1 0 afterCount bound).eval input := by
  have hField : 1 * index.val + 0 < (BuilderLocalConstraintPayload.variableValues variables).length := by
    simpa only [Nat.one_mul, Nat.add_zero, BuilderLocalConstraintPayload.variableValues, List.length_map] using index.isLt
  simpa only [Nat.one_mul, Nat.add_zero, BuilderLocalConstraintPayload.variableValues, List.getElem_map] using
    source_polynomial_bounds 1 0 afterCount index.val (BuilderLocalConstraintPayload.variableValues variables)
      older after outside bound input hAfter hField hSpan

end PNP.Concrete.CookLevin.BuilderPayloadFieldCopy
