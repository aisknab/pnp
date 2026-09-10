/-
Copyright (c) 2026 PNP Labs.

The first exclusion variable is copied from the actual exactly-one payload
after the complete pair lookup. The reader computes its address from the
terminal row registers and accounts for all retained history and scratch.
No pair, field value, history length or successful run is supplied at runtime.

The second variable, literal tokens and final source request/recovery remain
separate composition obligations. This does not earn the complete builder.
-/

import PNP.Concrete.CookLevinBuilderExclusionPairLookup
import PNP.Concrete.CookLevinBuilderPayloadFieldCopy

namespace PNP.Concrete.CookLevin.BuilderExclusionPairFirstVariable

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderExclusionPairSelection (rowSelection reverseCoordinate reversePair selectedPair)
open BuilderRegisterExpression (Expr)

def firstIndex (environment : Fin 9 → Nat) : Nat := environment ⟨3, by decide⟩
def rowWidth (environment : Fin 9 → Nat) : Nat := environment ⟨7, by decide⟩
def rowOffset (environment : Fin 9 → Nat) : Nat := environment ⟨8, by decide⟩
def secondIndex (environment : Fin 9 → Nat) : Nat := firstIndex environment + rowWidth environment - rowOffset environment

/-- Two payload headers, 25 preparation registers and six non-root scratch registers. -/
def expression : Expr 9 :=
  .binary .add
    (.binary .add (.binary .mul (.constant 9) (.argument ⟨7, by decide⟩))
      (.argument ⟨3, by decide⟩))
    (.constant 33)

def address (environment : Fin 9 → Nat) : Nat :=
  9 * rowWidth environment + firstIndex environment + 33

def scratchPrefix (environment : Fin 9 → Nat) : List Nat :=
  [9, rowWidth environment, 9 * rowWidth environment, firstIndex environment,
    9 * rowWidth environment + firstIndex environment, 33]
def scratch (environment : Fin 9 → Nat) : List Nat :=
  scratchPrefix environment ++ [address environment]

theorem expression_eval (environment : Fin 9 → Nat) :
    BuilderRegisterExpression.eval expression environment = address environment := rfl
theorem expression_values (environment : Fin 9 → Nat) :
    BuilderRegisterExpression.values expression environment = scratch environment := rfl
theorem expression_nodeCount : BuilderRegisterExpression.nodeCount expression = 7 := rfl
theorem scratch_length (environment : Fin 9 → Nat) : (scratch environment).length = 7 := rfl

def initialValues (payload older history : List Nat) (environment : Fin 9 → Nat) : List Nat :=
  older ++ payload.reverse ++ history ++ List.ofFn environment
def finalValues (payload older history : List Nat) (environment : Fin 9 → Nat) (value : Nat) : List Nat :=
  initialValues payload older history environment ++ scratch environment ++ [value]
def reader (payload history : List Nat) (environment : Fin 9 → Nat) : List Nat :=
  (scratchPrefix environment).reverse ++ (List.ofFn environment).reverse ++ history.reverse ++ payload
def allocation (environment : Fin 9 → Nat) (value : Nat) : Nat :=
  (registerWord (scratch environment)).length + (value + 1)

def machine : WorkMachine :=
  WorkMachineChain.machine (BuilderRegisterExpression.machine expression 0) BuilderRegisterIndexedCopy.machine
def workSteps (payload history : List Nat) (environment : Fin 9 → Nat) (value : Nat) : Nat :=
  BuilderRegisterExpression.workSteps expression environment [] + 1 +
    BuilderRegisterIndexedCopy.workSteps ((reader payload history environment).take (address environment)) value
def initialConfiguration (payload older history : List Nat) (environment : Fin 9 → Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration machine (endTape (initialValues payload older history environment) inside outside)
def finalConfiguration (payload older history : List Nat) (environment : Fin 9 → Nat) (value : Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  { state := machine.acceptState
    tape := endTape (finalValues payload older history environment value)
      inside (outside.drop (allocation environment value)) }

theorem reader_address_lt (payload history : List Nat) (environment : Fin 9 → Nat)
    (hHistory : history.length = 18 + 9 * rowWidth environment)
    (hField : firstIndex environment < payload.length) :
    address environment < (reader payload history environment).length := by
  simp only [address, reader, scratchPrefix, List.length_append, List.length_reverse,
    List.length_ofFn, List.length_cons, List.length_nil, hHistory]
  omega

theorem reader_address_value (payload history : List Nat) (environment : Fin 9 → Nat)
    (hHistory : history.length = 18 + 9 * rowWidth environment)
    (hField : firstIndex environment < payload.length) :
    (reader payload history environment)[address environment]'
      (reader_address_lt payload history environment hHistory hField) = payload[firstIndex environment] := by
  have hNear : ((scratchPrefix environment).reverse ++ (List.ofFn environment).reverse ++ history.reverse).length =
      33 + 9 * rowWidth environment := by
    simp only [scratchPrefix, List.length_append, List.length_reverse, List.length_ofFn,
      List.length_cons, List.length_nil, hHistory]
    omega
  unfold reader
  rw [List.getElem_append_right (by simp only [hNear, address]; omega)]
  congr 1
  simp only [hNear, address]
  omega

theorem reader_layout (payload older history : List Nat) (environment : Fin 9 → Nat) :
    older ++ (reader payload history environment).reverse ++ [address environment] =
      initialValues payload older history environment ++ scratch environment := by
  simp only [reader, initialValues, scratch, List.reverse_append, List.reverse_reverse, List.append_assoc]

private theorem chain_run (first second : WorkMachine) (n m : Nat) (initial middle final : WorkTape)
    (hFirst : workRunExact? first n (workStartConfiguration first initial) =
      some {state := first.acceptState, tape := middle})
    (hSecond : workRunExact? second m (workStartConfiguration second middle) =
      some {state := second.acceptState, tape := final}) :
    workRunExact? (WorkMachineChain.machine first second) (n + 1 + m)
      (workStartConfiguration (WorkMachineChain.machine first second) initial) =
      some {state := (WorkMachineChain.machine first second).acceptState, tape := final} :=
  WorkMachineChain.workRunExact first second n m _ _ _ hFirst rfl hSecond

theorem workRunExact (payload older history : List Nat) (environment : Fin 9 → Nat)
    (inside outside : List WorkSymbol) (hHistory : history.length = 18 + 9 * rowWidth environment)
    (hField : firstIndex environment < payload.length) :
    workRunExact? machine (workSteps payload history environment payload[firstIndex environment])
      (initialConfiguration payload older history environment inside outside) =
      some (finalConfiguration payload older history environment payload[firstIndex environment] inside outside) := by
  let value := payload[firstIndex environment]
  let middle := endTape (initialValues payload older history environment ++ scratch environment)
    inside (outside.drop (registerWord (scratch environment)).length)
  have hExpression := BuilderRegisterExpression.workRunExact expression 0
    (older ++ payload.reverse ++ history) environment [] inside outside rfl
  have hFirst : workRunExact? (BuilderRegisterExpression.machine expression 0)
      (BuilderRegisterExpression.workSteps expression environment [])
      (workStartConfiguration (BuilderRegisterExpression.machine expression 0)
        (endTape (initialValues payload older history environment) inside outside)) =
      some {state := (BuilderRegisterExpression.machine expression 0).acceptState, tape := middle} := by
    simpa only [BuilderRegisterExpression.initialConfiguration, BuilderRegisterExpression.finalConfiguration,
      expression_values, List.append_nil, initialValues, middle] using hExpression
  have hCopy := BuilderRegisterIndexedCopy.workRun_select_getElem
    (reader payload history environment) older
    ⟨address environment, reader_address_lt payload history environment hHistory hField⟩
    inside (outside.drop (registerWord (scratch environment)).length)
  simp only [reader_address_value payload history environment hHistory hField] at hCopy
  have hEnd : older ++ (reader payload history environment).reverse ++ [address environment, value] =
      finalValues payload older history environment value := by
    rw [show [address environment, value] = [address environment] ++ [value] from rfl,
      ← List.append_assoc, reader_layout]
    rfl
  have hSecond : workRunExact? BuilderRegisterIndexedCopy.machine
      (BuilderRegisterIndexedCopy.workSteps ((reader payload history environment).take (address environment)) value)
      (workStartConfiguration BuilderRegisterIndexedCopy.machine middle) =
      some {
        state := BuilderRegisterIndexedCopy.machine.acceptState
        tape := (finalConfiguration payload older history environment value inside outside).tape} := by
    simpa only [reader_layout, hEnd, List.drop_drop, middle, finalConfiguration, allocation, value] using hCopy
  have h := chain_run _ _ _ _ _ _ _ hFirst hSecond
  simpa only [machine, workSteps, initialConfiguration, finalConfiguration, value] using h

theorem run_compile_exact (payload older history : List Nat) (environment : Fin 9 → Nat)
    (inside outside : List WorkSymbol) (hHistory : history.length = 18 + 9 * rowWidth environment)
    (hField : firstIndex environment < payload.length) :
    run (compileWorkMachine machine) (6 * workSteps payload history environment payload[firstIndex environment])
      (encodeWorkConfiguration (initialConfiguration payload older history environment inside outside)) =
      encodeWorkConfiguration
        (finalConfiguration payload older history environment payload[firstIndex environment] inside outside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact payload older history environment inside outside hHistory hField)

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineChain.rules_pairwise_query_distinct _ _
    (BuilderRegisterExpression.rules_pairwise_query_distinct expression 0)
    BuilderRegisterIndexedCopy.rules_pairwise_query_distinct
    (BuilderRegisterExpression.noRuleAtAccept expression 0)
theorem noRuleAtAccept : WorkMachineChain.NoRuleAtAccept machine :=
  WorkMachineChain.noRuleAtAccept _ _ BuilderRegisterIndexedCopy.noRuleAtAccept
theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  WorkMachineChain.noRuleAtAccept _
    {BuilderRegisterIndexedCopy.machine with acceptState := BuilderRegisterIndexedCopy.machine.rejectState}
    BuilderRegisterIndexedCopy.noRuleAtReject
theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState :=
  WorkMachineChain.machine_acceptState_ne_rejectState _ _ BuilderRegisterIndexedCopy.acceptState_ne_rejectState

def middleSpanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (BuilderRegisterExpression.spanPolynomial expression bound) bound
def spanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterIndexedCopy.spanPolynomial (middleSpanPolynomial bound)
def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.add (BuilderRegisterExpression.rawTimePolynomial expression bound) (.constant 6))
    (BuilderRegisterIndexedCopy.rawTimePolynomial (middleSpanPolynomial bound))

theorem source_polynomial_bounds (payload older history : List Nat) (environment : Fin 9 → Nat)
    (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hHistory : history.length = 18 + 9 * rowWidth environment)
    (hField : firstIndex environment < payload.length)
    (hSpan : (registerWord (initialValues payload older history environment)).length + outside.length ≤ bound.eval input) :
    (registerWord (finalValues payload older history environment payload[firstIndex environment])).length +
        (outside.drop (allocation environment payload[firstIndex environment])).length ≤
          (spanPolynomial bound).eval input ∧
      6 * workSteps payload history environment payload[firstIndex environment] ≤ (rawTimePolynomial bound).eval input := by
  have hWord : (registerWord ((older ++ payload.reverse ++ history) ++ List.ofFn environment ++ [])).length ≤
      bound.eval input := by
    simpa only [List.append_nil, initialValues] using (show
      (registerWord (initialValues payload older history environment)).length ≤ bound.eval input by omega)
  have hExpression := BuilderRegisterExpression.source_polynomial_bounds expression bound input
    (older ++ payload.reverse ++ history) environment [] hWord
  simp only [expression_values, List.append_nil] at hExpression
  have hMiddle : (registerWord (older ++ (reader payload history environment).reverse ++ [address environment])).length +
      (outside.drop (registerWord (scratch environment)).length).length ≤
        (middleSpanPolynomial bound).eval input := by
    rw [reader_layout]
    simp only [middleSpanPolynomial, NatPolynomial.eval_add, List.length_drop]
    unfold initialValues at hSpan ⊢
    omega
  have hCopy := BuilderRegisterIndexedCopy.selected_source_polynomial_bounds
    (reader payload history environment) older
    ⟨address environment, reader_address_lt payload history environment hHistory hField⟩
    (outside.drop (registerWord (scratch environment)).length) (middleSpanPolynomial bound) input hMiddle
  simp only [reader_address_value payload history environment hHistory hField] at hCopy
  have hEnd : older ++ (reader payload history environment).reverse ++
      [address environment, payload[firstIndex environment]] =
      finalValues payload older history environment payload[firstIndex environment] := by
    rw [show [address environment, payload[firstIndex environment]] =
      [address environment] ++ [payload[firstIndex environment]] from rfl,
      ← List.append_assoc, reader_layout]
    rfl
  constructor
  · simpa only [hEnd, List.drop_drop, allocation, spanPolynomial] using hCopy.1
  · simp only [workSteps, rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

def payloadValues {width : Nat} (variables : List (Fin width)) : List Nat :=
  BuilderLocalConstraintPayload.values (some (some (.exactlyOne variables)))
def lookupValues {width : Nat} (variables : List (Fin width)) (coordinate : Nat) (older : List Nat) : List Nat :=
  BuilderExclusionPairLookup.resultValues variables.length coordinate (older ++ payloadValues variables)

theorem payload_values {width : Nat} (variables : List (Fin width)) :
    payloadValues variables = (BuilderLocalConstraintPayload.variableValues variables).reverse ++ [variables.length, 4] := by
  simp only [payloadValues, BuilderLocalConstraintPayload.values, BuilderLocalConstraintPayload.front,
    List.reverse_append]
  rfl

/-- The source run derives the complete history and both canonical indices; none is a runtime premise. -/
theorem source_layout {width : Nat} (variables : List (Fin width)) (coordinate : Nat) (older : List Nat)
    (hValid : coordinate < LocalConstraint.pairCount variables.length) :
    ∃ (first second : Fin variables.length) (environment : Fin 9 → Nat) (history : List Nat),
      selectedPair variables.length coordinate = some (first.val, second.val) ∧
      firstIndex environment = first.val ∧
      secondIndex environment = second.val ∧
      rowOffset environment < rowWidth environment ∧
      history.length = 18 + 9 * rowWidth environment ∧
      lookupValues variables coordinate older =
        initialValues (BuilderLocalConstraintPayload.variableValues variables) older history environment := by
  cases hFound : rowSelection variables.length coordinate with
  | none =>
      have hInvalid := (BuilderExclusionPairSelection.rowSelection_none_iff variables.length coordinate).mp hFound
      exfalso
      omega
  | some found =>
      rcases found with ⟨position, offset⟩
      have hSpec := BuilderExclusionPairSelection.rowSelection_pair_spec variables.length coordinate position offset hFound
      have hBounds := BuilderInitialLengthSelection.locate_some_bounds
        (variables.length - 1) 1 (reverseCoordinate variables.length coordinate) position offset hFound
      have hLess : offset < 1 + position.val := hBounds.1
      rcases BuilderExclusionPairRow.found_attempt (variables.length - 1) 0 1
        (reverseCoordinate variables.length coordinate) position offset hFound with ⟨prior, hPrior, hFinish⟩
      let environment := BuilderInitialRowLoop.attemptEnvironment position.val (1 + position.val)
        offset (variables.length - 2 - position.val)
      let history := [variables.length, 4] ++
        BuilderExclusionPairPreparation.history variables.length coordinate ++ prior
      have hFirst : variables.length - 2 - position.val < variables.length := Nat.lt_trans hSpec.1 hSpec.2.1
      have hSecond : variables.length - 1 - offset < variables.length := hSpec.2.1
      refine ⟨⟨variables.length - 2 - position.val, hFirst⟩, ⟨variables.length - 1 - offset, hSecond⟩,
        environment, history, ?_, rfl, ?_, ?_, ?_, ?_⟩
      · simp only [selectedPair, hFound, Option.map_some, reversePair]
      · simp only [secondIndex, firstIndex, rowWidth, rowOffset, environment,
          BuilderInitialRowLoop.attemptEnvironment, BuilderRegisterCompareResidual.resultBoundary_eq,
          BuilderRegisterCompareResidual.resultCoordinate_eq, if_pos hLess]
        have hPosition := position.isLt
        omega
      · simpa only [rowOffset, rowWidth, environment, BuilderInitialRowLoop.attemptEnvironment,
          BuilderRegisterCompareResidual.resultBoundary_eq, BuilderRegisterCompareResidual.resultCoordinate_eq,
          if_pos hLess] using hLess
      · simp only [history, List.length_append, List.length_cons, List.length_nil,
          BuilderExclusionPairPreparation.history_length, hPrior, rowWidth, environment,
          BuilderInitialRowLoop.attemptEnvironment, BuilderRegisterCompareResidual.resultBoundary_eq]
        omega
      · have hRemaining : variables.length - 1 - (position.val + 1) = variables.length - 2 - position.val := by omega
        simp only [lookupValues, BuilderExclusionPairLookup.resultValues, if_pos hValid,
          BuilderExclusionPairRow.resultValues, hFinish, Nat.zero_add, hRemaining,
          initialValues, history, environment, BuilderInitialRowLoop.attemptEnvironment_ofFn,
          payload_values, List.append_assoc]

/-- One fixed reader reaches the actual first variable for every valid source clause ordinal. -/
theorem source_read {width : Nat} (variables : List (Fin width)) (coordinate : Nat) (older : List Nat)
    (inside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hValid : coordinate < LocalConstraint.pairCount variables.length)
    (hSpan : (registerWord (lookupValues variables coordinate older)).length ≤ bound.eval input) :
    ∃ (first second : Fin variables.length) (written : List Nat) (steps : Nat),
      selectedPair variables.length coordinate = some (first.val, second.val) ∧
      written.length = 7 ∧
      workRunExact? machine steps
        (workStartConfiguration machine
          (BuilderExclusionPairLookup.finalConfiguration variables.length coordinate
            (older ++ payloadValues variables) inside).tape) =
        some {
          state := machine.acceptState
          tape := endTape (lookupValues variables coordinate older ++ written ++ [variables[first.val].val]) inside [] } ∧
      (registerWord (lookupValues variables coordinate older ++ written ++ [variables[first.val].val])).length ≤
        (spanPolynomial bound).eval input ∧
      6 * steps ≤ (rawTimePolynomial bound).eval input := by
  rcases source_layout variables coordinate older hValid with
    ⟨first, second, environment, history, hPair, hFirst, _, _, hHistory, hLayout⟩
  have hField : firstIndex environment < (BuilderLocalConstraintPayload.variableValues variables).length := by
    simpa only [hFirst, BuilderLocalConstraintPayload.variableValues, List.length_map] using first.isLt
  have hValue : (BuilderLocalConstraintPayload.variableValues variables)[firstIndex environment] = variables[first.val].val := by
    simp only [BuilderLocalConstraintPayload.variableValues, List.getElem_map, hFirst]
  have hRun := workRunExact (BuilderLocalConstraintPayload.variableValues variables) older history environment inside [] hHistory hField
  have hBound := source_polynomial_bounds (BuilderLocalConstraintPayload.variableValues variables) older history environment
    [] bound input hHistory hField (by simpa only [← hLayout, List.length_nil, Nat.add_zero] using hSpan)
  rw [hValue] at hRun hBound
  refine ⟨first, second, scratch environment,
    workSteps (BuilderLocalConstraintPayload.variableValues variables) history environment variables[first.val].val,
    hPair, scratch_length environment, ?_, ?_, hBound.2⟩
  · simpa only [initialConfiguration, finalConfiguration, finalValues, ← hLayout,
      BuilderExclusionPairLookup.final_tape, lookupValues, List.drop_nil] using hRun
  · simpa only [finalValues, ← hLayout, List.drop_nil, List.length_nil, Nat.add_zero] using hBound.1

def lookupMachine : WorkMachine := WorkMachineChain.machine BuilderExclusionPairLookup.machine machine
def completeSpanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  spanPolynomial (BuilderExclusionPairLookup.spanPolynomial bound)
def completeRawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.add (BuilderExclusionPairLookup.rawTimePolynomial bound) (.constant 6))
    (rawTimePolynomial (BuilderExclusionPairLookup.spanPolynomial bound))

/-- Complete count/ordinal lookup followed by the physical read, with original-source polynomial bounds. -/
theorem uniform_source_lookup {width : Nat} (variables : List (Fin width)) (coordinate : Nat)
    (older : List Nat) (inside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hValid : coordinate < LocalConstraint.pairCount variables.length)
    (hSpan : (registerWord (older ++ payloadValues variables ++ [variables.length, coordinate])).length ≤ bound.eval input) :
    ∃ (first second : Fin variables.length) (written : List Nat) (steps : Nat),
      selectedPair variables.length coordinate = some (first.val, second.val) ∧
      written.length = 7 ∧
      run (compileWorkMachine lookupMachine) (6 * steps)
        (encodeWorkConfiguration (workStartConfiguration lookupMachine
          (endTape (older ++ payloadValues variables ++ [variables.length, coordinate]) inside []))) =
        encodeWorkConfiguration {
          state := lookupMachine.acceptState
          tape := endTape (lookupValues variables coordinate older ++ written ++ [variables[first.val].val]) inside [] } ∧
      (registerWord (lookupValues variables coordinate older ++ written ++ [variables[first.val].val])).length ≤
        (completeSpanPolynomial bound).eval input ∧
      6 * steps ≤ (completeRawTimePolynomial bound).eval input := by
  have hLookupBounds := BuilderExclusionPairLookup.source_polynomial_bounds variables.length coordinate
    (older ++ payloadValues variables) bound input hSpan
  rcases source_read variables coordinate older inside (BuilderExclusionPairLookup.spanPolynomial bound) input
    hValid hLookupBounds.1 with ⟨first, second, written, readSteps, hPair, hWritten, hRead, hSpace, hTime⟩
  have hRun := BuilderExclusionPairLookup.workRunExact variables.length coordinate (older ++ payloadValues variables) inside
  have hState := (BuilderExclusionPairLookup.final_accept_iff variables.length coordinate
    (older ++ payloadValues variables) inside).mpr hValid
  have hFields : BuilderExclusionPairLookup.finalConfiguration variables.length coordinate
      (older ++ payloadValues variables) inside =
      {
        state := BuilderExclusionPairLookup.machine.acceptState
        tape := (BuilderExclusionPairLookup.finalConfiguration variables.length coordinate
          (older ++ payloadValues variables) inside).tape} := by
    cases hConfig : BuilderExclusionPairLookup.finalConfiguration variables.length coordinate
      (older ++ payloadValues variables) inside with
    | mk state tape =>
        simp only [hConfig] at hState ⊢
        cases hState
        rfl
  rw [hFields] at hRun
  have hChain := chain_run _ _ _ _ _ _ _ hRun hRead
  refine ⟨first, second, written, BuilderExclusionPairLookup.workSteps variables.length coordinate + 1 + readSteps,
    hPair, hWritten, ?_, hSpace, ?_⟩
  · exact run_compileWorkMachine_mul_of_workRunExact _ _ _ _ hChain
  · have hLookupTime := hLookupBounds.2
    simp only [completeRawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

end PNP.Concrete.CookLevin.BuilderExclusionPairFirstVariable
