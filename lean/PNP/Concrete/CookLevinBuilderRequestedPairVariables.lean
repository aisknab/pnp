/-
Copyright (c) 2026 PNP Labs.

Read both exclusion variables from the actual source/request after pair-index
selection. The retained request has one fixed schema; its registers are
included in both runtime-computed field addresses. The expression, comparison,
indexer and pair-selection kernels are reused unchanged.

The complete source path derives the pair and its payload fields internally.
Blank-equivalent execution preserves the actual scratch exterior, while a
separate real-transition bound controls its materialized work-tape window.
The caller still supplies the positive-clause and blank-exterior input
invariants. Outer dispatch, token emission, recovery and the full builder
remain separate obligations; this is not an earned builder milestone.
-/
import PNP.Concrete.CookLevinBuilderRequestedPairLookup
import PNP.Concrete.CookLevinBuilderPayloadFieldCopy

namespace PNP.Concrete.CookLevin.BuilderRequestedPairVariables.First

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderExclusionPairSelection (rowSelection reverseCoordinate reversePair selectedPair)
open BuilderRegisterExpression (Expr)

def requestLength : Nat := 11

def firstIndex (environment : Fin 9 → Nat) : Nat := environment ⟨3, by decide⟩
def rowWidth (environment : Fin 9 → Nat) : Nat := environment ⟨7, by decide⟩
def rowOffset (environment : Fin 9 → Nat) : Nat := environment ⟨8, by decide⟩
def secondIndex (environment : Fin 9 → Nat) : Nat := firstIndex environment + rowWidth environment - rowOffset environment

/-- The retained request extends the canonical pair-reader address by its fixed schema length. -/
def expression : Expr 9 :=
  .binary .add
    (.binary .add (.binary .mul (.constant 9) (.argument ⟨7, by decide⟩))
      (.argument ⟨3, by decide⟩))
    (.constant (33 + requestLength))

def address (environment : Fin 9 → Nat) : Nat :=
  9 * rowWidth environment + firstIndex environment + (33 + requestLength)

def scratchPrefix (environment : Fin 9 → Nat) : List Nat :=
  [9, rowWidth environment, 9 * rowWidth environment, firstIndex environment,
    9 * rowWidth environment + firstIndex environment, (33 + requestLength)]
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
    (hHistory : history.length = (18 + requestLength) + 9 * rowWidth environment)
    (hField : firstIndex environment < payload.length) :
    address environment < (reader payload history environment).length := by
  simp only [address, reader, scratchPrefix, List.length_append, List.length_reverse,
    List.length_ofFn, List.length_cons, List.length_nil, hHistory]
  omega

theorem reader_address_value (payload history : List Nat) (environment : Fin 9 → Nat)
    (hHistory : history.length = (18 + requestLength) + 9 * rowWidth environment)
    (hField : firstIndex environment < payload.length) :
    (reader payload history environment)[address environment]'
      (reader_address_lt payload history environment hHistory hField) = payload[firstIndex environment] := by
  have hNear : ((scratchPrefix environment).reverse ++ (List.ofFn environment).reverse ++ history.reverse).length =
      (33 + requestLength) + 9 * rowWidth environment := by
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
    (inside outside : List WorkSymbol) (hHistory : history.length = (18 + requestLength) + 9 * rowWidth environment)
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
    (inside outside : List WorkSymbol) (hHistory : history.length = (18 + requestLength) + 9 * rowWidth environment)
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
    (hHistory : history.length = (18 + requestLength) + 9 * rowWidth environment)
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

end PNP.Concrete.CookLevin.BuilderRequestedPairVariables.First

namespace PNP.Concrete.CookLevin.BuilderRequestedPairVariables.Second

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderArbitrarySlotHeaderRouter
open BuilderRequestedPairVariables.First (firstIndex secondIndex rowWidth rowOffset)
open BuilderRegisterExpression (Expr)
open WorkMachineProgramGraph (Node Graph Endpoint)
open WorkMachineProgramPath (AcceptPath)

/-- The first reader leaves seven expression registers and its copied source value. -/
def firstHistory (environment : Fin 9 → Nat) (firstValue : Nat) : List Nat :=
  BuilderRequestedPairVariables.First.scratch environment ++ [firstValue]

def upperExpression : Expr 9 :=
  .binary .add
    (.binary .add (.binary .mul (.constant 10) (.argument ⟨7, by decide⟩))
      (.argument ⟨3, by decide⟩))
    (.constant (45 + BuilderRequestedPairVariables.First.requestLength))
def offsetExpression : Expr 9 := .argument ⟨8, by decide⟩
def upper (environment : Fin 9 → Nat) : Nat := 10 * rowWidth environment + firstIndex environment + (45 + BuilderRequestedPairVariables.First.requestLength)
def upperPrefix (environment : Fin 9 → Nat) : List Nat :=
  [10, rowWidth environment, 10 * rowWidth environment, firstIndex environment,
    10 * rowWidth environment + firstIndex environment, (45 + BuilderRequestedPairVariables.First.requestLength)]
def upperScratch (environment : Fin 9 → Nat) : List Nat := upperPrefix environment ++ [upper environment]
def comparisonResult (environment : Fin 9 → Nat) : RawRouter.ComparisonResult :=
  RawRouter.compareResult 0 (upper environment) (rowOffset environment)
def address (environment : Fin 9 → Nat) : Nat := 9 * rowWidth environment + secondIndex environment + (45 + BuilderRequestedPairVariables.First.requestLength)
def comparisonPrefix (environment : Fin 9 → Nat) : List Nat :=
  BuilderRegisterLessThan.resultValues (comparisonResult environment) ++ [rowOffset environment]
def scratchPrefix (environment : Fin 9 → Nat) : List Nat := upperPrefix environment ++ comparisonPrefix environment
def scratch (environment : Fin 9 → Nat) : List Nat := scratchPrefix environment ++ [address environment]

theorem firstHistory_length (environment : Fin 9 → Nat) (firstValue : Nat) :
    (firstHistory environment firstValue).length = 8 := by
  rw [firstHistory, List.length_append, BuilderRequestedPairVariables.First.scratch_length]
  rfl
theorem upper_values (environment : Fin 9 → Nat) :
    BuilderRegisterExpression.values upperExpression environment = upperScratch environment := rfl
theorem upper_nodeCount : BuilderRegisterExpression.nodeCount upperExpression = 7 := rfl
theorem upperScratch_length (environment : Fin 9 → Nat) : (upperScratch environment).length = 7 := rfl
theorem offset_values (environment : Fin 9 → Nat) :
    BuilderRegisterExpression.values offsetExpression environment = [rowOffset environment] := rfl
theorem scratchPrefix_length (environment : Fin 9 → Nat) : (scratchPrefix environment).length = 10 := by
  simp only [scratchPrefix, upperPrefix, comparisonPrefix, List.length_append,
    BuilderRegisterLessThan.resultValues_length, List.length_cons, List.length_nil]
theorem scratch_length (environment : Fin 9 → Nat) : (scratch environment).length = 11 := by
  rw [scratch, List.length_append, scratchPrefix_length]
  rfl

theorem upper_not_less (environment : Fin 9 → Nat) (hOffset : rowOffset environment < rowWidth environment) :
    rowOffset environment ≤ upper environment := by
  unfold upper
  omega

theorem residual_eq_address (environment : Fin 9 → Nat) (hOffset : rowOffset environment < rowWidth environment) :
    BuilderRegisterCompareResidual.resultCoordinate (comparisonResult environment) = address environment := by
  have hNotLess : ¬ upper environment < rowOffset environment := Nat.not_lt.mpr (upper_not_less environment hOffset)
  rw [comparisonResult, BuilderRegisterCompareResidual.resultCoordinate_eq, if_neg hNotLess]
  unfold upper address secondIndex
  omega

theorem comparison_values (environment : Fin 9 → Nat) (hOffset : rowOffset environment < rowWidth environment) :
    BuilderRegisterCompareResidual.outputValues (comparisonResult environment) =
      comparisonPrefix environment ++ [address environment] := by
  have hBoundary : BuilderRegisterCompareResidual.resultBoundary (comparisonResult environment) = rowOffset environment :=
    BuilderRegisterCompareResidual.resultBoundary_eq _ _
  simp only [BuilderRegisterCompareResidual.outputValues, hBoundary, residual_eq_address environment hOffset,
    comparisonPrefix, List.append_assoc, List.cons_append, List.nil_append]

def initialValues (payload older history : List Nat) (environment : Fin 9 → Nat) (firstValue : Nat) : List Nat :=
  BuilderRequestedPairVariables.First.initialValues payload older history environment ++ firstHistory environment firstValue
def preparedValues (payload older history : List Nat) (environment : Fin 9 → Nat) (firstValue : Nat) : List Nat :=
  initialValues payload older history environment firstValue ++ upperPrefix environment ++ [upper environment, rowOffset environment]
def finalValues (payload older history : List Nat) (environment : Fin 9 → Nat) (firstValue secondValue : Nat) : List Nat :=
  initialValues payload older history environment firstValue ++ scratch environment ++ [secondValue]

theorem after_first_values (payload older history : List Nat) (environment : Fin 9 → Nat) (firstValue : Nat) :
    initialValues payload older history environment firstValue =
      BuilderRequestedPairVariables.First.finalValues payload older history environment firstValue := by
  simp only [initialValues, firstHistory, BuilderRequestedPairVariables.First.finalValues, List.append_assoc]

def prepareMachine : WorkMachine :=
  WorkMachineChain.machine (BuilderRegisterExpression.machine upperExpression 8)
    (BuilderRegisterExpression.machine offsetExpression 15)
def prepareSteps (environment : Fin 9 → Nat) (firstValue : Nat) : Nat :=
  BuilderRegisterExpression.workSteps upperExpression environment (firstHistory environment firstValue) + 1 +
    BuilderRegisterExpression.workSteps offsetExpression environment (firstHistory environment firstValue ++ upperScratch environment)

private theorem chain_run (first second : WorkMachine) (n m : Nat) (initial middle final : WorkTape)
    (hFirst : workRunExact? first n (workStartConfiguration first initial) =
      some {state := first.acceptState, tape := middle})
    (hSecond : workRunExact? second m (workStartConfiguration second middle) =
      some {state := second.acceptState, tape := final}) :
    workRunExact? (WorkMachineChain.machine first second) (n + 1 + m)
      (workStartConfiguration (WorkMachineChain.machine first second) initial) =
      some {state := (WorkMachineChain.machine first second).acceptState, tape := final} :=
  WorkMachineChain.workRunExact first second n m _ _ _ hFirst rfl hSecond

theorem prepare_workRunExact (payload older history : List Nat) (environment : Fin 9 → Nat)
    (firstValue : Nat) (inside : List WorkSymbol) :
    workRunExact? prepareMachine (prepareSteps environment firstValue)
      (workStartConfiguration prepareMachine (endTape (initialValues payload older history environment firstValue) inside [])) =
      some {
        state := prepareMachine.acceptState
        tape := endTape (preparedValues payload older history environment firstValue) inside [] } := by
  have hUpper := BuilderRegisterExpression.workRunExact upperExpression 8
    (older ++ payload.reverse ++ history) environment (firstHistory environment firstValue) inside []
    (firstHistory_length environment firstValue)
  have hAfter : (firstHistory environment firstValue ++ upperScratch environment).length = 15 := by
    rw [List.length_append, firstHistory_length, upperScratch_length]
  have hOffset := BuilderRegisterExpression.workRunExact offsetExpression 15
    (older ++ payload.reverse ++ history) environment
    (firstHistory environment firstValue ++ upperScratch environment) inside [] hAfter
  have hFirst : workRunExact? (BuilderRegisterExpression.machine upperExpression 8)
      (BuilderRegisterExpression.workSteps upperExpression environment (firstHistory environment firstValue))
      (workStartConfiguration (BuilderRegisterExpression.machine upperExpression 8)
        (endTape (initialValues payload older history environment firstValue) inside [])) =
      some {
        state := (BuilderRegisterExpression.machine upperExpression 8).acceptState
        tape := endTape (initialValues payload older history environment firstValue ++ upperScratch environment) inside [] } := by
    simpa only [BuilderRegisterExpression.initialConfiguration, BuilderRegisterExpression.finalConfiguration,
      upper_values, initialValues, BuilderRequestedPairVariables.First.initialValues, List.drop_nil] using hUpper
  have hSecond : workRunExact? (BuilderRegisterExpression.machine offsetExpression 15)
      (BuilderRegisterExpression.workSteps offsetExpression environment (firstHistory environment firstValue ++ upperScratch environment))
      (workStartConfiguration (BuilderRegisterExpression.machine offsetExpression 15)
        (endTape (initialValues payload older history environment firstValue ++ upperScratch environment) inside [])) =
      some {
        state := (BuilderRegisterExpression.machine offsetExpression 15).acceptState
        tape := endTape (preparedValues payload older history environment firstValue) inside [] } := by
    simpa only [BuilderRegisterExpression.initialConfiguration, BuilderRegisterExpression.finalConfiguration,
      offset_values, preparedValues, initialValues, BuilderRequestedPairVariables.First.initialValues,
      upperScratch, List.drop_nil, List.append_assoc, List.cons_append, List.nil_append] using hOffset
  exact chain_run _ _ _ _ _ _ _ hFirst hSecond

def reader (payload history : List Nat) (environment : Fin 9 → Nat) (firstValue : Nat) : List Nat :=
  (scratchPrefix environment).reverse ++ (firstHistory environment firstValue).reverse ++
    (List.ofFn environment).reverse ++ history.reverse ++ payload

theorem reader_address_lt (payload history : List Nat) (environment : Fin 9 → Nat) (firstValue : Nat)
    (hHistory : history.length = (18 + BuilderRequestedPairVariables.First.requestLength) + 9 * rowWidth environment)
    (hField : secondIndex environment < payload.length) :
    address environment < (reader payload history environment firstValue).length := by
  simp only [address, reader, List.length_append, List.length_reverse, scratchPrefix_length, firstHistory_length,
    List.length_ofFn, hHistory]
  omega

theorem reader_address_value (payload history : List Nat) (environment : Fin 9 → Nat) (firstValue : Nat)
    (hHistory : history.length = (18 + BuilderRequestedPairVariables.First.requestLength) + 9 * rowWidth environment)
    (hField : secondIndex environment < payload.length) :
    (reader payload history environment firstValue)[address environment]'
      (reader_address_lt payload history environment firstValue hHistory hField) = payload[secondIndex environment] := by
  have hNear : ((scratchPrefix environment).reverse ++ (firstHistory environment firstValue).reverse ++
      (List.ofFn environment).reverse ++ history.reverse).length = (45 + BuilderRequestedPairVariables.First.requestLength) + 9 * rowWidth environment := by
    simp only [List.length_append, List.length_reverse, scratchPrefix_length, firstHistory_length,
      List.length_ofFn, hHistory]
    omega
  unfold reader
  rw [List.getElem_append_right (by simp only [hNear, address]; omega)]
  congr 1
  simp only [hNear, address]
  omega

theorem reader_layout (payload older history : List Nat) (environment : Fin 9 → Nat) (firstValue : Nat) :
    older ++ (reader payload history environment firstValue).reverse ++ [address environment] =
      initialValues payload older history environment firstValue ++ scratch environment := by
  simp only [reader, initialValues, BuilderRequestedPairVariables.First.initialValues, scratch,
    List.reverse_append, List.reverse_reverse, List.append_assoc]

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineProgramGraph.QueryDistinct ∧
    WorkMachineProgramGraph.NoRuleAt program program.acceptState ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧
    program.acceptState ≠ program.rejectState
private theorem chain_good (first second : WorkMachine) (hFirst : Good first) (hSecond : Good second) :
    Good (WorkMachineChain.machine first second) :=
  ⟨WorkMachineChain.rules_pairwise_query_distinct _ _ hFirst.1 hSecond.1 hFirst.2.1,
    WorkMachineChain.noRuleAtAccept _ _ hSecond.2.1,
    WorkMachineChain.noRuleAtAccept first {second with acceptState := second.rejectState} hSecond.2.2.1,
    WorkMachineChain.machine_acceptState_ne_rejectState _ _ hSecond.2.2.2⟩
private theorem expression_good (expression : Expr 9) (afterCount : Nat) : Good (BuilderRegisterExpression.machine expression afterCount) :=
  ⟨BuilderRegisterExpression.rules_pairwise_query_distinct expression afterCount,
    BuilderRegisterExpression.noRuleAtAccept expression afterCount,
    BuilderRegisterExpression.noRuleAtReject expression afterCount,
    BuilderRegisterExpression.acceptState_ne_rejectState expression afterCount⟩
private theorem prepare_good : Good prepareMachine :=
  chain_good _ _ (expression_good upperExpression 8) (expression_good offsetExpression 15)

def copyNode : Node := {name := 2, program := BuilderRegisterIndexedCopy.machine, onAccept := .accept, onReject := .dead}
def compareNode : Node :=
  {name := 1, program := BuilderRegisterCompareResidual.machine, onAccept := .dead, onReject := .node copyNode.reference}
def prepareNode : Node := {name := 0, program := prepareMachine, onAccept := .node compareNode.reference, onReject := .dead}
def graph : Graph := {nodes := [prepareNode, compareNode, copyNode], entry := prepareNode.reference}
def machine : WorkMachine := WorkMachineProgramGraph.machine graph

private theorem prepare_mem : prepareNode ∈ graph.nodes := List.Mem.head _
private theorem compare_mem : compareNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.head _)
private theorem copy_mem : copyNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

theorem graph_nodes_length : graph.nodes.length = 3 := rfl
theorem graph_wellFormed : graph.WellFormed := by
  have hNames : (graph.nodes.map Node.name).Pairwise (fun left right : Nat => left ≠ right) := by
    change ([0, 1, 2] : List Nat).Pairwise _
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.pairwise_map] using hNames
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl
    · exact prepare_good
    · exact ⟨BuilderRegisterCompareResidual.rules_pairwise_query_distinct,
        BuilderRegisterCompareResidual.noRuleAtAccept, BuilderRegisterCompareResidual.noRuleAtReject,
        BuilderRegisterCompareResidual.acceptState_ne_rejectState⟩
    · exact ⟨BuilderRegisterIndexedCopy.rules_pairwise_query_distinct,
        BuilderRegisterIndexedCopy.noRuleAtAccept, BuilderRegisterIndexedCopy.noRuleAtReject,
        BuilderRegisterIndexedCopy.acceptState_ne_rejectState⟩
  · exact ⟨prepareNode, prepare_mem, rfl, rfl⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl
    · exact ⟨⟨compareNode, compare_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, ⟨copyNode, copy_mem, rfl, rfl⟩⟩
    · exact ⟨True.intro, True.intro⟩

def workSteps (payload history : List Nat) (environment : Fin 9 → Nat) (firstValue secondValue : Nat) : Nat :=
  prepareSteps environment firstValue + 1 +
    (BuilderRegisterCompareResidual.workSteps (upper environment) (rowOffset environment) + 1 +
      (BuilderRegisterIndexedCopy.workSteps ((reader payload history environment firstValue).take (address environment)) secondValue + 1))
def initialConfiguration (payload older history : List Nat) (environment : Fin 9 → Nat) (firstValue : Nat)
    (inside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration machine (endTape (initialValues payload older history environment firstValue) inside [])
def finalConfiguration (payload older history : List Nat) (environment : Fin 9 → Nat) (firstValue secondValue : Nat)
    (inside : List WorkSymbol) : WorkConfiguration :=
  { state := machine.acceptState
    tape := endTape (finalValues payload older history environment firstValue secondValue) inside [] }

private theorem configuration_eq_of_fields (config : WorkConfiguration) (state : Nat) (tape : WorkTape)
    (hState : config.state = state) (hTape : config.tape = tape) : config = {state := state, tape := tape} := by
  cases config
  cases hState
  cases hTape
  rfl

private theorem start_configuration (tape : WorkTape) :
    WorkMachineProgramGraph.endpointConfiguration (.node prepareNode.reference) tape =
      workStartConfiguration machine tape := rfl
private theorem accept_configuration (tape : WorkTape) :
    WorkMachineProgramGraph.endpointConfiguration .accept tape = {state := machine.acceptState, tape := tape} := rfl

theorem workRunExact (payload older history : List Nat) (environment : Fin 9 → Nat)
    (firstValue : Nat) (inside : List WorkSymbol)
    (hHistory : history.length = (18 + BuilderRequestedPairVariables.First.requestLength) + 9 * rowWidth environment)
    (hOffset : rowOffset environment < rowWidth environment) (hField : secondIndex environment < payload.length) :
    workRunExact? machine (workSteps payload history environment firstValue payload[secondIndex environment])
      (initialConfiguration payload older history environment firstValue inside) =
      some (finalConfiguration payload older history environment firstValue payload[secondIndex environment] inside) := by
  have hPrepare := prepare_workRunExact payload older history environment firstValue inside
  have hCompare := BuilderRegisterCompareResidual.workRunExact (upper environment) (rowOffset environment)
    (initialValues payload older history environment firstValue ++ upperPrefix environment) inside []
  have hState := (BuilderRegisterCompareResidual.final_reject_iff (upper environment) (rowOffset environment)
    (initialValues payload older history environment firstValue ++ upperPrefix environment) inside []).mpr
      (upper_not_less environment hOffset)
  have hTape : (BuilderRegisterCompareResidual.finalConfiguration (upper environment) (rowOffset environment)
      (initialValues payload older history environment firstValue ++ upperPrefix environment) inside []).tape =
      endTape (initialValues payload older history environment firstValue ++ scratch environment) inside [] := by
    change endTape ((initialValues payload older history environment firstValue ++ upperPrefix environment) ++
      BuilderRegisterCompareResidual.outputValues (comparisonResult environment)) inside
      (([] : List WorkSymbol).drop (BuilderRegisterCompareResidual.allocatedCells (comparisonResult environment))) = _
    rw [comparison_values environment hOffset]
    simp only [scratch, scratchPrefix, List.append_assoc, List.drop_nil]
  rw [configuration_eq_of_fields _ _ _ hState hTape] at hCompare
  have hCopy := BuilderRegisterIndexedCopy.workRun_select_getElem
    (reader payload history environment firstValue) older
    ⟨address environment, reader_address_lt payload history environment firstValue hHistory hField⟩ inside []
  simp only [reader_address_value payload history environment firstValue hHistory hField] at hCopy
  have hEnd : older ++ (reader payload history environment firstValue).reverse ++
      [address environment, payload[secondIndex environment]] =
      finalValues payload older history environment firstValue payload[secondIndex environment] := by
    rw [show [address environment, payload[secondIndex environment]] =
      [address environment] ++ [payload[secondIndex environment]] from rfl, ← List.append_assoc, reader_layout]
    rfl
  simp only [reader_layout, hEnd, List.drop_nil] at hCopy
  have hC := AcceptPath.step copyNode .accept _ 0 _ _ _ copy_mem hCopy (.terminal .accept _)
  have hR := AcceptPath.stepReject compareNode .accept _ _ _ _ _ compare_mem hCompare hC
  have hP := AcceptPath.step prepareNode .accept _ _ _ _ _ prepare_mem hPrepare hR
  have hRun := WorkMachineProgramPath.runExact graph _ _ _ _ _ graph_wellFormed hP
  rw [start_configuration, accept_configuration] at hRun
  simpa only [initialConfiguration, finalConfiguration, workSteps, machine, Nat.add_zero] using hRun

theorem run_compile_exact (payload older history : List Nat) (environment : Fin 9 → Nat)
    (firstValue : Nat) (inside : List WorkSymbol)
    (hHistory : history.length = (18 + BuilderRequestedPairVariables.First.requestLength) + 9 * rowWidth environment)
    (hOffset : rowOffset environment < rowWidth environment) (hField : secondIndex environment < payload.length) :
    run (compileWorkMachine machine) (6 * workSteps payload history environment firstValue payload[secondIndex environment])
      (encodeWorkConfiguration (initialConfiguration payload older history environment firstValue inside)) =
      encodeWorkConfiguration (finalConfiguration payload older history environment firstValue payload[secondIndex environment] inside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _
    (workRunExact payload older history environment firstValue inside hHistory hOffset hField)

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise graph graph_wellFormed
theorem noRuleAtAccept : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState :=
  WorkMachineProgramGraph.noRuleAt_globalAccept graph
theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  WorkMachineProgramGraph.noRuleAt_globalReject graph
theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := by
  change (0 : Nat) ≠ 1
  decide

def upperSpanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterExpression.spanPolynomial upperExpression bound
def preparedSpanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterExpression.spanPolynomial offsetExpression (upperSpanPolynomial bound)
def preparedRawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.add (BuilderRegisterExpression.rawTimePolynomial upperExpression bound) (.constant 6))
    (BuilderRegisterExpression.rawTimePolynomial offsetExpression (upperSpanPolynomial bound))
def comparisonSpanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterCompareResidual.spanPolynomial (preparedSpanPolynomial bound)
def spanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterIndexedCopy.spanPolynomial (comparisonSpanPolynomial bound)
def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (preparedRawTimePolynomial bound)
    (.add (BuilderRegisterCompareResidual.rawTimePolynomial (preparedSpanPolynomial bound))
      (.add (BuilderRegisterIndexedCopy.rawTimePolynomial (comparisonSpanPolynomial bound)) (.constant 18)))

theorem prepare_polynomial_bounds (payload older history : List Nat) (environment : Fin 9 → Nat) (firstValue : Nat)
    (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues payload older history environment firstValue)).length ≤ bound.eval input) :
    (registerWord (preparedValues payload older history environment firstValue)).length ≤
      (preparedSpanPolynomial bound).eval input ∧
    6 * prepareSteps environment firstValue ≤ (preparedRawTimePolynomial bound).eval input := by
  have hUpper := BuilderRegisterExpression.source_polynomial_bounds upperExpression bound input
    (older ++ payload.reverse ++ history) environment (firstHistory environment firstValue) hSpan
  simp only [upper_values] at hUpper
  have hMiddle : (registerWord ((older ++ payload.reverse ++ history) ++ List.ofFn environment ++
      (firstHistory environment firstValue ++ upperScratch environment))).length ≤ (upperSpanPolynomial bound).eval input := by
    simpa only [upperSpanPolynomial, List.append_assoc] using hUpper.1
  have hOffset := BuilderRegisterExpression.source_polynomial_bounds offsetExpression (upperSpanPolynomial bound) input
    (older ++ payload.reverse ++ history) environment
    (firstHistory environment firstValue ++ upperScratch environment) hMiddle
  constructor
  · simpa only [offset_values, preparedSpanPolynomial, preparedValues, initialValues,
      BuilderRequestedPairVariables.First.initialValues, upperScratch, List.append_assoc,
      List.cons_append, List.nil_append] using hOffset.1
  · have hUpperTime := hUpper.2
    have hOffsetTime := hOffset.2
    simp only [prepareSteps, preparedRawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

theorem source_polynomial_bounds (payload older history : List Nat) (environment : Fin 9 → Nat)
    (firstValue : Nat) (bound : NatPolynomial) (input : Nat)
    (hHistory : history.length = (18 + BuilderRequestedPairVariables.First.requestLength) + 9 * rowWidth environment)
    (hOffset : rowOffset environment < rowWidth environment) (hField : secondIndex environment < payload.length)
    (hSpan : (registerWord (initialValues payload older history environment firstValue)).length ≤ bound.eval input) :
    (registerWord (finalValues payload older history environment firstValue payload[secondIndex environment])).length ≤
      (spanPolynomial bound).eval input ∧
    6 * workSteps payload history environment firstValue payload[secondIndex environment] ≤ (rawTimePolynomial bound).eval input := by
  have hPrepare := prepare_polynomial_bounds payload older history environment firstValue bound input hSpan
  have hCompare := BuilderRegisterCompareResidual.source_polynomial_bounds (upper environment) (rowOffset environment)
    (initialValues payload older history environment firstValue ++ upperPrefix environment)
    (preparedSpanPolynomial bound) input hPrepare.1
  have hValues := comparison_values environment hOffset
  unfold comparisonResult at hValues
  have hMiddle : (registerWord (initialValues payload older history environment firstValue ++ scratch environment)).length ≤
      (comparisonSpanPolynomial bound).eval input := by
    simpa only [hValues, comparisonSpanPolynomial, scratch, scratchPrefix,
      List.append_assoc] using hCompare.1
  have hCopy := BuilderRegisterIndexedCopy.selected_source_polynomial_bounds
    (reader payload history environment firstValue) older
    ⟨address environment, reader_address_lt payload history environment firstValue hHistory hField⟩
    [] (comparisonSpanPolynomial bound) input
    (by simpa only [reader_layout, List.length_nil, Nat.add_zero] using hMiddle)
  simp only [reader_address_value payload history environment firstValue hHistory hField] at hCopy
  have hEnd : older ++ (reader payload history environment firstValue).reverse ++
      [address environment, payload[secondIndex environment]] =
      finalValues payload older history environment firstValue payload[secondIndex environment] := by
    rw [show [address environment, payload[secondIndex environment]] =
      [address environment] ++ [payload[secondIndex environment]] from rfl, ← List.append_assoc, reader_layout]
    rfl
  constructor
  · simpa only [hEnd, List.drop_nil, List.length_nil, Nat.add_zero, spanPolynomial] using hCopy.1
  · have hPrepareTime := hPrepare.2
    have hCompareTime := hCompare.2
    have hCopyTime := hCopy.2
    simp only [workSteps, rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

def pairMachine : WorkMachine := WorkMachineChain.machine BuilderRequestedPairVariables.First.machine machine
def pairSteps (payload history : List Nat) (environment : Fin 9 → Nat) (firstValue secondValue : Nat) : Nat :=
  BuilderRequestedPairVariables.First.workSteps payload history environment firstValue + 1 +
    workSteps payload history environment firstValue secondValue
def pairSpanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  spanPolynomial (BuilderRequestedPairVariables.First.spanPolynomial bound)
def pairRawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.add (BuilderRequestedPairVariables.First.rawTimePolynomial bound) (.constant 6))
    (rawTimePolynomial (BuilderRequestedPairVariables.First.spanPolynomial bound))

theorem pair_workRunExact (payload older history : List Nat) (environment : Fin 9 → Nat) (inside : List WorkSymbol)
    (hHistory : history.length = (18 + BuilderRequestedPairVariables.First.requestLength) + 9 * rowWidth environment)
    (hOffset : rowOffset environment < rowWidth environment)
    (hFirst : firstIndex environment < payload.length) (hSecond : secondIndex environment < payload.length) :
    workRunExact? pairMachine (pairSteps payload history environment payload[firstIndex environment] payload[secondIndex environment])
      (workStartConfiguration pairMachine
        (endTape (BuilderRequestedPairVariables.First.initialValues payload older history environment) inside [])) =
      some {
        state := pairMachine.acceptState
        tape := endTape (finalValues payload older history environment payload[firstIndex environment] payload[secondIndex environment]) inside [] } := by
  have hReadFirst := BuilderRequestedPairVariables.First.workRunExact payload older history environment inside [] hHistory hFirst
  simp only [BuilderRequestedPairVariables.First.initialConfiguration, BuilderRequestedPairVariables.First.finalConfiguration,
    ← after_first_values, List.drop_nil] at hReadFirst
  have hReadSecond := workRunExact payload older history environment payload[firstIndex environment] inside hHistory hOffset hSecond
  exact chain_run _ _ _ _ _ _ _ hReadFirst hReadSecond

theorem pair_polynomial_bounds (payload older history : List Nat) (environment : Fin 9 → Nat)
    (bound : NatPolynomial) (input : Nat)
    (hHistory : history.length = (18 + BuilderRequestedPairVariables.First.requestLength) + 9 * rowWidth environment)
    (hOffset : rowOffset environment < rowWidth environment)
    (hFirst : firstIndex environment < payload.length) (hSecond : secondIndex environment < payload.length)
    (hSpan : (registerWord (BuilderRequestedPairVariables.First.initialValues payload older history environment)).length ≤ bound.eval input) :
    (registerWord (finalValues payload older history environment payload[firstIndex environment] payload[secondIndex environment])).length ≤
      (pairSpanPolynomial bound).eval input ∧
    6 * pairSteps payload history environment payload[firstIndex environment] payload[secondIndex environment] ≤
      (pairRawTimePolynomial bound).eval input := by
  have hReadFirst := BuilderRequestedPairVariables.First.source_polynomial_bounds payload older history environment []
    bound input hHistory hFirst (by simpa only [List.length_nil, Nat.add_zero] using hSpan)
  have hMiddle : (registerWord (initialValues payload older history environment payload[firstIndex environment])).length ≤
      (BuilderRequestedPairVariables.First.spanPolynomial bound).eval input := by
    simpa only [← after_first_values, List.drop_nil, List.length_nil, Nat.add_zero] using hReadFirst.1
  have hReadSecond := source_polynomial_bounds payload older history environment payload[firstIndex environment]
    (BuilderRequestedPairVariables.First.spanPolynomial bound) input hHistory hOffset hSecond hMiddle
  refine ⟨hReadSecond.1, ?_⟩
  have hFirstTime := hReadFirst.2
  have hSecondTime := hReadSecond.2
  simp only [pairSteps, pairRawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
  omega

private theorem pair_good : Good pairMachine :=
  chain_good _ _
    ⟨BuilderRequestedPairVariables.First.rules_pairwise_query_distinct,
      BuilderRequestedPairVariables.First.noRuleAtAccept, BuilderRequestedPairVariables.First.noRuleAtReject,
      BuilderRequestedPairVariables.First.acceptState_ne_rejectState⟩
    ⟨rules_pairwise_query_distinct, noRuleAtAccept, noRuleAtReject, acceptState_ne_rejectState⟩

theorem pair_rules_pairwise_query_distinct : pairMachine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  pair_good.1
theorem pair_noRuleAtAccept : WorkMachineProgramGraph.NoRuleAt pairMachine pairMachine.acceptState :=
  pair_good.2.1
theorem pair_noRuleAtReject : WorkMachineProgramGraph.NoRuleAt pairMachine pairMachine.rejectState :=
  pair_good.2.2.1
theorem pair_acceptState_ne_rejectState : pairMachine.acceptState ≠ pairMachine.rejectState :=
  pair_good.2.2.2

end PNP.Concrete.CookLevin.BuilderRequestedPairVariables.Second


namespace PNP.Concrete.CookLevin.BuilderRequestedPairVariables

open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape)
open BuilderPayloadSearchSource (Request requestValues)
open BuilderLocalConstraintPayload (variableValues)
open BuilderExclusionPairSelection (rowSelection reverseCoordinate reversePair selectedPair)
open First (firstIndex secondIndex rowWidth rowOffset)
open WorkMachineProgramGraph (Node Graph)
open WorkMachineProgramPath (AcceptPath)

def lookupValues {width : Nat} (variables : List (Fin width)) (request : Request) (older : List Nat) : List Nat :=
  BuilderExclusionPairLookup.resultValues variables.length (request.clauseIndex - 1)
    (BuilderRequestedPairLookup.initialValues variables request older)

theorem request_length (request : Request) :
    (request.gap ++ [request.clauseIndex, request.originalPosition]).length = First.requestLength := by
  simp only [List.length_append, List.length_cons, List.length_nil, request.gap_length, First.requestLength]

theorem input_layout {width : Nat} (variables : List (Fin width)) (request : Request) (older : List Nat) :
    BuilderRequestedPairLookup.initialValues variables request older =
      older ++ (variableValues variables).reverse ++ [variables.length, 4] ++ request.gap ++
        [request.clauseIndex, request.originalPosition] := by
  simp only [BuilderRequestedPairLookup.initialValues, requestValues, BuilderLocalConstraintPayload.values,
    BuilderLocalConstraintPayload.front, List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]

theorem canonical_tape {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (inside : List WorkSymbol) :
    (BuilderRequestedPairLookup.canonicalFinal variables request older inside).tape =
      endTape (lookupValues variables request older) inside [] := rfl

/-- Both indices, the terminal environment and the request-aware history are
derived from the complete row selection, not supplied by an external caller. -/
theorem source_layout {width : Nat} (variables : List (Fin width)) (request : Request) (older : List Nat)
    (hValid : request.clauseIndex - 1 < LocalConstraint.pairCount variables.length) :
    ∃ (first second : Fin variables.length) (environment : Fin 9 → Nat) (history : List Nat),
      selectedPair variables.length (request.clauseIndex - 1) = some (first.val, second.val) ∧
      firstIndex environment = first.val ∧ secondIndex environment = second.val ∧
      rowOffset environment < rowWidth environment ∧
      history.length = (18 + First.requestLength) + 9 * rowWidth environment ∧
      lookupValues variables request older = First.initialValues (variableValues variables) older history environment := by
  cases hFound : rowSelection variables.length (request.clauseIndex - 1) with
  | none =>
      have hInvalid := (BuilderExclusionPairSelection.rowSelection_none_iff variables.length (request.clauseIndex - 1)).mp hFound
      exfalso
      omega
  | some found =>
      rcases found with ⟨position, offset⟩
      have hSpec := BuilderExclusionPairSelection.rowSelection_pair_spec variables.length (request.clauseIndex - 1) position offset hFound
      have hBounds := BuilderInitialLengthSelection.locate_some_bounds
        (variables.length - 1) 1 (reverseCoordinate variables.length (request.clauseIndex - 1)) position offset hFound
      have hLess : offset < 1 + position.val := hBounds.1
      rcases BuilderExclusionPairRow.found_attempt (variables.length - 1) 0 1
        (reverseCoordinate variables.length (request.clauseIndex - 1)) position offset hFound with ⟨prior, hPrior, hFinish⟩
      let environment := BuilderInitialRowLoop.attemptEnvironment position.val (1 + position.val)
        offset (variables.length - 2 - position.val)
      let history := [variables.length, 4] ++ request.gap ++ [request.clauseIndex, request.originalPosition] ++
        BuilderExclusionPairPreparation.history variables.length (request.clauseIndex - 1) ++ prior
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
          request.gap_length, First.requestLength, BuilderExclusionPairPreparation.history_length,
          hPrior, rowWidth, environment, BuilderInitialRowLoop.attemptEnvironment,
          BuilderRegisterCompareResidual.resultBoundary_eq]
        omega
      · have hRemaining : variables.length - 1 - (position.val + 1) = variables.length - 2 - position.val := by omega
        simp only [lookupValues, BuilderExclusionPairLookup.resultValues, if_pos hValid,
          BuilderExclusionPairRow.resultValues, hFinish, Nat.zero_add, hRemaining,
          First.initialValues, history, environment, BuilderInitialRowLoop.attemptEnvironment_ofFn,
          input_layout, List.append_assoc]

/-- Exact reads of both actual payload variables from the canonical request-aware
pair frame. No history, row environment or chosen field values are supplied. -/
theorem canonical_source_read {width : Nat} (variables : List (Fin width)) (request : Request) (older : List Nat)
    (inside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hValid : request.clauseIndex - 1 < LocalConstraint.pairCount variables.length)
    (hSpan : (registerWord (lookupValues variables request older)).length ≤ bound.eval input) :
    ∃ (first second : Fin variables.length) (firstWritten secondWritten : List Nat) (steps : Nat),
      selectedPair variables.length (request.clauseIndex - 1) = some (first.val, second.val) ∧
      firstWritten.length = 7 ∧ secondWritten.length = 11 ∧
      workRunExact? Second.pairMachine steps
        (workStartConfiguration Second.pairMachine (endTape (lookupValues variables request older) inside [])) =
        some {
          state := Second.pairMachine.acceptState
          tape := endTape (lookupValues variables request older ++ firstWritten ++ [variables[first.val].val] ++
            secondWritten ++ [variables[second.val].val]) inside []
        } ∧
      (registerWord (lookupValues variables request older ++ firstWritten ++ [variables[first.val].val] ++
        secondWritten ++ [variables[second.val].val])).length ≤ (Second.pairSpanPolynomial bound).eval input ∧
      6 * steps ≤ (Second.pairRawTimePolynomial bound).eval input := by
  rcases source_layout variables request older hValid with
    ⟨first, second, environment, history, hPair, hFirst, hSecond, hOffset, hHistory, hLayout⟩
  have hFirstField : firstIndex environment < (variableValues variables).length := by
    simpa only [hFirst, variableValues, List.length_map] using first.isLt
  have hSecondField : secondIndex environment < (variableValues variables).length := by
    simpa only [hSecond, variableValues, List.length_map] using second.isLt
  have hFirstValue : (variableValues variables)[firstIndex environment] = variables[first.val].val := by
    simp only [variableValues, List.getElem_map, hFirst]
  have hSecondValue : (variableValues variables)[secondIndex environment] = variables[second.val].val := by
    simp only [variableValues, List.getElem_map, hSecond]
  have hRead := Second.pair_workRunExact (variableValues variables) older history environment inside
    hHistory hOffset hFirstField hSecondField
  have hBounds := Second.pair_polynomial_bounds (variableValues variables) older history environment bound input
    hHistory hOffset hFirstField hSecondField (by simpa only [← hLayout] using hSpan)
  rw [hFirstValue, hSecondValue] at hRead hBounds
  refine ⟨first, second, First.scratch environment, Second.scratch environment,
    Second.pairSteps (variableValues variables) history environment variables[first.val].val variables[second.val].val,
    hPair, First.scratch_length environment, Second.scratch_length environment, ?_, ?_, hBounds.2⟩
  · simpa only [Second.finalValues, Second.initialValues, Second.firstHistory, ← hLayout, List.append_assoc] using hRead
  · simpa only [Second.finalValues, Second.initialValues, Second.firstHistory, ← hLayout, List.append_assoc] using hBounds.1

def pairNode : Node := {name := 1, program := Second.pairMachine, onAccept := .accept, onReject := .dead}
def lookupNode : Node :=
  {name := 0, program := BuilderRequestedPairLookup.machine, onAccept := .node pairNode.reference, onReject := .reject}
def graph : Graph := {nodes := [lookupNode, pairNode], entry := lookupNode.reference}
def machine : WorkMachine := WorkMachineProgramGraph.machine graph
private theorem machine_projection : WorkMachineProgramGraph.machine graph = machine := rfl
private theorem lookup_mem : lookupNode ∈ graph.nodes := List.Mem.head _
private theorem pair_mem : pairNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.head _)

theorem graph_nodes_length : graph.nodes.length = 2 := rfl
theorem graph_wellFormed : graph.WellFormed := by
  have hNames : (graph.nodes.map Node.name).Pairwise (fun left right : Nat => left ≠ right) := by
    change ([0, 1] : List Nat).Pairwise _
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.pairwise_map] using hNames
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl
    · exact ⟨BuilderRequestedPairLookup.rules_pairwise_query_distinct,
        BuilderRequestedPairLookup.noRuleAtAccept, BuilderRequestedPairLookup.noRuleAtReject,
        BuilderRequestedPairLookup.acceptState_ne_rejectState⟩
    · exact ⟨Second.pair_rules_pairwise_query_distinct, Second.pair_noRuleAtAccept,
        Second.pair_noRuleAtReject, Second.pair_acceptState_ne_rejectState⟩
  · exact ⟨lookupNode, lookup_mem, rfl, rfl⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl
    · exact ⟨⟨pairNode, pair_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, True.intro⟩

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise graph graph_wellFormed
theorem noRuleAtAccept : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState :=
  WorkMachineProgramGraph.noRuleAt_globalAccept graph
theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  WorkMachineProgramGraph.noRuleAt_globalReject graph
theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := by
  change (0 : Nat) ≠ 1
  decide

def canonicalSpanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  BuilderExclusionPairLookup.spanPolynomial (BuilderPayloadBodyPreparation.spanPolynomial bound)
def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.add (BuilderRequestedPairLookup.rawTimePolynomial bound) (.constant 12))
    (Second.pairRawTimePolynomial (canonicalSpanPolynomial bound))
def spanPolynomial (bound : NatPolynomial) : NatPolynomial := .add bound (rawTimePolynomial bound)

private theorem canonical_span {width : Nat} (variables : List (Fin width)) (request : Request) (older : List Nat)
    (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (BuilderRequestedPairLookup.initialValues variables request older)).length + outside.length ≤ bound.eval input) :
    (registerWord (lookupValues variables request older)).length ≤ (canonicalSpanPolynomial bound).eval input := by
  have hPrep := BuilderRequestedPairLookup.preparation_polynomial_bounds variables request older outside bound input hSpan
  exact (BuilderExclusionPairLookup.source_polynomial_bounds variables.length (request.clauseIndex - 1)
    (BuilderRequestedPairLookup.initialValues variables request older) (BuilderPayloadBodyPreparation.spanPolynomial bound) input
    (by exact Nat.le_trans (Nat.le_add_right _ _) hPrep.1)).1

private theorem configuration_eq_of_state (configuration : WorkConfiguration) (state : Nat)
    (hState : configuration.state = state) : configuration = {state := state, tape := configuration.tape} := by
  cases configuration
  cases hState
  rfl
private theorem start_configuration (tape : WorkTape) :
    WorkMachineProgramGraph.endpointConfiguration (.node lookupNode.reference) tape =
      workStartConfiguration machine tape := rfl
private theorem accept_configuration (tape : WorkTape) :
    WorkMachineProgramGraph.endpointConfiguration .accept tape = {state := machine.acceptState, tape := tape} := rfl
private theorem reject_configuration (tape : WorkTape) :
    WorkMachineProgramGraph.endpointConfiguration .reject tape = {state := machine.rejectState, tape := tape} := rfl

/-- The actual count/index lookup and both actual variable reads are one fixed
execution, including real blank tails and all original-input polynomial costs. -/
theorem workRun_source_lookup_with_canonical_span {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hPositive : 0 < request.clauseIndex) (hBlank : BuilderRequestedPairLookup.BlankExterior outside)
    (hValid : request.clauseIndex - 1 < LocalConstraint.pairCount variables.length)
    (hSpan : (registerWord (BuilderRequestedPairLookup.initialValues variables request older)).length + outside.length ≤ bound.eval input) :
    ∃ (first second : Fin variables.length) (firstWritten secondWritten : List Nat) (steps : Nat) (final : WorkConfiguration),
      selectedPair variables.length (request.clauseIndex - 1) = some (first.val, second.val) ∧
      firstWritten.length = 7 ∧ secondWritten.length = 11 ∧
      workRunExact? machine steps
        (workStartConfiguration machine (endTape (BuilderRequestedPairLookup.initialValues variables request older) inside outside)) = some final ∧
      WorkConfiguration.BlankEquivalent final {
        state := machine.acceptState
        tape := endTape (lookupValues variables request older ++ firstWritten ++ [variables[first.val].val] ++
          secondWritten ++ [variables[second.val].val]) inside []
      } ∧
      (registerWord (lookupValues variables request older ++ firstWritten ++ [variables[first.val].val] ++
        secondWritten ++ [variables[second.val].val])).length ≤
          (Second.pairSpanPolynomial (canonicalSpanPolynomial bound)).eval input ∧
      BuilderRequestedPairLookup.storedCells final.tape ≤ inside.length + (spanPolynomial bound).eval input ∧
      6 * steps ≤ (rawTimePolynomial bound).eval input := by
  have hCanonicalSpan := canonical_span variables request older outside bound input hSpan
  obtain ⟨first, second, firstWritten, secondWritten, readSteps, hPair, hFirstWritten, hSecondWritten,
      hCanonicalRead, hReadSpan, hReadTime⟩ :=
    canonical_source_read variables request older inside (canonicalSpanPolynomial bound) input hValid hCanonicalSpan
  obtain ⟨middle, hLookup, hMiddleEquivalent, hAccept, _, _, hLookupTime⟩ :=
    BuilderRequestedPairLookup.workRun_polynomial_lookup variables request older inside outside bound input hPositive hBlank hSpan
  have hReadInitial : WorkConfiguration.BlankEquivalent
      (workStartConfiguration Second.pairMachine middle.tape)
      (workStartConfiguration Second.pairMachine (endTape (lookupValues variables request older) inside [])) := by
    refine ⟨rfl, ?_⟩
    have hTape := hMiddleEquivalent.tape
    rw [canonical_tape] at hTape
    exact hTape
  obtain ⟨readFinal, hReadActual, hReadEquivalent⟩ :=
    workRunExact?_transport Second.pairMachine readSteps hReadInitial hCanonicalRead
  have hLookupEnd : middle = {state := BuilderRequestedPairLookup.machine.acceptState, tape := middle.tape} :=
    configuration_eq_of_state middle _ (hAccept.mpr hValid)
  have hReadEnd : readFinal = {state := Second.pairMachine.acceptState, tape := readFinal.tape} :=
    configuration_eq_of_state readFinal _ hReadEquivalent.state
  rw [hLookupEnd] at hLookup
  rw [hReadEnd] at hReadActual
  have hReadPath := AcceptPath.step pairNode .accept _ 0 _ _ _ pair_mem hReadActual (.terminal .accept _)
  have hPath := AcceptPath.step lookupNode .accept _ _ _ _ _ lookup_mem hLookup hReadPath
  have hRun := WorkMachineProgramPath.runExact graph _ _ _ _ _ graph_wellFormed hPath
  rw [machine_projection, start_configuration, accept_configuration] at hRun
  let steps := BuilderRequestedPairLookup.workSteps variables request + 1 + (readSteps + 1)
  have hExecution : workRunExact? machine steps
      (workStartConfiguration machine (endTape (BuilderRequestedPairLookup.initialValues variables request older) inside outside)) =
      some {state := machine.acceptState, tape := readFinal.tape} := by
    simpa only [BuilderRequestedPairLookup.initialConfiguration, Nat.add_zero, steps] using hRun
  have hTime : 6 * steps ≤ (rawTimePolynomial bound).eval input := by
    simp only [steps, rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega
  refine ⟨first, second, firstWritten, secondWritten, steps, _, hPair, hFirstWritten, hSecondWritten,
    hExecution, ⟨rfl, hReadEquivalent.tape⟩, hReadSpan, ?_, hTime⟩
  have hCells := BuilderRequestedPairLookup.workRun_storedCells machine steps _ _ hExecution
  simp only [BuilderRequestedPairLookup.storedCells, workStartConfiguration, endTape,
    List.length_append, List.length_reverse] at hCells ⊢
  simp only [spanPolynomial, NatPolynomial.eval_add]
  omega

theorem workRun_source_lookup {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hPositive : 0 < request.clauseIndex) (hBlank : BuilderRequestedPairLookup.BlankExterior outside)
    (hValid : request.clauseIndex - 1 < LocalConstraint.pairCount variables.length)
    (hSpan : (registerWord (BuilderRequestedPairLookup.initialValues variables request older)).length + outside.length ≤ bound.eval input) :
    ∃ (first second : Fin variables.length) (firstWritten secondWritten : List Nat) (steps : Nat) (final : WorkConfiguration),
      selectedPair variables.length (request.clauseIndex - 1) = some (first.val, second.val) ∧
      firstWritten.length = 7 ∧ secondWritten.length = 11 ∧
      workRunExact? machine steps
        (workStartConfiguration machine (endTape (BuilderRequestedPairLookup.initialValues variables request older) inside outside)) = some final ∧
      WorkConfiguration.BlankEquivalent final {
        state := machine.acceptState
        tape := endTape (lookupValues variables request older ++ firstWritten ++ [variables[first.val].val] ++
          secondWritten ++ [variables[second.val].val]) inside []
      } ∧
      BuilderRequestedPairLookup.storedCells final.tape ≤ inside.length + (spanPolynomial bound).eval input ∧
      6 * steps ≤ (rawTimePolynomial bound).eval input := by
  obtain ⟨first, second, firstWritten, secondWritten, steps, final, hPair, hFirstWritten, hSecondWritten,
      hRun, hEquivalent, _, hSpace, hTime⟩ :=
    workRun_source_lookup_with_canonical_span variables request older inside outside bound input hPositive hBlank hValid hSpan
  exact ⟨first, second, firstWritten, secondWritten, steps, final, hPair, hFirstWritten, hSecondWritten,
    hRun, hEquivalent, hSpace, hTime⟩

theorem uniform_source_lookup {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hPositive : 0 < request.clauseIndex) (hBlank : BuilderRequestedPairLookup.BlankExterior outside)
    (hValid : request.clauseIndex - 1 < LocalConstraint.pairCount variables.length)
    (hSpan : (registerWord (BuilderRequestedPairLookup.initialValues variables request older)).length + outside.length ≤ bound.eval input) :
    ∃ (first second : Fin variables.length) (firstWritten secondWritten : List Nat) (rawSteps : Nat) (final : WorkConfiguration),
      selectedPair variables.length (request.clauseIndex - 1) = some (first.val, second.val) ∧
      firstWritten.length = 7 ∧ secondWritten.length = 11 ∧
      rawSteps ≤ (rawTimePolynomial bound).eval input ∧
      run (compileWorkMachine machine) rawSteps
        (encodeWorkConfiguration (workStartConfiguration machine
          (endTape (BuilderRequestedPairLookup.initialValues variables request older) inside outside))) =
        encodeWorkConfiguration final ∧
      WorkConfiguration.BlankEquivalent final {
        state := machine.acceptState
        tape := endTape (lookupValues variables request older ++ firstWritten ++ [variables[first.val].val] ++
          secondWritten ++ [variables[second.val].val]) inside []
      } ∧
      BuilderRequestedPairLookup.storedCells final.tape ≤ inside.length + (spanPolynomial bound).eval input := by
  obtain ⟨first, second, firstWritten, secondWritten, steps, final, hPair, hFirstWritten, hSecondWritten,
      hRun, hEquivalent, hSpace, hTime⟩ :=
    workRun_source_lookup variables request older inside outside bound input hPositive hBlank hValid hSpan
  exact ⟨first, second, firstWritten, secondWritten, 6 * steps, final, hPair, hFirstWritten, hSecondWritten,
    hTime, run_compileWorkMachine_mul_of_workRunExact _ _ _ _ hRun, hEquivalent, hSpace⟩

/-- Out-of-range pair requests reject before either variable reader executes. -/
theorem workRun_invalid_source_lookup {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hPositive : 0 < request.clauseIndex) (hBlank : BuilderRequestedPairLookup.BlankExterior outside)
    (hInvalid : LocalConstraint.pairCount variables.length ≤ request.clauseIndex - 1)
    (hSpan : (registerWord (BuilderRequestedPairLookup.initialValues variables request older)).length + outside.length ≤ bound.eval input) :
    ∃ steps final,
      workRunExact? machine steps
        (workStartConfiguration machine (endTape (BuilderRequestedPairLookup.initialValues variables request older) inside outside)) =
        some final ∧
      WorkConfiguration.BlankEquivalent final {
        state := machine.rejectState
        tape := endTape (lookupValues variables request older) inside []
      } ∧
      BuilderRequestedPairLookup.storedCells final.tape ≤ inside.length + (spanPolynomial bound).eval input ∧
      6 * steps ≤ (rawTimePolynomial bound).eval input := by
  obtain ⟨middle, hLookup, hEquivalent, _, hReject, _, hLookupTime⟩ :=
    BuilderRequestedPairLookup.workRun_polynomial_lookup variables request older inside outside bound input hPositive hBlank hSpan
  have hEnd : middle = {state := BuilderRequestedPairLookup.machine.rejectState, tape := middle.tape} :=
    configuration_eq_of_state middle _ (hReject.mpr hInvalid)
  rw [hEnd] at hLookup
  have hPath := AcceptPath.stepReject lookupNode .reject _ 0 _ _ _ lookup_mem hLookup (.terminal .reject _)
  have hRun := WorkMachineProgramPath.runExact graph _ _ _ _ _ graph_wellFormed hPath
  rw [machine_projection, start_configuration, reject_configuration] at hRun
  let steps := BuilderRequestedPairLookup.workSteps variables request + 1
  have hExecution : workRunExact? machine steps
      (workStartConfiguration machine (endTape (BuilderRequestedPairLookup.initialValues variables request older) inside outside)) =
      some {state := machine.rejectState, tape := middle.tape} := by
    simpa only [BuilderRequestedPairLookup.initialConfiguration, Nat.add_zero, steps] using hRun
  have hTime : 6 * steps ≤ (rawTimePolynomial bound).eval input := by
    simp only [steps, rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega
  refine ⟨steps, _, hExecution, ⟨rfl, ?_⟩, ?_, hTime⟩
  · have hTape := hEquivalent.tape
    rw [canonical_tape] at hTape
    exact hTape
  · have hCells := BuilderRequestedPairLookup.workRun_storedCells machine steps _ _ hExecution
    simp only [BuilderRequestedPairLookup.storedCells, workStartConfiguration, endTape,
      List.length_append, List.length_reverse] at hCells ⊢
    simp only [spanPolynomial, NatPolynomial.eval_add]
    omega

theorem uniform_invalid_source_lookup {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hPositive : 0 < request.clauseIndex) (hBlank : BuilderRequestedPairLookup.BlankExterior outside)
    (hInvalid : LocalConstraint.pairCount variables.length ≤ request.clauseIndex - 1)
    (hSpan : (registerWord (BuilderRequestedPairLookup.initialValues variables request older)).length + outside.length ≤ bound.eval input) :
    ∃ rawSteps final,
      rawSteps ≤ (rawTimePolynomial bound).eval input ∧
      run (compileWorkMachine machine) rawSteps
        (encodeWorkConfiguration (workStartConfiguration machine
          (endTape (BuilderRequestedPairLookup.initialValues variables request older) inside outside))) =
        encodeWorkConfiguration final ∧
      WorkConfiguration.BlankEquivalent final {
        state := machine.rejectState
        tape := endTape (lookupValues variables request older) inside []
      } ∧
      BuilderRequestedPairLookup.storedCells final.tape ≤ inside.length + (spanPolynomial bound).eval input := by
  obtain ⟨steps, final, hRun, hEquivalent, hSpace, hTime⟩ :=
    workRun_invalid_source_lookup variables request older inside outside bound input hPositive hBlank hInvalid hSpan
  exact ⟨6 * steps, final, hTime, run_compileWorkMachine_mul_of_workRunExact _ _ _ _ hRun, hEquivalent, hSpace⟩

end PNP.Concrete.CookLevin.BuilderRequestedPairVariables
