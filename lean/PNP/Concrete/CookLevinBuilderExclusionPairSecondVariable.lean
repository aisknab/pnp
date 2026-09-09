/-
Copyright (c) 2026 PNP Labs.

Read the second selected variable from the retained exactly-one payload.
The actual comparison residual accounts for both variable-length row history
and all fixed first/second-read scratch. Control is independent of the source
variables, selected pair, history length and arithmetic results.

The complete pair-value lookup preserves both actual source values and rejects
invalid clause ordinals before entering the readers. Literal tokens, source
request/recovery and the complete formula builder remain separate obligations.
-/

import PNP.Concrete.CookLevinBuilderExclusionPairFirstVariable

namespace PNP.Concrete.CookLevin.BuilderExclusionPairSecondVariable

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderArbitrarySlotHeaderRouter
open BuilderExclusionPairFirstVariable (firstIndex secondIndex rowWidth rowOffset)
open BuilderRegisterExpression (Expr)
open WorkMachineProgramGraph (Node Graph Endpoint)
open WorkMachineProgramPath (AcceptPath)

/-- The first reader leaves seven expression registers and its copied source value. -/
def firstHistory (environment : Fin 9 → Nat) (firstValue : Nat) : List Nat :=
  BuilderExclusionPairFirstVariable.scratch environment ++ [firstValue]

def upperExpression : Expr 9 :=
  .binary .add
    (.binary .add (.binary .mul (.constant 10) (.argument ⟨7, by decide⟩))
      (.argument ⟨3, by decide⟩))
    (.constant 45)
def offsetExpression : Expr 9 := .argument ⟨8, by decide⟩
def upper (environment : Fin 9 → Nat) : Nat := 10 * rowWidth environment + firstIndex environment + 45
def upperPrefix (environment : Fin 9 → Nat) : List Nat :=
  [10, rowWidth environment, 10 * rowWidth environment, firstIndex environment,
    10 * rowWidth environment + firstIndex environment, 45]
def upperScratch (environment : Fin 9 → Nat) : List Nat := upperPrefix environment ++ [upper environment]
def comparisonResult (environment : Fin 9 → Nat) : RawRouter.ComparisonResult :=
  RawRouter.compareResult 0 (upper environment) (rowOffset environment)
def address (environment : Fin 9 → Nat) : Nat := 9 * rowWidth environment + secondIndex environment + 45
def comparisonPrefix (environment : Fin 9 → Nat) : List Nat :=
  BuilderRegisterLessThan.resultValues (comparisonResult environment) ++ [rowOffset environment]
def scratchPrefix (environment : Fin 9 → Nat) : List Nat := upperPrefix environment ++ comparisonPrefix environment
def scratch (environment : Fin 9 → Nat) : List Nat := scratchPrefix environment ++ [address environment]

theorem firstHistory_length (environment : Fin 9 → Nat) (firstValue : Nat) :
    (firstHistory environment firstValue).length = 8 := by
  rw [firstHistory, List.length_append, BuilderExclusionPairFirstVariable.scratch_length]
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
  BuilderExclusionPairFirstVariable.initialValues payload older history environment ++ firstHistory environment firstValue
def preparedValues (payload older history : List Nat) (environment : Fin 9 → Nat) (firstValue : Nat) : List Nat :=
  initialValues payload older history environment firstValue ++ upperPrefix environment ++ [upper environment, rowOffset environment]
def finalValues (payload older history : List Nat) (environment : Fin 9 → Nat) (firstValue secondValue : Nat) : List Nat :=
  initialValues payload older history environment firstValue ++ scratch environment ++ [secondValue]

theorem after_first_values (payload older history : List Nat) (environment : Fin 9 → Nat) (firstValue : Nat) :
    initialValues payload older history environment firstValue =
      BuilderExclusionPairFirstVariable.finalValues payload older history environment firstValue := by
  simp only [initialValues, firstHistory, BuilderExclusionPairFirstVariable.finalValues, List.append_assoc]

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
      upper_values, initialValues, BuilderExclusionPairFirstVariable.initialValues, List.drop_nil] using hUpper
  have hSecond : workRunExact? (BuilderRegisterExpression.machine offsetExpression 15)
      (BuilderRegisterExpression.workSteps offsetExpression environment (firstHistory environment firstValue ++ upperScratch environment))
      (workStartConfiguration (BuilderRegisterExpression.machine offsetExpression 15)
        (endTape (initialValues payload older history environment firstValue ++ upperScratch environment) inside [])) =
      some {
        state := (BuilderRegisterExpression.machine offsetExpression 15).acceptState
        tape := endTape (preparedValues payload older history environment firstValue) inside [] } := by
    simpa only [BuilderRegisterExpression.initialConfiguration, BuilderRegisterExpression.finalConfiguration,
      offset_values, preparedValues, initialValues, BuilderExclusionPairFirstVariable.initialValues,
      upperScratch, List.drop_nil, List.append_assoc, List.cons_append, List.nil_append] using hOffset
  exact chain_run _ _ _ _ _ _ _ hFirst hSecond

def reader (payload history : List Nat) (environment : Fin 9 → Nat) (firstValue : Nat) : List Nat :=
  (scratchPrefix environment).reverse ++ (firstHistory environment firstValue).reverse ++
    (List.ofFn environment).reverse ++ history.reverse ++ payload

theorem reader_address_lt (payload history : List Nat) (environment : Fin 9 → Nat) (firstValue : Nat)
    (hHistory : history.length = 18 + 9 * rowWidth environment)
    (hField : secondIndex environment < payload.length) :
    address environment < (reader payload history environment firstValue).length := by
  simp only [address, reader, List.length_append, List.length_reverse, scratchPrefix_length, firstHistory_length,
    List.length_ofFn, hHistory]
  omega

theorem reader_address_value (payload history : List Nat) (environment : Fin 9 → Nat) (firstValue : Nat)
    (hHistory : history.length = 18 + 9 * rowWidth environment)
    (hField : secondIndex environment < payload.length) :
    (reader payload history environment firstValue)[address environment]'
      (reader_address_lt payload history environment firstValue hHistory hField) = payload[secondIndex environment] := by
  have hNear : ((scratchPrefix environment).reverse ++ (firstHistory environment firstValue).reverse ++
      (List.ofFn environment).reverse ++ history.reverse).length = 45 + 9 * rowWidth environment := by
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
  simp only [reader, initialValues, BuilderExclusionPairFirstVariable.initialValues, scratch,
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
    (hHistory : history.length = 18 + 9 * rowWidth environment)
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
    (hHistory : history.length = 18 + 9 * rowWidth environment)
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
      BuilderExclusionPairFirstVariable.initialValues, upperScratch, List.append_assoc,
      List.cons_append, List.nil_append] using hOffset.1
  · have hUpperTime := hUpper.2
    have hOffsetTime := hOffset.2
    simp only [prepareSteps, preparedRawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

theorem source_polynomial_bounds (payload older history : List Nat) (environment : Fin 9 → Nat)
    (firstValue : Nat) (bound : NatPolynomial) (input : Nat)
    (hHistory : history.length = 18 + 9 * rowWidth environment)
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

def pairMachine : WorkMachine := WorkMachineChain.machine BuilderExclusionPairFirstVariable.machine machine
def pairSteps (payload history : List Nat) (environment : Fin 9 → Nat) (firstValue secondValue : Nat) : Nat :=
  BuilderExclusionPairFirstVariable.workSteps payload history environment firstValue + 1 +
    workSteps payload history environment firstValue secondValue
def pairSpanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  spanPolynomial (BuilderExclusionPairFirstVariable.spanPolynomial bound)
def pairRawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.add (BuilderExclusionPairFirstVariable.rawTimePolynomial bound) (.constant 6))
    (rawTimePolynomial (BuilderExclusionPairFirstVariable.spanPolynomial bound))

theorem pair_workRunExact (payload older history : List Nat) (environment : Fin 9 → Nat) (inside : List WorkSymbol)
    (hHistory : history.length = 18 + 9 * rowWidth environment)
    (hOffset : rowOffset environment < rowWidth environment)
    (hFirst : firstIndex environment < payload.length) (hSecond : secondIndex environment < payload.length) :
    workRunExact? pairMachine (pairSteps payload history environment payload[firstIndex environment] payload[secondIndex environment])
      (workStartConfiguration pairMachine
        (endTape (BuilderExclusionPairFirstVariable.initialValues payload older history environment) inside [])) =
      some {
        state := pairMachine.acceptState
        tape := endTape (finalValues payload older history environment payload[firstIndex environment] payload[secondIndex environment]) inside [] } := by
  have hReadFirst := BuilderExclusionPairFirstVariable.workRunExact payload older history environment inside [] hHistory hFirst
  simp only [BuilderExclusionPairFirstVariable.initialConfiguration, BuilderExclusionPairFirstVariable.finalConfiguration,
    ← after_first_values, List.drop_nil] at hReadFirst
  have hReadSecond := workRunExact payload older history environment payload[firstIndex environment] inside hHistory hOffset hSecond
  exact chain_run _ _ _ _ _ _ _ hReadFirst hReadSecond

theorem pair_polynomial_bounds (payload older history : List Nat) (environment : Fin 9 → Nat)
    (bound : NatPolynomial) (input : Nat)
    (hHistory : history.length = 18 + 9 * rowWidth environment)
    (hOffset : rowOffset environment < rowWidth environment)
    (hFirst : firstIndex environment < payload.length) (hSecond : secondIndex environment < payload.length)
    (hSpan : (registerWord (BuilderExclusionPairFirstVariable.initialValues payload older history environment)).length ≤ bound.eval input) :
    (registerWord (finalValues payload older history environment payload[firstIndex environment] payload[secondIndex environment])).length ≤
      (pairSpanPolynomial bound).eval input ∧
    6 * pairSteps payload history environment payload[firstIndex environment] payload[secondIndex environment] ≤
      (pairRawTimePolynomial bound).eval input := by
  have hReadFirst := BuilderExclusionPairFirstVariable.source_polynomial_bounds payload older history environment []
    bound input hHistory hFirst (by simpa only [List.length_nil, Nat.add_zero] using hSpan)
  have hMiddle : (registerWord (initialValues payload older history environment payload[firstIndex environment])).length ≤
      (BuilderExclusionPairFirstVariable.spanPolynomial bound).eval input := by
    simpa only [← after_first_values, List.drop_nil, List.length_nil, Nat.add_zero] using hReadFirst.1
  have hReadSecond := source_polynomial_bounds payload older history environment payload[firstIndex environment]
    (BuilderExclusionPairFirstVariable.spanPolynomial bound) input hHistory hOffset hSecond hMiddle
  refine ⟨hReadSecond.1, ?_⟩
  have hFirstTime := hReadFirst.2
  have hSecondTime := hReadSecond.2
  simp only [pairSteps, pairRawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
  omega

private theorem pair_good : Good pairMachine :=
  chain_good _ _
    ⟨BuilderExclusionPairFirstVariable.rules_pairwise_query_distinct,
      BuilderExclusionPairFirstVariable.noRuleAtAccept, BuilderExclusionPairFirstVariable.noRuleAtReject,
      BuilderExclusionPairFirstVariable.acceptState_ne_rejectState⟩
    ⟨rules_pairwise_query_distinct, noRuleAtAccept, noRuleAtReject, acceptState_ne_rejectState⟩

def pairNode : Node := {name := 1, program := pairMachine, onAccept := .accept, onReject := .dead}
def lookupNode : Node :=
  {name := 0, program := BuilderExclusionPairLookup.machine, onAccept := .node pairNode.reference, onReject := .reject}
def lookupGraph : Graph := {nodes := [lookupNode, pairNode], entry := lookupNode.reference}
def lookupMachine : WorkMachine := WorkMachineProgramGraph.machine lookupGraph
private theorem lookup_mem : lookupNode ∈ lookupGraph.nodes := List.Mem.head _
private theorem pair_mem : pairNode ∈ lookupGraph.nodes := List.Mem.tail _ (List.Mem.head _)

theorem lookupGraph_nodes_length : lookupGraph.nodes.length = 2 := rfl
theorem lookupGraph_wellFormed : lookupGraph.WellFormed := by
  have hNames : (lookupGraph.nodes.map Node.name).Pairwise (fun left right : Nat => left ≠ right) := by
    change ([0, 1] : List Nat).Pairwise _
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.pairwise_map] using hNames
  · intro node hMem
    simp only [lookupGraph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl
    · exact ⟨BuilderExclusionPairLookup.rules_pairwise_query_distinct,
        BuilderExclusionPairLookup.noRuleAtAccept, BuilderExclusionPairLookup.noRuleAtReject,
        BuilderExclusionPairLookup.acceptState_ne_rejectState⟩
    · exact pair_good
  · exact ⟨lookupNode, lookup_mem, rfl, rfl⟩
  · intro node hMem
    simp only [lookupGraph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl
    · exact ⟨⟨pairNode, pair_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, True.intro⟩

theorem lookup_rules_pairwise_query_distinct : lookupMachine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise lookupGraph lookupGraph_wellFormed
theorem lookup_noRuleAtAccept : WorkMachineProgramGraph.NoRuleAt lookupMachine lookupMachine.acceptState :=
  WorkMachineProgramGraph.noRuleAt_globalAccept lookupGraph
theorem lookup_noRuleAtReject : WorkMachineProgramGraph.NoRuleAt lookupMachine lookupMachine.rejectState :=
  WorkMachineProgramGraph.noRuleAt_globalReject lookupGraph
theorem lookup_acceptState_ne_rejectState : lookupMachine.acceptState ≠ lookupMachine.rejectState := by
  change (0 : Nat) ≠ 1
  decide

def completeSpanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  pairSpanPolynomial (BuilderExclusionPairLookup.spanPolynomial bound)
def completeRawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.add (BuilderExclusionPairLookup.rawTimePolynomial bound) (.constant 12))
    (pairRawTimePolynomial (BuilderExclusionPairLookup.spanPolynomial bound))

private theorem lookup_start_configuration (tape : WorkTape) :
    WorkMachineProgramGraph.endpointConfiguration (.node lookupNode.reference) tape =
      workStartConfiguration lookupMachine tape := rfl
private theorem lookup_accept_configuration (tape : WorkTape) :
    WorkMachineProgramGraph.endpointConfiguration .accept tape = {state := lookupMachine.acceptState, tape := tape} := rfl
private theorem lookup_reject_configuration (tape : WorkTape) :
    WorkMachineProgramGraph.endpointConfiguration .reject tape = {state := lookupMachine.rejectState, tape := tape} := rfl

/-- All valid source ordinals physically yield both canonical source-variable values. -/
theorem uniform_source_lookup {width : Nat} (variables : List (Fin width)) (coordinate : Nat)
    (older : List Nat) (inside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hValid : coordinate < LocalConstraint.pairCount variables.length)
    (hSpan : (registerWord (older ++ BuilderExclusionPairFirstVariable.payloadValues variables ++
      [variables.length, coordinate])).length ≤ bound.eval input) :
    ∃ (first second : Fin variables.length) (firstWritten secondWritten : List Nat) (steps : Nat),
      BuilderExclusionPairSelection.selectedPair variables.length coordinate = some (first.val, second.val) ∧
      firstWritten.length = 7 ∧ secondWritten.length = 11 ∧
      run (compileWorkMachine lookupMachine) (6 * steps)
        (encodeWorkConfiguration (workStartConfiguration lookupMachine
          (endTape (older ++ BuilderExclusionPairFirstVariable.payloadValues variables ++
            [variables.length, coordinate]) inside []))) =
        encodeWorkConfiguration {
          state := lookupMachine.acceptState
          tape := endTape (BuilderExclusionPairFirstVariable.lookupValues variables coordinate older ++
            firstWritten ++ [variables[first.val].val] ++ secondWritten ++ [variables[second.val].val]) inside [] } ∧
      (registerWord (BuilderExclusionPairFirstVariable.lookupValues variables coordinate older ++
        firstWritten ++ [variables[first.val].val] ++ secondWritten ++ [variables[second.val].val])).length ≤
          (completeSpanPolynomial bound).eval input ∧
      6 * steps ≤ (completeRawTimePolynomial bound).eval input := by
  rcases BuilderExclusionPairFirstVariable.source_layout variables coordinate older hValid with
    ⟨first, second, environment, history, hPair, hFirst, hSecond, hOffset, hHistory, hLayout⟩
  have hFirstField : firstIndex environment < (BuilderLocalConstraintPayload.variableValues variables).length := by
    simpa only [hFirst, BuilderLocalConstraintPayload.variableValues, List.length_map] using first.isLt
  have hSecondField : secondIndex environment < (BuilderLocalConstraintPayload.variableValues variables).length := by
    simpa only [hSecond, BuilderLocalConstraintPayload.variableValues, List.length_map] using second.isLt
  have hFirstValue : (BuilderLocalConstraintPayload.variableValues variables)[firstIndex environment] = variables[first.val].val := by
    simp only [BuilderLocalConstraintPayload.variableValues, List.getElem_map, hFirst]
  have hSecondValue : (BuilderLocalConstraintPayload.variableValues variables)[secondIndex environment] = variables[second.val].val := by
    simp only [BuilderLocalConstraintPayload.variableValues, List.getElem_map, hSecond]
  have hLookupBounds := BuilderExclusionPairLookup.source_polynomial_bounds variables.length coordinate
    (older ++ BuilderExclusionPairFirstVariable.payloadValues variables) bound input hSpan
  have hPairBounds := pair_polynomial_bounds (BuilderLocalConstraintPayload.variableValues variables) older history environment
    (BuilderExclusionPairLookup.spanPolynomial bound) input hHistory hOffset hFirstField hSecondField
    (by simpa only [← hLayout, BuilderExclusionPairFirstVariable.lookupValues] using hLookupBounds.1)
  have hRead := pair_workRunExact (BuilderLocalConstraintPayload.variableValues variables) older history environment inside
    hHistory hOffset hFirstField hSecondField
  rw [hFirstValue, hSecondValue] at hRead hPairBounds
  have hLookup := BuilderExclusionPairLookup.workRunExact variables.length coordinate
    (older ++ BuilderExclusionPairFirstVariable.payloadValues variables) inside
  have hState := (BuilderExclusionPairLookup.final_accept_iff variables.length coordinate
    (older ++ BuilderExclusionPairFirstVariable.payloadValues variables) inside).mpr hValid
  have hTape := BuilderExclusionPairLookup.final_tape variables.length coordinate
    (older ++ BuilderExclusionPairFirstVariable.payloadValues variables) inside
  rw [configuration_eq_of_fields _ _ _ hState hTape] at hLookup
  simp only [← hLayout, BuilderExclusionPairFirstVariable.lookupValues] at hRead
  have hReadPath := AcceptPath.step pairNode .accept _ 0 _ _ _ pair_mem hRead (.terminal .accept _)
  have hPath := AcceptPath.step lookupNode .accept _ _ _ _ _ lookup_mem hLookup hReadPath
  have hRun := WorkMachineProgramPath.runExact lookupGraph _ _ _ _ _ lookupGraph_wellFormed hPath
  rw [lookup_start_configuration, lookup_accept_configuration] at hRun
  refine ⟨first, second, BuilderExclusionPairFirstVariable.scratch environment, scratch environment,
    BuilderExclusionPairLookup.workSteps variables.length coordinate + 1 +
      (pairSteps (BuilderLocalConstraintPayload.variableValues variables) history environment variables[first.val].val variables[second.val].val + 1),
    hPair, BuilderExclusionPairFirstVariable.scratch_length environment, scratch_length environment, ?_, ?_, ?_⟩
  · have hRaw := run_compileWorkMachine_mul_of_workRunExact _ _ _ _ hRun
    simpa only [Nat.add_zero, lookupMachine, finalValues, initialValues, firstHistory, ← hLayout,
      BuilderExclusionPairFirstVariable.lookupValues, List.append_assoc] using hRaw
  · simpa only [completeSpanPolynomial, finalValues, initialValues, firstHistory, ← hLayout,
      List.append_assoc] using hPairBounds.1
  · have hLookupTime := hLookupBounds.2
    have hReadTime := hPairBounds.2
    simp only [completeRawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

/-- Invalid ordinals reject at the lookup node, without running either variable reader. -/
theorem invalid_source_lookup {width : Nat} (variables : List (Fin width)) (coordinate : Nat)
    (older : List Nat) (inside : List WorkSymbol)
    (hInvalid : LocalConstraint.pairCount variables.length ≤ coordinate) :
    run (compileWorkMachine lookupMachine) (6 * (BuilderExclusionPairLookup.workSteps variables.length coordinate + 1))
      (encodeWorkConfiguration (workStartConfiguration lookupMachine
        (endTape (older ++ BuilderExclusionPairFirstVariable.payloadValues variables ++ [variables.length, coordinate]) inside []))) =
      encodeWorkConfiguration {
        state := lookupMachine.rejectState
        tape := endTape (BuilderExclusionPairFirstVariable.lookupValues variables coordinate older) inside [] } := by
  have hLookup := BuilderExclusionPairLookup.workRunExact variables.length coordinate
    (older ++ BuilderExclusionPairFirstVariable.payloadValues variables) inside
  have hState := (BuilderExclusionPairLookup.final_reject_iff variables.length coordinate
    (older ++ BuilderExclusionPairFirstVariable.payloadValues variables) inside).mpr hInvalid
  have hTape := BuilderExclusionPairLookup.final_tape variables.length coordinate
    (older ++ BuilderExclusionPairFirstVariable.payloadValues variables) inside
  rw [configuration_eq_of_fields _ _ _ hState hTape] at hLookup
  have hPath := AcceptPath.stepReject lookupNode .reject _ 0 _ _ _ lookup_mem hLookup (.terminal .reject _)
  have hRun := WorkMachineProgramPath.runExact lookupGraph _ _ _ _ _ lookupGraph_wellFormed hPath
  rw [lookup_start_configuration, lookup_reject_configuration] at hRun
  have hRaw := run_compileWorkMachine_mul_of_workRunExact _ _ _ _ hRun
  simpa only [Nat.add_zero, lookupMachine, BuilderExclusionPairFirstVariable.lookupValues] using hRaw


theorem uniform_invalid_source_lookup {width : Nat} (variables : List (Fin width)) (coordinate : Nat)
    (older : List Nat) (inside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hInvalid : LocalConstraint.pairCount variables.length ≤ coordinate)
    (hSpan : (registerWord (older ++ BuilderExclusionPairFirstVariable.payloadValues variables ++
      [variables.length, coordinate])).length ≤ bound.eval input) :
    ∃ rawSteps, rawSteps ≤ (NatPolynomial.add (BuilderExclusionPairLookup.rawTimePolynomial bound) (.constant 6)).eval input ∧
      run (compileWorkMachine lookupMachine) rawSteps
        (encodeWorkConfiguration (workStartConfiguration lookupMachine
          (endTape (older ++ BuilderExclusionPairFirstVariable.payloadValues variables ++ [variables.length, coordinate]) inside []))) =
        encodeWorkConfiguration {
          state := lookupMachine.rejectState
          tape := endTape (BuilderExclusionPairFirstVariable.lookupValues variables coordinate older) inside [] } ∧
      (registerWord (BuilderExclusionPairFirstVariable.lookupValues variables coordinate older)).length ≤
        (BuilderExclusionPairLookup.spanPolynomial bound).eval input := by
  have hBounds := BuilderExclusionPairLookup.source_polynomial_bounds variables.length coordinate
    (older ++ BuilderExclusionPairFirstVariable.payloadValues variables) bound input hSpan
  refine ⟨6 * (BuilderExclusionPairLookup.workSteps variables.length coordinate + 1), ?_,
    invalid_source_lookup variables coordinate older inside hInvalid, hBounds.1⟩
  have hTime := hBounds.2
  simp only [NatPolynomial.eval_add, NatPolynomial.eval_constant]
  omega

end PNP.Concrete.CookLevin.BuilderExclusionPairSecondVariable
