/-
Copyright (c) 2026 PNP Labs.

Read the current variable index from the actual source payload, construct its
literal width, and compare the physical residual position. The fixed finite
schema chooses only field layout, never an index value or a hit verdict.
The resulting seventeen-register chunk feeds the unchanged cursor machine.

Guarded source dispatch and the complete cyclic clause search remain to be
composed; a valid-ordinal source here is an intermediate physical-frame contract.
-/
import PNP.Concrete.CookLevinBuilderPayloadLiteralTokenSelector
import PNP.Concrete.CookLevinBuilderLiteralSearchFrame

namespace PNP.Concrete.CookLevin.BuilderPayloadSearchComparison

open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderPayloadLiteralTokenSelector (Kind Source Context stride valueSlot reader valueHistory)
open BuilderLiteralSearchFrame (widthExpression widthHistory comparisonResult comparisonHistory residual)
open PipelineStateNamespace (renameConfiguration)

def valueEnvironment (kind : Kind) (ordinal count position value : Nat) (index : Fin 9) : Nat :=
  match index.val with
  | 0 => ordinal
  | 1 => count
  | 2 => position
  | 3 => stride kind
  | 4 => ordinal
  | 5 => stride kind * ordinal
  | 6 => BuilderPayloadFieldCopy.offset (valueSlot kind) 2
  | 7 => BuilderPayloadFieldCopy.address (stride kind) (valueSlot kind) 2 ordinal
  | _ => value
def packedEnvironment (kind : Kind) (ordinal count position value : Nat) (index : Fin 12) : Nat :=
  match index.val with
  | 0 => ordinal
  | 1 => count
  | 2 => position
  | 3 => stride kind
  | 4 => ordinal
  | 5 => stride kind * ordinal
  | 6 => BuilderPayloadFieldCopy.offset (valueSlot kind) 2
  | 7 => BuilderPayloadFieldCopy.address (stride kind) (valueSlot kind) 2 ordinal
  | 8 | 9 => value
  | 10 => 2
  | _ => value + 2
def argumentFields : List (BuilderRegisterPack.Field 12) :=
  [.argument ⟨2, by decide⟩, .argument ⟨11, by decide⟩]
def preparationHistory (kind : Kind) (ordinal count position value : Nat) : List Nat :=
  [ordinal,count,position] ++ valueHistory kind ordinal value ++ widthHistory value
def chunk (kind : Kind) (ordinal count position value : Nat) : List Nat :=
  preparationHistory kind ordinal count position value ++ comparisonHistory position value
def cursorMiddle (kind : Kind) (ordinal position value : Nat) : List Nat :=
  [position] ++ valueHistory kind ordinal value ++ widthHistory value ++
    BuilderRegisterLessThan.resultValues (comparisonResult position value) ++ [value + 2]
def comparisonScratch (kind : Kind) (ordinal position value : Nat) : List Nat :=
  valueHistory kind ordinal value ++ widthHistory value ++ comparisonHistory position value

theorem valueEnvironment_values (kind : Kind) (ordinal count position value : Nat) :
    List.ofFn (valueEnvironment kind ordinal count position value) =
      [ordinal,count,position] ++ valueHistory kind ordinal value := rfl
theorem widthExpression_values (kind : Kind) (ordinal count position value : Nat) :
    BuilderRegisterExpression.values widthExpression (valueEnvironment kind ordinal count position value) =
      widthHistory value := rfl
theorem environment_values (kind : Kind) (ordinal count position value : Nat) :
    List.ofFn (packedEnvironment kind ordinal count position value) =
      preparationHistory kind ordinal count position value := rfl
theorem packed_values (kind : Kind) (ordinal count position value : Nat) :
    BuilderRegisterPack.values argumentFields (packedEnvironment kind ordinal count position value) =
      [position,value + 2] := rfl
theorem preparationHistory_length (kind : Kind) (ordinal count position value : Nat) :
    (preparationHistory kind ordinal count position value).length = 12 := rfl
theorem chunk_length (kind : Kind) (ordinal count position value : Nat) :
    (chunk kind ordinal count position value).length = 17 := by
  simp only [chunk, preparationHistory_length, List.length_append, comparisonHistory,
    BuilderRegisterCompareResidual.outputValues_length]
theorem comparisonScratch_length (kind : Kind) (ordinal position value : Nat) :
    (comparisonScratch kind ordinal position value).length = 14 := by
  simp only [comparisonScratch, BuilderPayloadLiteralTokenSelector.valueHistory_length, List.length_append,
    widthHistory, comparisonHistory, BuilderRegisterCompareResidual.outputValues_length, List.length_cons, List.length_nil]
theorem cursorMiddle_length (kind : Kind) (ordinal position value : Nat) :
    (cursorMiddle kind ordinal position value).length = 14 := by
  have h : (BuilderRegisterLessThan.resultValues (comparisonResult position value)).length = 3 := rfl
  simp only [cursorMiddle, BuilderPayloadLiteralTokenSelector.valueHistory_length, List.length_append,
    widthHistory, h, List.length_cons, List.length_nil]
theorem chunk_cursor_layout (kind : Kind) (ordinal count position value : Nat) :
    chunk kind ordinal count position value =
      [ordinal,count] ++ cursorMiddle kind ordinal position value ++ [residual position value] := by
  simp only [chunk, preparationHistory, cursorMiddle, comparisonHistory, BuilderRegisterCompareResidual.outputValues,
    comparisonResult, BuilderRegisterCompareResidual.resultBoundary_eq, BuilderRegisterCompareResidual.resultCoordinate_eq,
    residual, List.append_assoc, List.cons_append, List.nil_append]
theorem chunk_scratch_layout (kind : Kind) (ordinal count position value : Nat) :
    chunk kind ordinal count position value = [ordinal,count,position] ++ comparisonScratch kind ordinal position value := by
  simp only [chunk, preparationHistory, comparisonScratch, List.append_assoc]
theorem history_step (kind : Kind) (prior : List Nat) (ordinal count position value : Nat)
    (hPrior : prior.length = 17 * ordinal) :
    (prior ++ chunk kind ordinal count position value).length = 17 * (ordinal + 1) := by
  rw [List.length_append, chunk_length, hPrior, Nat.mul_add, Nat.mul_one]

def prepareMachine (kind : Kind) : WorkMachine :=
  WorkMachineChain.machine (BuilderPayloadFieldCopy.machine (stride kind) (valueSlot kind) 2)
    (WorkMachineChain.machine (BuilderRegisterExpression.machine widthExpression 0)
      (BuilderRegisterPack.machine argumentFields 0))
def machine (kind : Kind) : WorkMachine :=
  WorkMachineChain.machine (prepareMachine kind) BuilderRegisterCompareResidual.machine

def prepareSteps {width : Nat} (source : Source width) (context : Context source.ordinal) : Nat :=
  BuilderPayloadFieldCopy.workSteps (stride source.kind) (valueSlot source.kind) 2 source.ordinal
    [context.remaining,context.position] (reader source context) source.originalLiteral.index.val + 1 +
    (BuilderRegisterExpression.workSteps widthExpression
      (valueEnvironment source.kind source.ordinal context.remaining context.position source.originalLiteral.index.val) [] + 1 +
      BuilderRegisterPack.workSteps argumentFields
        (packedEnvironment source.kind source.ordinal context.remaining context.position source.originalLiteral.index.val) [])
def workSteps {width : Nat} (source : Source width) (context : Context source.ordinal) : Nat :=
  prepareSteps source context + 1 + BuilderRegisterCompareResidual.workSteps context.position (source.originalLiteral.index.val + 2)

def valueOutside {width : Nat} (source : Source width) (outside : List WorkSymbol) : List WorkSymbol :=
  BuilderPayloadLiteralTokenSelector.valueOutside source outside
def widthOutside {width : Nat} (source : Source width) (outside : List WorkSymbol) : List WorkSymbol :=
  (valueOutside source outside).drop (registerWord (widthHistory source.originalLiteral.index.val)).length
def prepareOutside {width : Nat} (source : Source width) (context : Context source.ordinal) (outside : List WorkSymbol) : List WorkSymbol :=
  (widthOutside source outside).drop (registerWord [context.position,source.originalLiteral.index.val + 2]).length
def finalOutside {width : Nat} (source : Source width) (context : Context source.ordinal) (outside : List WorkSymbol) : List WorkSymbol :=
  (prepareOutside source context outside).drop
    (BuilderRegisterCompareResidual.allocatedCells (comparisonResult context.position source.originalLiteral.index.val))

def baseValues {width : Nat} (source : Source width) (context : Context source.ordinal) (older : List Nat) : List Nat :=
  older ++ (reader source context).reverse
def initialValues {width : Nat} (source : Source width) (context : Context source.ordinal) (older : List Nat) : List Nat :=
  BuilderPayloadLiteralTokenSelector.initialValues source context older
def prepareOlder {width : Nat} (source : Source width) (context : Context source.ordinal) (older : List Nat) : List Nat :=
  baseValues source context older ++
    preparationHistory source.kind source.ordinal context.remaining context.position source.originalLiteral.index.val
def prepareTape {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) : WorkTape :=
  endTape (prepareOlder source context older ++ [context.position,source.originalLiteral.index.val + 2])
    inside (prepareOutside source context outside)
def finalValues {width : Nat} (source : Source width) (context : Context source.ordinal) (older : List Nat) : List Nat :=
  baseValues source context older ++ chunk source.kind source.ordinal context.remaining context.position source.originalLiteral.index.val
def initialConfiguration {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration (machine source.kind) (endTape (initialValues source context older) inside outside)
def finalConfiguration {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.secondState
    (BuilderRegisterCompareResidual.finalConfiguration context.position (source.originalLiteral.index.val + 2)
      (prepareOlder source context older) inside (prepareOutside source context outside))

private theorem chain_run (first second : WorkMachine) (n m : Nat) (initial middle final : WorkTape)
    (hFirst : workRunExact? first n (workStartConfiguration first initial) = some {state := first.acceptState, tape := middle})
    (hSecond : workRunExact? second m (workStartConfiguration second middle) = some {state := second.acceptState, tape := final}) :
    workRunExact? (WorkMachineChain.machine first second) (n + 1 + m)
      (workStartConfiguration (WorkMachineChain.machine first second) initial) =
      some {state := (WorkMachineChain.machine first second).acceptState, tape := final} :=
  WorkMachineChain.workRunExact first second n m _ _ _ hFirst rfl hSecond

/-- Derive both operands from actual source fields and the physical search frame. -/
theorem prepare_workRunExact {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (prepareMachine source.kind) (prepareSteps source context)
      (workStartConfiguration (prepareMachine source.kind) (endTape (initialValues source context older) inside outside)) =
      some {state := (prepareMachine source.kind).acceptState, tape := prepareTape source context older inside outside} := by
  let value := source.originalLiteral.index.val
  let base := baseValues source context older
  have hField := BuilderPayloadFieldCopy.workRunExact (stride source.kind) (valueSlot source.kind) 2 source.ordinal
    (reader source context) older [context.remaining,context.position] inside outside rfl
    (BuilderPayloadLiteralTokenSelector.value_field_lt source context)
  have hWidth := BuilderRegisterExpression.workRunExact widthExpression 0 base
    (valueEnvironment source.kind source.ordinal context.remaining context.position value) [] inside (valueOutside source outside) rfl
  have hPack := BuilderRegisterPack.workRunExact argumentFields 0 base
    (packedEnvironment source.kind source.ordinal context.remaining context.position value) [] inside (widthOutside source outside) rfl
  have hLast : workRunExact? (BuilderRegisterPack.machine argumentFields 0)
      (BuilderRegisterPack.workSteps argumentFields (packedEnvironment source.kind source.ordinal context.remaining context.position value) [])
      (workStartConfiguration (BuilderRegisterPack.machine argumentFields 0)
        (endTape (prepareOlder source context older) inside (widthOutside source outside))) =
      some {state := (BuilderRegisterPack.machine argumentFields 0).acceptState, tape := prepareTape source context older inside outside} := by
    simpa only [BuilderRegisterPack.initialConfiguration, BuilderRegisterPack.finalConfiguration, environment_values, packed_values,
      List.append_nil, prepareOlder, prepareTape, prepareOutside, base, value] using hPack
  have hSecond : workRunExact? (BuilderRegisterExpression.machine widthExpression 0)
      (BuilderRegisterExpression.workSteps widthExpression
        (valueEnvironment source.kind source.ordinal context.remaining context.position value) [])
      (workStartConfiguration (BuilderRegisterExpression.machine widthExpression 0)
        (endTape (base ++ [source.ordinal,context.remaining,context.position] ++ valueHistory source.kind source.ordinal value)
          inside (valueOutside source outside))) =
      some {state := (BuilderRegisterExpression.machine widthExpression 0).acceptState, tape := endTape (prepareOlder source context older) inside (widthOutside source outside)} := by
    simpa only [BuilderRegisterExpression.initialConfiguration, BuilderRegisterExpression.finalConfiguration,
      valueEnvironment_values, widthExpression_values, List.append_nil, List.append_assoc,
      preparationHistory, prepareOlder, widthOutside, base, value] using hWidth
  have hRest := chain_run _ _ _ _ _ _ _ hSecond hLast
  have hFirst : workRunExact? (BuilderPayloadFieldCopy.machine (stride source.kind) (valueSlot source.kind) 2)
      (BuilderPayloadFieldCopy.workSteps (stride source.kind) (valueSlot source.kind) 2 source.ordinal
        [context.remaining,context.position] (reader source context) value)
      (workStartConfiguration (BuilderPayloadFieldCopy.machine (stride source.kind) (valueSlot source.kind) 2)
        (endTape (initialValues source context older) inside outside)) =
      some {state := (BuilderPayloadFieldCopy.machine (stride source.kind) (valueSlot source.kind) 2).acceptState, tape := endTape (base ++ [source.ordinal,context.remaining,context.position] ++ valueHistory source.kind source.ordinal value) inside (valueOutside source outside)} := by
    simpa only [BuilderPayloadLiteralTokenSelector.value_field, BuilderPayloadFieldCopy.initialConfiguration,
      BuilderPayloadFieldCopy.finalConfiguration, BuilderPayloadFieldCopy.initialValues, BuilderPayloadFieldCopy.finalValues,
      initialValues, BuilderPayloadLiteralTokenSelector.initialValues, baseValues, base, value,
      valueHistory, valueOutside, BuilderPayloadLiteralTokenSelector.valueOutside,
      List.append_assoc, List.cons_append, List.nil_append] using hField
  exact chain_run _ _ _ _ _ _ _ hFirst hRest

theorem workRunExact {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (machine source.kind) (workSteps source context) (initialConfiguration source context older inside outside) =
      some (finalConfiguration source context older inside outside) := by
  have hPrepare := prepare_workRunExact source context older inside outside
  have hCompare := BuilderRegisterCompareResidual.workRunExact context.position (source.originalLiteral.index.val + 2)
    (prepareOlder source context older) inside (prepareOutside source context outside)
  exact WorkMachineChain.workRunExact _ _ _ _ _ _ _ hPrepare rfl hCompare

theorem run_compile_exact {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine (machine source.kind)) (6 * workSteps source context)
      (encodeWorkConfiguration (initialConfiguration source context older inside outside)) =
      encodeWorkConfiguration (finalConfiguration source context older inside outside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact source context older inside outside)

theorem final_accept_iff {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration source context older inside outside).state = (machine source.kind).acceptState ↔
      context.position < source.originalLiteral.index.val + 2 := by
  change WorkMachineChain.secondState (BuilderRegisterCompareResidual.finalConfiguration context.position
      (source.originalLiteral.index.val + 2) (prepareOlder source context older) inside (prepareOutside source context outside)).state =
    WorkMachineChain.secondState BuilderRegisterCompareResidual.machine.acceptState ↔ _
  constructor
  · intro h
    exact (BuilderRegisterCompareResidual.final_accept_iff context.position (source.originalLiteral.index.val + 2) _ inside _).1
      (WorkMachineChain.secondState_injective h)
  · intro h
    exact congrArg WorkMachineChain.secondState
      ((BuilderRegisterCompareResidual.final_accept_iff context.position (source.originalLiteral.index.val + 2) _ inside _).2 h)

theorem final_reject_iff {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration source context older inside outside).state = (machine source.kind).rejectState ↔
      source.originalLiteral.index.val + 2 ≤ context.position := by
  change WorkMachineChain.secondState (BuilderRegisterCompareResidual.finalConfiguration context.position
      (source.originalLiteral.index.val + 2) (prepareOlder source context older) inside (prepareOutside source context outside)).state =
    WorkMachineChain.secondState BuilderRegisterCompareResidual.machine.rejectState ↔ _
  constructor
  · intro h
    exact (BuilderRegisterCompareResidual.final_reject_iff context.position (source.originalLiteral.index.val + 2) _ inside _).1
      (WorkMachineChain.secondState_injective h)
  · intro h
    exact congrArg WorkMachineChain.secondState
      ((BuilderRegisterCompareResidual.final_reject_iff context.position (source.originalLiteral.index.val + 2) _ inside _).2 h)

theorem final_tape {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration source context older inside outside).tape =
      endTape (finalValues source context older) inside (finalOutside source context outside) := by
  change BuilderRegisterCompareResidual.outputTape (comparisonResult context.position source.originalLiteral.index.val)
    (prepareOlder source context older) inside (prepareOutside source context outside) = _
  simp only [BuilderRegisterCompareResidual.outputTape, finalValues, finalOutside, prepareOlder, chunk, comparisonHistory, List.append_assoc]

theorem finalOutside_length_le {width : Nat} (source : Source width) (context : Context source.ordinal) (outside : List WorkSymbol) :
    (finalOutside source context outside).length ≤ outside.length := by
  simp only [finalOutside, prepareOutside, widthOutside, valueOutside, BuilderPayloadLiteralTokenSelector.valueOutside, List.length_drop]
  omega

theorem final_span_le_initial_add_chunk {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (outside : List WorkSymbol) :
    (registerWord (finalValues source context older)).length + (finalOutside source context outside).length ≤
      (registerWord (initialValues source context older)).length + outside.length +
        (registerWord (chunk source.kind source.ordinal context.remaining context.position source.originalLiteral.index.val)).length := by
  have hOutside := finalOutside_length_le source context outside
  simp only [finalValues, initialValues, BuilderPayloadLiteralTokenSelector.initialValues, baseValues,
    registerWord_append, List.length_append]
  omega

theorem chunk_word_le_old_add_thirty (kind : Kind) (ordinal count position value : Nat) :
    (registerWord (chunk kind ordinal count position value)).length ≤
      (registerWord (BuilderLiteralSearchFrame.chunk ordinal count position value)).length + 30 := by
  cases kind <;>
    simp only [chunk, preparationHistory, BuilderLiteralSearchFrame.chunk,
      valueHistory, BuilderLiteralSearchFrame.valueHistory, BuilderPayloadFieldCopy.scratch, BuilderPayloadFieldCopy.scratchPrefix,
      BuilderPayloadFieldCopy.offset, BuilderPayloadFieldCopy.address, stride, valueSlot,
      BuilderLiteralSearchFrame.fieldStride, BuilderLiteralSearchFrame.historyStride,
      registerWord_length, List.length_append, List.sum_append, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil] <;> omega


private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineChain.QueryDistinct ∧ WorkMachineChain.NoRuleAtAccept program ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧ program.acceptState ≠ program.rejectState
private theorem chain_good (first second : WorkMachine) (hFirst : Good first) (hSecond : Good second) :
    Good (WorkMachineChain.machine first second) :=
  ⟨WorkMachineChain.rules_pairwise_query_distinct _ _ hFirst.1 hSecond.1 hFirst.2.1,
   WorkMachineChain.noRuleAtAccept _ _ hSecond.2.1,
   WorkMachineChain.noRuleAtAccept first {second with acceptState := second.rejectState} hSecond.2.2.1,
   WorkMachineChain.machine_acceptState_ne_rejectState _ _ hSecond.2.2.2⟩
private theorem field_good (kind : Kind) : Good (BuilderPayloadFieldCopy.machine (stride kind) (valueSlot kind) 2) :=
  ⟨BuilderPayloadFieldCopy.rules_pairwise_query_distinct _ _ _, BuilderPayloadFieldCopy.noRuleAtAccept _ _ _,
   BuilderPayloadFieldCopy.noRuleAtReject _ _ _, BuilderPayloadFieldCopy.acceptState_ne_rejectState _ _ _⟩
private theorem width_good : Good (BuilderRegisterExpression.machine widthExpression 0) :=
  ⟨BuilderRegisterExpression.rules_pairwise_query_distinct _ _, BuilderRegisterExpression.noRuleAtAccept _ _,
   BuilderRegisterExpression.noRuleAtReject _ _, BuilderRegisterExpression.acceptState_ne_rejectState _ _⟩
private theorem pack_good : Good (BuilderRegisterPack.machine argumentFields 0) :=
  ⟨BuilderRegisterPack.rules_pairwise_query_distinct _ _, BuilderRegisterPack.noRuleAtAccept _ _,
   BuilderRegisterPack.noRuleAtReject _ _, BuilderRegisterPack.acceptState_ne_rejectState _ _⟩
private theorem compare_good : Good BuilderRegisterCompareResidual.machine :=
  ⟨BuilderRegisterCompareResidual.rules_pairwise_query_distinct, BuilderRegisterCompareResidual.noRuleAtAccept,
   BuilderRegisterCompareResidual.noRuleAtReject, BuilderRegisterCompareResidual.acceptState_ne_rejectState⟩
private theorem prepare_good (kind : Kind) : Good (prepareMachine kind) :=
  chain_good _ _ (field_good kind) (chain_good _ _ width_good pack_good)
private theorem good (kind : Kind) : Good (machine kind) := chain_good _ _ (prepare_good kind) compare_good

theorem rules_pairwise_query_distinct (kind : Kind) : (machine kind).rules.Pairwise WorkMachineChain.QueryDistinct := (good kind).1
theorem noRuleAtAccept (kind : Kind) : WorkMachineChain.NoRuleAtAccept (machine kind) := (good kind).2.1
theorem noRuleAtReject (kind : Kind) : WorkMachineProgramGraph.NoRuleAt (machine kind) (machine kind).rejectState := (good kind).2.2.1
theorem acceptState_ne_rejectState (kind : Kind) : (machine kind).acceptState ≠ (machine kind).rejectState := (good kind).2.2.2

def valueSpanPolynomial (kind : Kind) (bound : NatPolynomial) : NatPolynomial :=
  BuilderPayloadFieldCopy.spanPolynomial (stride kind) (valueSlot kind) 2 bound
def widthSpanPolynomial (kind : Kind) (bound : NatPolynomial) : NatPolynomial :=
  .add (BuilderRegisterExpression.spanPolynomial widthExpression (valueSpanPolynomial kind bound)) (valueSpanPolynomial kind bound)
def prepareSpanPolynomial (kind : Kind) (bound : NatPolynomial) : NatPolynomial :=
  .add (BuilderRegisterPack.spanPolynomial argumentFields (widthSpanPolynomial kind bound)) (widthSpanPolynomial kind bound)
def spanPolynomial (kind : Kind) (bound : NatPolynomial) : NatPolynomial :=
  .add (BuilderRegisterCompareResidual.spanPolynomial (prepareSpanPolynomial kind bound)) (prepareSpanPolynomial kind bound)
def prepareRawTimePolynomial (kind : Kind) (bound : NatPolynomial) : NatPolynomial :=
  .add (.add (BuilderPayloadFieldCopy.rawTimePolynomial (stride kind) (valueSlot kind) 2 bound) (.constant 6))
    (.add (.add (BuilderRegisterExpression.rawTimePolynomial widthExpression (valueSpanPolynomial kind bound)) (.constant 6))
      (BuilderRegisterPack.rawTimePolynomial argumentFields (widthSpanPolynomial kind bound)))
def rawTimePolynomial (kind : Kind) (bound : NatPolynomial) : NatPolynomial :=
  .add (.add (prepareRawTimePolynomial kind bound) (.constant 6))
    (BuilderRegisterCompareResidual.rawTimePolynomial (prepareSpanPolynomial kind bound))

theorem prepare_source_polynomial_bounds {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues source context older)).length + outside.length ≤ bound.eval input) :
    (registerWord (prepareOlder source context older ++ [context.position,source.originalLiteral.index.val + 2])).length +
      (prepareOutside source context outside).length ≤ (prepareSpanPolynomial source.kind bound).eval input ∧
    6 * prepareSteps source context ≤ (prepareRawTimePolynomial source.kind bound).eval input := by
  let value := source.originalLiteral.index.val
  let base := baseValues source context older
  have hInitial : (registerWord (BuilderPayloadFieldCopy.initialValues (reader source context) older source.ordinal
      [context.remaining,context.position])).length + outside.length ≤ bound.eval input := by
    simpa only [initialValues, BuilderPayloadLiteralTokenSelector.initialValues, BuilderPayloadFieldCopy.initialValues,
      List.append_assoc, List.cons_append, List.nil_append] using hSpan
  have hValue := BuilderPayloadFieldCopy.source_polynomial_bounds (stride source.kind) (valueSlot source.kind) 2 source.ordinal
    (reader source context) older [context.remaining,context.position] outside bound input rfl
    (BuilderPayloadLiteralTokenSelector.value_field_lt source context) hInitial
  simp only [BuilderPayloadLiteralTokenSelector.value_field] at hValue
  have hAfterValue : (registerWord (base ++ [source.ordinal,context.remaining,context.position] ++
      valueHistory source.kind source.ordinal value)).length + (valueOutside source outside).length ≤
      (valueSpanPolynomial source.kind bound).eval input := by
    simpa only [BuilderPayloadFieldCopy.finalValues, BuilderPayloadFieldCopy.initialValues,
      valueOutside, BuilderPayloadLiteralTokenSelector.valueOutside, valueSpanPolynomial,
      valueHistory, base, baseValues, value, List.append_assoc, List.cons_append, List.nil_append] using hValue.1
  have hWidthInput : (registerWord (base ++ List.ofFn
      (valueEnvironment source.kind source.ordinal context.remaining context.position value) ++ [])).length ≤
      (valueSpanPolynomial source.kind bound).eval input := by
    simpa only [valueEnvironment_values, List.append_nil, List.append_assoc] using Nat.le_trans (Nat.le_add_right _ _) hAfterValue
  have hWidth := BuilderRegisterExpression.source_polynomial_bounds widthExpression (valueSpanPolynomial source.kind bound)
    input base (valueEnvironment source.kind source.ordinal context.remaining context.position value) [] hWidthInput
  simp only [valueEnvironment_values, widthExpression_values, List.append_nil, List.append_assoc] at hWidth
  have hAfterWidth : (registerWord (prepareOlder source context older)).length + (widthOutside source outside).length ≤
      (widthSpanPolynomial source.kind bound).eval input := by
    have hExterior : (valueOutside source outside).length ≤ (valueSpanPolynomial source.kind bound).eval input := by omega
    simp only [widthSpanPolynomial, NatPolynomial.eval_add, widthOutside, List.length_drop, prepareOlder, preparationHistory, List.append_assoc]
    change (registerWord (base ++ ([source.ordinal,context.remaining,context.position] ++
      (valueHistory source.kind source.ordinal value ++ widthHistory value)))).length + _ ≤ _
    omega
  have hPackInput : (registerWord (base ++ List.ofFn
      (packedEnvironment source.kind source.ordinal context.remaining context.position value) ++ [])).length ≤
      (widthSpanPolynomial source.kind bound).eval input := by
    rw [environment_values, List.append_nil]
    exact Nat.le_trans (Nat.le_add_right _ _) hAfterWidth
  have hPack := BuilderRegisterPack.source_polynomial_bounds argumentFields (widthSpanPolynomial source.kind bound) input base
    (packedEnvironment source.kind source.ordinal context.remaining context.position value) [] hPackInput
  simp only [environment_values, packed_values, List.append_nil] at hPack
  constructor
  · have hExterior : (widthOutside source outside).length ≤ (widthSpanPolynomial source.kind bound).eval input := by omega
    simp only [prepareSpanPolynomial, NatPolynomial.eval_add, prepareOutside, List.length_drop]
    change (registerWord ((base ++ preparationHistory source.kind source.ordinal context.remaining context.position value) ++
      [context.position,value + 2])).length +
      ((widthOutside source outside).length - (registerWord [context.position,value + 2]).length) ≤ _
    omega
  · simp only [prepareSteps, prepareRawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    dsimp only [value] at hPack hValue hWidth ⊢
    omega

theorem source_polynomial_bounds {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues source context older)).length + outside.length ≤ bound.eval input) :
    (registerWord (finalValues source context older)).length + (finalOutside source context outside).length ≤
      (spanPolynomial source.kind bound).eval input ∧
    6 * workSteps source context ≤ (rawTimePolynomial source.kind bound).eval input := by
  have hPrepare := prepare_source_polynomial_bounds source context older outside bound input hSpan
  have hCompare := BuilderRegisterCompareResidual.source_polynomial_bounds context.position (source.originalLiteral.index.val + 2)
    (prepareOlder source context older) (prepareSpanPolynomial source.kind bound) input (Nat.le_trans (Nat.le_add_right _ _) hPrepare.1)
  constructor
  · have hExterior : (prepareOutside source context outside).length ≤ (prepareSpanPolynomial source.kind bound).eval input := by omega
    have hOutput : (registerWord (finalValues source context older)).length ≤
        (BuilderRegisterCompareResidual.spanPolynomial (prepareSpanPolynomial source.kind bound)).eval input := by
      simpa only [finalValues, prepareOlder, chunk, comparisonHistory, comparisonResult, List.append_assoc] using hCompare.1
    simp only [spanPolynomial, NatPolynomial.eval_add, finalOutside, List.length_drop]
    omega
  · simp only [workSteps, rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

end PNP.Concrete.CookLevin.BuilderPayloadSearchComparison
